(** * NbE Invents No Variables

    Normalizing a weakened term in the extended context never mentions the
    new variable: if [M[↑]] is normalized in [Γ ▹ A], its normal form is
    fresh at [#0] ([nbe_wk_fresh]).  Evaluation builds no variable, so a
    value can only mention a variable its environment holds; and readback
    introduces only variables above the ones in scope.

    The invariant is [domain_avoids v b d]: the value [d] mentions no de Bruijn level
    [v], and only levels below [b].  It cannot be stated on environments
    alone: the environment of the extended context holds the new variable,
    at index [0], and so does every closure built in it.  What makes the
    value fresh is that the weakened term never *reads* that index.  So a
    closure records one position [K] of its environment that may be bad,
    together with the freshness of its body at that position, shifted by the
    closure's binders.  [K = None] is a closure whose environment avoids [v]
    everywhere.

    The proof is structural, in the pattern of [Core.Semantic.Stuck]
    ([domain_stuck]); readback is where the level arithmetic happens: a variable at
    level [x] reads back at length [n] as the index [n - x - 1], which is not
    [n - v - 1] when [x <> v] and both are below [n]. *)
From Stdlib Require Import Arith Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE.
From Mctt.Core.Syntactic Require Import Fresh Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
Import Domain_Notations Syntax_Notations Wk_Notations.

Create HintDb avoid.

(** ** Freshness at an Optional Position *)

Definition optional_shift (j : nat) (K : option nat) : option nat := option_map (Nat.add j) K.

Lemma optional_shift_optional_shift : forall i j K, optional_shift i (optional_shift j K) = optional_shift (i + j) K.
Proof. intros i j []; cbn; [ f_equal; lia | reflexivity ]. Qed.

Lemma optional_shift_zero : forall K, optional_shift 0 K = K.
Proof. intros []; reflexivity. Qed.

Definition optional_exp_fresh (K : option nat) (M : exp) : Prop :=
  match K with None => True | Some k => exp_fresh k M end.
Definition optional_modexp_fresh (K : option nat) (H : modexp) : Prop :=
  match K with None => True | Some k => modexp_fresh k H end.
Definition optional_gunit_fresh (K : option nat) (U : gunit) : Prop :=
  match K with None => True | Some k => gunit_fresh k U end.
Definition optional_gmod_fresh (K : option nat) (Φ : gmod) : Prop :=
  match K with None => True | Some k => gmod_fresh k Φ end.

(** The components of a shape, each under the domains before it. *)
Fixpoint optional_ptyp_fresh (K : option nat) (t : ptyp) : Prop :=
  match t with
  | pt_pi B t => optional_exp_fresh K B /\ optional_ptyp_fresh (optional_shift 1 K) t
  | pt_self _ Ps => Forall (optional_exp_fresh K) Ps
  end.

Lemma optional_ptyp_fresh_none : forall t, optional_ptyp_fresh None t.
Proof.
  induction t as [? Ps | B t IH]; cbn; [ apply Forall_forall; intros; exact I | split; [ exact I | exact IH ] ].
Qed.

(** The blocks of an eliminator: each motive fresh under the binders it
    has, and so is each branch under its own.  (The annotations are never
    evaluated.) *)
Definition blocks_optional_exp_fresh (K : option nat) (Bks : list eblock) : Prop :=
  forall b, In b Bks -> optional_exp_fresh (optional_shift (eb_binder_count b) K) (eb_motive b) /\
    (forall c n B, In (c, n, B) (eb_brs b) -> optional_exp_fresh (optional_shift n K) B).

Lemma blocks_optional_exp_fresh_none : forall Bks, blocks_optional_exp_fresh None Bks.
Proof. intros Bks b _; split; [ exact I | intros; exact I ]. Qed.

(** ** The Invariant

    The invariant follows the record views of the groups an eliminator is
    of, so it is over a global context, fixed for the rest of the file. *)

Section Global.
  Variables (Θ : gdeps) (Ξ : gstack).

(** [ends_fresh p Km As t]: at every end of the leaf paths of the shape
    [t] of the group at [p], through its record views' fields, the motive
    of the member the path ends in, among [As], is fresh at [Km] under as
    many binders as the end's parameters and the argument: the motives the
    types of the recursive results along [t] are evaluated at
    ([eval_ihty]).  It is what the family of a recursive result's type
    keeps of its eliminator's blocks ([domain_avoids_ihfam]). *)
Inductive ends_fresh (p : qname) (Km : option nat) (As : list exp) : ptyp -> Prop :=
(** At a member with a block: its motive, under the end's parameters and
    the argument *)
| ends_fresh_self : forall D j Mj Ps, ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> im_is_rview Mj = false ->
    optional_exp_fresh (optional_shift (S (List.length Ps)) Km) (List.nth j As a_prop) -> ends_fresh p Km As (pt_self j Ps)
(** At a record view: every recursive field's shape, of its one
    constructor *)
| ends_fresh_rview : forall D j Mj qr Is fl Ps, ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl ->
    (forall c gs gs1 t gs2, im_cons Mj = (c, gs) :: nil -> gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p Km As t) ->
    ends_fresh p Km As (pt_self j Ps)
(** At a function shape: the rest's *)
| ends_fresh_pi : forall B t, ends_fresh p Km As t -> ends_fresh p Km As (pt_pi B t).

Section Avoid.
  Variables (v b : nat).

  (** [domain_avoids d]: the value [d] mentions no level [v], and only levels below
      [b] (see the file header); mutually, for neutrals, normal values,
      module values, level atoms and environment entries. *)
  Inductive domain_avoids : domain -> Prop :=
  (** A [Π] at any kinds: its domain avoids, and its closure avoids but at
      [K], where the codomain is fresh *)
  | domain_avoids_pi : forall κd κc a (ρ : env) B K,
      domain_avoids a ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_exp_fresh (optional_shift 1 K) B ->
      domain_avoids (d_pi κd κc a ρ B)
  (** A large universe *)
  | domain_avoids_univ : forall i, domain_avoids 𝕌ω@i
  (** A small universe at an avoiding level *)
  | domain_avoids_suniv : forall l, domain_avoids l -> domain_avoids 𝕌@l
  (** A type of levels *)
  | domain_avoids_level : forall n, domain_avoids (Levelᵈ@n)
  (** The sort of the types of levels *)
  | domain_avoids_level_sort : domain_avoids LevelSortᵈ
  (** A level of avoiding atoms *)
  | domain_avoids_lvl : forall c xs, level_atoms_avoid xs -> domain_avoids (lvᵈ c xs)
  (** [Prop] *)
  | domain_avoids_prop : domain_avoids Propᵈ
  (** The true proposition *)
  | domain_avoids_True : domain_avoids ⊤ᵈ
  (** A kept proof, whatever its term and environment: proofs are exempt,
      as their readback is compared only up to erasure *)
  | domain_avoids_proof : forall M (ρ : env), domain_avoids ⋆ᵈ⟨M, ρ⟩
  (** The false proposition *)
  | domain_avoids_False : domain_avoids ⊥ᵈ
  (** A [Σₚ], as a [Π] *)
  | domain_avoids_and : forall a (ρ : env) Q K,
      domain_avoids a ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_exp_fresh (optional_shift 1 K) Q ->
      domain_avoids (Σₚᵈ a ρ Q)
  (** A λ: its domain avoids, and its closure avoids but at [K], where the
      body is fresh *)
  | domain_avoids_fn : forall a (ρ : env) M K,
      domain_avoids a ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_exp_fresh (optional_shift 1 K) M ->
      domain_avoids (λᵈ a ρ M)
  (** A neutral at an avoiding type *)
  | domain_avoids_neut : forall a m, domain_avoids a -> domain_ne_avoids m -> domain_avoids (⇑ a m)
  (** A member of an avoiding module value *)
  | domain_avoids_member : forall h ch, dmod_avoids h -> domain_avoids (d_member h ch)
  (** A type former at avoiding arguments *)
  | domain_avoids_indty : forall p k args, (forall a, In a args -> domain_avoids a) -> domain_avoids (d_ind p k args)
  (** A constructor at avoiding arguments *)
  | domain_avoids_con : forall p k c args, (forall a, In a args -> domain_avoids a) -> domain_avoids (d_con p k c args)
  (** The recursive result of a function shape: the eliminator's closure,
      as [domain_avoids_elim], and the argument. *)
  | domain_avoids_ihfn : forall (ρ : env) Bks p ups t i f K,
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      blocks_optional_exp_fresh K Bks ->
      (forall a, In a ups -> domain_avoids a) ->
      domain_avoids f ->
      domain_avoids (d_ihfn ρ Bks p ups t i f)
  (** The families of a function shape: the shape's rest is fresh under the
      domain the family binds; the motive, under the shape's parameters and
      the argument.  The domain [B] is only the type the argument is stored
      at, read by a kept proof's readback alone. *)
  | domain_avoids_shfam : forall p ups (ρ : env) B t K,
      (forall a, In a ups -> domain_avoids a) ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_ptyp_fresh (optional_shift 1 K) t ->
      domain_avoids (d_shfam p ups ρ B t)
  (** The family of a recursive result at a function shape: the motives
      fresh at the rest's ends ([ends_fresh]), the group's uniform
      parameters (over which its record views' fields are) avoiding, the
      shape's rest fresh, the argument avoiding *)
  | domain_avoids_ihfam : forall (ρm : env) As p ups (ρ : env) B t i f Km K,
      (forall x, Km <> Some x -> dentry_avoids (env_entry ρm x)) ->
      ends_fresh p Km As t ->
      (forall a, In a ups -> domain_avoids a) ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_ptyp_fresh (optional_shift 1 K) t ->
      domain_avoids f ->
      domain_avoids (d_ihfam ρm As p ups ρ B t i f)
  (** A record type former at avoiding arguments *)
  | domain_avoids_record : forall p args, (forall a, In a args -> domain_avoids a) -> domain_avoids (d_record p args)
  (** A tuple of avoiding fields *)
  | domain_avoids_tuple : forall vs, (forall f a, In (f, a) vs -> domain_avoids a) -> domain_avoids (d_tuple vs)
  with domain_ne_avoids : domain_ne -> Prop :=
  (** A variable other than [v], below [b] *)
  | domain_avoids_var : forall x, x <> v -> x < b -> domain_ne_avoids (#ᵈ x)
  (** An application of an avoiding neutral to an avoiding normal value *)
  | domain_avoids_app : forall m n, domain_ne_avoids m -> domain_nf_avoids n -> domain_ne_avoids (m $ᵈ n)
  (** Ex falso at an avoiding type; its proof is a proof *)
  | domain_avoids_absurd : forall c p, domain_avoids c -> domain_ne_avoids (d_absurd c p)
  (** A global *)
  | domain_avoids_glob : forall p, domain_ne_avoids (d_glob p)
  (** A stuck eliminator: the motives are fresh under their binders, and so
      is each branch under its own. *)
  | domain_avoids_elim : forall (ρ : env) Bks p ups j args m K,
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      blocks_optional_exp_fresh K Bks ->
      (forall a, In a ups -> domain_avoids a) ->
      (forall a, In a args -> domain_avoids a) ->
      domain_ne_avoids m ->
      domain_ne_avoids (d_elim ρ Bks p ups j args m)
  (** The field of an avoiding neutral *)
  | domain_avoids_proj : forall f m, domain_ne_avoids m -> domain_ne_avoids (d_proj f m)
  with domain_nf_avoids : domain_nf -> Prop :=
  | domain_avoids_dom : forall a m, domain_avoids a -> domain_avoids m -> domain_nf_avoids (⇓ a m)
  with dmod_avoids : dmod -> Prop :=
  | dmod_avoids_global : forall p args, (forall a, In a args -> domain_avoids a) -> dmod_avoids (dm_global p args)
  | dmod_avoids_local : forall Δ D (ρ : env) K,
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_gunit_fresh K (gu_mk Δ D) ->
      dmod_avoids (dm_local Δ D ρ)
  | dmod_avoids_member : forall h ch, dmod_avoids h -> dmod_avoids (dm_member h ch)
  with level_atoms_avoid : list (nat * nat * domain_ne) -> Prop :=
  | level_atoms_avoid_nil : level_atoms_avoid nil
  | level_atoms_avoid_cons : forall k n m xs, domain_ne_avoids m -> level_atoms_avoid xs -> level_atoms_avoid ((k, n, m) :: xs)
  (** The entries: their values.  The types and units they are stored at
      are read only by a kept proof's readback, a proof. *)
  with dentry_avoids : dentry -> Prop :=
  (** A term: its value *)
  | dentry_avoids_term : forall d t, domain_avoids d -> dentry_avoids (de_term d t)
  (** A module slot: its module value *)
  | dentry_avoids_mod : forall h U, dmod_avoids h -> dentry_avoids (de_mod h U)
  (** A term with a module part: both avoid *)
  | dentry_avoids_dm : forall d t h U, domain_avoids d -> dmod_avoids h -> dentry_avoids (de_dm d t h U).

  (** An environment that avoids at every position but [K]. *)
  Definition env_avoids (K : option nat) (ρ : env) : Prop :=
    forall x, K <> Some x -> dentry_avoids (env_entry ρ x).

  (** The uniform parameters an eliminator carries.  A definition, so that
      the search does not use it as a lemma about every value. *)
  Definition ups_avoids (ups : list domain) : Prop := forall a, In a ups -> domain_avoids a.
End Avoid.

Scheme domain_avoids_mind := Induction for domain_avoids Sort Prop
  with domain_ne_avoids_mind := Induction for domain_ne_avoids Sort Prop
  with domain_nf_avoids_mind := Induction for domain_nf_avoids Sort Prop
  with dmod_avoids_mind := Induction for dmod_avoids Sort Prop
  with level_atoms_avoid_mind := Induction for level_atoms_avoid Sort Prop
  with dentry_avoids_mind := Induction for dentry_avoids Sort Prop.
Combined Scheme domain_avoids_mut_ind from domain_avoids_mind, domain_ne_avoids_mind, domain_nf_avoids_mind, dmod_avoids_mind, level_atoms_avoid_mind, dentry_avoids_mind.

#[local] Hint Constructors domain_avoids domain_ne_avoids domain_nf_avoids dmod_avoids level_atoms_avoid dentry_avoids : mctt.

(** The bound only grows. *)
Lemma domain_avoids_mono : forall v b,
    (forall d, domain_avoids v b d -> forall b', b <= b' -> domain_avoids v b' d) /\
    (forall m, domain_ne_avoids v b m -> forall b', b <= b' -> domain_ne_avoids v b' m) /\
    (forall n, domain_nf_avoids v b n -> forall b', b <= b' -> domain_nf_avoids v b' n) /\
    (forall h, dmod_avoids v b h -> forall b', b <= b' -> dmod_avoids v b' h) /\
    (forall xs, level_atoms_avoid v b xs -> forall b', b <= b' -> level_atoms_avoid v b' xs) /\
    (forall e, dentry_avoids v b e -> forall b', b <= b' -> dentry_avoids v b' e).
Proof.
  intros v b.
  apply (domain_avoids_mut_ind v b
           (fun d _ => forall b', b <= b' -> domain_avoids v b' d)
           (fun m _ => forall b', b <= b' -> domain_ne_avoids v b' m)
           (fun n _ => forall b', b <= b' -> domain_nf_avoids v b' n)
           (fun h _ => forall b', b <= b' -> dmod_avoids v b' h)
           (fun xs _ => forall b', b <= b' -> level_atoms_avoid v b' xs)
           (fun e _ => forall b', b <= b' -> dentry_avoids v b' e));
    intros; econstructor; eauto; lia.
Qed.

Lemma env_avoids_mono : forall v b b' K ρ, b <= b' -> env_avoids v b K ρ -> env_avoids v b' K ρ.
Proof. intros * Hb H x Hx; eapply (proj2 (proj2 (proj2 (proj2 (proj2 (domain_avoids_mono v b)))))); eauto. Qed.

(** ** Environments *)
Section Env.
  Variables (v b : nat).

  Lemma env_avoids_nil : forall K, env_avoids v b K nil.
  Proof. intros K x _; induction x; cbn; [ repeat constructor | assumption ]. Qed.

  Lemma env_avoids_cons : forall K e ρ, env_avoids v b K ρ -> dentry_avoids v b e -> env_avoids v b (optional_shift 1 K) (e :: ρ).
  Proof.
    intros * Hρ He [| x] Hx; cbn; [ exact He |].
    apply Hρ; intros ->; apply Hx; reflexivity.
  Qed.

  (** The excluded entry: the head of the environment may be anything. *)
  Lemma env_avoids_cons_bad : forall e ρ, env_avoids v b None ρ -> env_avoids v b (Some 0) (e :: ρ).
  Proof.
    intros * Hρ [| x] Hx; cbn; [ contradiction Hx; reflexivity |].
    apply Hρ; discriminate.
  Qed.

  (** An environment extended by avoiding values, at any types. *)
  Lemma env_avoids_extend_typed : forall vts K ρ,
      env_avoids v b K ρ -> (forall a, In a (List.map fst vts) -> domain_avoids v b a) ->
      env_avoids v b (optional_shift (List.length vts) K) (env_extend_typed ρ vts).
  Proof.
    induction vts as [| vt vts IH]; intros * Hρ Ha; cbn; [ rewrite optional_shift_zero; exact Hρ |].
    replace (S (List.length vts)) with (List.length vts + 1) by lia.
    rewrite <- optional_shift_optional_shift.
    apply IH; [ apply env_avoids_cons; [ exact Hρ | constructor; apply Ha; left; reflexivity ]
              | intros; apply Ha; right; assumption ].
  Qed.

  (** An environment that avoids [v] everywhere, extended. *)
  Lemma env_avoids_cons_none : forall ρ d t, env_avoids v b None ρ -> domain_avoids v b d -> env_avoids v b None (ρ ↦ d ⦂ t).
  Proof. intros; change (@None nat) with (optional_shift 1 None); apply env_avoids_cons; [ assumption | constructor; assumption ]. Qed.

  Lemma env_avoids_extend_typed_none : forall vts ρ,
      env_avoids v b None ρ -> (forall a, In a (List.map fst vts) -> domain_avoids v b a) -> env_avoids v b None (env_extend_typed ρ vts).
  Proof.
    intros; change (@None nat) with (optional_shift (List.length vts) None); apply env_avoids_extend_typed; assumption.
  Qed.

  (** An environment extended at a telescope by avoiding values. *)
  Lemma env_avoids_env_tele_none : forall ρ T vs,
      env_avoids v b None ρ -> (forall a, In a vs -> domain_avoids v b a) -> env_avoids v b None (env_tele ρ T vs).
  Proof. intros * Hρ Hv; unfold env_tele; apply env_avoids_extend_typed_none; [ exact Hρ | rewrite tele_entries_values; exact Hv ]. Qed.

  (** Pads are [absent_entry]: [Prop] at no type. *)
  Lemma env_avoids_kinds_pads : forall n K ρ, env_avoids v b K ρ -> env_avoids v b (optional_shift n K) (kinds_pads n ρ).
  Proof.
    unfold kinds_pads; induction n as [| n IH]; intros K ρ Hρ; cbn; [ rewrite optional_shift_zero; exact Hρ |].
    replace (S n) with (1 + n) by lia; rewrite <- optional_shift_optional_shift.
    apply env_avoids_cons; [ apply IH; exact Hρ | repeat constructor ].
  Qed.

  Lemma env_avoids_var : forall K ρ x, env_avoids v b K ρ -> K <> Some x -> domain_avoids v b (ρ x).
  Proof.
    intros * H Hx; unfold env_var; destruct (H x Hx); [ assumption | repeat constructor | assumption ].
  Qed.

  Lemma env_avoids_mod : forall K ρ x, env_avoids v b K ρ -> K <> Some x -> dmod_avoids v b (env_mod ρ x).
  Proof.
    intros * H Hx; unfold env_mod; destruct (H x Hx); [| assumption | assumption ].
    constructor; intros ? [].
  Qed.

  (** The atoms of a level value avoid [v] when the value does. *)
  Lemma level_atoms_avoid_view : forall d, domain_avoids v b d -> level_atoms_avoid v b (domain_level_atoms d).
  Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

  Lemma level_atoms_avoid_suc : forall xs, level_atoms_avoid v b xs -> level_atoms_avoid v b (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
  Proof. induction 1; cbn; repeat constructor; assumption. Qed.

  Lemma level_atoms_avoid_app : forall xs ys, level_atoms_avoid v b xs -> level_atoms_avoid v b ys -> level_atoms_avoid v b (xs ++ ys).
  Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

  Lemma domain_avoids_lvl_suc : forall d, domain_avoids v b d -> domain_avoids v b (domain_level_suc d).
  Proof. intros; unfold domain_level_suc; constructor; apply level_atoms_avoid_suc, level_atoms_avoid_view; assumption. Qed.

  Lemma domain_avoids_lvl_max : forall d e, domain_avoids v b d -> domain_avoids v b e -> domain_avoids v b (domain_level_max d e).
  Proof. intros; unfold domain_level_max; constructor; apply level_atoms_avoid_app; apply level_atoms_avoid_view; assumption. Qed.

  Lemma dmod_avoids_global_nil : forall p, dmod_avoids v b (dm_global p nil).
  Proof. intros; constructor; intros ? []. Qed.

  Lemma domain_avoids_args_snoc : forall (args : list domain) n,
      (forall a, In a args -> domain_avoids v b a) -> domain_avoids v b n -> forall a, In a (args ++ n :: nil) -> domain_avoids v b a.
  Proof. intros * H Hn a Ha; apply in_app_or in Ha as [Ha | [<- | []]]; auto. Qed.
End Env.

(** ** Freshness Through the Module Syntax *)

Lemma modexp_spine_fresh : forall H k R args pre,
    modexp_spine H = (R, args, pre) ->
    modexp_fresh k H ->
    modexp_fresh k R /\ Forall (exp_fresh k) args.
Proof.
  induction H; intros * Hs Hf; cbn in Hs, Hf;
    try (inversion Hs; subst; split; [ assumption | constructor ]).
  - destruct (modexp_spine H) as [[R0 args0] pre0] eqn:E; inversion Hs; subst.
    exact (IHmodexp _ _ _ _ eq_refl Hf).
  - destruct (modexp_spine H) as [[R0 args0] pre0] eqn:E; inversion Hs; subst.
    destruct Hf as [HH HN].
    destruct (IHmodexp _ _ _ _ eq_refl HH) as [HR Ha].
    split; [ assumption | apply Forall_app; split; [ assumption | constructor; [ assumption | constructor ] ] ].
Qed.

Lemma prefix_upto_fresh : forall Φ x Φ0 k,
    gm_prefix_upto Φ x = Some Φ0 ->
    gmod_fresh k Φ ->
    gmod_fresh k Φ0.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hp Hf; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb x y); [ inversion Hp; subst; exact Hf |].
    cbn in Hf; destruct Hf; eapply IH; eassumption.
  - destruct (existsb _ _); [ discriminate |].
    cbn in Hf; destruct Hf; eapply IH; eassumption.
Qed.

Lemma optional_exp_fresh_prefix_upto : forall Φ x Φ0 K,
    gm_prefix_upto Φ x = Some Φ0 -> optional_gmod_fresh K Φ -> optional_gmod_fresh K Φ0.
Proof. intros * Hp; destruct K; cbn; [ eapply prefix_upto_fresh; eassumption | auto ]. Qed.

(** A body with the entries of another after it is fresh where both are,
    the other past the body's binders. *)
Lemma gmod_fresh_graft : forall Φg Φ k, gmod_fresh k Φ -> gmod_fresh (gm_binders Φ + k) Φg -> gmod_fresh k (gm_graft Φ Φg).
Proof.
  induction Φg as [| Φg IH x E | Φg IH H its Φgg _]; intros * HΦ Hg; cbn in Hg |- *; [ exact HΦ | |].
  - destruct Hg as [Hg HE]; split; [ apply IH; assumption |].
    rewrite gm_binders_graft; replace (gm_binders Φg + gm_binders Φ + k) with (gm_binders Φg + (gm_binders Φ + k)) by lia; exact HE.
  - destruct Hg as (Hg & HH & Hgg); split; [ apply IH; assumption |].
    rewrite gm_binders_graft; replace (gm_binders Φg + gm_binders Φ + k) with (gm_binders Φg + (gm_binders Φ + k)) by lia.
    split; assumption.
Qed.

(** A body with its local opens replaced by the entries they store is
    fresh where the body is ([gm_expand]). *)
Lemma gmod_fresh_expand : forall Φ k, gmod_fresh k Φ -> gmod_fresh k (gm_expand Φ).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg IHg]; intros k Hf; cbn in Hf |- *; [ exact I | |].
  - destruct Hf as [Hf HE]; split; [ apply IH; exact Hf | rewrite gm_binders_expand; exact HE ].
  - destruct Hf as (Hf & _ & Hg); apply gmod_fresh_graft; [ apply IH; exact Hf |].
    rewrite gm_binders_expand; apply IHg; exact Hg.
Qed.

Lemma optional_gmod_fresh_expand : forall K Φ, optional_gmod_fresh K Φ -> optional_gmod_fresh K (gm_expand Φ).
Proof. intros [k |] Φ; cbn; [ apply gmod_fresh_expand | auto ]. Qed.

Lemma optional_gunit_fresh_expand : forall K U, optional_gunit_fresh K U -> optional_gunit_fresh K (gunit_expand U).
Proof.
  intros [k |] [Δ [sm Φ | E]]; cbn; [| auto | auto | auto ].
  intros [HΔ HΦ]; split; [ exact HΔ | apply gmod_fresh_expand; exact HΦ ].
Qed.

(** A unit lacking one parameter fewer, the parameter now a variable. *)
Lemma optional_gunit_fresh_snoc : forall K Δ e D, optional_gunit_fresh K (gu_mk (Δ ++ e :: nil) D) -> optional_gunit_fresh (optional_shift 1 K) (gu_mk Δ D).
Proof.
  intros [k |] * H; cbn in H |- *; [| exact I ].
  destruct H as [HΔ HD]; split.
  - clear HD; induction Δ as [| e' Δ IH]; cbn in HΔ |- *; [ exact I |].
    destruct HΔ as [He HΔ]; rewrite List.length_app in He; cbn in He.
    split; [ replace (List.length Δ + S k) with (List.length Δ + 1 + k) by lia; exact He | exact (IH HΔ) ].
  - rewrite List.length_app in HD; cbn in HD; replace (List.length Δ + S k) with (List.length Δ + 1 + k) by lia; exact HD.
Qed.

(** The parts of a fresh compound, each at the position its binders shift
    to.  Stated at an optional position, so that one lemma serves both the
    environment with a bad position and the one without. *)
Section OFresh.
  Variable K : option nat.

  Lemma optional_exp_fresh_univ : forall M, optional_exp_fresh K Type⟨M⟩ -> optional_exp_fresh K M.
  Proof. destruct K; cbn; auto. Qed.
  Lemma optional_exp_fresh_succl : forall M, optional_exp_fresh K (succl M) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; auto. Qed.
  Lemma optional_exp_fresh_maxl_l : forall M N, optional_exp_fresh K (maxl M N) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_maxl_r : forall M N, optional_exp_fresh K (maxl M N) -> optional_exp_fresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_absurd_type : forall C M, optional_exp_fresh K (efq M return C) -> optional_exp_fresh K C.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_absurd_proof : forall C M, optional_exp_fresh K (efq M return C) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_and_left : forall P Q, optional_exp_fresh K (Σₚ P Q) -> optional_exp_fresh K P.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_and_right : forall P Q, optional_exp_fresh K (Σₚ P Q) -> optional_exp_fresh (optional_shift 1 K) Q.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_fn_A : forall A M, optional_exp_fresh K (λ A M) -> optional_exp_fresh K A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_pi_A : forall κd κc A B, optional_exp_fresh K (a_pi κd κc A B) -> optional_exp_fresh K A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_pi_B : forall κd κc A B, optional_exp_fresh K (a_pi κd κc A B) -> optional_exp_fresh (optional_shift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_fn_M : forall A M, optional_exp_fresh K (λ A M) -> optional_exp_fresh (optional_shift 1 K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_app_l : forall M N, optional_exp_fresh K (M $ N) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_app_r : forall M N, optional_exp_fresh K (M $ N) -> optional_exp_fresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_let_A : forall A M B, optional_exp_fresh K (a_let (b_def A M) B) -> optional_exp_fresh K A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_tuple_T : forall T fs, optional_exp_fresh K (a_tuple T fs) -> optional_exp_fresh K T.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_let_M : forall A M B, optional_exp_fresh K (a_let (b_def A M) B) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_let_B : forall bd B, optional_exp_fresh K (a_let bd B) -> optional_exp_fresh (optional_shift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_letmod_U : forall U B, optional_exp_fresh K (a_let (b_mod U) B) -> optional_gunit_fresh K U.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_mem : forall H x, optional_exp_fresh K (a_mem H x) -> optional_modexp_fresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_elim_blocks : forall r oq oUs j Bks M, optional_exp_fresh K (a_elim r oq oUs j Bks M) -> blocks_optional_exp_fresh K Bks.
  Proof.
    destruct K as [k |]; cbn; [| intros; apply blocks_optional_exp_fresh_none ].
    intros r oq oUs j Bks M H; apply (proj1 (exp_fresh_elim _ r oq oUs j Bks M)) in H as [_ [H _]]; unfold blocks_fresh in H.
    induction Bks as [| [nm oZ A Bs] Bks IH]; intros b Hb; [ destruct Hb |].
    cbn [all_blocks] in H; destruct H as [(_ & HA & HBs) HBks].
    destruct Hb as [<- | Hb]; [| exact (IH HBks _ Hb) ].
    cbn [eb_binder_count eb_motive eb_brs optional_shift option_map optional_exp_fresh]; split; [ exact HA |].
    intros c n B Hin; apply all_brs_Forall in HBs; exact (proj1 (Forall_forall _ _) HBs _ Hin).
  Qed.
  Lemma optional_exp_fresh_elim_M : forall r oq oUs j Bks M, optional_exp_fresh K (a_elim r oq oUs j Bks M) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; [ intros r oq oUs j Bks M H; apply (proj1 (exp_fresh_elim _ r oq oUs j Bks M)) in H; tauto | auto ]. Qed.
  Lemma optional_exp_fresh_elim_ups : forall r oq Us j Bks M, optional_exp_fresh K (a_elim r oq Us j Bks M) -> forall U, In U Us -> optional_exp_fresh K U.
  Proof.
    destruct K; cbn; [| auto ].
    intros r oq Us j Bks M H; apply (proj1 (exp_fresh_elim _ r oq Us j Bks M)) in H as [H _].
    apply all_list_Forall in H; exact (proj1 (Forall_forall _ _) H).
  Qed.
  Lemma optional_exp_fresh_var : forall x, optional_exp_fresh K #x -> K <> Some x.
  Proof. destruct K; cbn; congruence. Qed.
  Lemma optional_exp_fresh_tuple_fields : forall T fs, optional_exp_fresh K (a_tuple T fs) -> Forall (optional_exp_fresh K) (List.map snd fs).
  Proof.
    destruct K as [k |]; cbn; [| intros; apply Forall_forall; intros; exact I ].
    intros T fs [_ H]; induction fs as [| [f M] fs IH]; cbn in H |- *; constructor; tauto.
  Qed.
  Lemma optional_exp_fresh_proj : forall f M, optional_exp_fresh K (a_proj f M) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; auto. Qed.

  Lemma optional_modexp_fresh_var : forall x, optional_modexp_fresh K (me_var x) -> K <> Some x.
  Proof. destruct K; cbn; congruence. Qed.
  Lemma optional_modexp_fresh_lit : forall U, optional_modexp_fresh K (me_lit U) -> optional_gunit_fresh K U.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_modexp_fresh_mem : forall H y, optional_modexp_fresh K (me_mem H y) -> optional_modexp_fresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_modexp_fresh_app_l : forall H N, optional_modexp_fresh K (me_app H N) -> optional_modexp_fresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_modexp_fresh_app_r : forall H N, optional_modexp_fresh K (me_app H N) -> optional_exp_fresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_modexp_fresh_spine : forall H R args pre,
      modexp_spine H = (R, args, pre) -> optional_modexp_fresh K H -> optional_modexp_fresh K R /\ Forall (optional_exp_fresh K) args.
  Proof.
    destruct K as [k |]; cbn; intros * Hs Hf.
    - destruct (modexp_spine_fresh _ _ _ _ _ Hs Hf); split; assumption.
    - split; [ exact I | apply Forall_forall; intros; exact I ].
  Qed.

  Lemma optional_gunit_fresh_body : forall Δ sm Φ, optional_gunit_fresh K (gu_mk Δ (md_body sm Φ)) -> optional_gmod_fresh (optional_shift (List.length Δ) K) Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gunit_fresh_alias : forall Δ E, optional_gunit_fresh K (gu_mk Δ (md_alias E)) -> optional_modexp_fresh (optional_shift (List.length Δ) K) E.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_def_prefix : forall Φ y b pv r A M,
      optional_gmod_fresh K (gm_ext Φ y (ge_def b pv r A (Some M))) -> optional_gmod_fresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_def_body : forall Φ y b pv r A M,
      optional_gmod_fresh K (gm_ext Φ y (ge_def b pv r A (Some M))) -> optional_exp_fresh (optional_shift (gm_binders Φ) K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_mod_prefix : forall Φ y pm U,
      optional_gmod_fresh K (gm_ext Φ y (ge_mod pm U)) -> optional_gmod_fresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_mod_unit : forall Φ y pm U,
      optional_gmod_fresh K (gm_ext Φ y (ge_mod pm U)) -> optional_gunit_fresh (optional_shift (gm_binders Φ) K) U.
  Proof. destruct K; cbn; tauto. Qed.
  (** The term part of an entry ([entry_tm]) and its module part
      ([entry_unit]), under the entries before it. *)
  Lemma optional_gmod_fresh_ext_prefix : forall Φ y E, optional_gmod_fresh K (gm_ext Φ y E) -> optional_gmod_fresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_tm_body : forall Φ y E A M, entry_tm E = Some (A, M) ->
      optional_gmod_fresh K (gm_ext Φ y E) -> optional_exp_fresh (optional_shift (gm_binders Φ) K) M.
  Proof.
    destruct K; cbn; [| tauto ].
    intros Φ y E A M HE Hf; destruct E as [? ? ? ? [] | | | |]; cbn in HE, Hf; try discriminate; injection HE as <- <-; tauto.
  Qed.
  Lemma optional_gmod_fresh_unit_unit : forall Φ y E U, entry_unit E = Some U ->
      optional_gmod_fresh K (gm_ext Φ y E) -> optional_gunit_fresh (optional_shift (gm_binders Φ) K) U.
  Proof.
    destruct K; cbn; [| tauto ].
    intros Φ y E U HE Hf; destruct E as [| | | |]; cbn in HE, Hf; try discriminate; injection HE as <-; tauto.
  Qed.
  Lemma optional_gmod_fresh_dm_prefix : forall Φ y pv A M U,
      optional_gmod_fresh K (gm_ext Φ y (ge_def_mod pv A M U)) -> optional_gmod_fresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_dm_body : forall Φ y pv A M U,
      optional_gmod_fresh K (gm_ext Φ y (ge_def_mod pv A M U)) -> optional_exp_fresh (optional_shift (gm_binders Φ) K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_dm_unit : forall Φ y pv A M U,
      optional_gmod_fresh K (gm_ext Φ y (ge_def_mod pv A M U)) -> optional_gunit_fresh (optional_shift (gm_binders Φ) K) U.
  Proof. destruct K; cbn; tauto. Qed.
End OFresh.

#[local] Hint Resolve optional_exp_fresh_univ optional_exp_fresh_succl optional_exp_fresh_maxl_l optional_exp_fresh_maxl_r
  optional_exp_fresh_absurd_type optional_exp_fresh_absurd_proof
  optional_exp_fresh_and_left optional_exp_fresh_and_right optional_exp_fresh_fn_A optional_exp_fresh_let_A optional_exp_fresh_tuple_T
  optional_exp_fresh_pi_A optional_exp_fresh_pi_B optional_exp_fresh_fn_M optional_exp_fresh_app_l optional_exp_fresh_app_r optional_exp_fresh_let_M optional_exp_fresh_let_B
  optional_exp_fresh_letmod_U optional_exp_fresh_mem optional_exp_fresh_var optional_exp_fresh_tuple_fields optional_exp_fresh_proj optional_modexp_fresh_var optional_modexp_fresh_lit optional_modexp_fresh_mem optional_modexp_fresh_app_l optional_modexp_fresh_app_r
  optional_gunit_fresh_body optional_gunit_fresh_alias optional_gmod_fresh_def_prefix optional_gmod_fresh_def_body optional_gmod_fresh_mod_prefix optional_gmod_fresh_mod_unit
  optional_gmod_fresh_dm_prefix optional_gmod_fresh_dm_body optional_gmod_fresh_dm_unit
  : avoid.
(** Freshness does not read the group or the member of an eliminator, so
    they are taken from the hypothesis rather than left to unification. *)
#[local] Hint Extern 1 (optional_exp_fresh _ _) =>
  match goal with
  | H : optional_exp_fresh ?K (a_elim ?r ?oq ?o ?j ?Bks ?M) |- optional_exp_fresh ?K ?M => exact (optional_exp_fresh_elim_M K r oq o j Bks M H)
  end : avoid.
#[local] Hint Extern 1 (blocks_optional_exp_fresh _ _) =>
  match goal with
  | H : optional_exp_fresh ?K (a_elim ?r ?oq ?o ?j ?Bks ?M) |- blocks_optional_exp_fresh ?K ?Bks => exact (optional_exp_fresh_elim_blocks K r oq o j Bks M H)
  end : avoid.

(** ** Evaluation Builds No Variable *)

Section Eval.
  Variables (v b : nat).

  #[local] Hint Resolve env_avoids_nil env_avoids_cons env_avoids_var env_avoids_mod domain_avoids_args_snoc
    dmod_avoids_global_nil : mctt.
  (** The uniform parameters an eliminator carries are fresh where it is. *)
  #[local] Hint Extern 1 (Forall (optional_exp_fresh _) _) =>
    match goal with
    | H : optional_exp_fresh ?K (a_elim ?r ?oq ?Us ?j ?Bks ?M) |- Forall (optional_exp_fresh ?K) ?Us =>
        apply Forall_forall; exact (optional_exp_fresh_elim_ups K r oq Us j Bks M H)
    end : avoid.
  #[local] Hint Extern 1 (ups_avoids _ _ _) => unfold ups_avoids : avoid.
  #[local] Hint Extern 1 (domain_avoids _ _ (domain_level_lit _)) => repeat constructor : mctt.
  #[local] Hint Extern 1 (domain_avoids _ _ (domain_level_suc _)) => apply domain_avoids_lvl_suc : mctt.
  #[local] Hint Extern 1 (domain_avoids _ _ (domain_level_max _ _)) => apply domain_avoids_lvl_max : mctt.

  (** The entry an extension adds, given the invariant of its value. *)
  Ltac dentry_avoids_of d :=
    first [ apply dentry_avoids_term; solve [ eassumption | eauto 3 with mctt avoid ]
          | apply dentry_avoids_mod; solve [ eassumption | eauto 3 with mctt avoid ] ].

  (** The values of a typed list of entries an environment is extended by
      ([env_extend_typed]): the values given, whatever their types. *)
  Ltac av_vals :=
    unfold branch_entries, motive_entries; cbv zeta;
    rewrite ?List.map_app, ?tele_entries_values, ?cargs_entries_values, ?pair_values_with_types_values;
    cbn [List.map fst];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    repeat match goal with
           | H : In _ (_ ++ _) |- _ => apply List.in_app_or in H as [H | H]
           | H : In _ (_ :: _) |- _ => destruct H as [<- | H]
           | H : In _ nil |- _ => destruct H
           | H : In _ (List.skipn _ _) |- _ => apply in_skipn_in in H
           | H : In _ (List.firstn _ _) |- _ => apply in_firstn_in in H
           end;
    solve [ eassumption | eauto 3 with mctt avoid | constructor; solve [ eassumption | constructor; eassumption ] ].

  (** The environments of a group's uniform parameters, avoiding
      everywhere. *)
  Lemma env_avoids_decl_env : forall D ups, (forall a, In a ups -> domain_avoids v b a) -> env_avoids v b None (decl_env D ups).
  Proof.
    intros * Hu; unfold decl_env, env_tele; apply env_avoids_extend_typed_none; [ apply env_avoids_nil |].
    rewrite tele_entries_values; exact Hu.
  Qed.

  (** Forward reasoning: instantiate each induction hypothesis at the
      position the environment it is about has its bad entry at, and
      discharge its premises. *)
  Ltac av_fwd :=
    repeat match goal with
    | H : forall x, ?K <> Some x -> dentry_avoids ?v ?b (env_entry ?ρ x) |- _ => change (env_avoids v b K ρ) in H
    | H : Forall _ (_ :: _) |- _ => inversion_clear H
    | H : In _ (_ :: _) |- _ => destruct H as [<- | H]
    | H : In _ nil |- _ => destruct H
    | H : forall a, In a (?x :: ?l) -> ?P |- _ =>
        let H1 := fresh "H" in let H2 := fresh "H" in
        assert (H1 : forall a, a = x -> P) by (intros a Ha; apply H; left; symmetry; exact Ha);
        assert (H2 : forall a, In a l -> P) by (intros a Ha; apply H; right; exact Ha);
        specialize (H1 x eq_refl); clear H
    | Hs : modexp_spine ?H = _, Hf : optional_exp_fresh ?K (a_mem ?H _) |- _ =>
        apply optional_exp_fresh_mem in Hf; destruct (optional_modexp_fresh_spine _ _ _ _ _ Hs Hf); clear Hs
    | IH : forall K0, env_avoids ?v ?b K0 nil -> _ |- _ => specialize (IH None (env_avoids_nil _ _ None) I)
    | IH : forall K0, env_avoids ?v ?b K0 ?ρ -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ => specialize (IH K Hρ)
    | IH : forall K0, env_avoids ?v ?b K0 (extend_env (extend_env ?ρ ?d1 ?t1) ?d2 ?t2) -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in let E2 := fresh "E" in
        assert (E1 : dentry_avoids v b (de_term d1 t1)) by dentry_avoids_of d1;
        assert (E2 : dentry_avoids v b (de_term d2 t2)) by dentry_avoids_of d2;
        specialize (IH (optional_shift 1 (optional_shift 1 K)) (env_avoids_cons _ _ _ _ _ (env_avoids_cons _ _ _ _ _ Hρ E1) E2));
        rewrite optional_shift_optional_shift in IH; cbn [Nat.add] in IH
    | IH : forall K0, env_avoids ?v ?b K0 (extend_env ?ρ ?d ?t) -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : dentry_avoids v b (de_term d t)) by dentry_avoids_of d;
        specialize (IH (optional_shift 1 K) (env_avoids_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_avoids ?v ?b K0 (extend_env_mod ?ρ ?h ?U) -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : dentry_avoids v b (de_mod h U)) by dentry_avoids_of h;
        specialize (IH (optional_shift 1 K) (env_avoids_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_avoids ?v ?b K0 (decl_env ?D ?ups) -> _, Hu : forall a, In a ?ups -> domain_avoids ?v ?b a |- _ =>
        specialize (IH None (env_avoids_decl_env D ups Hu))
    | IH : forall K0, env_avoids ?v ?b K0 (env_extend_typed ?ρ ?L) -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ =>
        let HL := fresh "HL" in
        assert (HL : forall a, In a (List.map fst L) -> domain_avoids v b a) by av_vals;
        specialize (IH (optional_shift (List.length L) K) (env_avoids_extend_typed _ _ _ _ _ Hρ HL))
    | IH : ?P -> ?Q |- _ =>
        let HP := fresh "HP" in assert (HP : P) by (solve [ eassumption | eauto 3 with mctt avoid ]); specialize (IH HP)
    end.

  (** An avoiding value, environment or list of values, built of avoiding
      parts, within [n] steps: an environment through its builders at no
      bad position; a member of a list by its segments; a value by its
      rule; otherwise by a hypothesis, its premises in turn.  The closures,
      whose bad position is the environment's, are left to the caller. *)
  Ltac av_go n :=
    lazymatch n with
    | O => fail
    | S ?n' =>
        first
          [ assumption
          | exact I
          | match goal with
            | |- env_avoids _ _ _ (decl_env _ _) => apply env_avoids_decl_env; av_go n'
            | |- env_avoids _ _ _ nil => apply env_avoids_nil
            | |- env_avoids _ _ None (_ ↦ _ ⦂ _) => apply env_avoids_cons_none; av_go n'
            | |- Forall (optional_exp_fresh None) _ => apply Forall_forall; intros; exact I
            | |- optional_exp_fresh None _ => exact I
            | |- forall _, _ => intro; av_go n
            | H : In _ (_ ++ _) |- _ => apply List.in_app_or in H as [H | H]; av_go n
            | H : In _ (_ :: _) |- _ => destruct H as [<- | H]; av_go n
            | H : In _ nil |- _ => destruct H
            | H : In _ (List.map _ _) |- _ => apply List.in_map_iff in H as (? & <- & ?); av_go n
            | H : In _ (List.skipn _ _) |- _ => apply in_skipn_in in H; av_go n
            | H : In _ (List.firstn _ _) |- _ => apply in_firstn_in in H; av_go n
            | H : In (_, _) (List.combine _ _) |- _ => apply List.in_combine_r in H; av_go n
            | H : List.nth_error _ _ = Some _ |- _ => apply List.nth_error_In in H; av_go n
            | H : forall x, In x ?l -> domain_avoids _ _ x, Ha : In ?a ?l |- domain_avoids _ _ ?a => exact (H _ Ha)
            | H : ups_avoids _ _ ?l, Ha : In ?a ?l |- domain_avoids _ _ ?a => exact (H _ Ha)
            | |- ups_avoids _ _ _ => unfold ups_avoids; av_go n
            | |- In _ _ => solve [ cbn; auto 6 using List.in_or_app, List.in_eq, List.in_cons ]
            | |- domain_avoids _ _ (domain_level_lit _) => repeat constructor
            | |- domain_avoids _ _ (domain_level_suc _) => apply domain_avoids_lvl_suc; av_go n'
            | |- domain_avoids _ _ (domain_level_max _ _) => apply domain_avoids_lvl_max; av_go n'
            | |- domain_avoids _ _ (env_var _ _) => eapply env_avoids_var; [ eassumption | eapply optional_exp_fresh_var; eassumption ]
            | |- domain_avoids _ _ _ => constructor; av_go n'
            | |- domain_ne_avoids _ _ _ => constructor; av_go n'
            | |- domain_nf_avoids _ _ _ => constructor; av_go n'
            | |- dmod_avoids _ _ _ => constructor; av_go n'
            | |- dentry_avoids _ _ _ => constructor; av_go n'
            end
          | match goal with H : _ |- _ => solve [ eapply H; av_go n' ] end ]
    end.

  Lemma eval_avoids :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall K, env_avoids v b K ρ -> optional_exp_fresh K M -> domain_avoids v b m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> domain_avoids v b m -> domain_avoids v b n -> domain_avoids v b r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms ->
       forall K, env_avoids v b K ρ -> Forall (optional_exp_fresh K) Ms -> forall a, In a ms -> domain_avoids v b a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r ->
       domain_avoids v b m -> (forall a, In a args -> domain_avoids v b a) -> domain_avoids v b r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall K, env_avoids v b K ρ -> optional_modexp_fresh K H -> dmod_avoids v b h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall K, env_avoids v b K ρ -> optional_gunit_fresh K (gu_mk Δ D) -> dmod_avoids v b h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmod_avoids v b h -> domain_avoids v b n -> dmod_avoids v b r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> dmod_avoids v b h -> (forall a, In a ns -> domain_avoids v b a) -> dmod_avoids v b r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmod_avoids v b h -> domain_avoids v b r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmod_avoids v b h -> dmod_avoids v b r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmod_avoids v b h -> domain_avoids v b r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmod_avoids v b h -> dmod_avoids v b r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
       forall K, env_avoids v b K ρ -> optional_gmod_fresh K Φ -> env_avoids v b (optional_shift (gm_binders Φ) K) ρ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       forall K, env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups -> domain_avoids v b m -> domain_avoids v b r) /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       forall K, env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups ->
            (forall a, In a vs -> domain_avoids v b a) -> forall a, In a ihs -> domain_avoids v b a) /\
    (forall ρ p ups Bks t m rs, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
       forall K, env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups -> domain_avoids v b m -> forall a, In a rs -> domain_avoids v b a) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r ->
       (forall u, In u ups -> domain_avoids v b u) -> forall a, In a (snd r) -> domain_avoids v b a) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
       forall K, env_avoids v b K ρ -> optional_ptyp_fresh K t -> (forall u, In u ups -> domain_avoids v b u) -> domain_avoids v b a) /\
    (forall p ups ρm As ρ t m as', ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
       forall Km, env_avoids v b Km ρm -> ends_fresh p Km As t -> ups_avoids v b ups ->
       forall K, env_avoids v b K ρ -> optional_ptyp_fresh K t -> domain_avoids v b m -> forall a, In a as' -> domain_avoids v b a) /\
    (forall f m r, eval_proj Θ Ξ f m r -> domain_avoids v b m -> domain_avoids v b r) /\
    (forall m ρ fl rs, eval_neutral_fields Θ Ξ m ρ fl rs ->
       domain_ne_avoids v b m -> env_avoids v b None ρ -> forall a, In a rs -> domain_avoids v b a) /\
    (forall fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> domain_avoids v b m -> forall a, In a ws -> domain_avoids v b a) /\
    (forall p ups ρm As ρ gs vs as', ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
       forall Km, env_avoids v b Km ρm -> (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p Km As t) ->
       ups_avoids v b ups -> env_avoids v b None ρ -> (forall a, In a vs -> domain_avoids v b a) -> forall a, In a as' -> domain_avoids v b a) /\
    (forall rs Ms ρ vs, eval_field_vals Θ Ξ rs Ms ρ vs ->
       forall K, env_avoids v b K ρ -> Forall (optional_exp_fresh K) Ms -> forall a, In a vs -> domain_avoids v b a) /\
    (forall f Ms ρ r, eval_app_args Θ Ξ f Ms ρ r ->
       forall K, env_avoids v b K ρ -> Forall (optional_exp_fresh K) Ms -> domain_avoids v b f -> domain_avoids v b r).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => forall K, env_avoids v b K ρ -> optional_exp_fresh K M -> domain_avoids v b m)
             (fun m n r _ => domain_avoids v b m -> domain_avoids v b n -> domain_avoids v b r)
             (fun Ms ρ ms _ => forall K, env_avoids v b K ρ -> Forall (optional_exp_fresh K) Ms ->
                                forall a, In a ms -> domain_avoids v b a)
             (fun m args r _ => domain_avoids v b m -> (forall a, In a args -> domain_avoids v b a) -> domain_avoids v b r)
             (fun H ρ h _ => forall K, env_avoids v b K ρ -> optional_modexp_fresh K H -> dmod_avoids v b h)
             (fun Δ D ρ h _ => forall K, env_avoids v b K ρ -> optional_gunit_fresh K (gu_mk Δ D) -> dmod_avoids v b h)
             (fun h n r _ => dmod_avoids v b h -> domain_avoids v b n -> dmod_avoids v b r)
             (fun h ns r _ => dmod_avoids v b h -> (forall a, In a ns -> domain_avoids v b a) -> dmod_avoids v b r)
             (fun h x r _ => dmod_avoids v b h -> domain_avoids v b r)
             (fun h y r _ => dmod_avoids v b h -> dmod_avoids v b r)
             (fun h ch r _ => dmod_avoids v b h -> domain_avoids v b r)
             (fun h ch r _ => dmod_avoids v b h -> dmod_avoids v b r)
             (fun ρ Φ ρ' _ => forall K, env_avoids v b K ρ -> optional_gmod_fresh K Φ ->
                               env_avoids v b (optional_shift (gm_binders Φ) K) ρ')
             (fun ρ p ups Bks j m r _ => forall K, env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups ->
                                         domain_avoids v b m -> domain_avoids v b r)
             (fun ρ p ups Bks gs vs ihs _ => forall K, env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups ->
                                       (forall a, In a vs -> domain_avoids v b a) -> forall a, In a ihs -> domain_avoids v b a)
             (fun ρ p ups Bks t m rs _ => forall K, env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups ->
                                          domain_avoids v b m -> forall a, In a rs -> domain_avoids v b a)
             (fun p ups j r _ => (forall u, In u ups -> domain_avoids v b u) -> forall a, In a (snd r) -> domain_avoids v b a)
             (fun p ups ρ t a _ => forall K, env_avoids v b K ρ -> optional_ptyp_fresh K t -> (forall u, In u ups -> domain_avoids v b u) -> domain_avoids v b a)
             (fun p ups ρm As ρ t m as' _ => forall Km, env_avoids v b Km ρm -> ends_fresh p Km As t -> ups_avoids v b ups ->
                                    forall K, env_avoids v b K ρ -> optional_ptyp_fresh K t -> domain_avoids v b m -> forall a, In a as' -> domain_avoids v b a)
             (fun f m r _ => domain_avoids v b m -> domain_avoids v b r)
             (fun m ρ fl rs _ => domain_ne_avoids v b m -> env_avoids v b None ρ -> forall a, In a rs -> domain_avoids v b a)
             (fun fl m ws _ => domain_avoids v b m -> forall a, In a ws -> domain_avoids v b a)
             (fun p ups ρm As ρ gs vs as' _ => forall Km, env_avoids v b Km ρm ->
                                    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p Km As t) ->
                                    ups_avoids v b ups -> env_avoids v b None ρ -> (forall a, In a vs -> domain_avoids v b a) ->
                                    forall a, In a as' -> domain_avoids v b a)
             (fun rs Ms ρ vs _ => forall K, env_avoids v b K ρ -> Forall (optional_exp_fresh K) Ms ->
                                   forall a, In a vs -> domain_avoids v b a)
             (fun f Ms ρ r _ => forall K, env_avoids v b K ρ -> Forall (optional_exp_fresh K) Ms ->
                                 domain_avoids v b f -> domain_avoids v b r));
      intros; cbn [optional_ptyp_fresh ptyp_ps ptyp_mem snd] in *.
    all: repeat match goal with
           | H : domain_avoids _ _ (_ _) |- _ => inversion_clear H
           | H : dmod_avoids _ _ (_ _ _) |- _ => inversion_clear H
           | H : dmod_avoids _ _ (_ _ _ _) |- _ => inversion_clear H
           end.
    all: av_fwd.
    (** The values the rules build of avoiding parts, shallowly *)
    all: try solve [ assumption | constructor | eauto 2 with mctt avoid ].
    all: try solve [ eapply env_avoids_var; [ eassumption | eapply optional_exp_fresh_var; eassumption ] ].
    all: try solve [ eapply env_avoids_mod; [ eassumption | eapply optional_modexp_fresh_var; eassumption ] ].
    (** Ex falso: the neutral at its type, its proof kept *)
    all: try solve [ constructor; [ assumption | constructor; assumption ] ].
    (** A former or a tuple at no argument *)
    all: try solve [ constructor; intros ? [] ].
    all: try solve [ constructor; intros ? ? [] ].
    (** A closure over the environment, its body fresh where it is *)
    all: try solve [ econstructor; [ eassumption | eassumption | eauto 3 with avoid ] ].
    (** The values built of avoiding ones, through lists *)
    all: try solve [ av_go 4 ].
    (** A constructor of a view at the uniform parameters: the container's
        at the view's arguments, closed terms evaluated at the group's
        uniform parameters *)
    all: try solve [ match goal with IH : forall K0, env_avoids _ _ K0 _ -> Forall _ _ -> forall a, In a ?cups -> _
                       |- domain_avoids _ _ (d_con _ _ _ ?cups) =>
                       constructor; intros a Ha; first [ eapply (IH None) | eapply IH ];
                       [ first [ apply env_avoids_nil | apply env_avoids_decl_env; av_go 3 ] | apply Forall_forall; intros; exact I | exact Ha ] end ].
    (** A closure of a unit: its body expanded ([eval_close_body]) *)
    all: try solve [ match goal with Hu : optional_gunit_fresh ?K (gu_mk ?Δ (md_body ?sm ?Φ)), Hρ : env_avoids _ _ ?K _
                       |- dmod_avoids _ _ (dm_local _ _ _) =>
                       eapply dmod_avoids_local; [ exact Hρ | exact (optional_gunit_fresh_expand K (gu_mk Δ (md_body sm Φ)) Hu) ] end ].
    (** An alias lacking no parameter: its target *)
    all: try solve [ match goal with IH : optional_modexp_fresh ?K ?E -> _, Hu : optional_gunit_fresh ?K (gu_mk nil (md_alias ?E)) |- _ =>
        apply IH; pose proof (optional_gunit_fresh_alias _ _ _ Hu) as Hx; cbn [List.length] in Hx; rewrite optional_shift_zero in Hx; exact Hx end ].
    (** A closure given its outermost parameter *)
    all: try solve [ match goal with IH : optional_gunit_fresh (optional_shift 1 ?K) _ -> _, Hu : optional_gunit_fresh ?K (gu_mk (_ ++ _) _) |- _ =>
        exact (IH (optional_gunit_fresh_snoc _ _ _ _ Hu)) end ].
    (** A member of a closure lacking a parameter *)
    all: try solve [ constructor; econstructor; [ eassumption | assumption ] ].
    (** The body of a module: its entries, at the positions they shift
        the bad one to *)
    all: try solve [ cbn [gm_binders]; rewrite optional_shift_zero; assumption ].
    all: try solve [ cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- optional_shift_optional_shift;
      apply env_avoids_cons; [ assumption | constructor; first [ assumption | constructor ] ] ].
    (** The recursive results of a function shape: one family per leaf
        path *)
    all: try solve [ match goal with Ha : In _ (List.map _ _) |- _ => apply List.in_map_iff in Ha as (? & <- & _) end;
      econstructor; first [ eassumption | av_go 3 ] ].
    (** A term part and a module part of a saturated body, in its
        expansion *)
    all: try solve [ match goal with Hp : gm_prefix_upto (gm_expand ?Φ) _ = Some _, HE : entry_tm _ = Some _,
                      Hu : optional_gunit_fresh ?K (gu_mk nil (md_body _ ?Φ)),
                      IHb : optional_gmod_fresh ?K _ -> _, IHM : forall K0, _ -> optional_exp_fresh K0 _ -> _ |- _ =>
        pose proof (optional_gunit_fresh_body _ _ _ _ Hu) as HΦ; cbn [List.length] in HΦ; rewrite optional_shift_zero in HΦ;
        pose proof (optional_exp_fresh_prefix_upto _ _ _ _ Hp (optional_gmod_fresh_expand _ _ HΦ)) as HΦ';
        exact (IHM _ (IHb (optional_gmod_fresh_ext_prefix _ _ _ _ HΦ')) (optional_gmod_fresh_tm_body _ _ _ _ _ _ HE HΦ')) end ].
    all: try solve [ match goal with Hp : gm_prefix_upto (gm_expand ?Φ) _ = Some _, HE : entry_unit _ = Some _,
                      Hu : optional_gunit_fresh ?K (gu_mk nil (md_body _ ?Φ)),
                      IHb : optional_gmod_fresh ?K _ -> _, IHM : forall K0, _ -> optional_gunit_fresh K0 _ -> _ |- _ =>
        pose proof (optional_gunit_fresh_body _ _ _ _ Hu) as HΦ; cbn [List.length] in HΦ; rewrite optional_shift_zero in HΦ;
        pose proof (optional_exp_fresh_prefix_upto _ _ _ _ Hp (optional_gmod_fresh_expand _ _ HΦ)) as HΦ';
        exact (IHM _ (IHb (optional_gmod_fresh_ext_prefix _ _ _ _ HΦ')) (optional_gmod_fresh_unit_unit _ _ _ _ _ HE HΦ')) end ].
    (** The types of a function shape's argument and recursive result: a
        [Π] over the family, in an environment that holds only the family *)
    all: try solve [ lazymatch goal with |- domain_avoids _ _ (Πᵈ{_} _ (_ ↦ d_shfam _ _ _ _ _ ⦂ _) _) => idtac end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      eapply domain_avoids_pi with (K := None); [ eauto | | exact I ];
      apply env_avoids_cons_none; [ apply env_avoids_nil | eapply domain_avoids_shfam; eassumption ] ].
    all: try solve [ match goal with
      | Ha : In ?d0 (List.map (fun i => Πᵈ{_} _ (nil ↦ d_ihfam _ _ _ _ _ _ _ i _ ⦂ _) _) _) |- domain_avoids _ _ ?d0 =>
          apply List.in_map_iff in Ha as (? & <- & _)
      end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      match goal with HE : ends_fresh _ _ _ (pt_pi _ _) |- _ => inversion HE; subst end;
      eapply domain_avoids_pi with (K := None); [ eauto | | exact I ];
      apply env_avoids_cons_none; [ apply env_avoids_nil | eapply domain_avoids_ihfam; eassumption ] ].
    (** A field of a tuple *)
    all: try solve [ match goal with H : forall f y, In (f, y) ?vs -> domain_avoids _ _ y, Hl : field_lookup ?vs _ = Some ?r |- domain_avoids _ _ ?r =>
          exact (H _ _ (field_lookup_In _ _ _ Hl)) end ].
    (** The projections of a neutral record: at the field types, closed
        over the type's parameters, and the projections before them *)
    all: try solve [ match goal with H : env_avoids _ _ None (env_tele _ _ ?ns) -> _ |- _ =>
        eapply H; [ unfold env_tele; apply env_avoids_extend_typed_none; [ apply env_avoids_nil | rewrite tele_entries_values; assumption ] | ];
        eapply List.nth_error_In; eassumption end ].
    all: try solve [ match goal with H0 : env_avoids _ _ None (?ρ ↦ ⇑ ?a (d_proj ?g ?m) ⦂ _) -> _, H : optional_exp_fresh None _ -> domain_avoids _ _ ?a |- _ =>
        eapply H0; [ apply env_avoids_cons_none; [ assumption | constructor; [ apply H; exact I | constructor; assumption ] ] | assumption ] end ].
    (** The types of the recursive results of a record view's fields: a
        non-recursive field joins the environment, a recursive one's shape
        ends fresh *)
    all: try solve [ match goal with
      | IH : (forall gs1 t gs2, ?gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh ?p ?Km ?As t) -> ups_avoids _ _ ?ups -> env_avoids _ _ None (?ρ ↦ ?v0 ⦂ ?t0) ->
             (forall y1, In y1 ?vs -> domain_avoids _ _ y1) -> forall y2, In y2 ?rs -> domain_avoids _ _ y2,
        Hf : forall gs1 t gs2, ca_arg ?r ?T :: ?gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh ?p ?Km ?As t,
        Hu : ups_avoids _ _ ?ups, Hρ : env_avoids _ _ None ?ρ, Hv : forall y3, In y3 (?v0 :: ?vs) -> domain_avoids _ _ y3, Ha : In ?d0 ?rs |- domain_avoids _ _ ?d0 =>
          apply (IH ltac:(intros gs1 t gs2 E; apply (Hf (ca_arg r T :: gs1) t gs2); rewrite E; reflexivity) Hu
                      (env_avoids_cons_none _ _ _ _ _ Hρ (all_in_head _ _ _ Hv)) (all_in_tail _ _ _ Hv) _ Ha)
      end ].
    all: try solve [ match goal with
      | Ha : In ?d0 (?l1 ++ ?l2), Hf : forall gs1 t0 gs2, ca_rec ?t :: ?gs = gs1 ++ ca_rec t0 :: gs2 -> ends_fresh _ _ _ t0,
        Hv : forall y1, In y1 (?v0 :: ?vs) -> domain_avoids _ _ y1 |- domain_avoids _ _ ?d0 =>
          destruct (List.in_app_or _ _ _ Ha) as [Hin1 | Hin1];
          [ match goal with IH : ends_fresh _ _ _ t -> _ |- _ =>
              exact (IH (Hf nil t gs eq_refl) ltac:(assumption) None ltac:(assumption) (optional_ptyp_fresh_none t) (all_in_head _ _ _ Hv) _ Hin1) end
          | match goal with IH : _ -> _ -> _ -> _ -> forall y2, In y2 l2 -> _ |- _ =>
              eapply IH; [ | assumption | assumption | exact (all_in_tail _ _ _ Hv) | exact Hin1 ];
              let gs1 := fresh "gs" in let t0 := fresh "t" in let gs2 := fresh "gs" in let E := fresh "E" in
              intros gs1 t0 gs2 E; apply (Hf (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity end ]
      end ].
    (** The end of a shape: at a member with a block, its motive, fresh
        under the end's parameters and the argument ([ends_fresh_self]);
        at a record view, its fields' types ([ends_fresh_rview]) *)
    all: try solve [ match goal with HE : ends_fresh _ _ _ (pt_self _ _) |- _ => inversion HE; subst; clear HE end;
      repeat match goal with
        | H1 : ind_lookup ?x ?y ?p = Some ?X, H2 : ind_lookup ?x ?y ?p = Some ?Y |- _ =>
            tryif constr_eq X Y then fail else (rewrite H1 in H2; let E := fresh "E" in injection H2 as E; subst Y)
        | H1 : ind_member ?D ?j = Some ?X, H2 : ind_member ?D ?j = Some ?Y |- _ =>
            tryif constr_eq X Y then fail else (rewrite H1 in H2; let E := fresh "E" in injection H2 as E; subst Y)
        end;
      first
        [ match goal with Hr : im_is_rview ?M = false, Hh : im_head ?M = mh_record _ _ _ |- _ =>
            unfold im_is_rview in Hr; rewrite Hh in Hr; discriminate end
        | match goal with
          | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs, IH : optional_exp_fresh (optional_shift (List.length (tele_entries _ _ ?bs ++ _ :: nil)) ?Km) ?A -> _,
            HA : optional_exp_fresh (optional_shift (S (List.length ?Ps)) ?Km) ?A |- _ =>
              let Hlb := fresh "Hlb" in
              assert (Hlb : List.length bs = List.length Ps) by (clear - e; induction e; cbn; congruence);
              apply IH; rewrite List.length_app, <- (List.length_map fst (tele_entries _ _ _)), tele_entries_values, Hlb;
              cbn [List.length]; replace (List.length Ps + 1) with (S (List.length Ps)) by lia; exact HA
          end
        | match goal with
          | IH : _ -> ups_avoids _ _ ?ups -> env_avoids _ _ None (decl_env _ ?ups) -> (forall y1, In y1 ?ws -> domain_avoids _ _ y1) ->
                 forall y2, In y2 ?rs -> domain_avoids _ _ y2,
            Hf : forall c gs gs1 t gs2, im_cons ?M = (c, gs) :: nil -> _, Hc : im_cons ?M = (?c0, ?gs0) :: nil,
            Hu : ups_avoids _ _ ?ups, Hw : forall y3, In y3 ?ws -> domain_avoids _ _ y3, Ha : In ?d0 ?rs |- domain_avoids _ _ ?d0 =>
              eapply IH; [ intros gs1 t gs2 E; exact (Hf c0 gs0 gs1 t gs2 Hc E) | exact Hu | apply env_avoids_decl_env; exact Hu | exact Hw | exact Ha ]
          end ] ].
    (** The branch of a constructor, in the environment of its parameters,
        arguments and recursive results: as many as it binds, the group's
        table coherent ([eval_elim_con]'s gate) *)
    all: try solve [ match goal with
      | e7 : brs_lookup (eb_brs ?bk) ?c = Some (?n, ?B), Hb : List.nth_error ?Bks _ = Some ?bk,
        Hl : List.length ?vs = (im_np ?Dq ?Mk + List.length ?gs)%nat,
        Hn : ?n = _, HD : ind_lookup _ _ ?p = Some ?D, Hco : leaves_coherent ?D,
        Hih : eval_ihs _ _ _ ?p _ _ ?gs _ ?ihs,
        IHi : (forall x1, In x1 (skipn _ _) -> domain_avoids _ _ x1) -> forall x2, In x2 ?ihs -> domain_avoids _ _ x2,
        HBk : blocks_optional_exp_fresh ?K ?Bks, Hρ : env_avoids _ _ ?K ?ρ,
        IHB : forall K0, env_avoids _ _ K0 (env_extend_typed ?ρ ?L) -> optional_exp_fresh K0 ?B -> domain_avoids _ _ ?r |- domain_avoids _ _ ?r =>
          let Hi := fresh "Hi" in let Hni := fresh "Hni" in let HL := fresh "HL" in
          pose proof (IHi ltac:(intros x Hx; apply in_skipn_in in Hx; auto)) as Hi;
          destruct (eval_ihs_length _ _ _ _ _ _ _ _ HD Hco Hih) as [_ Hni];
          assert (HL : forall a, In a (List.map fst L) -> domain_avoids v b a) by av_vals;
          apply (IHB (optional_shift (List.length L) K)); [ apply env_avoids_extend_typed; assumption |];
          rewrite <- (List.length_map fst L); unfold branch_entries; cbv zeta;
          rewrite !List.map_app, tele_entries_values, cargs_entries_values, pair_values_with_types_values;
          rewrite (ind_branch_args_length _ _ _ _ _ Hl), Hni, <- Hn;
          exact (proj2 (HBk _ (List.nth_error_In _ _ Hb)) _ _ _ (brs_lookup_in _ _ _ _ e7))
      end ].
    (** A stuck eliminator: its motive, under the neutral's non-uniform
        parameters and the neutral, as many as the block binds *)
    all: match goal with
      | Hb : nth_error ?Bks _ = Some ?bk, Hn : eb_binder_count ?bk = S (im_nn ?Mk), Hl : List.length ?as' = im_np ?Dq ?Mk,
        HBk : blocks_optional_exp_fresh ?K ?Bks,
        IH : optional_exp_fresh (optional_shift (List.length (motive_entries _ _ _ (skipn _ ?as') _ _)) ?K) (eb_motive ?bk) ->
             domain_avoids _ _ ?a |- _ =>
          let Ha := fresh "Ha" in
          assert (Ha : domain_avoids v b a);
          [ apply IH; replace (List.length _) with (eb_binder_count bk); [ exact (proj1 (HBk _ (List.nth_error_In _ _ Hb))) |];
            rewrite Hn, <- (List.length_map fst); unfold motive_entries;
            rewrite List.map_app, tele_entries_values, List.length_app, List.length_skipn, Hl; cbn [List.map List.length fst];
            unfold im_np; lia
          | constructor; [ exact Ha | econstructor; eassumption ] ]
      end.
  Qed.
End Eval.

(** A closure, evaluated at one or two more entries. *)
Lemma eval_clo_avoids : forall v b K (ρ : env) B c t d,
    env_avoids v b K ρ -> optional_exp_fresh (optional_shift 1 K) B -> domain_avoids v b c ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ⦂ t ↘ d -> domain_avoids v b d.
Proof.
  intros * Hρ HB Hc Hd.
  eapply (proj1 (eval_avoids v b)); [ exact Hd | apply env_avoids_cons; [ exact Hρ | constructor; exact Hc ] | exact HB ].
Qed.

Lemma eval_clo2_avoids : forall v b K (ρ : env) B c1 t1 c2 t2 d,
    env_avoids v b K ρ -> optional_exp_fresh (optional_shift 2 K) B -> domain_avoids v b c1 -> domain_avoids v b c2 ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ⦂ t1 ↦ c2 ⦂ t2 ↘ d -> domain_avoids v b d.
Proof.
  intros * Hρ HB Hc1 Hc2 Hd.
  eapply (proj1 (eval_avoids v b) _ _ _ Hd (optional_shift 1 (optional_shift 1 K))).
  - apply env_avoids_cons; [ apply env_avoids_cons; [ exact Hρ | constructor; exact Hc1 ] | constructor; exact Hc2 ].
  - rewrite optional_shift_optional_shift; exact HB.
Qed.

Lemma app_avoids : forall v b m n r, $| m & n | Θ ⍮ Ξ ↘ r -> domain_avoids v b m -> domain_avoids v b n -> domain_avoids v b r.
Proof. intros * H; exact (proj1 (proj2 (eval_avoids v b)) _ _ _ H). Qed.

Lemma shape_type_avoids : forall v b p ups ρ t a K, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
    env_avoids v b K ρ -> optional_ptyp_fresh K t -> (forall u, In u ups -> domain_avoids v b u) -> domain_avoids v b a.
Proof.
  intros * H; destruct (eval_avoids v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
  exact (Hs _ _ _ _ _ H K).
Qed.

(** The types of the recursive results along the leaf paths of a shape. *)
Lemma ihty_avoids : forall v b p ups ρm As ρ t m as' Km K, ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
    env_avoids v b Km ρm -> ends_fresh p Km As t -> ups_avoids v b ups ->
    env_avoids v b K ρ -> optional_ptyp_fresh K t -> domain_avoids v b m -> forall a, In a as' -> domain_avoids v b a.
Proof.
  intros * H; destruct (eval_avoids v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy & _).
  intros; eapply Hy; eassumption.
Qed.

Lemma proj_avoids : forall v b f m r, eval_proj Θ Ξ f m r -> domain_avoids v b m -> domain_avoids v b r.
Proof.
  intros * H; destruct (eval_avoids v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
  exact (Hp _ _ _ H).
Qed.

(** The recursive results along the leaf paths of a shape. *)
Lemma ih_avoids : forall v b ρ p ups Bks t m rs K, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
    env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups -> domain_avoids v b m -> forall a, In a rs -> domain_avoids v b a.
Proof.
  intros * H; destruct (eval_avoids v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _).
  intros; eapply Hi; eassumption.
Qed.

Lemma mref_avoids : forall v b p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r ->
    (forall u, In u ups -> domain_avoids v b u) -> forall a, In a (snd r) -> domain_avoids v b a.
Proof.
  intros * H; destruct (eval_avoids v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _).
  exact (Hm _ _ _ _ H).
Qed.

(** The projections of a value at a list of fields. *)
Lemma projs_avoids : forall v b fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> domain_avoids v b m -> forall a, In a ws -> domain_avoids v b a.
Proof.
  intros * H; destruct (eval_avoids v b)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _).
  exact (Hpj _ _ _ H).
Qed.

(** The values along the leaf paths of an argument: the container's
    variables and the group's results. *)
Lemma wrap_leaf_vals_avoids : forall v b bs rs ihs ihs' out, wrap_leaf_vals bs rs ihs ihs' out ->
    (forall a, In a rs -> domain_avoids v b a) -> (forall a, In a ihs -> domain_avoids v b a) ->
    (forall a, In a out -> domain_avoids v b a) /\ (forall a, In a ihs' -> domain_avoids v b a).
Proof.
  induction 1; intros Hr Hi; [ split; [ apply all_in_nil | assumption ] | |].
  - destruct IHwrap_leaf_vals as [H1 H2]; [ all_in_with assumption | all_in_with assumption |].
    split; [ apply all_in_cons; [ apply Hi; left; reflexivity | exact H1 ] | exact H2 ].
  - destruct IHwrap_leaf_vals as [H1 H2]; [ all_in_with assumption | assumption |].
    split; [ apply all_in_cons; [ apply Hr; left; reflexivity | exact H1 ] | exact H2 ].
Qed.

(** The recursive results a branch is read under, when the eliminator is
    read as its container's: the fresh ones, and the eliminator's along the
    paths nested through. *)
Lemma wrap_ihs_eval_avoids : forall v b ρ p ups Bks Dc gs' gs vs ihs r K,
    ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
    env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups ->
    (forall a, In a vs -> domain_avoids v b a) -> (forall a, In a ihs -> domain_avoids v b a) -> forall a, In a r -> domain_avoids v b a.
Proof.
  induction 1; intros Hρ HB Ho Hv Hi; [ apply all_in_nil | | |].
  - match goal with Hw : wrap_leaf_vals _ _ _ _ _ |- _ => pose proof (wrap_leaf_vals_avoids v b _ _ _ _ _ Hw) as Hwl end.
    destruct Hwl as [Hw1 Hw2]; [ eapply ih_avoids; [ eassumption | eassumption | assumption | assumption | apply Hv; left; reflexivity ]
                               | exact Hi |].
    apply all_in_app; [ exact Hw1 |].
    apply IHwrap_ihs_eval; [ assumption | assumption | assumption | all_in_with assumption | exact Hw2 ].
  - apply all_in_app; [ eapply ih_avoids; [ eassumption | eassumption | assumption | assumption | apply Hv; left; reflexivity ] |].
    apply IHwrap_ihs_eval; [ assumption | assumption | assumption | all_in_with assumption | assumption ].
  - apply IHwrap_ihs_eval; [ assumption | assumption | assumption | all_in_with assumption | assumption ].
Qed.

(** As many values along the leaf paths as there are paths. *)
Lemma wrap_leaf_vals_length : forall bs rs ihs ihs' out, wrap_leaf_vals bs rs ihs ihs' out -> List.length out = List.length bs.
Proof. induction 1; cbn; congruence. Qed.

(** As many recursive results a branch is read under as the group's
    branch binds, when the group's table of leaf paths is coherent. *)
Lemma wrap_ihs_eval_length : forall ρ p ups Bks Dc gs' gs vs ihs r D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
    ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
    List.length r = cargs_nrec D gs /\ List.length vs = List.length gs'.
Proof.
  intros * HD Hc H; induction H; cbn [cargs_nrec List.length]; [ auto | | |].
  - match goal with H1 : ind_lookup _ _ _ = Some _ |- _ => rewrite HD in H1; injection H1 as <- end.
    destruct IHwrap_ihs_eval as [IH1 IH2].
    rewrite List.length_app, IH1, (wrap_leaf_vals_length _ _ _ _ _ H1), List.length_map; auto.
  - destruct IHwrap_ihs_eval as [IH1 IH2].
    rewrite List.length_app, IH1, (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ H _ HD Hc); auto.
  - destruct IHwrap_ihs_eval as [IH1 IH2]; auto.
Qed.

(** The motive of the member [j] of the group read, among the blocks'
    motives: a block's, the one [elim_src] gives, or the default. *)
Lemma nth_motives_sel : forall sel Bks j,
    List.nth j (motives_sel sel (blocks_motives Bks)) a_prop = a_prop \/
    exists b, List.nth_error Bks (elim_src sel j) = Some b /\ List.nth j (motives_sel sel (blocks_motives Bks)) a_prop = eb_motive b.
Proof.
  assert (Hb : forall (Bks : list eblock) i, List.nth i (blocks_motives Bks) a_prop = a_prop \/
             exists b, List.nth_error Bks i = Some b /\ List.nth i (blocks_motives Bks) a_prop = eb_motive b).
  { intros Bks i; destruct (List.nth_error Bks i) as [b |] eqn:E.
    - right; exists b; split; [ reflexivity |].
      unfold blocks_motives; apply List.nth_error_nth; rewrite List.nth_error_map, E; reflexivity.
    - left; apply List.nth_overflow; unfold blocks_motives; rewrite List.length_map; apply List.nth_error_None; exact E. }
  intros [vm |] Bks j; cbn [motives_sel elim_src]; [| apply Hb ].
  destruct (Nat.lt_ge_cases j (List.length vm)) as [Hj | Hj].
  - assert (E : List.nth j (List.map (fun v => List.nth v (blocks_motives Bks) a_prop) vm) a_prop
                 = List.nth (List.nth j vm 0) (blocks_motives Bks) a_prop).
    { rewrite (List.nth_indep _ a_prop ((fun v => List.nth v (blocks_motives Bks) a_prop) 0))
        by (rewrite List.length_map; exact Hj).
      apply (List.map_nth (fun v => List.nth v (blocks_motives Bks) a_prop)). }
    rewrite E; apply Hb.
  - left; apply List.nth_overflow; rewrite List.length_map; exact Hj.
Qed.

(** The shapes of a constructor's recursive arguments end in a member at
    as many parameters as it has non-uniform ones, argument by argument. *)
Lemma params_length_forall : forall D (gs : list carg), cargs_params_length D gs ->
    Forall (fun g => match g with
                     | ca_rec t => exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj
                     | ca_arg _ _ => True end) gs.
Proof.
  unfold cargs_params_length; intros D; induction gs as [| g gs IH]; intros H; constructor.
  - destruct g as [r A | t]; [ exact I | exact (H nil t gs eq_refl) ].
  - apply IH; intros gs1 t gs2 E; apply (H (g :: gs1) t gs2); rewrite E; reflexivity.
Qed.

(** The motives at the ends of the leaf paths of a shape, fresh under
    their binders, from the blocks: each end at as many parameters as its
    member's motive binds ([rview_leaf_arity], [blocks_binder_count_at]), down the
    record views' fields by their order. *)
Lemma ends_fresh_of_blocks : forall p D Bks K, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
    blocks_binder_count_at D None Bks -> blocks_optional_exp_fresh K Bks ->
    forall t, (exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj) ->
      ends_fresh p K (blocks_motives Bks) t.
Proof.
  intros p D Bks K HD Har Hnm HB.
  enough (H : forall n t, (forall Mj, ind_member D (ptyp_mem t) = Some Mj -> im_is_rview Mj = true -> ptyp_mem t < n) ->
                (exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj) ->
                ends_fresh p K (blocks_motives Bks) t)
    by (intros t Hpl; apply (H (S (ptyp_mem t)) t); [ intros; lia | exact Hpl ]).
  induction n as [n IHn] using Wf_nat.lt_wf_ind.
  induction t as [j Ps | B t IHt]; intros Hrk (Mj & HMj & Hl); cbn [ptyp_mem ptyp_ps] in *.
  - destruct (im_is_rview Mj) eqn:Hrv.
    + (** A record view: its fields, at members before it. *)
      unfold im_is_rview in Hrv; destruct (im_head Mj) as [| | qr Is fl] eqn:Hh; try discriminate Hrv.
      eapply ends_fresh_rview; [ exact HD | exact HMj | exact Hh |].
      intros c gs gs1 t gs2 Hcs E.
      pose proof (rview_leaf_params_length _ Har _ _ _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity)
                    ltac:(rewrite Hcs; left; reflexivity) gs1 t gs2 E) as Hpt.
      apply (IHn j (Hrk Mj HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity)) t); [| exact Hpt ].
      intros Mt HMt HrT; exact (rview_leaf_order _ Har _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs E HMt HrT).
    + (** A member with a block: its motive. *)
      eapply ends_fresh_self; [ exact HD | exact HMj | exact Hrv |].
      pose proof (nth_motives_sel None Bks j) as Hm; cbn [motives_sel elim_src] in Hm.
      destruct Hm as [-> | (b & Hb & ->)]; [ destruct K; exact I |].
      rewrite Hl, <- (Hnm _ _ _ HMj Hb); exact (proj1 (HB _ (List.nth_error_In _ _ Hb))).
  - apply ends_fresh_pi, IHt; [ exact Hrk | exists Mj; split; assumption ].
Qed.

(** And so of every recursive argument of a constructor of [D]. *)
Lemma cargs_ends_fresh : forall p D Bks K gs, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
    blocks_binder_count_at D None Bks -> blocks_optional_exp_fresh K Bks -> cargs_params_length D gs ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p K (blocks_motives Bks) t.
Proof. intros * HD Har Hnm HB Hpl gs1 t gs2 E; exact (ends_fresh_of_blocks _ _ _ _ HD Har Hnm HB t (Hpl gs1 t gs2 E)). Qed.

Lemma domain_avoids_mono' : forall v b b' d, b <= b' -> domain_avoids v b d -> domain_avoids v b' d.
Proof. intros; eapply (proj1 (domain_avoids_mono v b)); eassumption. Qed.

Lemma ups_avoids_mono : forall v b b' ups, b <= b' -> ups_avoids v b ups -> ups_avoids v b' ups.
Proof. intros * Hb H a Ha; exact (domain_avoids_mono' _ _ _ _ Hb (H a Ha)). Qed.

(** ** Freshness Outside Proofs

    [nf_fresh_outside_proofs k W]: the variable [k] does not occur in the
    normal form [W] outside its proofs; mutually, in the neutral [u].  A
    proof is read back as its term under definitions of the entries it
    reads ([read_proof_kept]), which may include [k], and normal forms are
    compared up to their proofs, so proofs are exempt; it is the freshness
    of the erasure ([nf_fresh_outside_proofs_erase]). *)
Fixpoint nf_fresh_outside_proofs (k : nat) (W : nf) {struct W} : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_False
  | nf_proof_erased | nf_proof _ => True
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_fresh_outside_proofs k (atom_level a)) xs
  | nf_pi _ _ A B | nf_fn A B | nf_and A B => nf_fresh_outside_proofs k A /\ nf_fresh_outside_proofs (S k) B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => all_list (nf_fresh_outside_proofs k) Ms
  | nf_neut u => ne_fresh_outside_proofs k u
  | nf_record _ Ms => all_list (nf_fresh_outside_proofs k) Ms
  | nf_tuple _ Ms _ Ns => all_list (nf_fresh_outside_proofs k) Ms /\ all_list (nf_fresh_outside_proofs k) Ns
  end
with ne_fresh_outside_proofs (k : nat) (u : ne) {struct u} : Prop :=
  match u with
  | ne_absurd A _ | ne_absurd_erased A => nf_fresh_outside_proofs k A
  | ne_elim _ Us _ Bks u =>
      all_list (nf_fresh_outside_proofs k) Us /\
      all_list (normal_block_forall (fun n => nf_fresh_outside_proofs (n + k))) Bks /\ ne_fresh_outside_proofs k u
  | ne_app u W => ne_fresh_outside_proofs k u /\ nf_fresh_outside_proofs k W
  | ne_var x => x <> k
  | ne_glob _ => True
  | ne_proj _ u => ne_fresh_outside_proofs k u
  end.

(** Freshness outside proofs is the freshness of the erasure, and erasure
    keeps it. *)
Lemma nf_ne_fresh_outside_proofs_erase :
    (forall W k, nf_fresh_outside_proofs k W -> nf_fresh k (nf_erase W) /\ nf_fresh_outside_proofs k (nf_erase W)) /\
    (forall u k, ne_fresh_outside_proofs k u -> ne_fresh k (ne_erase u) /\ ne_fresh_outside_proofs k (ne_erase u)).
Proof.
  apply nf_ne_ind; intros; cbn [nf_erase ne_erase nf_fresh ne_fresh nf_fresh_outside_proofs ne_fresh_outside_proofs] in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    rewrite ?all_list_map; repeat split; try solve [ auto | firstorder ].
  all: eapply list_all_all_list_impl; [ eassumption | eassumption |]; cbn; intros x Hx Hy.
  all: try solve [ firstorder ].
  (** An atom of a level: its neutral *)
  all: try solve [ destruct Hx; unfold map_level_atom; cbn in *; firstorder ].
  (** A block: its scrutinee's type, its motive and its branches *)
  all: destruct Hx as [n' Z HZ A HA brs Hbrs]; unfold normal_block_forall, map_normal_block in *; cbn in *;
    destruct Hy as [HyZ [HyA Hybrs]]; split; [ firstorder | split; [ firstorder |] ];
    rewrite all_list_map; eapply list_all_all_list_impl; [ exact Hbrs | exact Hybrs |];
    intros br Hbr Hy'; destruct Hbr; cbn in *; firstorder.
Qed.

Lemma nf_fresh_outside_proofs_erase : forall k W, nf_fresh_outside_proofs k W -> nf_fresh k (nf_erase W).
Proof. intros k W H; exact (proj1 (proj1 nf_ne_fresh_outside_proofs_erase W k H)). Qed.

Lemma ne_fresh_outside_proofs_erased : forall k u, ne_fresh_outside_proofs k u -> ne_fresh_outside_proofs k (ne_erase u).
Proof. intros k u H; exact (proj2 (proj2 nf_ne_fresh_outside_proofs_erase u k H)). Qed.

(** ** Readback Introduces Only Variables Above the Ones in Scope *)

Lemma level_atoms_fresh_canon : forall k c xs, all_list (fun a => ne_fresh_outside_proofs k (atom_level a)) xs ->
    all_list (fun a => ne_fresh_outside_proofs k (atom_level a)) (snd (lvl_canon (c, xs))).
Proof.
  intros * H; apply level_atoms_all_all_list, level_atoms_all_canon, level_atoms_all_all_list;
    [ apply ne_fresh_outside_proofs_erased | assumption ].
Qed.

Section Read.
  Variables (v : nat).

  (** A neutral variable at the readback length, at a bound past it. *)
  Lemma domain_avoids_fresh_var : forall b s a, v < s -> b <= s -> domain_avoids v b a -> domain_avoids v (S s) (⇑! a s).
  Proof.
    intros * Hv Hb Ha; constructor; [ eapply (proj1 (domain_avoids_mono v b)); [ exact Ha | lia ] | constructor; lia ].
  Qed.

  (** The invariant of a value built during readback: by its constructor, by
      monotonicity, or by the evaluation it came from. *)
  Ltac domain_avoids_tac v :=
    first [ eassumption
          | solve [ constructor ]
          | match goal with H : domain_avoids v ?b0 ?d |- domain_avoids v ?n ?d => eapply (domain_avoids_mono' v b0 n d); [ lia | exact H ] end
          | match goal with |- domain_avoids v _ (d_neut _ (d_var _)) => constructor; [ domain_avoids_tac v | constructor; lia ] end
          | match goal with
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env (extend_env ?ρ ?c1 ?t1) ?c2 ?t2 ↘ ?d,
              Hρ : forall x, ?K <> Some x -> dentry_avoids v ?b0 (env_entry ?ρ x) |- domain_avoids v ?n ?d =>
                eapply (eval_clo2_avoids v n K ρ B c1 t1 c2 t2 d);
                  [ eapply env_avoids_mono; [| exact Hρ ]; lia | assumption | domain_avoids_tac v | domain_avoids_tac v | exact e ]
            end
          | match goal with
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env ?ρ ?c ?t ↘ ?d,
              Hρ : forall x, ?K <> Some x -> dentry_avoids v ?b0 (env_entry ?ρ x) |- domain_avoids v ?n ?d =>
                eapply (eval_clo_avoids v n K ρ B c t d);
                  [ eapply env_avoids_mono; [| exact Hρ ]; lia | assumption | domain_avoids_tac v | exact e ]
            end
          | match goal with
            | e : $| ?m & ?c | _ ⍮ _ ↘ ?d |- domain_avoids v ?n ?d =>
                eapply (app_avoids v n m c d); [ exact e | domain_avoids_tac v | domain_avoids_tac v ]
            end ].

  (** The fresh variables of the telescopes of a declaration are above the
      readback length, and below the length past them.  The types of the
      telescopes are closed, so their environments avoid [v] everywhere. *)
  Lemma fresh_tele_avoids : forall ρ T s vs, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      forall b, v < s -> b <= s -> env_avoids v b None ρ -> forall a, In a vs -> domain_avoids v (s + List.length T) a.
  Proof.
    induction 1; intros b0 Hv Hb Hρ; [ apply all_in_nil |].
    assert (Ha : domain_avoids v b0 a) by (eapply (proj1 (eval_avoids v b0)); [ eassumption | exact Hρ | exact I ]).
    cbn [List.length]; replace (s + S (List.length T)) with (S s + List.length T) by lia.
    apply all_in_cons.
    - eapply domain_avoids_mono'; [| apply (domain_avoids_fresh_var b0); assumption ]; lia.
    - apply (IHfresh_tele (S s)); [ lia | lia |].
      change (@None nat) with (optional_shift 1 None).
      apply env_avoids_cons; [ eapply env_avoids_mono; [| exact Hρ ]; lia | constructor; apply (domain_avoids_fresh_var b0); assumption ].
  Qed.

  Lemma fresh_cargs_avoids : forall p ups ρ gs s vs, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      forall b, v < s -> b <= s -> env_avoids v b None ρ -> (forall a, In a ups -> domain_avoids v b a) ->
      forall a, In a vs -> domain_avoids v (s + List.length gs) a.
  Proof.
    induction 1; intros b0 Hv Hb Hρ Hu.
    - apply all_in_nil.
    - assert (Ha : domain_avoids v b0 a) by (eapply (proj1 (eval_avoids v b0)); [ eassumption | exact Hρ | exact I ]).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      apply all_in_cons; [ eapply domain_avoids_mono'; [| apply (domain_avoids_fresh_var b0); assumption ]; lia |].
      apply (IHfresh_cargs (S s)); [ lia | lia | | intros; eapply domain_avoids_mono'; [| apply Hu; eassumption ]; lia ].
      change (@None nat) with (optional_shift 1 None).
      apply env_avoids_cons; [ eapply env_avoids_mono; [| exact Hρ ]; lia | constructor; apply (domain_avoids_fresh_var b0); assumption ].
    - assert (Ha : domain_avoids v b0 a) by (eapply shape_type_avoids; [ eassumption | exact Hρ | apply optional_ptyp_fresh_none | exact Hu ]).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      apply all_in_cons; [ eapply domain_avoids_mono'; [| apply (domain_avoids_fresh_var b0); assumption ]; lia |].
      apply (IHfresh_cargs b0); [ lia | lia | exact Hρ | exact Hu ].
  Qed.

  (** The fresh variables along the leaf paths of an argument, at avoiding
      types, are above the readback length and below the length past
      them. *)
  Lemma fresh_leaf_vars_avoids : forall bs as' s vs, fresh_leaf_vars bs as' s vs ->
      forall b, v < s -> b <= s -> (forall a, In a as' -> domain_avoids v b a) -> forall a, In a vs -> domain_avoids v (s + List.length vs) a.
  Proof.
    induction 1; intros b0 Hv Hb Ha; [ apply all_in_nil | | ].
    - cbn [List.length]; replace (s + S (List.length vs)) with (S s + List.length vs) by lia.
      apply all_in_cons.
      + eapply domain_avoids_mono'; [| apply (domain_avoids_fresh_var b0); [ assumption | assumption | apply Ha; left; reflexivity ] ]; lia.
      + apply (IHfresh_leaf_vars b0); [ lia | lia | all_in_with assumption ].
    - apply (IHfresh_leaf_vars b0); [ lia | lia | all_in_with assumption ].
  Qed.

  (** The recursive results are at the motive's instance at the recursive
      argument and its parameters, along each leaf path: as many as the
      motive binds, when the ends' motives are fresh ([ends_fresh]); they
      are below the length past them. *)
  Lemma fresh_ihs_avoids : forall ρ As p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
      forall b K, v < s -> b <= s -> env_avoids v b K ρ -> env_avoids v b None ρa -> ups_avoids v b ups ->
      (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p K As t) ->
      (forall a, In a vs -> domain_avoids v b a) ->
      forall a, In a ihs -> domain_avoids v (s + List.length ihs) a.
  Proof.
    induction 1; intros b0 K Hv Hb Hρ Hρa Hu Hl Hvs.
    - apply all_in_nil.
    - apply (IHfresh_ihs b0 K); try assumption.
      + apply env_avoids_cons_none; [ exact Hρa | exact (all_in_head _ _ _ Hvs) ].
      + intros gs1 t gs2 E; eapply (Hl (ca_arg _ _ :: gs1) t gs2); rewrite E; reflexivity.
      + exact (all_in_tail _ _ _ Hvs).
    - assert (Has : forall a, In a as' -> domain_avoids v b0 a)
        by (eapply ihty_avoids; [ eassumption | exact Hρ | exact (Hl nil t gs eq_refl) | exact Hu | exact Hρa | apply optional_ptyp_fresh_none
                            | exact (all_in_head _ _ _ Hvs) ]).
      match goal with Hf : fresh_leaf_vars _ _ _ _ |- _ => pose proof (fresh_leaf_vars_avoids _ _ _ _ Hf b0 Hv Hb Has) as H1v end.
      rewrite List.length_app; apply all_in_app.
      + intros a Ha; eapply domain_avoids_mono'; [| exact (H1v a Ha) ]; lia.
      + assert (Hr : forall a, In a ihs -> domain_avoids v (List.length ihs1 + s + List.length ihs) a).
        { apply (IHfresh_ihs b0 K); [ lia | lia | exact Hρ | exact Hρa | exact Hu | | exact (all_in_tail _ _ _ Hvs) ].
          intros gs1 t0 gs2 E; apply (Hl (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity. }
        intros a Ha; eapply domain_avoids_mono'; [| exact (Hr a Ha) ]; lia.
    - apply (IHfresh_ihs b0 K); try assumption.
      + intros gs1 t0 gs2 E; apply (Hl (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity.
      + exact (all_in_tail _ _ _ Hvs).
  Qed.

  (** The motive of a block of a stuck eliminator, at the fresh non-uniform
      parameters and scrutinee, which are above the readback length. *)
  Lemma motive_avoids : forall ρ K A D Mv ups pre hd k Mi s ns a b,
      Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns -> im_nn Mv = im_nn Mi ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns))
                                     (⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mi))) ↘ a ->
      v < s -> b <= s -> env_avoids v b K ρ -> optional_exp_fresh (optional_shift (S (im_nn Mi)) K) A ->
      (forall x, In x ups -> domain_avoids v b x) -> (forall x, In x pre -> domain_avoids v b x) ->
      domain_avoids v (S (s + im_nn Mi)) a.
  Proof.
    intros * f Hnn e Hv Hb Hρ HA HX Hp.
    pose proof (fresh_tele_length _ _ _ _ f) as Hlen; rewrite List.length_rev in Hlen.
    change (List.length (im_nparams Mv)) with (im_nn Mv) in Hlen; rewrite Hnn in Hlen.
    assert (Hns : forall x, In x ns -> domain_avoids v (s + im_nn Mi) x).
    { pose proof (fresh_tele_avoids _ _ _ _ f b Hv Hb (env_avoids_decl_env v b D ups HX)) as H.
      rewrite List.length_rev in H; change (List.length (im_nparams Mv)) with (im_nn Mv) in H; rewrite Hnn in H; exact H. }
    eapply (proj1 (eval_avoids v (S (s + im_nn Mi))));
      [ exact e | apply env_avoids_extend_typed; [ eapply env_avoids_mono; [| exact Hρ ]; lia |] |].
    - unfold motive_entries; rewrite List.map_app, tele_entries_values; cbn [List.map fst].
      apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; lia |].
      apply all_in_cons; [| apply all_in_nil ].
      apply (domain_avoids_fresh_var (s + im_nn Mi)); [ lia | lia |].
      constructor; apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hp; eassumption ]; lia | exact Hns ].
    - unfold motive_entries; rewrite <- List.length_map with (f := fst), List.map_app, tele_entries_values, List.length_app, Hlen;
        cbn [List.length List.map]; replace (im_nn Mi + 1) with (S (im_nn Mi)) by lia; exact HA.
  Qed.

  (** A branch of a block of a stuck eliminator, and the motive's instance
      it is read at: under the fresh non-uniform parameters, arguments and
      recursive results of the group read, as many as the branch binds. *)
  Lemma branch_avoids : forall ρ K p ups Bks Dc A B pre hd k c Mi Mv D gs' gs s n0 ns vs ihs wihs bv t b,
      Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi) ↘ vs ->
      Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮
        (s + im_nn Mi + List.length gs') ↘ ihs ->
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs) ↘ bv ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) (d_con hd k c (pre ++ ns ++ vs))) ↘ t ->
      ind_lookup Θ Ξ p = Some D ->
      n0 = (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat -> im_nn Mv = im_nn Mi ->
      cargs_container_count D Dc gs' gs = cargs_nrec Dc gs' ->
      cargs_params_length D gs -> blocks_binder_count_at D None Bks -> rview_leaf_arity D ->
      v < s -> b <= s -> env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks -> ups_avoids v b ups ->
      optional_exp_fresh (optional_shift (S (im_nn Mi)) K) A -> optional_exp_fresh (optional_shift n0 K) B ->
      (forall x, In x pre -> domain_avoids v b x) ->
      domain_avoids v (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) t /\
      domain_avoids v (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs')) bv.
  Proof.
    intros * f f0 f2 fw e0 e1 HD Hn0 Hnn Hcnt Hpl Hnm Har Hv Hb Hρ HBk HX HA HB Hp.
    set (n := (im_nn Mi + List.length gs' + cargs_nrec Dc gs')%nat).
    pose proof (fresh_tele_length _ _ _ _ f) as Hl1; rewrite List.length_rev in Hl1.
    change (List.length (im_nparams Mv)) with (im_nn Mv) in Hl1; rewrite Hnn in Hl1.
    pose proof (fresh_cargs_length _ _ _ _ _ _ f0) as Hl2.
    pose proof (leaves_coherent_of_order _ (rview_leaf_order _ Har)) as Hco.
    destruct (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ HD Hco fw) as [Hl3 Hl4].
    pose proof (fresh_ihs_length _ _ _ _ _ _ _ _ _ _ _ _ HD f2) as Hl5; rewrite Hcnt in Hl5.
    assert (Ho : ups_avoids v b ups) by exact HX.
    assert (Hns : forall x, In x ns -> domain_avoids v (s + im_nn Mi) x).
    { pose proof (fresh_tele_avoids _ _ _ _ f b Hv Hb (env_avoids_decl_env v b D ups HX)) as H.
      rewrite List.length_rev in H; change (List.length (im_nparams Mv)) with (im_nn Mv) in H; rewrite Hnn in H; exact H. }
    assert (Hρa : env_avoids v (s + im_nn Mi) None (env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns)).
    { unfold env_tele; apply env_avoids_extend_typed_none;
        [ eapply env_avoids_mono; [| exact (env_avoids_decl_env v b D ups HX) ]; lia | rewrite tele_entries_values; exact Hns ]. }
    pose proof (fresh_cargs_avoids _ _ _ _ _ _ f0 (s + im_nn Mi) ltac:(lia) ltac:(lia) Hρa
                  ltac:(intros; eapply domain_avoids_mono'; [| apply HX; eassumption ]; lia)) as Hvs.
    assert (Hgl : List.length gs = List.length gs') by congruence.
    rewrite Hgl in Hvs.
    pose proof (fresh_ihs_avoids _ _ _ _ _ _ _ _ _ _ _ f2 (s + im_nn Mi + List.length gs') K
                  ltac:(lia) ltac:(lia) ltac:(eapply env_avoids_mono; [| exact Hρ ]; lia)
                  ltac:(eapply env_avoids_mono; [| exact Hρa ]; lia)
                  ltac:(eapply ups_avoids_mono; [| exact Ho ]; lia)
                  (cargs_ends_fresh _ _ _ _ _ HD Har Hnm HBk Hpl) Hvs) as Hihs.
    rewrite Hl5 in Hihs.
    assert (Hw : forall x, In x wihs -> domain_avoids v (s + n) x).
    { eapply wrap_ihs_eval_avoids; [ exact fw | eapply env_avoids_mono; [| exact Hρ ]; unfold n; lia | exact HBk |
        eapply ups_avoids_mono; [| exact Ho ]; unfold n; lia |
        intros; eapply domain_avoids_mono'; [| apply Hvs; eassumption ]; unfold n; lia |
        intros; eapply domain_avoids_mono'; [| apply Hihs; eassumption ]; unfold n; lia ]. }
    split.
    - eapply (proj1 (eval_avoids v (s + n)));
        [ exact e1 | apply env_avoids_extend_typed; [ eapply env_avoids_mono; [| exact Hρ ]; unfold n; lia |] |].
      + unfold motive_entries; rewrite List.map_app, tele_entries_values; cbn [List.map fst].
        apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_cons; [| apply all_in_nil ].
        constructor; apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hp; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; unfold n; lia
                          | intros; eapply domain_avoids_mono'; [| apply Hvs; eassumption ]; unfold n; lia ].
      + unfold motive_entries; rewrite <- List.length_map with (f := fst), List.map_app, tele_entries_values, List.length_app, Hl1;
          cbn [List.length List.map]; replace (im_nn Mi + 1) with (S (im_nn Mi)) by lia; exact HA.
    - eapply (proj1 (eval_avoids v (s + n)));
        [ exact e0 | apply env_avoids_extend_typed; [ eapply env_avoids_mono; [| exact Hρ ]; unfold n; lia |] |].
      + unfold branch_entries; cbv zeta;
          rewrite !List.map_app, tele_entries_values, cargs_entries_values, pair_values_with_types_values.
        apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hvs; eassumption ]; unfold n; lia | exact Hw ].
      + rewrite <- List.length_map with (f := fst); unfold branch_entries; cbv zeta;
          rewrite !List.map_app, tele_entries_values, cargs_entries_values, pair_values_with_types_values.
        rewrite !List.length_app, Hl1, Hl2, Hgl, Hl3, Nat.add_assoc, <- Hn0; exact HB.
  Qed.

  Lemma read_avoids :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall b, v < s -> b <= s -> domain_nf_avoids v b m -> nf_fresh_outside_proofs (s - v - 1) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall b, v < s -> b <= s -> domain_ne_avoids v b m -> ne_fresh_outside_proofs (s - v - 1) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall b, v < s -> b <= s -> domain_avoids v b a -> nf_fresh_outside_proofs (s - v - 1) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall b, v < s -> b <= s -> level_atoms_avoid v b xs -> all_list (fun a => ne_fresh_outside_proofs (s - v - 1) (atom_level a)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> (forall a, In a vs -> domain_avoids v b a) ->
       all_list (nf_fresh_outside_proofs (s - v - 1)) Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> (forall a, In a ups -> domain_avoids v b a) ->
       (forall a, In a vs -> domain_avoids v b a) -> all_list (nf_fresh_outside_proofs (s - v - 1)) Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> (forall a, In a ups -> domain_avoids v b a) ->
       domain_avoids v b x -> nf_fresh_outside_proofs (s - v - 1) X) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       forall b K D, v < s -> b <= s -> env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks ->
       ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks -> rview_leaf_arity D ->
       (forall a, In a ups -> domain_avoids v b a) -> all_list (normal_block_forall (fun n => nf_fresh_outside_proofs (n + (s - v - 1)))) NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       forall b K D, v < s -> b <= s -> env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks ->
       ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks -> rview_leaf_arity D -> im_nn Mv = im_nn Mi ->
       optional_exp_fresh (optional_shift (S (im_nn Mi)) K) A ->
       (forall c n B, In (c, n, B) Bs -> optional_exp_fresh (optional_shift n K) B) ->
       (forall a, In a ups -> domain_avoids v b a) -> (forall a, In a (snd r) -> domain_avoids v b a) -> all_list (fun br => nf_fresh_outside_proofs (branch_arity br + (s - v - 1)) (branch_body br)) Bs') /\
    (forall s ρ fl d Fs, Rflds d at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> domain_avoids v b d -> all_list (nf_fresh_outside_proofs (s - v - 1)) Fs) /\
    (** The readbacks of a kept proof, which freshness outside proofs
        exempts, ask nothing *)
    (forall s d M, Rprf d in Θ ⍮ Ξ ⍮ s ↘ M -> True) /\
    (forall s ρ k bs, Rlets ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs -> True) /\
    (forall s e bd, Rent e in Θ ⍮ Ξ ⍮ s ↘ bd -> True).
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall b, v < s -> b <= s -> domain_nf_avoids v b m -> nf_fresh_outside_proofs (s - v - 1) W)
             (fun s m M _ => forall b, v < s -> b <= s -> domain_ne_avoids v b m -> ne_fresh_outside_proofs (s - v - 1) M)
             (fun s a A _ => forall b, v < s -> b <= s -> domain_avoids v b a -> nf_fresh_outside_proofs (s - v - 1) A)
             (fun s xs ys _ => forall b, v < s -> b <= s -> level_atoms_avoid v b xs -> all_list (fun a => ne_fresh_outside_proofs (s - v - 1) (atom_level a)) ys)
             (fun s ρ T vs Ms _ => forall b, v < s -> b <= s -> env_avoids v b None ρ ->
                                  (forall a, In a vs -> domain_avoids v b a) -> all_list (nf_fresh_outside_proofs (s - v - 1)) Ms)
             (fun s p ups ρ gs vs Ms _ => forall b, v < s -> b <= s -> env_avoids v b None ρ ->
                                        (forall a, In a ups -> domain_avoids v b a) ->
                                        (forall a, In a vs -> domain_avoids v b a) -> all_list (nf_fresh_outside_proofs (s - v - 1)) Ms)
             (fun s p ups ρ t x X _ => forall b, v < s -> b <= s -> env_avoids v b None ρ ->
                                     (forall a, In a ups -> domain_avoids v b a) -> domain_avoids v b x -> nf_fresh_outside_proofs (s - v - 1) X)
             (fun s ρ p ups Bks Dc sel i Ms NBks _ => forall b K D, v < s -> b <= s -> env_avoids v b K ρ ->
                                                      blocks_optional_exp_fresh K Bks ->
                                                      ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks ->
                                                      rview_leaf_arity D ->
                                                      (forall a, In a ups -> domain_avoids v b a) -> all_list (normal_block_forall (fun n => nf_fresh_outside_proofs (n + (s - v - 1)))) NBks)
             (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ => forall b K D, v < s -> b <= s -> env_avoids v b K ρ ->
                                                            blocks_optional_exp_fresh K Bks ->
                                                            ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks ->
                                                            rview_leaf_arity D ->
                                                            im_nn Mv = im_nn Mi ->
                                                            optional_exp_fresh (optional_shift (S (im_nn Mi)) K) A ->
                                                            (forall c n B, In (c, n, B) Bs -> optional_exp_fresh (optional_shift n K) B) ->
                                                            (forall a, In a ups -> domain_avoids v b a) ->
                                                            (forall a, In a (snd r) -> domain_avoids v b a) -> all_list (fun br => nf_fresh_outside_proofs (branch_arity br + (s - v - 1)) (branch_body br)) Bs')
             (fun s ρ fl d Fs _ => forall b, v < s -> b <= s -> env_avoids v b None ρ -> domain_avoids v b d -> all_list (nf_fresh_outside_proofs (s - v - 1)) Fs)
             (fun s d M _ => True)
             (fun s ρ k bs _ => True)
             (fun s e bd _ => True));
      intros; cbn [snd] in *; try exact I;
      repeat match goal with
        | H : domain_nf_avoids _ _ (_ _ _) |- _ => inversion_clear H
        | H : level_atoms_avoid _ _ (_ :: _) |- _ => inversion_clear H
        end.
    all: repeat match goal with
      | H : domain_avoids _ _ (d_neut _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_lvl _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_suniv _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_pi _ _ _ _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_ind _ _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_con _ _ _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_app _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_var _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_and _ _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_absurd _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_elim _ _ _ _ _ _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_record _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_proj _ _) |- _ => inversion_clear H
      | H : domain_nf_avoids _ _ (_ _ _) |- _ => inversion_clear H
      end.
    (** The group of a stuck eliminator's blocks, looked up once. *)
    all: repeat match goal with
      | H1 : ind_lookup _ _ ?p = Some ?D1, H2 : ind_lookup _ _ ?p = Some ?D2 |- _ =>
          assert_fails (constr_eq D1 D2); rewrite H1 in H2; injection H2 as <-
      end.
    all: cbn [nf_fresh_outside_proofs ne_fresh_outside_proofs all_list nf_lvl_of nf_univ_of fst snd]; unfold normal_block_forall;
      cbn [block_arity block_motive block_branches branch_arity branch_body]; repeat split.
    all: try exact I.
    all: try lia.
    all: try solve [ eauto 3 with mctt ].
    all: try solve [ apply level_atoms_fresh_canon; eauto 3 with mctt ].
    (** Inductive types.  The parameters and the arguments of a constructor,
        and the parameters of a type, are read back at their types, which
        are closed. *)
    all: try solve [ match goal with
      | IH1 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh_outside_proofs _) ?Ps,
        IH2 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (env_tele nil _ ?as') -> _ -> _ -> all_list (nf_fresh_outside_proofs _) ?Args,
        Hb : ?b <= ?s, Ha : forall a, In a ?as' -> domain_avoids v ?b a |- all_list (nf_fresh_outside_proofs _) (?Ps ++ ?Args) =>
          apply all_list_app;
            [ apply (IH1 b); [ lia | lia | apply env_avoids_nil | assumption ]
            | apply (IH2 b); [ lia | lia | apply env_avoids_env_tele_none; [ apply env_avoids_nil | assumption ]
                             | all_in_with assumption | all_in_with assumption ] ]
      end ].
    (** A record view's element: the group's uniform parameters, then its
        fields, read from its projections. *)
    all: try solve [ match goal with
      | e : eval_projs _ _ _ ?x ?ws, Hx : domain_avoids v ?b ?x,
        IH1 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh_outside_proofs _) ?Ps,
        IH2 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (env_tele nil _ ?as') -> _ -> _ -> all_list (nf_fresh_outside_proofs _) ?Args,
        Hb : ?b <= ?s, Ha : forall a, In a ?as' -> domain_avoids v ?b a |- all_list (nf_fresh_outside_proofs _) (?Ps ++ ?Args) =>
          apply all_list_app;
            [ apply (IH1 b); [ lia | lia | apply env_avoids_nil | assumption ]
            | apply (IH2 b); [ lia | lia | apply env_avoids_env_tele_none; [ apply env_avoids_nil | assumption ]
                             | exact Ha | exact (projs_avoids _ _ _ _ _ e Hx) ] ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh_outside_proofs _) ?Ps,
        Hb : ?b <= ?s |- all_list (nf_fresh_outside_proofs _) ?Ps =>
          apply (IH b); [ lia | lia | apply env_avoids_nil | assumption ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> domain_avoids v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> domain_nf_avoids v b0 (⇓ ?a ?v0) -> nf_fresh_outside_proofs _ ?V |- nf_fresh_outside_proofs _ ?V =>
          apply (IH b); [ lia | lia | constructor;
            [ eapply (proj1 (eval_avoids v b)); [ exact e | exact Hρ | exact I ] | exact (all_in_head _ _ _ Hv) ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> domain_avoids v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (?ρ ↦ ?v0 ⦂ _) -> _ |- all_list (nf_fresh_outside_proofs _) _ =>
          apply (IH b); try lia;
            [ apply env_avoids_cons_none; [ exact Hρ | exact (all_in_head _ _ _ Hv) ] |..]; all_in_with assumption
      end ].
    (** A recursive argument, by its shape. *)
    all: try solve [ match goal with
      | Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> domain_avoids v ?b x,
        Hv : forall x, In x (?v0 :: _) -> domain_avoids v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None ?ρ -> (forall a, In a ?ups -> _) -> domain_avoids v b0 ?v0 ->
             nf_fresh_outside_proofs _ ?V |- nf_fresh_outside_proofs _ ?V =>
          apply (IH b); [ lia | lia | exact Hρ | exact Hu | exact (all_in_head _ _ _ Hv) ]
      end ].
    (** The end of a shape: the member at the uniform parameters and the
        shape's own. *)
    all: try solve [ match goal with
      | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ ?ρ ↘ ?bs, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> domain_avoids v ?b x, Hx : domain_avoids v ?b ?x0,
        IH : forall b0, v < ?s -> b0 <= ?s -> domain_nf_avoids v b0 (⇓ (d_ind ?p ?j (?ups ++ ?bs)) ?x0) -> nf_fresh_outside_proofs _ ?V
        |- nf_fresh_outside_proofs _ ?V =>
          apply (IH b); [ lia | lia | constructor; [| exact Hx ] ];
          apply domain_avoids_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha];
            [ exact (Hu _ Ha)
            | exact (proj1 (proj2 (proj2 (eval_avoids v b))) _ _ _ e None Hρ
                       (proj2 (List.Forall_forall _ _) (fun _ _ => I)) _ Ha) ]
      end ].
    (** A function shape: under a fresh variable of its domain. *)
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b0, ea : $| ?x0 & ⇑! ?b0 ?s | _ ⍮ _ ↘ ?r,
        Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> domain_avoids v ?b x, Hx : domain_avoids v ?b ?x0,
        IHA : forall b1, v < ?s -> b1 <= ?s -> domain_avoids v b1 ?b0 -> nf_fresh_outside_proofs _ ?A |- nf_fresh_outside_proofs _ ?A =>
          apply (IHA b); [ lia | lia | eapply (proj1 (eval_avoids v b)); [ exact e | exact Hρ | exact I ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b0, ea : $| ?x0 & ⇑! ?b0 ?s | _ ⍮ _ ↘ ?r,
        Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> domain_avoids v ?b x, Hx : domain_avoids v ?b ?x0,
        IHV : forall b1, v < S ?s -> b1 <= S ?s -> env_avoids v b1 None (?ρ ↦ ⇑! ?b0 ?s ⦂ _) ->
              (forall a, In a ?ups -> _) -> domain_avoids v b1 ?r -> nf_fresh_outside_proofs _ ?V |- nf_fresh_outside_proofs _ ?V =>
          let Hb0 := fresh "Hb0" in
          assert (Hb0 : domain_avoids v b b0) by (eapply (proj1 (eval_avoids v b)); [ exact e | exact Hρ | exact I ]);
          try replace (S (s - v - 1)) with (S s - v - 1) by lia;
          apply (IHV (S s));
            [ lia | lia
            | apply env_avoids_cons_none; [ eapply env_avoids_mono; [| exact Hρ ]; lia | eapply domain_avoids_fresh_var; eassumption ]
            | intros; eapply domain_avoids_mono'; [| apply Hu; eassumption ]; lia
            | eapply app_avoids; [ exact ea | eapply domain_avoids_mono'; [| exact Hx ]; lia | eapply domain_avoids_fresh_var; eassumption ] ]
      end ].
    all: try solve [ match goal with
      | Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (_ :: ?vs) -> domain_avoids v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None ?ρ -> _ -> (forall x, In x ?vs -> _) -> all_list (nf_fresh_outside_proofs _) ?W
        |- all_list (nf_fresh_outside_proofs _) ?W =>
          apply (IH b); [ lia | lia | exact Hρ | assumption | exact (all_in_tail _ _ _ Hv) ]
      end ].
    (** A stuck eliminator: the container's uniform parameters read at
        their telescope; the blocks at the eliminator's uniform
        parameters. *)
    all: try solve [ match goal with
      | em : eval_mref _ _ _ ?ups _ (_, _, ?pre),
        Hu : forall a, In a ?ups -> domain_avoids v ?b a, Hb : ?b <= ?s,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh_outside_proofs _) ?Ps |- all_list (nf_fresh_outside_proofs _) ?Ps =>
          apply (IH b); [ lia | lia | apply env_avoids_nil | exact (mref_avoids _ _ _ _ _ _ em Hu) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_avoids v b0 K0 ?ρ -> blocks_optional_exp_fresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_binder_count_at D0 None ?Bks -> rview_leaf_arity D0 ->
               (forall a, In a ?ups -> _) -> all_list _ ?W,
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_binder_count_at ?D None ?Bks, Har : rview_leaf_arity ?D,
        Hb : ?b <= ?s, Hρ : forall x, ?K <> Some x -> dentry_avoids v ?b (env_entry ?ρ x), HBk : blocks_optional_exp_fresh ?K ?Bks,
        Hu : forall a, In a ?ups -> domain_avoids v ?b a |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm | exact Har | exact Hu ]
      end ].
    (** A block: its motive under the fresh non-uniform parameters of its
        member and the scrutinee; its branches; and the blocks after it.
        The block's member has as many non-uniform parameters as the member
        read, both being the motive's binders. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (decl_env _ ?X) (List.rev (im_nparams ?Mv)) ?s ?ns,
        Hnth : List.nth_error ?Bks ?ix = Some ?bk, Hnmb : eb_binder_count ?bk = S (im_nn ?Mi), HMv : ind_member ?D ?ix = Some ?Mv,
        Hnm : blocks_binder_count_at ?D None ?Bks,
        em : eval_mref _ _ _ ?X _ (_, _, ?pre),
        e2 : ⟦ eb_motive ?bk ⟧ _ ⍮ _ ⍮ env_extend_typed ?ρ (motive_entries _ _ _ ?ns _ _) ↘ ?a,
        IH : forall b0, _ -> _ -> domain_avoids v b0 ?a -> nf_fresh_outside_proofs _ ?A',
        Hb : ?b <= ?s, Hρ : env_avoids v ?b ?K ?ρ, HBk : blocks_optional_exp_fresh ?K ?Bks,
        HX : forall x, In x ?X -> domain_avoids v ?b x |- nf_fresh_outside_proofs (S (im_nn ?Mi) + _) ?A' =>
          let Hnn := fresh "Hnn" in
          assert (Hnn : im_nn Mv = im_nn Mi) by (pose proof (Hnm _ _ _ HMv Hnth) as Hx; cbn [elim_src] in Hx; congruence);
          replace (S (im_nn Mi) + (s - v - 1)) with (S (s + im_nn Mi) - v - 1) by lia;
          apply (IH (S (s + im_nn Mi))); [ lia | lia |];
          eapply motive_avoids; [ exact f | exact Hnn | exact e2 | assumption | exact Hb | exact Hρ
                            | rewrite <- Hnmb; exact (proj1 (HBk _ (List.nth_error_In _ _ Hnth))) | exact HX
                            | exact (mref_avoids _ _ _ _ _ _ em HX) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_avoids v b0 K0 ?ρ -> blocks_optional_exp_fresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_binder_count_at D0 None ?Bks -> rview_leaf_arity D0 -> im_nn ?Mv = im_nn ?Mi ->
               _ -> _ -> _ -> _ -> all_list _ ?W,
        Hnth : List.nth_error ?Bks ?ix = Some ?bk, Hnmb : eb_binder_count ?bk = S (im_nn ?Mi), HMv : ind_member ?D ?ix = Some ?Mv,
        em : eval_mref _ _ _ ?X _ (_, _, ?pre),
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_binder_count_at ?D None ?Bks, Har : rview_leaf_arity ?D,
        Hb : ?b <= ?s, Hρ : env_avoids v ?b ?K ?ρ, HBk : blocks_optional_exp_fresh ?K ?Bks,
        HX : forall x, In x ?X -> domain_avoids v ?b x |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm | exact Har
                            | pose proof (Hnm _ _ _ HMv Hnth) as Hx; cbn [elim_src] in Hx; congruence
                            | rewrite <- Hnmb; exact (proj1 (HBk _ (List.nth_error_In _ _ Hnth)))
                            | exact (proj2 (HBk _ (List.nth_error_In _ _ Hnth))) | exact HX
                            | exact (mref_avoids _ _ _ _ _ _ em HX) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_avoids v b0 K0 ?ρ -> blocks_optional_exp_fresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_binder_count_at D0 None ?Bks -> rview_leaf_arity D0 ->
               (forall a, In a ?X -> _) -> all_list _ ?W,
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_binder_count_at ?D None ?Bks, Har : rview_leaf_arity ?D,
        Hb : ?b <= ?s, Hρ : env_avoids v ?b ?K ?ρ, HBk : blocks_optional_exp_fresh ?K ?Bks,
        HX : forall x, In x ?X -> domain_avoids v ?b x |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm | exact Har | exact HX ]
      end ].
    (** A branch: under the fresh non-uniform parameters, arguments and
        recursive results, as many as it binds. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (decl_env _ ?X) _ ?s ?ns,
        f0 : fresh_cargs _ _ _ _ _ ?gs _ ?vs,
        f2 : fresh_ihs _ _ ?ρ _ _ _ _ _ ?gs' ?gs ?vs _ ?ihs,
        fw : wrap_ihs_eval _ _ ?ρ _ _ _ _ ?gs' ?gs ?vs ?ihs ?wihs,
        e0 : ⟦ ?B ⟧ _ ⍮ _ ⍮ env_extend_typed ?ρ (branch_entries _ _ _ _ _ _ _ ?ns ?vs ?wihs) ↘ ?bv,
        e1 : ⟦ ?A ⟧ _ ⍮ _ ⍮ env_extend_typed ?ρ (motive_entries _ _ _ ?ns _ _) ↘ ?t,
        HD0 : ind_lookup _ _ _ = Some ?D0,
        Hn0 : ?n0 = _, Hn : ?n = _, Hnn : im_nn _ = im_nn ?Mi, Hcnt : cargs_container_count ?D0 _ ?gs' ?gs = _,
        Hpl : cargs_params_length ?D0 ?gs, Hnm : blocks_binder_count_at ?D0 None ?Bks, Har : rview_leaf_arity ?D0,
        IH : forall b0, _ -> _ -> domain_nf_avoids v b0 (⇓ ?t ?bv) -> nf_fresh_outside_proofs _ ?B',
        Hb : ?b <= ?s, Hρ : env_avoids v ?b ?K ?ρ, HBk : blocks_optional_exp_fresh ?K ?Bks,
        HA : optional_exp_fresh (optional_shift (S (im_nn ?Mi)) ?K) ?A,
        HB : forall c0 n0 B0, In (c0, n0, B0) (_ :: _) -> optional_exp_fresh (optional_shift n0 ?K) B0,
        HX : forall x, In x ?X -> domain_avoids v ?b x, Hp : forall x, In x ?pre -> domain_avoids v ?b x |- nf_fresh_outside_proofs (?n + _) ?B' =>
          let Hbr := fresh "Hbr" in
          pose proof (branch_avoids _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b f f0 f2 fw e0 e1 HD0 Hn0 Hnn Hcnt Hpl Hnm
                        Har ltac:(assumption) Hb Hρ HBk HX HA (HB _ _ _ (or_introl eq_refl)) Hp) as Hbr;
          rewrite <- Hn in Hbr;
          replace (n + (s - v - 1)) with (s + n - v - 1) by lia;
          apply (IH (s + n)); [ lia | lia | constructor; apply Hbr ]
      end ].
    all: try solve [ match goal with
      | IH : context [ all_list _ ?W ], HB : forall c0 n0 B0, In (c0, n0, B0) (_ :: _) -> _ |- all_list _ ?W =>
          eapply IH;
            [ lia | | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
            | intros c1 n1 B1 Hin; exact (HB c1 n1 B1 (or_intror Hin)) | eassumption | eassumption ];
          lia
      end ].
    (** Records: the fields of a tuple read in the environment of the
        parameters; each field projected, at its type evaluated in the
        environment of the fields before it. *)
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (env_tele nil _ ?ns) -> domain_avoids v b0 ?d -> all_list (nf_fresh_outside_proofs _) ?W,
        Hb : ?b <= ?s, Hn : forall a, In a ?ns -> domain_avoids v ?b a, Hd : domain_avoids v ?b ?d |- all_list (nf_fresh_outside_proofs _) ?W =>
          apply (IH b); [ lia | lia | apply env_avoids_env_tele_none; [ apply env_avoids_nil | exact Hn ] | exact Hd ]
      end ].
    all: try solve [ match goal with
      | e : eval_proj _ _ _ ?d ?r, e0 : ⟦ ?T ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?t, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s, Hd : domain_avoids v ?b ?d,
        IH : forall b0, v < ?s -> b0 <= ?s -> domain_nf_avoids v b0 (⇓ ?t ?r) -> nf_fresh_outside_proofs _ ?W |- nf_fresh_outside_proofs _ ?W =>
          apply (IH b);
            [ lia | lia
            | constructor; [ eapply (proj1 (eval_avoids v b)); [ exact e0 | exact Hρ | exact I ] | exact (proj_avoids _ _ _ _ _ e Hd) ] ]
      end ].
    all: try solve [ match goal with
      | e : eval_proj _ _ _ ?d ?r, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s, Hd : domain_avoids v ?b ?d,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (?ρ ↦ ?r ⦂ _) -> domain_avoids v b0 ?d -> all_list (nf_fresh_outside_proofs _) ?W |- all_list (nf_fresh_outside_proofs _) ?W =>
          apply (IH b); [ lia | lia | apply env_avoids_cons_none; [ exact Hρ | exact (proj_avoids _ _ _ _ _ e Hd) ] | exact Hd ]
      end ].
    (** A small universe reads back at the canonical level its level reads
        back as, and the two normal forms have the same atoms, so this case
        is the level's. *)
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> _ -> nf_fresh_outside_proofs _ (nf_lvl_of _), Hb : ?b <= ?s |- all_list _ _ =>
          apply (IH b); [ lia | lia |]; repeat constructor; assumption
      end ].
    all: cbn [atom_level block_scrutinee_type block_arity] in *.
    (** A neutral level: its atom, erased *)
    all: try solve [ apply ne_fresh_outside_proofs_erased;
                     match goal with IH : forall b0, _ -> b0 <= _ -> domain_ne_avoids _ b0 ?m -> _, Hm : domain_ne_avoids _ ?b ?m |- _ =>
                       apply (IH b); [ lia | lia | exact Hm ] end ].
    (** Ex falso: its type; its proof is exempt *)
    all: try solve [ match goal with H3 : domain_ne_avoids _ _ (d_absurd _ _) |- _ => inversion_clear H3 end;
                     match goal with IH : forall b0, _ -> b0 <= _ -> domain_avoids _ b0 ?c -> _, Hc : domain_avoids _ ?b ?c |- _ =>
                       apply (IH b); [ lia | lia | exact Hc ] end ].
    (** A record view's element: the group's uniform parameters, then its
        fields, read from its projections in the parameters' environment *)
    all: try solve [ match goal with
      | e : eval_projs _ _ _ ?x ?ws, Hx : domain_avoids v ?b ?x,
        IH1 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh_outside_proofs _) ?Ps,
        IH2 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (decl_env _ ?as') -> _ -> _ -> all_list (nf_fresh_outside_proofs _) ?Args,
        Hb : ?b <= ?s, Ha : forall a, In a ?as' -> domain_avoids v ?b a |- all_list (nf_fresh_outside_proofs _) (?Ps ++ ?Args) =>
          apply all_list_app;
            [ apply (IH1 b); [ lia | lia | apply env_avoids_nil | assumption ]
            | apply (IH2 b); [ lia | lia | apply env_avoids_decl_env; exact Ha | exact Ha | exact (projs_avoids _ _ _ _ _ e Hx) ] ]
      end ].
    (** A block's scrutinee type: the member read, at the container's
        uniform parameters and the fresh non-uniform ones *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (decl_env ?D ?ups) (List.rev (im_nparams ?Mv)) ?s ?ns, e0 : ind_member ?D _ = Some ?Mv, e1 : List.nth_error ?Bks _ = Some ?bk,
        e2 : eb_binder_count ?bk = S (im_nn ?Mi), Hnm : blocks_binder_count_at ?D None ?Bks, em : eval_mref _ _ _ ?ups _ (_, _, ?pre),
        Hu : forall a0, In a0 ?ups -> domain_avoids v ?b0 a0, Hv : v < ?s, Hb : ?b0 <= ?s,
        IH : forall b1, _ -> _ -> domain_avoids v b1 (d_ind _ _ (?pre ++ ?ns)) -> nf_fresh_outside_proofs _ ?Z |- nf_fresh_outside_proofs _ ?Z =>
          let Hnn := fresh "Hnn" in let Hns := fresh "Hns" in
          assert (Hnn : im_nn Mv = im_nn Mi) by (pose proof (Hnm _ _ _ e0 e1) as Hx; cbn [elim_src] in Hx; congruence);
          replace (S (im_nn Mi) - 1 + (s - v - 1)) with (s + im_nn Mi - v - 1) by lia;
          apply (IH (s + im_nn Mi)); [ lia | lia |];
          pose proof (fresh_tele_avoids _ _ _ _ f b0 Hv Hb (env_avoids_decl_env v b0 D ups Hu)) as Hns;
          rewrite List.length_rev in Hns; change (List.length (im_nparams Mv)) with (im_nn Mv) in Hns; rewrite Hnn in Hns;
          apply domain_avoids_indty; intros x Hx; apply List.in_app_or in Hx as [Hx | Hx];
            [ eapply domain_avoids_mono'; [| exact (mref_avoids _ _ _ _ _ _ em Hu _ Hx) ]; lia | exact (Hns _ Hx) ]
      end ].
    (** Under a binder: the closure is evaluated at a neutral at the readback
        length, which is above the bound, and read back one step further. *)
    all: repeat match goal with
      | |- context [ S (S (?s - v - 1)) ] => replace (S (S (s - v - 1))) with (S (S s) - v - 1) by lia
      | |- context [ S (?s - v - 1) ] => replace (S (s - v - 1)) with (S s - v - 1) by lia
      end.
    all: match goal with H : forall b1, _ -> b1 <= ?n -> _ -> ?C |- ?C => apply (H n); [ lia | lia |] end.
    all: repeat constructor.
    all: domain_avoids_tac v.
  Qed.
End Read.

End Global.

(** ** The Initial Environment, and the Corollary *)

(** The initial environment of a context mentions only the levels below its
    length. *)
Lemma initial_env_avoids : forall Θ Ξ Γ ρ,
    initial_env Θ Ξ Γ ρ ->
    forall v b, List.length Γ <= v -> List.length Γ <= b -> env_avoids Θ Ξ v b None ρ.
Proof.
  intros Θ Ξ; induction 1; intros v' b' Hv Hb; cbn [List.length] in *.
  - apply env_avoids_nil.
  - (* an assumption: a variable, at its type *)
    change None with (optional_shift 1 None).
    apply env_avoids_cons; [ apply IHinitial_env; lia |].
    constructor; constructor;
      [ eapply (proj1 (eval_avoids Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ]
      | constructor; lia ].
  - change None with (optional_shift 1 None).
    apply env_avoids_cons; [ apply IHinitial_env; lia |].
    constructor; eapply (proj1 (eval_avoids Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ].
  - (* a definition of a proposition: the proof *)
    change None with (optional_shift 1 None).
    apply env_avoids_cons; [ apply IHinitial_env; lia |].
    constructor; constructor.
  - change None with (optional_shift 1 None).
    apply env_avoids_cons; [ apply IHinitial_env; lia |].
    constructor; eapply (proj1 (proj2 (proj2 (proj2 (proj2 (eval_avoids Θ Ξ v' b')))))); [ eassumption | apply IHinitial_env; lia | exact I ].
  - change None with (optional_shift 1 None).
    apply env_avoids_cons; [ apply IHinitial_env; lia |].
    constructor;
      [ eapply (proj1 (eval_avoids Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ]
      | eapply (proj1 (proj2 (proj2 (proj2 (proj2 (eval_avoids Θ Ξ v' b')))))); [ eassumption | apply IHinitial_env; lia | exact I ] ].
Qed.

(** The environment of [Γ ▹ A] avoids the new variable everywhere except at
    its own position. *)
Lemma initial_env_wk_avoids : forall Θ Ξ Γ κ A ρ,
    initial_env Θ Ξ (Γ ▹{κ} A) ρ ->
    env_avoids Θ Ξ (List.length Γ) (S (List.length Γ)) (Some 0) ρ.
Proof.
  intros * Hρ; inversion_clear Hρ.
  apply env_avoids_cons_bad; eapply initial_env_avoids; [ eassumption | lia | lia ].
Qed.

(** NbE invents no variables: a weakened term, normalized in the extended
    context at its weakened type, has a normal form fresh at the new
    variable outside its proofs: its erasure is fresh.  The proofs need
    not be: a proof is kept over the environment and read back under
    definitions of the positions its term reaches, which for a weakened
    term include the new variable.  For example, in
    [Γ = (P : Prop) ▹ (h : P)] extended by [A = ⊤], the weakened proof
    [h[↑] = #1] of [P[↑] = #2] reads back as
    [let x : P ≔ h in let y : ⊤ ≔ #k in #1], [#k] the new variable. *)
Theorem nbe_wk_fresh : forall Θ Ξ Γ κ A M T W,
    nbe Θ Ξ (Γ ▹{κ} A) M[↑]ʷ T[↑]ʷ W ->
    nf_fresh 0 (nf_erase W).
Proof.
  intros * Hn; destruct Hn as [? ? Hρ ? Hnt]; apply nf_fresh_outside_proofs_erase.
  pose proof (initial_env_wk_avoids _ _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  (** The value read back: a proof kept as it is, or the term's value *)
  destruct Hnt as [w _ Hw | m W' _ ? ?];
    (eapply (proj1 (read_avoids Θ Ξ (List.length Γ))); [ eassumption | cbn; lia | cbn; reflexivity |]);
    constructor; first [ constructor | eapply (proj1 (eval_avoids Θ Ξ _ _)); (eassumption || apply exp_shift_fresh) ].
Qed.

(** The same for the normal form of a weakened type: a type holds proofs
    at its indices. *)
Theorem nbe_ty_wk_fresh : forall Θ Ξ Γ κ A T W,
    nbe_ty Θ Ξ (Γ ▹{κ} A) T[↑]ʷ W ->
    nf_fresh 0 (nf_erase W).
Proof.
  intros * Hn; inversion_clear Hn as [? ? Hρ]; apply nf_fresh_outside_proofs_erase.
  pose proof (initial_env_wk_avoids _ _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  eapply (proj1 (proj2 (proj2 (read_avoids Θ Ξ (List.length Γ))))); [ eassumption | cbn; lia | cbn; reflexivity |].
  eapply (proj1 (eval_avoids Θ Ξ _ _)); (eassumption || apply exp_shift_fresh).
Qed.
