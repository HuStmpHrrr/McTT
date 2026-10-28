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

    The proof is structural, in the pattern of [Core.Semantic.Transparency]
    ([dclean]); readback is where the level arithmetic happens: a variable at
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
  forall b, In b Bks -> optional_exp_fresh (optional_shift (eb_nm b) K) (eb_motive b) /\
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
    optional_exp_fresh (optional_shift (S (List.length Ps)) Km) (List.nth j As a_True) -> ends_fresh p Km As (pt_self j Ps)
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
  (** A [Π]: its domain avoids, and its closure avoids but at [K], where
      the codomain is fresh *)
  | domain_avoids_pi : forall a (ρ : env) B K,
      domain_avoids a ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_exp_fresh (optional_shift 1 K) B ->
      domain_avoids (Πᵈ a ρ B)
  (** A large universe *)
  | domain_avoids_univ : forall i, domain_avoids 𝕌ω@i
  (** A small universe at an avoiding level *)
  | domain_avoids_suniv : forall l, domain_avoids l -> domain_avoids 𝕌@l
  (** A type of levels *)
  | domain_avoids_level : forall n, domain_avoids (Levelᵈ@n)
  (** A level of avoiding atoms *)
  | domain_avoids_lvl : forall c xs, level_atoms_avoid xs -> domain_avoids (lvᵈ c xs)
  (** The unit type *)
  | domain_avoids_True : domain_avoids ⊤ᵈ
  (** The unit's element *)
  | domain_avoids_true : domain_avoids ⋆ᵈ
  (** The empty type *)
  | domain_avoids_False : domain_avoids ⊥ᵈ
  (** A λ: its closure avoids but at [K], where the body is fresh *)
  | domain_avoids_fn : forall (ρ : env) M K,
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_exp_fresh (optional_shift 1 K) M ->
      domain_avoids (λᵈ ρ M)
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
      the argument. *)
  | domain_avoids_shfam : forall p ups (ρ : env) t K,
      (forall a, In a ups -> domain_avoids a) ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_ptyp_fresh (optional_shift 1 K) t ->
      domain_avoids (d_shfam p ups ρ t)
  (** The family of a recursive result at a function shape: the motives
      fresh at the rest's ends ([ends_fresh]), the group's uniform
      parameters (over which its record views' fields are) avoiding, the
      shape's rest fresh, the argument avoiding *)
  | domain_avoids_ihfam : forall (ρm : env) As p ups (ρ : env) t i f Km K,
      (forall x, Km <> Some x -> dentry_avoids (env_entry ρm x)) ->
      ends_fresh p Km As t ->
      (forall a, In a ups -> domain_avoids a) ->
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_ptyp_fresh (optional_shift 1 K) t ->
      domain_avoids f ->
      domain_avoids (d_ihfam ρm As p ups ρ t i f)
  (** A record type former at avoiding arguments *)
  | domain_avoids_record : forall p args, (forall a, In a args -> domain_avoids a) -> domain_avoids (d_record p args)
  (** A tuple of avoiding fields *)
  | domain_avoids_tuple : forall vs, (forall f a, In (f, a) vs -> domain_avoids a) -> domain_avoids (d_tuple vs)
  with domain_ne_avoids : domain_ne -> Prop :=
  (** A variable other than [v], below [b] *)
  | domain_avoids_var : forall x, x <> v -> x < b -> domain_ne_avoids (#ᵈ x)
  (** An application of an avoiding neutral to an avoiding normal value *)
  | domain_avoids_app : forall m n, domain_ne_avoids m -> domain_nf_avoids n -> domain_ne_avoids (m $ᵈ n)
  (** A stuck [efq]: its motive fresh under its closure, its scrutinee
      avoiding *)
  | domain_avoids_exfalso : forall (ρ : env) A m K,
      (forall x, K <> Some x -> dentry_avoids (env_entry ρ x)) ->
      optional_exp_fresh (optional_shift 1 K) A ->
      domain_ne_avoids m ->
      domain_ne_avoids (efqᵈ m under ρ return A)
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
  with dentry_avoids : dentry -> Prop :=
  | dentry_avoids_term : forall d, domain_avoids d -> dentry_avoids (de_term d)
  | dentry_avoids_mod : forall h, dmod_avoids h -> dentry_avoids (de_mod h)
  (** A term with a module part: both avoid *)
  | dentry_avoids_dm : forall d h, domain_avoids d -> dmod_avoids h -> dentry_avoids (de_dm d h).

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

  Lemma env_avoids_args : forall args K ρ,
      env_avoids v b K ρ -> (forall a, In a args -> domain_avoids v b a) ->
      env_avoids v b (optional_shift (List.length args) K) (env_args ρ args).
  Proof.
    induction args as [| a args IH]; intros * Hρ Ha; cbn; [ rewrite optional_shift_zero; exact Hρ |].
    replace (S (List.length args)) with (List.length args + 1) by lia.
    rewrite <- optional_shift_optional_shift.
    apply IH; [ apply env_avoids_cons; [ exact Hρ | constructor; apply Ha; left; reflexivity ]
              | intros; apply Ha; right; assumption ].
  Qed.

  (** An environment that avoids [v] everywhere, extended. *)
  Lemma env_avoids_cons_none : forall ρ d, env_avoids v b None ρ -> domain_avoids v b d -> env_avoids v b None (ρ ↦ d).
  Proof. intros; change (@None nat) with (optional_shift 1 None); apply env_avoids_cons; [ assumption | constructor; assumption ]. Qed.

  Lemma env_avoids_args_none : forall args ρ,
      env_avoids v b None ρ -> (forall a, In a args -> domain_avoids v b a) -> env_avoids v b None (env_args ρ args).
  Proof. intros; change (@None nat) with (optional_shift (List.length args) None); apply env_avoids_args; assumption. Qed.

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
  Lemma level_atoms_avoid_view : forall d, domain_avoids v b d -> level_atoms_avoid v b (dlvl_atoms d).
  Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

  Lemma level_atoms_avoid_suc : forall xs, level_atoms_avoid v b xs -> level_atoms_avoid v b (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
  Proof. induction 1; cbn; repeat constructor; assumption. Qed.

  Lemma level_atoms_avoid_app : forall xs ys, level_atoms_avoid v b xs -> level_atoms_avoid v b ys -> level_atoms_avoid v b (xs ++ ys).
  Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

  Lemma domain_avoids_lvl_suc : forall d, domain_avoids v b d -> domain_avoids v b (dlvl_suc d).
  Proof. intros; unfold dlvl_suc; constructor; apply level_atoms_avoid_suc, level_atoms_avoid_view; assumption. Qed.

  Lemma domain_avoids_lvl_max : forall d e, domain_avoids v b d -> domain_avoids v b e -> domain_avoids v b (dlvl_max d e).
  Proof. intros; unfold dlvl_max; constructor; apply level_atoms_avoid_app; apply level_atoms_avoid_view; assumption. Qed.

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

(** The open that declares a name, and the entries it generates. *)
Lemma item_upto_fresh : forall Φ x Φ0 H its1 it k,
    gm_item_upto Φ x = Some (Φ0, H, its1, it) -> gmod_fresh k Φ -> gmod_fresh k (gm_open Φ0 H its1).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H0 its]; intros * Hp Hf; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb x y); [ discriminate |]; cbn in Hf; destruct Hf; eapply IH; eassumption.
  - destruct (items_upto x its) as [[its1' it'] |]; [ injection Hp as <- <- <- <-; exact Hf |].
    cbn in Hf; destruct Hf; eapply IH; eassumption.
Qed.

Lemma optional_exp_fresh_item_upto : forall Φ x Φ0 H its1 it K,
    gm_item_upto Φ x = Some (Φ0, H, its1, it) -> optional_gmod_fresh K Φ -> optional_gmod_fresh K (gm_open Φ0 H its1).
Proof. intros * Hp; destruct K; cbn; [ eapply item_upto_fresh; eassumption | auto ]. Qed.

Lemma optional_gmod_fresh_open_prefix : forall K Φ H its, optional_gmod_fresh K (gm_open Φ H its) -> optional_gmod_fresh K Φ.
Proof. intros [] *; cbn; tauto. Qed.

Lemma optional_gmod_fresh_open_target : forall K Φ H its, optional_gmod_fresh K (gm_open Φ H its) -> optional_modexp_fresh (optional_shift (gm_binders Φ) K) H.
Proof. intros [] *; cbn; [ intros [_ HH]; exact HH | auto ]. Qed.

Lemma gens_append_fresh : forall gs Φ k,
    gmod_fresh k Φ -> List.Forall (fun g => gentry_fresh k (snd (generated_item_entry g))) gs ->
    gmod_fresh k (gens_append Φ (gm_binders Φ) gs).
Proof.
  induction gs as [| g gs IH]; intros * HΦ Hg; cbn [gens_append]; [ exact HΦ |].
  inversion Hg as [| ? ? Hg1 Hgs]; subst.
  destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [snd] in Hg1.
  replace (S (gm_binders Φ)) with (gm_binders (gm_ext Φ d (gentry_wk E (wk_shiftn (gm_binders Φ))))) by reflexivity.
  apply IH; [ cbn; split; [ exact HΦ | apply gentry_fresh_shiftn; exact Hg1 ] | exact Hgs ].
Qed.

Lemma kgens_entries_fresh : forall Θ Ξ ρ H its gs, kgens Θ Ξ ρ H its gs ->
    forall k, modexp_fresh k H -> List.Forall (fun g => gentry_fresh k (snd (generated_item_entry g))) gs.
Proof. induction 1; intros k Hk; constructor; cbn; auto. Qed.

Lemma optional_gmod_fresh_gens : forall Θ Ξ ρ H its gs K,
    kgens Θ Ξ ρ H its gs -> optional_modexp_fresh K H -> optional_gmod_fresh K (gens_append gm_nil 0 gs).
Proof.
  intros * Hg; destruct K as [k |]; cbn; [| auto ]; intros Hk.
  exact (gens_append_fresh gs gm_nil k I (kgens_entries_fresh _ _ _ _ _ _ Hg _ Hk)).
Qed.

(** The entries generated items add after a body, the [j]-th weakened past
    the [j] before it, are fresh where the items are. *)
Lemma gens_append_fresh0 : forall gs Φ j m k,
    gm_binders Φ = j + m -> gmod_fresh k Φ -> List.Forall (fun g => gentry_fresh (m + k) (snd (generated_item_entry g))) gs ->
    gmod_fresh k (gens_append Φ j gs).
Proof.
  induction gs as [| g gs IH]; intros * Hb HΦ Hg; cbn [gens_append]; [ exact HΦ |].
  inversion Hg as [| ? ? Hg1 Hgs]; subst.
  destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [snd] in Hg1.
  apply IH with (m := m); [ cbn; lia | | exact Hgs ].
  cbn; split; [ exact HΦ |]; rewrite Hb.
  replace (j + m + k) with (j + (m + k)) by lia; apply gentry_fresh_shiftn; exact Hg1.
Qed.

(** A body read through the entries its local opens generate is fresh
    where the body is. *)
Lemma kbody_fresh : forall Θ Ξ ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> forall k, gmod_fresh k Φ -> gmod_fresh k Φx /\ gm_binders Φx = gm_binders Φ.
Proof.
  induction 1 as [| ρ Φ Φx x E Hb IH | ρ Φ Φx ρ1 H its gs Hb IH Hk Hg]; intros k Hf.
  - split; [ exact I | reflexivity ].
  - cbn in Hf |- *; destruct Hf as [Hf HE]; destruct (IH _ Hf) as [Hx Hn]; rewrite Hn; auto.
  - cbn in Hf; destruct Hf as [Hf HH]; destruct (IH _ Hf) as [Hx Hn].
    rewrite gens_append_binders, (kgens_length _ _ _ _ _ _ Hg); cbn [gm_binders]; split; [| lia ].
    apply gens_append_fresh0 with (m := gm_binders Φx); [ lia | exact Hx |].
    rewrite Hn; exact (kgens_entries_fresh _ _ _ _ _ _ Hg _ HH).
Qed.

Lemma kbody_optional_gmod_fresh : forall Θ Ξ ρ Φ Φx K, kbody Θ Ξ ρ Φ Φx -> optional_gmod_fresh K Φ -> optional_gmod_fresh K Φx.
Proof. intros * Hb; destruct K as [k |]; cbn; [ intros Hf; exact (proj1 (kbody_fresh _ _ _ _ _ Hb _ Hf)) | auto ]. Qed.

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
  Lemma optional_exp_fresh_exfalso_A : forall A M, optional_exp_fresh K (efq M return A) -> optional_exp_fresh (optional_shift 1 K) A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_exfalso_M : forall A M, optional_exp_fresh K (efq M return A) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_pi_A : forall A B, optional_exp_fresh K (Π A B) -> optional_exp_fresh K A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_pi_B : forall A B, optional_exp_fresh K (Π A B) -> optional_exp_fresh (optional_shift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_fn_M : forall A M, optional_exp_fresh K (λ A M) -> optional_exp_fresh (optional_shift 1 K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_app_l : forall M N, optional_exp_fresh K (M $ N) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_app_r : forall M N, optional_exp_fresh K (M $ N) -> optional_exp_fresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_let_M : forall oA M B, optional_exp_fresh K (a_let (b_def oA M) B) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_let_B : forall bd B, optional_exp_fresh K (a_let bd B) -> optional_exp_fresh (optional_shift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_letmod_U : forall U B, optional_exp_fresh K (a_let (b_mod U) B) -> optional_gunit_fresh K U.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_mem : forall H x, optional_exp_fresh K (a_mem H x) -> optional_modexp_fresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_exp_fresh_elim_blocks : forall oq oUs j Bks M, optional_exp_fresh K (a_elim oq oUs j Bks M) -> blocks_optional_exp_fresh K Bks.
  Proof.
    destruct K as [k |]; cbn; [| intros; apply blocks_optional_exp_fresh_none ].
    intros oq oUs j Bks M H; apply (proj1 (exp_fresh_elim _ oq oUs j Bks M)) in H as [_ [H _]]; unfold blocks_fresh in H.
    induction Bks as [| [nm oZ A Bs] Bks IH]; intros b Hb; [ destruct Hb |].
    cbn [all_blocks] in H; destruct H as [(_ & HA & HBs) HBks].
    destruct Hb as [<- | Hb]; [| exact (IH HBks _ Hb) ].
    cbn [eb_nm eb_motive eb_brs optional_shift option_map optional_exp_fresh]; split; [ exact HA |].
    intros c n B Hin; apply all_brs_Forall in HBs; exact (proj1 (Forall_forall _ _) HBs _ Hin).
  Qed.
  Lemma optional_exp_fresh_elim_M : forall oq oUs j Bks M, optional_exp_fresh K (a_elim oq oUs j Bks M) -> optional_exp_fresh K M.
  Proof. destruct K; cbn; [ intros oq oUs j Bks M H; apply (proj1 (exp_fresh_elim _ oq oUs j Bks M)) in H; tauto | auto ]. Qed.
  Lemma optional_exp_fresh_elim_ups : forall oq Us j Bks M, optional_exp_fresh K (a_elim oq Us j Bks M) -> forall U, In U Us -> optional_exp_fresh K U.
  Proof.
    destruct K; cbn; [| auto ].
    intros oq Us j Bks M H; apply (proj1 (exp_fresh_elim _ oq Us j Bks M)) in H as [H _].
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
  Lemma optional_gmod_fresh_def_prefix : forall Φ y b pv A M,
      optional_gmod_fresh K (gm_ext Φ y (ge_def b pv A (Some M))) -> optional_gmod_fresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma optional_gmod_fresh_def_body : forall Φ y b pv A M,
      optional_gmod_fresh K (gm_ext Φ y (ge_def b pv A (Some M))) -> optional_exp_fresh (optional_shift (gm_binders Φ) K) M.
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
    intros Φ y E A M HE Hf; destruct E as [? ? ? [] | | | |]; cbn in HE, Hf; try discriminate; injection HE as <- <-; tauto.
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
  optional_exp_fresh_exfalso_A optional_exp_fresh_exfalso_M
  optional_exp_fresh_pi_A optional_exp_fresh_pi_B optional_exp_fresh_fn_M optional_exp_fresh_app_l optional_exp_fresh_app_r optional_exp_fresh_let_M optional_exp_fresh_let_B
  optional_exp_fresh_letmod_U optional_exp_fresh_mem optional_exp_fresh_var optional_exp_fresh_tuple_fields optional_exp_fresh_proj optional_modexp_fresh_var optional_modexp_fresh_lit optional_modexp_fresh_mem optional_modexp_fresh_app_l optional_modexp_fresh_app_r
  optional_gunit_fresh_body optional_gunit_fresh_alias optional_gmod_fresh_def_prefix optional_gmod_fresh_def_body optional_gmod_fresh_mod_prefix optional_gmod_fresh_mod_unit
  optional_gmod_fresh_dm_prefix optional_gmod_fresh_dm_body optional_gmod_fresh_dm_unit
  : avoid.
(** Freshness does not read the group or the member of an eliminator, so
    they are taken from the hypothesis rather than left to unification. *)
#[local] Hint Extern 1 (optional_exp_fresh _ _) =>
  match goal with
  | H : optional_exp_fresh ?K (a_elim ?oq ?o ?j ?Bks ?M) |- optional_exp_fresh ?K ?M => exact (optional_exp_fresh_elim_M K oq o j Bks M H)
  end : avoid.
#[local] Hint Extern 1 (blocks_optional_exp_fresh _ _) =>
  match goal with
  | H : optional_exp_fresh ?K (a_elim ?oq ?o ?j ?Bks ?M) |- blocks_optional_exp_fresh ?K ?Bks => exact (optional_exp_fresh_elim_blocks K oq o j Bks M H)
  end : avoid.

(** ** Evaluation Builds No Variable *)

Section Eval.
  Variables (v b : nat).

  #[local] Hint Resolve env_avoids_nil env_avoids_cons env_avoids_var env_avoids_mod domain_avoids_args_snoc env_avoids_args
    dmod_avoids_global_nil : mctt.
  (** The uniform parameters an eliminator carries are fresh where it is. *)
  #[local] Hint Extern 1 (Forall (optional_exp_fresh _) _) =>
    match goal with
    | H : optional_exp_fresh ?K (a_elim ?oq ?Us ?j ?Bks ?M) |- Forall (optional_exp_fresh ?K) ?Us =>
        apply Forall_forall; exact (optional_exp_fresh_elim_ups K oq Us j Bks M H)
    end : avoid.
  #[local] Hint Extern 1 (ups_avoids _ _ _) => unfold ups_avoids : avoid.
  #[local] Hint Extern 1 (domain_avoids _ _ (dlvl_lit _)) => repeat constructor : mctt.
  #[local] Hint Extern 1 (domain_avoids _ _ (dlvl_suc _)) => apply domain_avoids_lvl_suc : mctt.
  #[local] Hint Extern 1 (domain_avoids _ _ (dlvl_max _ _)) => apply domain_avoids_lvl_max : mctt.

  (** The entry an extension adds, given the invariant of its value. *)
  Ltac dentry_avoids_of d :=
    first [ apply dentry_avoids_term; solve [ eassumption | eauto 3 with mctt avoid ]
          | apply dentry_avoids_mod; solve [ eassumption | eauto 3 with mctt avoid ] ].

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
    | IH : forall K0, env_avoids ?v ?b K0 (extend_env (extend_env ?ρ ?d1) ?d2) -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in let E2 := fresh "E" in
        assert (E1 : dentry_avoids v b (de_term d1)) by dentry_avoids_of d1;
        assert (E2 : dentry_avoids v b (de_term d2)) by dentry_avoids_of d2;
        specialize (IH (optional_shift 1 (optional_shift 1 K)) (env_avoids_cons _ _ _ _ _ (env_avoids_cons _ _ _ _ _ Hρ E1) E2));
        rewrite optional_shift_optional_shift in IH; cbn [Nat.add] in IH
    | IH : forall K0, env_avoids ?v ?b K0 (extend_env ?ρ ?d) -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : dentry_avoids v b (de_term d)) by dentry_avoids_of d;
        specialize (IH (optional_shift 1 K) (env_avoids_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_avoids ?v ?b K0 (extend_env_mod ?ρ ?h) -> _, Hρ : env_avoids ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : dentry_avoids v b (de_mod h)) by dentry_avoids_of h;
        specialize (IH (optional_shift 1 K) (env_avoids_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_avoids ?v ?b K0 (env_args ?ρ ?args) -> _, Hρ : env_avoids ?v ?b ?K ?ρ,
      Ha : forall a, In a ?args -> domain_avoids ?v ?b a |- _ =>
        specialize (IH (optional_shift (List.length args) K) (env_avoids_args _ _ _ _ _ Hρ Ha));
        repeat match goal with Hl : List.length args = List.length ?D |- _ => rewrite Hl in IH end
    | IH : ?P -> ?Q |- _ =>
        let HP := fresh "HP" in assert (HP : P) by (solve [ eassumption | eauto 3 with mctt avoid ]); specialize (IH HP)
    end.

  (** The next neutral projection of a neutral of a record type: at its
      field's type, evaluated in the parameters and the projections before
      it, which avoid. *)
  Ltac nflds_head_avoids :=
    match goal with IHT : forall K0, env_avoids _ _ K0 (env_args nil (?ns ++ ?pre)) -> optional_exp_fresh K0 _ -> domain_avoids _ _ ?t |- _ =>
      constructor;
        [ apply (IHT None);
            [ apply env_avoids_args_none; [ apply env_avoids_nil | intros x Hx; apply List.in_app_or in Hx as [Hx | Hx]; auto ]
            | exact I ]
        | constructor; assumption ]
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
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs ->
       (forall a, In a ns -> domain_avoids v b a) -> domain_ne_avoids v b m -> (forall a, In a pre -> domain_avoids v b a) ->
       forall a, In a rs -> domain_avoids v b a) /\
    (forall fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> domain_avoids v b m -> forall a, In a ws -> domain_avoids v b a) /\
    (forall p ups ρm As ρ gs vs as', ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
       forall Km, env_avoids v b Km ρm -> (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p Km As t) ->
       ups_avoids v b ups -> env_avoids v b None ρ -> (forall a, In a vs -> domain_avoids v b a) -> forall a, In a as' -> domain_avoids v b a).
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
             (fun ns m fl pre rs _ => (forall a, In a ns -> domain_avoids v b a) -> domain_ne_avoids v b m ->
                                     (forall a, In a pre -> domain_avoids v b a) -> forall a, In a rs -> domain_avoids v b a)
             (fun fl m ws _ => domain_avoids v b m -> forall a, In a ws -> domain_avoids v b a)
             (fun p ups ρm As ρ gs vs as' _ => forall Km, env_avoids v b Km ρm ->
                                    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p Km As t) ->
                                    ups_avoids v b ups -> env_avoids v b None ρ -> (forall a, In a vs -> domain_avoids v b a) ->
                                    forall a, In a as' -> domain_avoids v b a));
      intros; cbn [optional_ptyp_fresh ptyp_ps ptyp_mem snd] in *.
    all: repeat match goal with
           | H : domain_avoids _ _ (_ _) |- _ => inversion_clear H
           | H : dmod_avoids _ _ (_ _ _) |- _ => inversion_clear H
           | H : dmod_avoids _ _ (_ _ _ _) |- _ => inversion_clear H
           end.
    all: av_fwd.
    (** The uniform arguments of a view, evaluated at the group's. *)
    all: try solve [ match goal with
      | IH : forall K0, env_avoids _ _ K0 (env_args nil ?ups) -> Forall (optional_exp_fresh K0) ?Is -> forall a, In a ?cups -> domain_avoids _ _ a,
        Hu : forall u, In u ?ups -> domain_avoids _ _ u, Ha : In ?d0 ?cups |- domain_avoids _ _ ?d0 =>
          apply (IH None); [ apply env_avoids_args_none; [ apply env_avoids_nil | exact Hu ] | apply Forall_forall; intros; exact I | exact Ha ]
      end ].
    (** Inductive types.  The values are lists, of which evaluation takes
        segments; a branch and the motive are evaluated in an environment
        extended by as many values as they bind. *)
    all: try solve [ lazymatch goal with |- domain_avoids _ _ (d_ind _ _ _) => idtac | |- domain_avoids _ _ (d_con _ _ _ _) => idtac end;
                     constructor; all_in_with assumption ].
    all: try solve [ match goal with
      | Hf : optional_exp_fresh ?K (a_elim _ _ _ _ _), IH : _ -> _ -> _ -> domain_avoids _ _ ?r |- domain_avoids _ _ ?r =>
          apply IH; [ eapply optional_exp_fresh_elim_blocks; exact Hf | solve [ eauto 3 with mctt avoid ] | assumption ]
      end ].
    all: try solve [ match goal with
      | e : brs_lookup (eb_brs ?bk) ?c = Some (?n, ?B), Hb : List.nth_error ?Bks _ = Some ?bk,
        Hl : List.length ?vs = (im_np ?Dq ?Mk + List.length ?gs)%nat,
        Hn : ?n = _, HD : ind_lookup _ _ ?p = Some ?D, Hco : leaves_coherent ?D,
        Hih : eval_ihs _ _ _ ?p _ _ ?gs _ ?ihs,
        IHi : (forall x1, In x1 (skipn _ _) -> domain_avoids _ _ x1) -> forall x2, In x2 ?ihs -> domain_avoids _ _ x2,
        HBk : blocks_optional_exp_fresh ?K ?Bks,
        Hρ : env_avoids _ _ ?K ?ρ,
        IHB : forall K0, env_avoids _ _ K0 (env_args ?ρ ?L) -> optional_exp_fresh K0 ?B -> domain_avoids _ _ ?r |- domain_avoids _ _ ?r =>
          (* as many recursive results as the branch binds: the group's
             table is coherent, the gate of [eval_elim_con] *)
          let Hi := fresh "Hi" in
          pose proof (IHi ltac:(all_in_with assumption)) as Hi;
          destruct (eval_ihs_length _ _ _ _ _ _ _ _ HD Hco Hih) as [_ Hni];
          apply (IHB (optional_shift (List.length L) K));
            [ apply env_avoids_args; [ exact Hρ | all_in_with assumption ]
            | rewrite (ind_branch_args_length _ _ _ _ _ Hl), Hni, <- Hn;
              exact (proj2 (HBk _ (List.nth_error_In _ _ Hb)) _ _ _ (brs_lookup_in _ _ _ _ e)) ]
      end ].
    all: try solve [ match goal with
      | Hl : List.length ?as' = im_np ?Dq ?Mk, Hn : eb_nm ?bk = S (im_nn ?Mk), Hb : List.nth_error ?Bks _ = Some ?bk,
        HBk : blocks_optional_exp_fresh ?K ?Bks, Hρ : env_avoids _ _ ?K ?ρ,
        IHA : forall K0, env_avoids _ _ K0 (env_args ?ρ ?L) -> optional_exp_fresh K0 (eb_motive ?bk) -> domain_avoids _ _ ?a
        |- domain_avoids _ _ (⇑ ?a (d_elim _ _ _ _ _ _ _)) =>
          constructor;
            [ apply (IHA (optional_shift (List.length L) K));
                [ apply env_avoids_args; [ exact Hρ | all_in_with ltac:(constructor; [ constructor; assumption | assumption ]) ]
                | rewrite (ind_motive_args_length _ _ _ _ Hl), <- Hn; exact (proj1 (HBk _ (List.nth_error_In _ _ Hb))) ]
            | eapply domain_avoids_elim; eassumption ]
      end ].
    (* the recursive results *)
    all: try solve [ match goal with
      | IH : (forall x1, In x1 ?vs -> domain_avoids _ _ x1) -> forall x2, In x2 ?ihs -> domain_avoids _ _ x2,
        Hv : forall x3, In x3 (_ :: ?vs) -> domain_avoids _ _ x3, Ha : In ?d ?ihs |- domain_avoids _ _ ?d =>
          exact (IH (all_in_tail _ _ _ Hv) _ Ha)
      end ].
    all: try solve [ eauto 4 with mctt avoid ].
    (** The types of a function shape's argument and recursive result: a
        [Π] over the family, in an environment that holds only the family. *)
    all: try solve [ lazymatch goal with |- domain_avoids _ _ (Πᵈ _ (_ ↦ d_shfam _ _ _ _) _) => idtac end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      eapply domain_avoids_pi with (K := None); [ eauto | | exact I ];
      apply env_avoids_cons_none; [ apply env_avoids_nil | eapply domain_avoids_shfam; eassumption ] ].
    (** A constructor of a view at the uniform parameters: the container's
        at the view's arguments, closed terms evaluated in an environment of
        the values given. *)
    all: try solve [ apply domain_avoids_con;
      match goal with H : forall K0, env_avoids _ _ K0 (env_args nil _) -> Forall (optional_exp_fresh K0) _ -> forall a, In a _ -> domain_avoids _ _ a |- _ =>
        apply (H None);
          [ apply env_avoids_args_none; [ apply env_avoids_nil | first [ intros ? [] | apply domain_avoids_args_snoc; assumption ] ]
          | apply List.Forall_forall; intros; exact I ] end ].
    (** The type of a recursive argument: the member at the shape's
        parameters after the uniform ones. *)
    all: try solve [ apply domain_avoids_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha]; eauto ].
    (** Records: a type former's arguments, a tuple's fields, a field of a
        tuple, and the projections of a neutral at their types. *)
    all: try solve [ lazymatch goal with |- domain_avoids _ _ (d_record _ nil) => apply domain_avoids_record; intros ? [] end ].
    all: try solve [ match goal with
      | H : forall y, In y ?vs -> domain_avoids _ _ y |- domain_avoids _ _ (d_tuple (List.combine _ ?vs)) =>
          apply domain_avoids_tuple; intros f y Hin; exact (H _ (List.in_combine_r _ _ _ _ Hin))
      end ].
    all: try solve [ match goal with
      | H : forall f y, In (f, y) ?vs -> domain_avoids _ _ y, Hl : field_lookup ?vs _ = Some ?r |- domain_avoids _ _ ?r =>
          exact (H _ _ (field_lookup_In _ _ _ Hl))
      end ].
    all: try solve [ match goal with
      | IH : (forall y, In y nil -> domain_avoids _ _ y) -> forall z, In z ?rs -> domain_avoids _ _ z, Hk : List.nth_error ?rs _ = Some ?r |- domain_avoids _ _ ?r =>
          exact (IH (fun _ Hin => match Hin with end) _ (List.nth_error_In _ _ Hk))
      end ].
    all: try solve [ lazymatch goal with |- domain_avoids _ _ (⇑ _ (d_proj _ _)) => nflds_head_avoids end ].
    (** A record type of a global module: its type former, applied to the
        module's arguments. *)
    all: try solve [ match goal with IH : domain_avoids _ _ (d_record _ nil) -> _ -> _, Ha : forall a, In a _ -> domain_avoids _ _ a |- _ =>
                       apply IH; [ apply domain_avoids_record; intros ? [] | exact Ha ] end ].
    all: try solve [ match goal with
      | IH : (forall y, In y (?pre ++ ?x :: nil) -> domain_avoids _ _ y) -> forall z, In z ?rs -> domain_avoids _ _ z, Hin : In ?d ?rs |- domain_avoids _ _ ?d =>
          eapply IH; [ apply domain_avoids_args_snoc; [ assumption | nflds_head_avoids ] | exact Hin ]
      end ].
    (** The recursive results along leaf paths, and their types, are
        lists: the [i]-th of a function shape's, a member of one. *)
    all: try solve [ match goal with
      | H : forall a, In a ?l -> domain_avoids _ _ a, e : List.nth_error ?l _ = Some ?r |- domain_avoids _ _ ?r => exact (H _ (List.nth_error_In _ _ e))
      end ].
    (** A record view's constructor: a tuple of its fields, none or those
        after the uniform parameters. *)
    all: try solve [ lazymatch goal with |- domain_avoids _ _ (d_tuple nil) => apply domain_avoids_tuple; intros ? ? [] end ].
    all: try solve [ match goal with
      | H1 : forall a, In a ?vs -> domain_avoids _ _ a, H0 : domain_avoids _ _ ?n |- domain_avoids _ _ (d_tuple (List.combine _ (List.skipn ?k (?vs ++ ?n :: nil)))) =>
          apply domain_avoids_tuple; intros ? ? Hin; apply List.in_combine_r in Hin;
          eapply domain_avoids_args_snoc; [ exact H1 | exact H0 | rewrite <- (List.firstn_skipn k); apply List.in_or_app; right; exact Hin ]
      end ].
    (** The recursive results of the arguments: those of the first, then
        the rest's. *)
    all: try solve [ match goal with
      | IH1 : domain_avoids _ _ ?x -> forall y1, In y1 ?l1 -> domain_avoids _ _ y1,
        IH2 : (forall y2, In y2 ?vs -> domain_avoids _ _ y2) -> forall y3, In y3 ?l2 -> domain_avoids _ _ y3,
        Hv : forall y4, In y4 (?x :: ?vs) -> domain_avoids _ _ y4, Ha : In ?d0 (?l1 ++ ?l2) |- domain_avoids _ _ ?d0 =>
          apply List.in_app_or in Ha as [Ha | Ha]; [ exact (IH1 (all_in_head _ _ _ Hv) _ Ha) | exact (IH2 (all_in_tail _ _ _ Hv) _ Ha) ]
      end ].
    (** At a function shape: one family per leaf path of the rest, each of
        the eliminator's closure, as [domain_avoids_ihfn]. *)
    all: try solve [ match goal with
      | Ha : In ?d0 (List.map (fun i => d_ihfn _ _ _ _ _ i _) _) |- domain_avoids _ _ ?d0 =>
          apply List.in_map_iff in Ha as (? & <- & _); eapply domain_avoids_ihfn; eassumption
      end ].
    (** The type of an argument at a record view: the record at the view's
        instance, closed terms evaluated at the uniform parameters. *)
    all: try solve [ lazymatch goal with |- domain_avoids _ _ (d_record _ _) => apply domain_avoids_record; intros ? Ha end;
      match goal with
      | IH : forall K0, env_avoids _ _ K0 (env_args nil ?ups) -> Forall (optional_exp_fresh K0) ?Is -> forall a, In a ?cups -> domain_avoids _ _ a,
        Hu : forall u, In u ?ups -> domain_avoids _ _ u, Ha : In ?d0 ?cups |- domain_avoids _ _ ?d0 =>
          apply (IH None); [ apply env_avoids_args_none; [ apply env_avoids_nil | exact Hu ] | apply Forall_forall; intros; exact I | exact Ha ]
      end ].
    (** The types of the recursive results of a record view's fields: a
        non-recursive field joins the environment, a recursive one's shape
        ends fresh. *)
    all: try solve [ match goal with
      | IH : (forall gs1 t gs2, ?gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh ?p ?Km ?As t) -> ups_avoids _ _ ?ups -> env_avoids _ _ None (?ρ ↦ ?v0) ->
             (forall y1, In y1 ?vs -> domain_avoids _ _ y1) -> forall y2, In y2 ?rs -> domain_avoids _ _ y2,
        Hf : forall gs1 t gs2, ca_arg ?T :: ?gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh ?p ?Km ?As t,
        Hu : ups_avoids _ _ ?ups, Hρ : env_avoids _ _ None ?ρ, Hv : forall y3, In y3 (?v0 :: ?vs) -> domain_avoids _ _ y3, Ha : In ?d0 ?rs |- domain_avoids _ _ ?d0 =>
          apply (IH ltac:(intros gs1 t gs2 E; apply (Hf (ca_arg T :: gs1) t gs2); rewrite E; reflexivity) Hu
                      (env_avoids_cons_none _ _ _ _ Hρ (all_in_head _ _ _ Hv)) (all_in_tail _ _ _ Hv) _ Ha)
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
        at a record view, its fields' types ([ends_fresh_rview]). *)
    all: try solve [ match goal with HE : ends_fresh _ _ _ (pt_self _ _) |- _ => inversion HE; subst; clear HE end;
      repeat match goal with
        | H1 : ind_lookup ?x ?y ?p = Some ?X, H2 : ind_lookup ?x ?y ?p = Some ?Y |- _ =>
            tryif constr_eq X Y then fail else (rewrite H1 in H2; let E := fresh "E" in injection H2 as E; subst Y)
        | H1 : ind_member ?D ?j = Some ?X, H2 : ind_member ?D ?j = Some ?Y |- _ =>
            tryif constr_eq X Y then fail else (rewrite H1 in H2; let E := fresh "E" in injection H2 as E; subst Y)
        end;
      try match goal with
        | Hf : forall c gs gs1 t gs2, im_cons ?M = (c, gs) :: nil -> _, Hc : im_cons ?M = (?c0, ?gs0) :: nil |- _ =>
            let Hf' := fresh "Hf" in pose proof (fun gs1 t gs2 => Hf c0 gs0 gs1 t gs2 Hc) as Hf'; clear Hf
        end;
      first
        [ match goal with H : im_is_rview ?M = false, H' : im_head ?M = mh_record _ _ _ |- _ =>
            unfold im_is_rview in H; rewrite H' in H; discriminate end
        | match goal with
          | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs, IH : forall K0, env_avoids _ _ K0 (env_args ?ρm (?bs ++ ?v0 :: nil)) -> optional_exp_fresh K0 ?A -> _,
            Hm : env_avoids _ _ ?Km ?ρm, HA : optional_exp_fresh (optional_shift (S (List.length ?Ps)) ?Km) ?A |- _ =>
              let Hlb := fresh "Hlb" in
              assert (Hlb : List.length bs = List.length Ps) by (clear - e; induction e; cbn; congruence);
              apply (IH (optional_shift (List.length (bs ++ v0 :: nil)) Km));
                [ apply env_avoids_args; [ exact Hm | apply domain_avoids_args_snoc; assumption ]
                | rewrite List.length_app, Hlb; cbn [List.length]; replace (List.length Ps + 1) with (S (List.length Ps)) by lia;
                  exact HA ]
          end
        | match goal with
          | IH : (forall gs1 t gs2, ?gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh ?p ?Km ?As t) -> ups_avoids _ _ ?ups ->
                 env_avoids _ _ None (env_args nil ?ups) -> (forall y1, In y1 ?ws -> domain_avoids _ _ y1) -> forall y2, In y2 ?rs -> domain_avoids _ _ y2,
            Hf : forall gs1 t gs2, ?gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh ?p ?Km ?As t,
            Hu : ups_avoids _ _ ?ups, Hw : forall y3, In y3 ?ws -> domain_avoids _ _ y3, Ha : In ?d0 ?rs |- domain_avoids _ _ ?d0 =>
              exact (IH Hf Hu (env_avoids_args_none _ _ _ _ (env_avoids_nil _ _ None) Hu) Hw _ Ha)
          end ] ].
    (** At a domain: a [Π] over it, of each recursive result's family. *)
    all: try solve [ match goal with
      | Ha : In ?d0 (List.map (fun i => Πᵈ _ (nil ↦ d_ihfam _ _ _ _ _ _ i _) _) _) |- domain_avoids _ _ ?d0 =>
          apply List.in_map_iff in Ha as (? & <- & _)
      end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      match goal with HE : ends_fresh _ _ _ (pt_pi _ _) |- _ => inversion HE; subst end;
      eapply domain_avoids_pi with (K := None); [ eauto | | exact I ];
      apply env_avoids_cons_none; [ apply env_avoids_nil | eapply domain_avoids_ihfam; eassumption ] ].
    (** What is left: the closures the rules build, and the module bodies,
        whose freshness is at the position their parameters and entries
        shift it to. *)
    - (* [efq] on a neutral *)
      apply domain_avoids_neut; [ assumption |].
      match goal with Hn : domain_avoids _ _ (⇑ _ _) |- _ => inversion Hn; subst end.
      eapply domain_avoids_exfalso with (K := K); eassumption.
    - (* an alias lacking no parameter: its target *)
      match goal with IH : optional_modexp_fresh ?K ?E -> _, Hu : optional_gunit_fresh ?K (gu_mk nil (md_alias ?E)) |- _ =>
        apply IH; pose proof (optional_gunit_fresh_alias _ _ _ Hu) as Hx; cbn [List.length] in Hx; rewrite optional_shift_zero in Hx; exact Hx end.
    - (* a closure given its outermost parameter *)
      match goal with IH : optional_gunit_fresh (optional_shift 1 ?K) _ -> _, Hu : optional_gunit_fresh ?K (gu_mk (_ ++ _) _) |- _ =>
        exact (IH (optional_gunit_fresh_snoc _ _ _ _ Hu)) end.
    - (* the module of an inductive type, a member of a global module: the
         type former, applied to the module's arguments *)
      match goal with IH : domain_avoids _ _ (d_ind _ _ _) -> _ -> _, Ha : forall a, In a _ -> domain_avoids _ _ a |- _ =>
        apply IH; [ constructor; intros ? [] | exact Ha ] end.
    - (* a term part of a saturated body, in its expansion *)
      match goal with Hb : kbody _ _ _ ?Φ ?Φx, Hp : gm_prefix_upto ?Φx _ = Some _, HE : entry_tm _ = Some _,
                      Hu : optional_gunit_fresh ?K (gu_mk nil (md_body _ ?Φ)),
                      IHb : optional_gmod_fresh ?K _ -> _, IHM : forall K0, _ -> optional_exp_fresh K0 _ -> _ |- _ =>
        pose proof (optional_gunit_fresh_body _ _ _ _ Hu) as HΦ; cbn [List.length] in HΦ; rewrite optional_shift_zero in HΦ;
        pose proof (optional_exp_fresh_prefix_upto _ _ _ _ Hp (kbody_optional_gmod_fresh _ _ _ _ _ _ Hb HΦ)) as HΦ';
        exact (IHM _ (IHb (optional_gmod_fresh_ext_prefix _ _ _ _ HΦ')) (optional_gmod_fresh_tm_body _ _ _ _ _ _ HE HΦ')) end.
    - (* a module part of a saturated body, in its expansion *)
      match goal with Hb : kbody _ _ _ ?Φ ?Φx, Hp : gm_prefix_upto ?Φx _ = Some _, HE : entry_unit _ = Some _,
                      Hu : optional_gunit_fresh ?K (gu_mk nil (md_body _ ?Φ)),
                      IHb : optional_gmod_fresh ?K _ -> _, IHM : forall K0, _ -> optional_gunit_fresh K0 _ -> _ |- _ =>
        pose proof (optional_gunit_fresh_body _ _ _ _ Hu) as HΦ; cbn [List.length] in HΦ; rewrite optional_shift_zero in HΦ;
        pose proof (optional_exp_fresh_prefix_upto _ _ _ _ Hp (kbody_optional_gmod_fresh _ _ _ _ _ _ Hb HΦ)) as HΦ';
        exact (IHM _ (IHb (optional_gmod_fresh_ext_prefix _ _ _ _ HΦ')) (optional_gmod_fresh_unit_unit _ _ _ _ _ HE HΦ')) end.
    - (* the empty body *)
      cbn [gm_binders]; rewrite optional_shift_zero; assumption.
    - (* a definition entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- optional_shift_optional_shift.
      apply env_avoids_cons; [ assumption | constructor; assumption ].
    - (* a submodule entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- optional_shift_optional_shift.
      apply env_avoids_cons; [ assumption | constructor; assumption ].
    - (* a definition with a module part entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- optional_shift_optional_shift.
      apply env_avoids_cons; [ assumption | constructor; assumption ].
  Qed.
End Eval.

(** A closure, evaluated at one or two more entries. *)
Lemma eval_clo_avoids : forall v b K (ρ : env) B c d,
    env_avoids v b K ρ -> optional_exp_fresh (optional_shift 1 K) B -> domain_avoids v b c ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ d -> domain_avoids v b d.
Proof.
  intros * Hρ HB Hc Hd.
  eapply (proj1 (eval_avoids v b)); [ exact Hd | apply env_avoids_cons; [ exact Hρ | constructor; exact Hc ] | exact HB ].
Qed.

Lemma eval_clo2_avoids : forall v b K (ρ : env) B c1 c2 d,
    env_avoids v b K ρ -> optional_exp_fresh (optional_shift 2 K) B -> domain_avoids v b c1 -> domain_avoids v b c2 ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ d -> domain_avoids v b d.
Proof.
  intros * Hρ HB Hc1 Hc2 Hd.
  eapply (proj1 (eval_avoids v b) _ _ _ Hd (optional_shift 1 (optional_shift 1 K))).
  - apply env_avoids_cons; [ apply env_avoids_cons; [ exact Hρ | constructor; exact Hc1 ] | constructor; exact Hc2 ].
  - rewrite optional_shift_optional_shift; exact HB.
Qed.

Lemma app_avoids : forall v b m n r, $| m & n | Θ ⍮ Ξ ↘ r -> domain_avoids v b m -> domain_avoids v b n -> domain_avoids v b r.
Proof. intros * H; exact (proj1 (proj2 (eval_avoids v b)) _ _ _ H). Qed.

Lemma shty_avoids : forall v b p ups ρ t a K, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
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
    List.nth j (motives_sel sel (blocks_motives Bks)) a_True = a_True \/
    exists b, List.nth_error Bks (elim_src sel j) = Some b /\ List.nth j (motives_sel sel (blocks_motives Bks)) a_True = eb_motive b.
Proof.
  assert (Hb : forall (Bks : list eblock) i, List.nth i (blocks_motives Bks) a_True = a_True \/
             exists b, List.nth_error Bks i = Some b /\ List.nth i (blocks_motives Bks) a_True = eb_motive b).
  { intros Bks i; destruct (List.nth_error Bks i) as [b |] eqn:E.
    - right; exists b; split; [ reflexivity |].
      unfold blocks_motives; apply List.nth_error_nth; rewrite List.nth_error_map, E; reflexivity.
    - left; apply List.nth_overflow; unfold blocks_motives; rewrite List.length_map; apply List.nth_error_None; exact E. }
  intros [vm |] Bks j; cbn [motives_sel elim_src]; [| apply Hb ].
  destruct (Nat.lt_ge_cases j (List.length vm)) as [Hj | Hj].
  - assert (E : List.nth j (List.map (fun v => List.nth v (blocks_motives Bks) a_True) vm) a_True
                 = List.nth (List.nth j vm 0) (blocks_motives Bks) a_True).
    { rewrite (List.nth_indep _ a_True ((fun v => List.nth v (blocks_motives Bks) a_True) 0))
        by (rewrite List.length_map; exact Hj).
      apply (List.map_nth (fun v => List.nth v (blocks_motives Bks) a_True)). }
    rewrite E; apply Hb.
  - left; apply List.nth_overflow; rewrite List.length_map; exact Hj.
Qed.

(** The shapes of a constructor's recursive arguments end in a member at
    as many parameters as it has non-uniform ones, argument by argument. *)
Lemma plen_forall : forall D (gs : list carg), cargs_plen D gs ->
    Forall (fun g => match g with
                     | ca_rec t => exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj
                     | ca_arg _ => True end) gs.
Proof.
  unfold cargs_plen; intros D; induction gs as [| g gs IH]; intros H; constructor.
  - destruct g as [A | t]; [ exact I | exact (H nil t gs eq_refl) ].
  - apply IH; intros gs1 t gs2 E; apply (H (g :: gs1) t gs2); rewrite E; reflexivity.
Qed.

(** The motives at the ends of the leaf paths of a shape, fresh under
    their binders, from the blocks: each end at as many parameters as its
    member's motive binds ([rview_leaf_arity], [blocks_nm_at]), down the
    record views' fields by their order. *)
Lemma ends_fresh_of_blocks : forall p D Bks K, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
    blocks_nm_at D None Bks -> blocks_optional_exp_fresh K Bks ->
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
      pose proof (rview_leaf_plen _ Har _ _ _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity)
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
    blocks_nm_at D None Bks -> blocks_optional_exp_fresh K Bks -> cargs_plen D gs ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_fresh p K (blocks_motives Bks) t.
Proof. intros * HD Har Hnm HB Hpl gs1 t gs2 E; exact (ends_fresh_of_blocks _ _ _ _ HD Har Hnm HB t (Hpl gs1 t gs2 E)). Qed.

Lemma domain_avoids_mono' : forall v b b' d, b <= b' -> domain_avoids v b d -> domain_avoids v b' d.
Proof. intros; eapply (proj1 (domain_avoids_mono v b)); eassumption. Qed.

Lemma ups_avoids_mono : forall v b b' ups, b <= b' -> ups_avoids v b ups -> ups_avoids v b' ups.
Proof. intros * Hb H a Ha; exact (domain_avoids_mono' _ _ _ _ Hb (H a Ha)). Qed.

(** ** Readback Introduces Only Variables Above the Ones in Scope *)

Lemma la_fresh_canon : forall k c xs, all_list (fun a => ne_fresh k (atom_level a)) xs ->
    all_list (fun a => ne_fresh k (atom_level a)) (snd (lvl_canon (c, xs))).
Proof. intros * H; apply la_all_all_list, la_all_canon, la_all_all_list; assumption. Qed.

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
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env (extend_env ?ρ ?c1) ?c2 ↘ ?d,
              Hρ : forall x, ?K <> Some x -> dentry_avoids v ?b0 (env_entry ?ρ x) |- domain_avoids v ?n ?d =>
                eapply (eval_clo2_avoids v n K ρ B c1 c2 d);
                  [ eapply env_avoids_mono; [| exact Hρ ]; lia | assumption | domain_avoids_tac v | domain_avoids_tac v | exact e ]
            end
          | match goal with
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env ?ρ ?c ↘ ?d,
              Hρ : forall x, ?K <> Some x -> dentry_avoids v ?b0 (env_entry ?ρ x) |- domain_avoids v ?n ?d =>
                eapply (eval_clo_avoids v n K ρ B c d);
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
    - assert (Ha : domain_avoids v b0 a) by (eapply shty_avoids; [ eassumption | exact Hρ | apply optional_ptyp_fresh_none | exact Hu ]).
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
      + intros gs1 t gs2 E; apply (Hl (ca_arg T :: gs1) t gs2); rewrite E; reflexivity.
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
  Lemma motive_avoids : forall ρ K A X pre hd k Mi s ns a b,
      Ftele List.rev (im_nparams Mi) in Θ ⍮ Ξ ⍮ env_args nil X ⍮ s ↘ ns ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mi) :: nil) ↘ a ->
      v < s -> b <= s -> env_avoids v b K ρ -> optional_exp_fresh (optional_shift (S (im_nn Mi)) K) A ->
      (forall x, In x X -> domain_avoids v b x) -> (forall x, In x pre -> domain_avoids v b x) ->
      domain_avoids v (S (s + im_nn Mi)) a.
  Proof.
    intros * f e Hv Hb Hρ HA HX Hp.
    pose proof (fresh_tele_length _ _ _ _ f) as Hlen; rewrite List.length_rev in Hlen.
    change (List.length (im_nparams Mi)) with (im_nn Mi) in Hlen.
    assert (Hns : forall x, In x ns -> domain_avoids v (s + im_nn Mi) x).
    { pose proof (fresh_tele_avoids _ _ _ _ f b Hv Hb ltac:(apply env_avoids_args_none; [ apply env_avoids_nil | exact HX ])) as H.
      rewrite List.length_rev in H; exact H. }
    eapply (proj1 (eval_avoids v (S (s + im_nn Mi)))); [ exact e | apply env_avoids_args; [ eapply env_avoids_mono; [| exact Hρ ]; lia |] |].
    - apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; lia |].
      apply all_in_cons; [| apply all_in_nil ].
      apply (domain_avoids_fresh_var (s + im_nn Mi)); [ lia | lia |].
      constructor; apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hp; eassumption ]; lia | exact Hns ].
    - rewrite List.length_app, Hlen; cbn [List.length]; replace (im_nn Mi + 1) with (S (im_nn Mi)) by lia; exact HA.
  Qed.

  (** A branch of a block of a stuck eliminator, and the motive's instance
      it is read at: under the fresh non-uniform parameters, arguments and
      recursive results of the group read, as many as the branch binds. *)
  Lemma branch_avoids : forall ρ K p ups Bks Dc A B pre hd k c Mi Mv D gs' gs s n0 ns vs ihs wihs bv t b,
      Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
      Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ ⍮ env_args nil (ups ++ ns) ⍮
        (s + im_nn Mi + List.length gs') ↘ ihs ->
      ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ wihs) ↘ bv ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con hd k c (pre ++ ns ++ vs) :: nil) ↘ t ->
      ind_lookup Θ Ξ p = Some D ->
      n0 = (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat -> im_nn Mv = im_nn Mi ->
      cargs_nin D Dc gs' gs = cargs_nrec Dc gs' ->
      cargs_plen D gs -> blocks_nm_at D None Bks -> rview_leaf_arity D ->
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
    { pose proof (fresh_tele_avoids _ _ _ _ f b Hv Hb ltac:(apply env_avoids_args_none; [ apply env_avoids_nil | exact HX ])) as H.
      rewrite List.length_rev in H; change (List.length (im_nparams Mv)) with (im_nn Mv) in H; rewrite Hnn in H; exact H. }
    assert (Hρa : env_avoids v (s + im_nn Mi) None (env_args nil (ups ++ ns)))
      by (apply env_avoids_args_none; [ apply env_avoids_nil | apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply HX; eassumption ]; lia | exact Hns ] ]).
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
    - eapply (proj1 (eval_avoids v (s + n))); [ exact e1 | apply env_avoids_args; [ eapply env_avoids_mono; [| exact Hρ ]; unfold n; lia |] |].
      + apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_cons; [| apply all_in_nil ].
        constructor; apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hp; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; unfold n; lia
                          | intros; eapply domain_avoids_mono'; [| apply Hvs; eassumption ]; unfold n; lia ].
      + rewrite List.length_app, Hl1; cbn [List.length]; replace (im_nn Mi + 1) with (S (im_nn Mi)) by lia; exact HA.
    - eapply (proj1 (eval_avoids v (s + n))); [ exact e0 | apply env_avoids_args; [ eapply env_avoids_mono; [| exact Hρ ]; unfold n; lia |] |].
      + apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply domain_avoids_mono'; [| apply Hvs; eassumption ]; unfold n; lia | exact Hw ].
      + rewrite !List.length_app, Hl1, Hl2, Hgl, Hl3, Nat.add_assoc, <- Hn0; exact HB.
  Qed.

  Lemma read_avoids :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall b, v < s -> b <= s -> domain_nf_avoids v b m -> nf_fresh (s - v - 1) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall b, v < s -> b <= s -> domain_ne_avoids v b m -> ne_fresh (s - v - 1) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall b, v < s -> b <= s -> domain_avoids v b a -> nf_fresh (s - v - 1) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall b, v < s -> b <= s -> level_atoms_avoid v b xs -> all_list (fun a => ne_fresh (s - v - 1) (atom_level a)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> (forall a, In a vs -> domain_avoids v b a) ->
       all_list (nf_fresh (s - v - 1)) Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> (forall a, In a ups -> domain_avoids v b a) ->
       (forall a, In a vs -> domain_avoids v b a) -> all_list (nf_fresh (s - v - 1)) Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> (forall a, In a ups -> domain_avoids v b a) ->
       domain_avoids v b x -> nf_fresh (s - v - 1) X) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       forall b K D, v < s -> b <= s -> env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks ->
       ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks -> rview_leaf_arity D ->
       (forall a, In a ups -> domain_avoids v b a) -> all_list (normal_block_forall (fun n => nf_fresh (n + (s - v - 1)))) NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       forall b K D, v < s -> b <= s -> env_avoids v b K ρ -> blocks_optional_exp_fresh K Bks ->
       ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks -> rview_leaf_arity D -> im_nn Mv = im_nn Mi ->
       optional_exp_fresh (optional_shift (S (im_nn Mi)) K) A ->
       (forall c n B, In (c, n, B) Bs -> optional_exp_fresh (optional_shift n K) B) ->
       (forall a, In a ups -> domain_avoids v b a) -> (forall a, In a (snd r) -> domain_avoids v b a) -> all_list (fun br => nf_fresh (branch_arity br + (s - v - 1)) (branch_body br)) Bs') /\
    (forall s ρ fl d Fs, Rflds d at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       forall b, v < s -> b <= s -> env_avoids v b None ρ -> domain_avoids v b d -> all_list (nf_fresh (s - v - 1)) Fs).
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall b, v < s -> b <= s -> domain_nf_avoids v b m -> nf_fresh (s - v - 1) W)
             (fun s m M _ => forall b, v < s -> b <= s -> domain_ne_avoids v b m -> ne_fresh (s - v - 1) M)
             (fun s a A _ => forall b, v < s -> b <= s -> domain_avoids v b a -> nf_fresh (s - v - 1) A)
             (fun s xs ys _ => forall b, v < s -> b <= s -> level_atoms_avoid v b xs -> all_list (fun a => ne_fresh (s - v - 1) (atom_level a)) ys)
             (fun s ρ T vs Ms _ => forall b, v < s -> b <= s -> env_avoids v b None ρ ->
                                  (forall a, In a vs -> domain_avoids v b a) -> all_list (nf_fresh (s - v - 1)) Ms)
             (fun s p ups ρ gs vs Ms _ => forall b, v < s -> b <= s -> env_avoids v b None ρ ->
                                        (forall a, In a ups -> domain_avoids v b a) ->
                                        (forall a, In a vs -> domain_avoids v b a) -> all_list (nf_fresh (s - v - 1)) Ms)
             (fun s p ups ρ t x X _ => forall b, v < s -> b <= s -> env_avoids v b None ρ ->
                                     (forall a, In a ups -> domain_avoids v b a) -> domain_avoids v b x -> nf_fresh (s - v - 1) X)
             (fun s ρ p ups Bks Dc sel i Ms NBks _ => forall b K D, v < s -> b <= s -> env_avoids v b K ρ ->
                                                      blocks_optional_exp_fresh K Bks ->
                                                      ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks ->
                                                      rview_leaf_arity D ->
                                                      (forall a, In a ups -> domain_avoids v b a) -> all_list (normal_block_forall (fun n => nf_fresh (n + (s - v - 1)))) NBks)
             (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ => forall b K D, v < s -> b <= s -> env_avoids v b K ρ ->
                                                            blocks_optional_exp_fresh K Bks ->
                                                            ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks ->
                                                            rview_leaf_arity D ->
                                                            im_nn Mv = im_nn Mi ->
                                                            optional_exp_fresh (optional_shift (S (im_nn Mi)) K) A ->
                                                            (forall c n B, In (c, n, B) Bs -> optional_exp_fresh (optional_shift n K) B) ->
                                                            (forall a, In a ups -> domain_avoids v b a) ->
                                                            (forall a, In a (snd r) -> domain_avoids v b a) -> all_list (fun br => nf_fresh (branch_arity br + (s - v - 1)) (branch_body br)) Bs')
             (fun s ρ fl d Fs _ => forall b, v < s -> b <= s -> env_avoids v b None ρ -> domain_avoids v b d -> all_list (nf_fresh (s - v - 1)) Fs));
      intros; cbn [snd] in *;
      repeat match goal with
        | H : domain_nf_avoids _ _ (_ _ _) |- _ => inversion_clear H
        | H : level_atoms_avoid _ _ (_ :: _) |- _ => inversion_clear H
        end.
    all: repeat match goal with
      | H : domain_avoids _ _ (d_neut _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_lvl _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_suniv _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_pi _ _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_ind _ _ _) |- _ => inversion_clear H
      | H : domain_avoids _ _ (d_con _ _ _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_app _ _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_var _) |- _ => inversion_clear H
      | H : domain_ne_avoids _ _ (d_exfalso _ _ _) |- _ => inversion_clear H
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
    all: cbn [nf_fresh ne_fresh all_list nf_lvl_of nf_univ_of fst snd]; unfold normal_block_forall;
      cbn [block_arity block_motive block_branches branch_arity branch_body]; repeat split.
    all: try exact I.
    all: try lia.
    all: try solve [ eauto 3 with mctt ].
    all: try solve [ apply la_fresh_canon; eauto 3 with mctt ].
    (** Inductive types.  The parameters and the arguments of a constructor,
        and the parameters of a type, are read back at their types, which
        are closed. *)
    all: try solve [ match goal with
      | IH1 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh _) ?Ps,
        IH2 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (env_args nil ?as') -> _ -> _ -> all_list (nf_fresh _) ?Args,
        Hb : ?b <= ?s, Ha : forall a, In a ?as' -> domain_avoids v ?b a |- all_list (nf_fresh _) (?Ps ++ ?Args) =>
          apply all_list_app;
            [ apply (IH1 b); [ lia | lia | apply env_avoids_nil | assumption ]
            | apply (IH2 b); [ lia | lia | apply env_avoids_args_none; [ apply env_avoids_nil | assumption ]
                             | all_in_with assumption | all_in_with assumption ] ]
      end ].
    (** A record view's element: the group's uniform parameters, then its
        fields, read from its projections. *)
    all: try solve [ match goal with
      | e : eval_projs _ _ _ ?x ?ws, Hx : domain_avoids v ?b ?x,
        IH1 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh _) ?Ps,
        IH2 : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (env_args nil ?as') -> _ -> _ -> all_list (nf_fresh _) ?Args,
        Hb : ?b <= ?s, Ha : forall a, In a ?as' -> domain_avoids v ?b a |- all_list (nf_fresh _) (?Ps ++ ?Args) =>
          apply all_list_app;
            [ apply (IH1 b); [ lia | lia | apply env_avoids_nil | assumption ]
            | apply (IH2 b); [ lia | lia | apply env_avoids_args_none; [ apply env_avoids_nil | assumption ]
                             | exact Ha | exact (projs_avoids _ _ _ _ _ e Hx) ] ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh _) ?Ps,
        Hb : ?b <= ?s |- all_list (nf_fresh _) ?Ps =>
          apply (IH b); [ lia | lia | apply env_avoids_nil | assumption ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> domain_avoids v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> domain_nf_avoids v b0 (⇓ ?a ?v0) -> nf_fresh _ ?V |- nf_fresh _ ?V =>
          apply (IH b); [ lia | lia | constructor;
            [ eapply (proj1 (eval_avoids v b)); [ exact e | exact Hρ | exact I ] | exact (all_in_head _ _ _ Hv) ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> domain_avoids v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (?ρ ↦ ?v0) -> _ |- all_list (nf_fresh _) _ =>
          apply (IH b); try lia;
            [ apply env_avoids_cons_none; [ exact Hρ | exact (all_in_head _ _ _ Hv) ] |..]; all_in_with assumption
      end ].
    (** A recursive argument, by its shape. *)
    all: try solve [ match goal with
      | Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> domain_avoids v ?b x,
        Hv : forall x, In x (?v0 :: _) -> domain_avoids v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None ?ρ -> (forall a, In a ?ups -> _) -> domain_avoids v b0 ?v0 ->
             nf_fresh _ ?V |- nf_fresh _ ?V =>
          apply (IH b); [ lia | lia | exact Hρ | exact Hu | exact (all_in_head _ _ _ Hv) ]
      end ].
    (** The end of a shape: the member at the uniform parameters and the
        shape's own. *)
    all: try solve [ match goal with
      | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ ?ρ ↘ ?bs, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> domain_avoids v ?b x, Hx : domain_avoids v ?b ?x0,
        IH : forall b0, v < ?s -> b0 <= ?s -> domain_nf_avoids v b0 (⇓ (d_ind ?p ?j (?ups ++ ?bs)) ?x0) -> nf_fresh _ ?V
        |- nf_fresh _ ?V =>
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
        IHA : forall b1, v < ?s -> b1 <= ?s -> domain_avoids v b1 ?b0 -> nf_fresh _ ?A |- nf_fresh _ ?A =>
          apply (IHA b); [ lia | lia | eapply (proj1 (eval_avoids v b)); [ exact e | exact Hρ | exact I ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b0, ea : $| ?x0 & ⇑! ?b0 ?s | _ ⍮ _ ↘ ?r,
        Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> domain_avoids v ?b x, Hx : domain_avoids v ?b ?x0,
        IHV : forall b1, v < S ?s -> b1 <= S ?s -> env_avoids v b1 None (?ρ ↦ ⇑! ?b0 ?s) -> (forall a, In a ?ups -> _) ->
              domain_avoids v b1 ?r -> nf_fresh _ ?V |- nf_fresh _ ?V =>
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
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None ?ρ -> _ -> (forall x, In x ?vs -> _) -> all_list (nf_fresh _) ?W
        |- all_list (nf_fresh _) ?W =>
          apply (IH b); [ lia | lia | exact Hρ | assumption | exact (all_in_tail _ _ _ Hv) ]
      end ].
    (** A stuck eliminator: the container's uniform parameters read at
        their telescope; the blocks at the eliminator's uniform
        parameters. *)
    all: try solve [ match goal with
      | em : eval_mref _ _ _ ?ups _ (_, _, ?pre),
        Hu : forall a, In a ?ups -> domain_avoids v ?b a, Hb : ?b <= ?s,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None nil -> _ -> all_list (nf_fresh _) ?Ps |- all_list (nf_fresh _) ?Ps =>
          apply (IH b); [ lia | lia | apply env_avoids_nil | exact (mref_avoids _ _ _ _ _ _ em Hu) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_avoids v b0 K0 ?ρ -> blocks_optional_exp_fresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_nm_at D0 None ?Bks -> rview_leaf_arity D0 ->
               (forall a, In a ?ups -> _) -> all_list _ ?W,
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks, Har : rview_leaf_arity ?D,
        Hb : ?b <= ?s, Hρ : forall x, ?K <> Some x -> dentry_avoids v ?b (env_entry ?ρ x), HBk : blocks_optional_exp_fresh ?K ?Bks,
        Hu : forall a, In a ?ups -> domain_avoids v ?b a |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm | exact Har | exact Hu ]
      end ].
    (** A block: its motive under the fresh non-uniform parameters of its
        member and the scrutinee; its branches; and the blocks after it.
        The block's member has as many non-uniform parameters as the member
        read, both being the motive's binders. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (env_args nil ?X) (List.rev (im_nparams ?Mv)) ?s ?ns,
        Hnth : List.nth_error ?Bks ?ix = Some ?bk, Hnmb : eb_nm ?bk = S (im_nn ?Mi), HMv : ind_member ?D ?ix = Some ?Mv,
        Hnm : blocks_nm_at ?D None ?Bks,
        em : eval_mref _ _ _ ?X _ (_, _, ?pre),
        e2 : ⟦ eb_motive ?bk ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ _) ↘ ?a,
        IH : forall b0, _ -> _ -> domain_avoids v b0 ?a -> nf_fresh _ ?A',
        Hb : ?b <= ?s, Hρ : env_avoids v ?b ?K ?ρ, HBk : blocks_optional_exp_fresh ?K ?Bks,
        HX : forall x, In x ?X -> domain_avoids v ?b x |- nf_fresh (S (im_nn ?Mi) + _) ?A' =>
          let Hnn := fresh "Hnn" in
          assert (Hnn : im_nn Mv = im_nn Mi) by (pose proof (Hnm _ _ _ HMv Hnth) as Hx; cbn [elim_src] in Hx; congruence);
          replace (S (im_nn Mi) + (s - v - 1)) with (S (s + im_nn Mi) - v - 1) by lia;
          apply (IH (S (s + im_nn Mi))); [ lia | lia |];
          rewrite <- Hnn in e2 |- *;
          eapply motive_avoids; [ exact f | exact e2 | assumption | exact Hb | exact Hρ
                            | rewrite Hnn, <- Hnmb; exact (proj1 (HBk _ (List.nth_error_In _ _ Hnth))) | exact HX
                            | exact (mref_avoids _ _ _ _ _ _ em HX) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_avoids v b0 K0 ?ρ -> blocks_optional_exp_fresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_nm_at D0 None ?Bks -> rview_leaf_arity D0 -> im_nn ?Mv = im_nn ?Mi ->
               _ -> _ -> _ -> _ -> all_list _ ?W,
        Hnth : List.nth_error ?Bks ?ix = Some ?bk, Hnmb : eb_nm ?bk = S (im_nn ?Mi), HMv : ind_member ?D ?ix = Some ?Mv,
        em : eval_mref _ _ _ ?X _ (_, _, ?pre),
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks, Har : rview_leaf_arity ?D,
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
               ind_lookup _ _ ?p = Some D0 -> blocks_nm_at D0 None ?Bks -> rview_leaf_arity D0 ->
               (forall a, In a ?X -> _) -> all_list _ ?W,
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks, Har : rview_leaf_arity ?D,
        Hb : ?b <= ?s, Hρ : env_avoids v ?b ?K ?ρ, HBk : blocks_optional_exp_fresh ?K ?Bks,
        HX : forall x, In x ?X -> domain_avoids v ?b x |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm | exact Har | exact HX ]
      end ].
    (** A branch: under the fresh non-uniform parameters, arguments and
        recursive results, as many as it binds. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (env_args nil ?X) _ ?s ?ns,
        f0 : fresh_cargs _ _ _ _ _ ?gs _ ?vs,
        f2 : fresh_ihs _ _ ?ρ _ _ _ _ _ ?gs' ?gs ?vs _ ?ihs,
        fw : wrap_ihs_eval _ _ ?ρ _ _ _ _ ?gs' ?gs ?vs ?ihs ?wihs,
        e0 : ⟦ ?B ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ ?vs ++ ?wihs) ↘ ?bv,
        e1 : ⟦ ?A ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ _) ↘ ?t,
        HD0 : ind_lookup _ _ _ = Some ?D0,
        Hn0 : ?n0 = _, Hn : ?n = _, Hnn : im_nn _ = im_nn ?Mi, Hcnt : cargs_nin ?D0 _ ?gs' ?gs = _,
        Hpl : cargs_plen ?D0 ?gs, Hnm : blocks_nm_at ?D0 None ?Bks, Har : rview_leaf_arity ?D0,
        IH : forall b0, _ -> _ -> domain_nf_avoids v b0 (⇓ ?t ?bv) -> nf_fresh _ ?B',
        Hb : ?b <= ?s, Hρ : env_avoids v ?b ?K ?ρ, HBk : blocks_optional_exp_fresh ?K ?Bks,
        HA : optional_exp_fresh (optional_shift (S (im_nn ?Mi)) ?K) ?A,
        HB : forall c0 n0 B0, In (c0, n0, B0) (_ :: _) -> optional_exp_fresh (optional_shift n0 ?K) B0,
        HX : forall x, In x ?X -> domain_avoids v ?b x, Hp : forall x, In x ?pre -> domain_avoids v ?b x |- nf_fresh (?n + _) ?B' =>
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
      | IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (env_args nil ?ns) -> domain_avoids v b0 ?d -> all_list (nf_fresh _) ?W,
        Hb : ?b <= ?s, Hn : forall a, In a ?ns -> domain_avoids v ?b a, Hd : domain_avoids v ?b ?d |- all_list (nf_fresh _) ?W =>
          apply (IH b); [ lia | lia | apply env_avoids_args_none; [ apply env_avoids_nil | exact Hn ] | exact Hd ]
      end ].
    all: try solve [ match goal with
      | e : eval_proj _ _ _ ?d ?r, e0 : ⟦ ?T ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?t, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s, Hd : domain_avoids v ?b ?d,
        IH : forall b0, v < ?s -> b0 <= ?s -> domain_nf_avoids v b0 (⇓ ?t ?r) -> nf_fresh _ ?W |- nf_fresh _ ?W =>
          apply (IH b);
            [ lia | lia
            | constructor; [ eapply (proj1 (eval_avoids v b)); [ exact e0 | exact Hρ | exact I ] | exact (proj_avoids _ _ _ _ _ e Hd) ] ]
      end ].
    all: try solve [ match goal with
      | e : eval_proj _ _ _ ?d ?r, Hρ : env_avoids v ?b None ?ρ, Hb : ?b <= ?s, Hd : domain_avoids v ?b ?d,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_avoids v b0 None (?ρ ↦ ?r) -> domain_avoids v b0 ?d -> all_list (nf_fresh _) ?W |- all_list (nf_fresh _) ?W =>
          apply (IH b); [ lia | lia | apply env_avoids_cons_none; [ exact Hρ | exact (proj_avoids _ _ _ _ _ e Hd) ] | exact Hd ]
      end ].
    (** A small universe reads back at the canonical level its level reads
        back as, and the two normal forms have the same atoms, so this case
        is the level's. *)
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> _ -> nf_fresh _ (nf_lvl_of _), Hb : ?b <= ?s |- all_list _ _ =>
          apply (IH b); [ lia | lia |]; repeat constructor; assumption
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
  - change None with (optional_shift 1 None).
    apply env_avoids_cons; [ apply IHinitial_env; lia |].
    constructor; constructor;
      [ eapply (proj1 (eval_avoids Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ]
      | constructor; lia ].
  - change None with (optional_shift 1 None).
    apply env_avoids_cons; [ apply IHinitial_env; lia |].
    constructor; eapply (proj1 (eval_avoids Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ].
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
Lemma initial_env_wk_avoids : forall Θ Ξ Γ A ρ,
    initial_env Θ Ξ (Γ ▹ A) ρ ->
    env_avoids Θ Ξ (List.length Γ) (S (List.length Γ)) (Some 0) ρ.
Proof.
  intros * Hρ; inversion_clear Hρ.
  apply env_avoids_cons_bad; eapply initial_env_avoids; [ eassumption | lia | lia ].
Qed.

(** NbE invents no variables: a weakened term, normalized in the extended
    context at its weakened type, has a normal form fresh at the new
    variable. *)
Theorem nbe_wk_fresh : forall Θ Ξ Γ A M T W,
    nbe Θ Ξ (Γ ▹ A) M[↑]ʷ T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * Hn; inversion_clear Hn as [? ? ? Hρ].
  pose proof (initial_env_wk_avoids _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  eapply (proj1 (read_avoids Θ Ξ (List.length Γ))); [ eassumption | cbn; lia | cbn; reflexivity |].
  constructor; eapply (proj1 (eval_avoids Θ Ξ _ _)); (eassumption || apply exp_shift_fresh).
Qed.

(** The same for the normal form of a weakened type. *)
Theorem nbe_ty_wk_fresh : forall Θ Ξ Γ A T W,
    nbe_ty Θ Ξ (Γ ▹ A) T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * Hn; inversion_clear Hn as [? ? Hρ].
  pose proof (initial_env_wk_avoids _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  eapply (proj1 (proj2 (proj2 (read_avoids Θ Ξ (List.length Γ))))); [ eassumption | cbn; lia | cbn; reflexivity |].
  eapply (proj1 (eval_avoids Θ Ξ _ _)); (eassumption || apply exp_shift_fresh).
Qed.
