(** * NbE Invents No Variables

    Normalizing a weakened term in the extended context never mentions the
    new variable: if [M[↑]] is normalized in [Γ ▹ A], its normal form is
    fresh at [#0] ([nbe_wk_fresh]).  Evaluation builds no variable, so a
    value can only mention a variable its environment holds; and readback
    introduces only variables above the ones in scope.

    The invariant is [dav v b d]: the value [d] mentions no de Bruijn level
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

Definition oshift (j : nat) (K : option nat) : option nat := option_map (Nat.add j) K.

Lemma oshift_oshift : forall i j K, oshift i (oshift j K) = oshift (i + j) K.
Proof. intros i j []; cbn; [ f_equal; lia | reflexivity ]. Qed.

Lemma oshift_zero : forall K, oshift 0 K = K.
Proof. intros []; reflexivity. Qed.

Definition ofresh (K : option nat) (M : exp) : Prop :=
  match K with None => True | Some k => exp_fresh k M end.
Definition omfresh (K : option nat) (H : modexp) : Prop :=
  match K with None => True | Some k => modexp_fresh k H end.
Definition oufresh (K : option nat) (U : gunit) : Prop :=
  match K with None => True | Some k => gunit_fresh k U end.
Definition ogfresh (K : option nat) (Φ : gmod) : Prop :=
  match K with None => True | Some k => gmod_fresh k Φ end.

(** The components of a shape, each under the domains before it. *)
Fixpoint ptfresh (K : option nat) (t : ptyp) : Prop :=
  match t with
  | pt_pi B t => ofresh K B /\ ptfresh (oshift 1 K) t
  | pt_self _ Ps => Forall (ofresh K) Ps
  end.

Lemma ptfresh_none : forall t, ptfresh None t.
Proof.
  induction t as [? Ps | B t IH]; cbn; [ apply Forall_forall; intros; exact I | split; [ exact I | exact IH ] ].
Qed.

(** The blocks of an eliminator: each motive fresh under the binders it
    has, and so is each branch under its own.  (The annotations are never
    evaluated.) *)
Definition blocks_ofresh (K : option nat) (Bks : list eblock) : Prop :=
  forall b, In b Bks -> ofresh (oshift (eb_nm b) K) (eb_motive b) /\
    (forall c n B, In (c, n, B) (eb_brs b) -> ofresh (oshift n K) B).

Lemma blocks_ofresh_none : forall Bks, blocks_ofresh None Bks.
Proof. intros Bks b _; split; [ exact I | intros; exact I ]. Qed.

(** ** The Invariant *)

Section Avoid.
  Variables (v b : nat).

  (** [dav d]: the value [d] mentions no level [v], and only levels below
      [b] (see the file header); mutually, for neutrals, normal values,
      module values, level atoms and environment entries. *)
  Inductive dav : domain -> Prop :=
  (** A [Π]: its domain avoids, and its closure avoids but at [K], where
      the codomain is fresh *)
  | dav_pi : forall a (ρ : env) B K,
      dav a ->
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift 1 K) B ->
      dav (Πᵈ a ρ B)
  (** A large universe *)
  | dav_univ : forall i, dav 𝕌ω@i
  (** A small universe at an avoiding level *)
  | dav_suniv : forall l, dav l -> dav 𝕌@l
  (** A type of levels *)
  | dav_level : forall n, dav (Levelᵈ@n)
  (** A level of avoiding atoms *)
  | dav_lvl : forall c xs, dav_la xs -> dav (lvᵈ c xs)
  (** The unit type *)
  | dav_True : dav ⊤ᵈ
  (** The unit's element *)
  | dav_true : dav ⋆ᵈ
  (** The empty type *)
  | dav_False : dav ⊥ᵈ
  (** A λ: its closure avoids but at [K], where the body is fresh *)
  | dav_fn : forall (ρ : env) M K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift 1 K) M ->
      dav (λᵈ ρ M)
  (** A neutral at an avoiding type *)
  | dav_neut : forall a m, dav a -> dav_ne m -> dav (⇑ a m)
  (** A member of an avoiding module value *)
  | dav_member : forall h ch, dmav h -> dav (d_member h ch)
  (** A type former at avoiding arguments *)
  | dav_indty : forall p k args, (forall a, In a args -> dav a) -> dav (d_ind p k args)
  (** A constructor at avoiding arguments *)
  | dav_con : forall p k c args, (forall a, In a args -> dav a) -> dav (d_con p k c args)
  (** The recursive result of a function shape: the eliminator's closure,
      as [dav_elim], and the argument. *)
  | dav_ihfn : forall (ρ : env) Bks p ups t f K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      blocks_ofresh K Bks ->
      (forall a, In a ups -> dav a) ->
      dav f ->
      dav (d_ihfn ρ Bks p ups t f)
  (** The families of a function shape: the shape's rest is fresh under the
      domain the family binds; the motive, under the shape's parameters and
      the argument. *)
  | dav_shfam : forall p ups (ρ : env) t K,
      (forall a, In a ups -> dav a) ->
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ptfresh (oshift 1 K) t ->
      dav (d_shfam p ups ρ t)
  (** The family of a recursive result at a function shape: the motive
      fresh under its closure's binders, the shape's rest fresh, the
      argument avoiding *)
  | dav_ihfam : forall (ρm : env) As (ρ : env) t f Km K,
      (forall x, Km <> Some x -> deav (env_entry ρm x)) ->
      ofresh (oshift (S (List.length (ptyp_ps t))) Km) (List.nth (ptyp_mem t) As a_True) ->
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ptfresh (oshift 1 K) t ->
      dav f ->
      dav (d_ihfam ρm As ρ t f)
  (** A record type former at avoiding arguments *)
  | dav_record : forall p args, (forall a, In a args -> dav a) -> dav (d_record p args)
  (** A tuple of avoiding fields *)
  | dav_tuple : forall vs, (forall f a, In (f, a) vs -> dav a) -> dav (d_tuple vs)
  with dav_ne : domain_ne -> Prop :=
  (** A variable other than [v], below [b] *)
  | dav_var : forall x, x <> v -> x < b -> dav_ne (#ᵈ x)
  (** An application of an avoiding neutral to an avoiding normal value *)
  | dav_app : forall m n, dav_ne m -> dav_nf n -> dav_ne (m $ᵈ n)
  (** A stuck [efq]: its motive fresh under its closure, its scrutinee
      avoiding *)
  | dav_exfalso : forall (ρ : env) A m K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      ofresh (oshift 1 K) A ->
      dav_ne m ->
      dav_ne (efqᵈ m under ρ return A)
  (** A global *)
  | dav_glob : forall p, dav_ne (d_glob p)
  (** A stuck eliminator: the motives are fresh under their binders, and so
      is each branch under its own. *)
  | dav_elim : forall (ρ : env) Bks p ups j args m K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      blocks_ofresh K Bks ->
      (forall a, In a ups -> dav a) ->
      (forall a, In a args -> dav a) ->
      dav_ne m ->
      dav_ne (d_elim ρ Bks p ups j args m)
  (** The field of an avoiding neutral *)
  | dav_proj : forall f m, dav_ne m -> dav_ne (d_proj f m)
  with dav_nf : domain_nf -> Prop :=
  | dav_dom : forall a m, dav a -> dav m -> dav_nf (⇓ a m)
  with dmav : dmod -> Prop :=
  | dmav_global : forall p args, (forall a, In a args -> dav a) -> dmav (dm_global p args)
  | dmav_local : forall Δ D (ρ : env) K,
      (forall x, K <> Some x -> deav (env_entry ρ x)) ->
      oufresh K (gu_mk Δ D) ->
      dmav (dm_local Δ D ρ)
  | dmav_member : forall h ch, dmav h -> dmav (dm_member h ch)
  with dav_la : list (nat * nat * domain_ne) -> Prop :=
  | dav_la_nil : dav_la nil
  | dav_la_cons : forall k n m xs, dav_ne m -> dav_la xs -> dav_la ((k, n, m) :: xs)
  with deav : dentry -> Prop :=
  | deav_term : forall d, dav d -> deav (de_term d)
  | deav_mod : forall h, dmav h -> deav (de_mod h)
  (** A term with a module part: both avoid *)
  | deav_dm : forall d h, dav d -> dmav h -> deav (de_dm d h).

  (** An environment that avoids at every position but [K]. *)
  Definition env_av (K : option nat) (ρ : env) : Prop :=
    forall x, K <> Some x -> deav (env_entry ρ x).

  (** The uniform parameters an eliminator carries.  A definition, so that
      the search does not use it as a lemma about every value. *)
  Definition ups_av (ups : list domain) : Prop := forall a, In a ups -> dav a.
End Avoid.

Scheme dav_mind := Induction for dav Sort Prop
  with dav_ne_mind := Induction for dav_ne Sort Prop
  with dav_nf_mind := Induction for dav_nf Sort Prop
  with dmav_mind := Induction for dmav Sort Prop
  with dav_la_mind := Induction for dav_la Sort Prop
  with deav_mind := Induction for deav Sort Prop.
Combined Scheme dav_mut_ind from dav_mind, dav_ne_mind, dav_nf_mind, dmav_mind, dav_la_mind, deav_mind.

#[local] Hint Constructors dav dav_ne dav_nf dmav dav_la deav : mctt.

(** The bound only grows. *)
Lemma dav_mono : forall v b,
    (forall d, dav v b d -> forall b', b <= b' -> dav v b' d) /\
    (forall m, dav_ne v b m -> forall b', b <= b' -> dav_ne v b' m) /\
    (forall n, dav_nf v b n -> forall b', b <= b' -> dav_nf v b' n) /\
    (forall h, dmav v b h -> forall b', b <= b' -> dmav v b' h) /\
    (forall xs, dav_la v b xs -> forall b', b <= b' -> dav_la v b' xs) /\
    (forall e, deav v b e -> forall b', b <= b' -> deav v b' e).
Proof.
  intros v b.
  apply (dav_mut_ind v b
           (fun d _ => forall b', b <= b' -> dav v b' d)
           (fun m _ => forall b', b <= b' -> dav_ne v b' m)
           (fun n _ => forall b', b <= b' -> dav_nf v b' n)
           (fun h _ => forall b', b <= b' -> dmav v b' h)
           (fun xs _ => forall b', b <= b' -> dav_la v b' xs)
           (fun e _ => forall b', b <= b' -> deav v b' e));
    intros; econstructor; eauto; lia.
Qed.

Lemma env_av_mono : forall v b b' K ρ, b <= b' -> env_av v b K ρ -> env_av v b' K ρ.
Proof. intros * Hb H x Hx; eapply (proj2 (proj2 (proj2 (proj2 (proj2 (dav_mono v b)))))); eauto. Qed.

(** ** Environments *)
Section Env.
  Variables (v b : nat).

  Lemma env_av_nil : forall K, env_av v b K nil.
  Proof. intros K x _; induction x; cbn; [ repeat constructor | assumption ]. Qed.

  Lemma env_av_cons : forall K e ρ, env_av v b K ρ -> deav v b e -> env_av v b (oshift 1 K) (e :: ρ).
  Proof.
    intros * Hρ He [| x] Hx; cbn; [ exact He |].
    apply Hρ; intros ->; apply Hx; reflexivity.
  Qed.

  (** The excluded entry: the head of the environment may be anything. *)
  Lemma env_av_cons_bad : forall e ρ, env_av v b None ρ -> env_av v b (Some 0) (e :: ρ).
  Proof.
    intros * Hρ [| x] Hx; cbn; [ contradiction Hx; reflexivity |].
    apply Hρ; discriminate.
  Qed.

  Lemma env_av_args : forall args K ρ,
      env_av v b K ρ -> (forall a, In a args -> dav v b a) ->
      env_av v b (oshift (List.length args) K) (env_args ρ args).
  Proof.
    induction args as [| a args IH]; intros * Hρ Ha; cbn; [ rewrite oshift_zero; exact Hρ |].
    replace (S (List.length args)) with (List.length args + 1) by lia.
    rewrite <- oshift_oshift.
    apply IH; [ apply env_av_cons; [ exact Hρ | constructor; apply Ha; left; reflexivity ]
              | intros; apply Ha; right; assumption ].
  Qed.

  (** An environment that avoids [v] everywhere, extended. *)
  Lemma env_av_cons_none : forall ρ d, env_av v b None ρ -> dav v b d -> env_av v b None (ρ ↦ d).
  Proof. intros; change (@None nat) with (oshift 1 None); apply env_av_cons; [ assumption | constructor; assumption ]. Qed.

  Lemma env_av_args_none : forall args ρ,
      env_av v b None ρ -> (forall a, In a args -> dav v b a) -> env_av v b None (env_args ρ args).
  Proof. intros; change (@None nat) with (oshift (List.length args) None); apply env_av_args; assumption. Qed.

  Lemma env_av_var : forall K ρ x, env_av v b K ρ -> K <> Some x -> dav v b (ρ x).
  Proof.
    intros * H Hx; unfold env_var; destruct (H x Hx); [ assumption | repeat constructor | assumption ].
  Qed.

  Lemma env_av_mod : forall K ρ x, env_av v b K ρ -> K <> Some x -> dmav v b (env_mod ρ x).
  Proof.
    intros * H Hx; unfold env_mod; destruct (H x Hx); [| assumption | assumption ].
    constructor; intros ? [].
  Qed.

  (** The atoms of a level value avoid [v] when the value does. *)
  Lemma dav_la_view : forall d, dav v b d -> dav_la v b (dlvl_atoms d).
  Proof. destruct 1; cbn; repeat constructor; assumption. Qed.

  Lemma dav_la_suc : forall xs, dav_la v b xs -> dav_la v b (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs).
  Proof. induction 1; cbn; repeat constructor; assumption. Qed.

  Lemma dav_la_app : forall xs ys, dav_la v b xs -> dav_la v b ys -> dav_la v b (xs ++ ys).
  Proof. induction 1; cbn; intros; [ assumption | constructor; auto ]. Qed.

  Lemma dav_lvl_suc : forall d, dav v b d -> dav v b (dlvl_suc d).
  Proof. intros; unfold dlvl_suc; constructor; apply dav_la_suc, dav_la_view; assumption. Qed.

  Lemma dav_lvl_max : forall d e, dav v b d -> dav v b e -> dav v b (dlvl_max d e).
  Proof. intros; unfold dlvl_max; constructor; apply dav_la_app; apply dav_la_view; assumption. Qed.

  Lemma dmav_global_nil : forall p, dmav v b (dm_global p nil).
  Proof. intros; constructor; intros ? []. Qed.

  Lemma dav_args_snoc : forall (args : list domain) n,
      (forall a, In a args -> dav v b a) -> dav v b n -> forall a, In a (args ++ n :: nil) -> dav v b a.
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

Lemma ofresh_prefix_upto : forall Φ x Φ0 K,
    gm_prefix_upto Φ x = Some Φ0 -> ogfresh K Φ -> ogfresh K Φ0.
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

Lemma ofresh_item_upto : forall Φ x Φ0 H its1 it K,
    gm_item_upto Φ x = Some (Φ0, H, its1, it) -> ogfresh K Φ -> ogfresh K (gm_open Φ0 H its1).
Proof. intros * Hp; destruct K; cbn; [ eapply item_upto_fresh; eassumption | auto ]. Qed.

Lemma ogfresh_open_prefix : forall K Φ H its, ogfresh K (gm_open Φ H its) -> ogfresh K Φ.
Proof. intros [] *; cbn; tauto. Qed.

Lemma ogfresh_open_target : forall K Φ H its, ogfresh K (gm_open Φ H its) -> omfresh (oshift (gm_binders Φ) K) H.
Proof. intros [] *; cbn; [ intros [_ HH]; exact HH | auto ]. Qed.

Lemma gens_append_fresh : forall gs Φ k,
    gmod_fresh k Φ -> List.Forall (fun g => gentry_fresh k (snd (ig_entry g))) gs ->
    gmod_fresh k (gens_append Φ (gm_binders Φ) gs).
Proof.
  induction gs as [| g gs IH]; intros * HΦ Hg; cbn [gens_append]; [ exact HΦ |].
  inversion Hg as [| ? ? Hg1 Hgs]; subst.
  destruct (ig_entry g) as [d E] eqn:Eg; cbn [snd] in Hg1.
  replace (S (gm_binders Φ)) with (gm_binders (gm_ext Φ d (gentry_wk E (wk_shiftn (gm_binders Φ))))) by reflexivity.
  apply IH; [ cbn; split; [ exact HΦ | apply gentry_fresh_shiftn; exact Hg1 ] | exact Hgs ].
Qed.

Lemma kgens_entries_fresh : forall Θ Ξ ρ H its gs, kgens Θ Ξ ρ H its gs ->
    forall k, modexp_fresh k H -> List.Forall (fun g => gentry_fresh k (snd (ig_entry g))) gs.
Proof. induction 1; intros k Hk; constructor; cbn; auto. Qed.

Lemma ogfresh_gens : forall Θ Ξ ρ H its gs K,
    kgens Θ Ξ ρ H its gs -> omfresh K H -> ogfresh K (gens_append gm_nil 0 gs).
Proof.
  intros * Hg; destruct K as [k |]; cbn; [| auto ]; intros Hk.
  exact (gens_append_fresh gs gm_nil k I (kgens_entries_fresh _ _ _ _ _ _ Hg _ Hk)).
Qed.

(** The entries generated items add after a body, the [j]-th weakened past
    the [j] before it, are fresh where the items are. *)
Lemma gens_append_fresh0 : forall gs Φ j m k,
    gm_binders Φ = j + m -> gmod_fresh k Φ -> List.Forall (fun g => gentry_fresh (m + k) (snd (ig_entry g))) gs ->
    gmod_fresh k (gens_append Φ j gs).
Proof.
  induction gs as [| g gs IH]; intros * Hb HΦ Hg; cbn [gens_append]; [ exact HΦ |].
  inversion Hg as [| ? ? Hg1 Hgs]; subst.
  destruct (ig_entry g) as [d E] eqn:Eg; cbn [snd] in Hg1.
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

Lemma kbody_ogfresh : forall Θ Ξ ρ Φ Φx K, kbody Θ Ξ ρ Φ Φx -> ogfresh K Φ -> ogfresh K Φx.
Proof. intros * Hb; destruct K as [k |]; cbn; [ intros Hf; exact (proj1 (kbody_fresh _ _ _ _ _ Hb _ Hf)) | auto ]. Qed.

(** A unit lacking one parameter fewer, the parameter now a variable. *)
Lemma oufresh_snoc : forall K Δ e D, oufresh K (gu_mk (Δ ++ e :: nil) D) -> oufresh (oshift 1 K) (gu_mk Δ D).
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

  Lemma ofresh_univ : forall M, ofresh K Type⟨M⟩ -> ofresh K M.
  Proof. destruct K; cbn; auto. Qed.
  Lemma ofresh_succl : forall M, ofresh K (succl M) -> ofresh K M.
  Proof. destruct K; cbn; auto. Qed.
  Lemma ofresh_maxl_l : forall M N, ofresh K (maxl M N) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_maxl_r : forall M N, ofresh K (maxl M N) -> ofresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_exfalso_A : forall A M, ofresh K (efq M return A) -> ofresh (oshift 1 K) A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_exfalso_M : forall A M, ofresh K (efq M return A) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_pi_A : forall A B, ofresh K (Π A B) -> ofresh K A.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_pi_B : forall A B, ofresh K (Π A B) -> ofresh (oshift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_fn_M : forall A M, ofresh K (λ A M) -> ofresh (oshift 1 K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_app_l : forall M N, ofresh K (M $ N) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_app_r : forall M N, ofresh K (M $ N) -> ofresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_let_M : forall oA M B, ofresh K (a_let (b_def oA M) B) -> ofresh K M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_let_B : forall bd B, ofresh K (a_let bd B) -> ofresh (oshift 1 K) B.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_letmod_U : forall U B, ofresh K (a_let (b_mod U) B) -> oufresh K U.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_mem : forall H x, ofresh K (a_mem H x) -> omfresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ofresh_elim_blocks : forall oq oUs j Bks M, ofresh K (a_elim oq oUs j Bks M) -> blocks_ofresh K Bks.
  Proof.
    destruct K as [k |]; cbn; [| intros; apply blocks_ofresh_none ].
    intros oq oUs j Bks M H; apply (proj1 (exp_fresh_elim _ oq oUs j Bks M)) in H as [_ [H _]]; unfold blocks_fresh in H.
    induction Bks as [| [nm oZ A Bs] Bks IH]; intros b Hb; [ destruct Hb |].
    cbn [all_blocks] in H; destruct H as [(_ & HA & HBs) HBks].
    destruct Hb as [<- | Hb]; [| exact (IH HBks _ Hb) ].
    cbn [eb_nm eb_motive eb_brs oshift option_map ofresh]; split; [ exact HA |].
    intros c n B Hin; apply all_brs_Forall in HBs; exact (proj1 (Forall_forall _ _) HBs _ Hin).
  Qed.
  Lemma ofresh_elim_M : forall oq oUs j Bks M, ofresh K (a_elim oq oUs j Bks M) -> ofresh K M.
  Proof. destruct K; cbn; [ intros oq oUs j Bks M H; apply (proj1 (exp_fresh_elim _ oq oUs j Bks M)) in H; tauto | auto ]. Qed.
  Lemma ofresh_elim_ups : forall oq Us j Bks M, ofresh K (a_elim oq Us j Bks M) -> forall U, In U Us -> ofresh K U.
  Proof.
    destruct K; cbn; [| auto ].
    intros oq Us j Bks M H; apply (proj1 (exp_fresh_elim _ oq Us j Bks M)) in H as [H _].
    apply all_list_Forall in H; exact (proj1 (Forall_forall _ _) H).
  Qed.
  Lemma ofresh_var : forall x, ofresh K #x -> K <> Some x.
  Proof. destruct K; cbn; congruence. Qed.
  Lemma ofresh_tuple_fields : forall T fs, ofresh K (a_tuple T fs) -> Forall (ofresh K) (List.map snd fs).
  Proof.
    destruct K as [k |]; cbn; [| intros; apply Forall_forall; intros; exact I ].
    intros T fs [_ H]; induction fs as [| [f M] fs IH]; cbn in H |- *; constructor; tauto.
  Qed.
  Lemma ofresh_proj : forall f M, ofresh K (a_proj f M) -> ofresh K M.
  Proof. destruct K; cbn; auto. Qed.

  Lemma omfresh_var : forall x, omfresh K (me_var x) -> K <> Some x.
  Proof. destruct K; cbn; congruence. Qed.
  Lemma omfresh_lit : forall U, omfresh K (me_lit U) -> oufresh K U.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_mem : forall H y, omfresh K (me_mem H y) -> omfresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_app_l : forall H N, omfresh K (me_app H N) -> omfresh K H.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_app_r : forall H N, omfresh K (me_app H N) -> ofresh K N.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma omfresh_spine : forall H R args pre,
      modexp_spine H = (R, args, pre) -> omfresh K H -> omfresh K R /\ Forall (ofresh K) args.
  Proof.
    destruct K as [k |]; cbn; intros * Hs Hf.
    - destruct (modexp_spine_fresh _ _ _ _ _ Hs Hf); split; assumption.
    - split; [ exact I | apply Forall_forall; intros; exact I ].
  Qed.

  Lemma oufresh_body : forall Δ sm Φ, oufresh K (gu_mk Δ (md_body sm Φ)) -> ogfresh (oshift (List.length Δ) K) Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma oufresh_alias : forall Δ E, oufresh K (gu_mk Δ (md_alias E)) -> omfresh (oshift (List.length Δ) K) E.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_def_prefix : forall Φ y b pv A M,
      ogfresh K (gm_ext Φ y (ge_def b pv A (Some M))) -> ogfresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_def_body : forall Φ y b pv A M,
      ogfresh K (gm_ext Φ y (ge_def b pv A (Some M))) -> ofresh (oshift (gm_binders Φ) K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_mod_prefix : forall Φ y pm U,
      ogfresh K (gm_ext Φ y (ge_mod pm U)) -> ogfresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_mod_unit : forall Φ y pm U,
      ogfresh K (gm_ext Φ y (ge_mod pm U)) -> oufresh (oshift (gm_binders Φ) K) U.
  Proof. destruct K; cbn; tauto. Qed.
  (** The term part of an entry ([entry_tm]) and its module part
      ([entry_unit]), under the entries before it. *)
  Lemma ogfresh_ext_prefix : forall Φ y E, ogfresh K (gm_ext Φ y E) -> ogfresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_tm_body : forall Φ y E A M, entry_tm E = Some (A, M) ->
      ogfresh K (gm_ext Φ y E) -> ofresh (oshift (gm_binders Φ) K) M.
  Proof.
    destruct K; cbn; [| tauto ].
    intros Φ y E A M HE Hf; destruct E as [? ? ? [] | | | |]; cbn in HE, Hf; try discriminate; injection HE as <- <-; tauto.
  Qed.
  Lemma ogfresh_unit_unit : forall Φ y E U, entry_unit E = Some U ->
      ogfresh K (gm_ext Φ y E) -> oufresh (oshift (gm_binders Φ) K) U.
  Proof.
    destruct K; cbn; [| tauto ].
    intros Φ y E U HE Hf; destruct E as [| | | |]; cbn in HE, Hf; try discriminate; injection HE as <-; tauto.
  Qed.
  Lemma ogfresh_dm_prefix : forall Φ y pv A M U,
      ogfresh K (gm_ext Φ y (ge_def_mod pv A M U)) -> ogfresh K Φ.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_dm_body : forall Φ y pv A M U,
      ogfresh K (gm_ext Φ y (ge_def_mod pv A M U)) -> ofresh (oshift (gm_binders Φ) K) M.
  Proof. destruct K; cbn; tauto. Qed.
  Lemma ogfresh_dm_unit : forall Φ y pv A M U,
      ogfresh K (gm_ext Φ y (ge_def_mod pv A M U)) -> oufresh (oshift (gm_binders Φ) K) U.
  Proof. destruct K; cbn; tauto. Qed.
End OFresh.

#[local] Hint Resolve ofresh_univ ofresh_succl ofresh_maxl_l ofresh_maxl_r
  ofresh_exfalso_A ofresh_exfalso_M
  ofresh_pi_A ofresh_pi_B ofresh_fn_M ofresh_app_l ofresh_app_r ofresh_let_M ofresh_let_B
  ofresh_letmod_U ofresh_mem ofresh_var ofresh_tuple_fields ofresh_proj omfresh_var omfresh_lit omfresh_mem omfresh_app_l omfresh_app_r
  oufresh_body oufresh_alias ogfresh_def_prefix ogfresh_def_body ogfresh_mod_prefix ogfresh_mod_unit
  ogfresh_dm_prefix ogfresh_dm_body ogfresh_dm_unit
  : avoid.
(** Freshness does not read the group or the member of an eliminator, so
    they are taken from the hypothesis rather than left to unification. *)
#[local] Hint Extern 1 (ofresh _ _) =>
  match goal with
  | H : ofresh ?K (a_elim ?oq ?o ?j ?Bks ?M) |- ofresh ?K ?M => exact (ofresh_elim_M K oq o j Bks M H)
  end : avoid.
#[local] Hint Extern 1 (blocks_ofresh _ _) =>
  match goal with
  | H : ofresh ?K (a_elim ?oq ?o ?j ?Bks ?M) |- blocks_ofresh ?K ?Bks => exact (ofresh_elim_blocks K oq o j Bks M H)
  end : avoid.

(** ** Evaluation Builds No Variable *)

Section Eval.
  Variables (Θ : gdeps) (Ξ : gstack) (v b : nat).

  #[local] Hint Resolve env_av_nil env_av_cons env_av_var env_av_mod dav_args_snoc env_av_args
    dmav_global_nil : mctt.
  (** The uniform parameters an eliminator carries are fresh where it is. *)
  #[local] Hint Extern 1 (Forall (ofresh _) _) =>
    match goal with
    | H : ofresh ?K (a_elim ?oq ?Us ?j ?Bks ?M) |- Forall (ofresh ?K) ?Us =>
        apply Forall_forall; exact (ofresh_elim_ups K oq Us j Bks M H)
    end : avoid.
  #[local] Hint Extern 1 (ups_av _ _ _) => unfold ups_av : avoid.
  #[local] Hint Extern 1 (dav _ _ (dlvl_lit _)) => repeat constructor : mctt.
  #[local] Hint Extern 1 (dav _ _ (dlvl_suc _)) => apply dav_lvl_suc : mctt.
  #[local] Hint Extern 1 (dav _ _ (dlvl_max _ _)) => apply dav_lvl_max : mctt.

  (** The entry an extension adds, given the invariant of its value. *)
  Ltac deav_of d :=
    first [ apply deav_term; solve [ eassumption | eauto 3 with mctt avoid ]
          | apply deav_mod; solve [ eassumption | eauto 3 with mctt avoid ] ].

  (** Forward reasoning: instantiate each induction hypothesis at the
      position the environment it is about has its bad entry at, and
      discharge its premises. *)
  Ltac av_fwd :=
    repeat match goal with
    | H : forall x, ?K <> Some x -> deav ?v ?b (env_entry ?ρ x) |- _ => change (env_av v b K ρ) in H
    | H : Forall _ (_ :: _) |- _ => inversion_clear H
    | H : In _ (_ :: _) |- _ => destruct H as [<- | H]
    | H : In _ nil |- _ => destruct H
    | H : forall a, In a (?x :: ?l) -> ?P |- _ =>
        let H1 := fresh "H" in let H2 := fresh "H" in
        assert (H1 : forall a, a = x -> P) by (intros a Ha; apply H; left; symmetry; exact Ha);
        assert (H2 : forall a, In a l -> P) by (intros a Ha; apply H; right; exact Ha);
        specialize (H1 x eq_refl); clear H
    | Hs : modexp_spine ?H = _, Hf : ofresh ?K (a_mem ?H _) |- _ =>
        apply ofresh_mem in Hf; destruct (omfresh_spine _ _ _ _ _ Hs Hf); clear Hs
    | IH : forall K0, env_av ?v ?b K0 nil -> _ |- _ => specialize (IH None (env_av_nil _ _ None) I)
    | IH : forall K0, env_av ?v ?b K0 ?ρ -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ => specialize (IH K Hρ)
    | IH : forall K0, env_av ?v ?b K0 (extend_env (extend_env ?ρ ?d1) ?d2) -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in let E2 := fresh "E" in
        assert (E1 : deav v b (de_term d1)) by deav_of d1;
        assert (E2 : deav v b (de_term d2)) by deav_of d2;
        specialize (IH (oshift 1 (oshift 1 K)) (env_av_cons _ _ _ _ _ (env_av_cons _ _ _ _ _ Hρ E1) E2));
        rewrite oshift_oshift in IH; cbn [Nat.add] in IH
    | IH : forall K0, env_av ?v ?b K0 (extend_env ?ρ ?d) -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : deav v b (de_term d)) by deav_of d;
        specialize (IH (oshift 1 K) (env_av_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_av ?v ?b K0 (extend_env_mod ?ρ ?h) -> _, Hρ : env_av ?v ?b ?K ?ρ |- _ =>
        let E1 := fresh "E" in
        assert (E1 : deav v b (de_mod h)) by deav_of h;
        specialize (IH (oshift 1 K) (env_av_cons _ _ _ _ _ Hρ E1))
    | IH : forall K0, env_av ?v ?b K0 (env_args ?ρ ?args) -> _, Hρ : env_av ?v ?b ?K ?ρ,
      Ha : forall a, In a ?args -> dav ?v ?b a |- _ =>
        specialize (IH (oshift (List.length args) K) (env_av_args _ _ _ _ _ Hρ Ha));
        repeat match goal with Hl : List.length args = List.length ?D |- _ => rewrite Hl in IH end
    | IH : ?P -> ?Q |- _ =>
        let HP := fresh "HP" in assert (HP : P) by (solve [ eassumption | eauto 3 with mctt avoid ]); specialize (IH HP)
    end.

  (** The next neutral projection of a neutral of a record type: at its
      field's type, evaluated in the parameters and the projections before
      it, which avoid. *)
  Ltac nflds_head_av :=
    match goal with IHT : forall K0, env_av _ _ K0 (env_args nil (?ns ++ ?pre)) -> ofresh K0 _ -> dav _ _ ?t |- _ =>
      constructor;
        [ apply (IHT None);
            [ apply env_av_args_none; [ apply env_av_nil | intros x Hx; apply List.in_app_or in Hx as [Hx | Hx]; auto ]
            | exact I ]
        | constructor; assumption ]
    end.

  Lemma eval_av :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall K, env_av v b K ρ -> ofresh K M -> dav v b m) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dav v b m -> dav v b n -> dav v b r) /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms ->
       forall K, env_av v b K ρ -> Forall (ofresh K) Ms -> forall a, In a ms -> dav v b a) /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r ->
       dav v b m -> (forall a, In a args -> dav v b a) -> dav v b r) /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall K, env_av v b K ρ -> omfresh K H -> dmav v b h) /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall K, env_av v b K ρ -> oufresh K (gu_mk Δ D) -> dmav v b h) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> dmav v b h -> dav v b n -> dmav v b r) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> dmav v b h -> (forall a, In a ns -> dav v b a) -> dmav v b r) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> dmav v b h -> dav v b r) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> dmav v b h -> dmav v b r) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> dmav v b h -> dav v b r) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> dmav v b h -> dmav v b r) /\
    (forall ρ Φ ρ', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
       forall K, env_av v b K ρ -> ogfresh K Φ -> env_av v b (oshift (gm_binders Φ) K) ρ') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       forall K, env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups -> dav v b m -> dav v b r) /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
       forall K, env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups ->
            (forall a, In a vs -> dav v b a) -> forall a, In a ihs -> dav v b a) /\
    (forall ρ p ups Bks t m r, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       forall K, env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups -> dav v b m -> dav v b r) /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r ->
       (forall u, In u ups -> dav v b u) -> forall a, In a (snd r) -> dav v b a) /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
       forall K, env_av v b K ρ -> ptfresh K t -> (forall u, In u ups -> dav v b u) -> dav v b a) /\
    (forall ρm As ρ t m a, ⟦ihty m of t under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
       forall Km, env_av v b Km ρm -> ofresh (oshift (S (List.length (ptyp_ps t))) Km) (List.nth (ptyp_mem t) As a_True) ->
       forall K, env_av v b K ρ -> ptfresh K t -> dav v b m -> dav v b a) /\
    (forall f m r, eval_proj Θ Ξ f m r -> dav v b m -> dav v b r) /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs ->
       (forall a, In a ns -> dav v b a) -> dav_ne v b m -> (forall a, In a pre -> dav v b a) ->
       forall a, In a rs -> dav v b a).
  Proof.
    apply (eval_mut_ind Θ Ξ
             (fun M ρ m _ => forall K, env_av v b K ρ -> ofresh K M -> dav v b m)
             (fun m n r _ => dav v b m -> dav v b n -> dav v b r)
             (fun Ms ρ ms _ => forall K, env_av v b K ρ -> Forall (ofresh K) Ms ->
                                forall a, In a ms -> dav v b a)
             (fun m args r _ => dav v b m -> (forall a, In a args -> dav v b a) -> dav v b r)
             (fun H ρ h _ => forall K, env_av v b K ρ -> omfresh K H -> dmav v b h)
             (fun Δ D ρ h _ => forall K, env_av v b K ρ -> oufresh K (gu_mk Δ D) -> dmav v b h)
             (fun h n r _ => dmav v b h -> dav v b n -> dmav v b r)
             (fun h ns r _ => dmav v b h -> (forall a, In a ns -> dav v b a) -> dmav v b r)
             (fun h x r _ => dmav v b h -> dav v b r)
             (fun h y r _ => dmav v b h -> dmav v b r)
             (fun h ch r _ => dmav v b h -> dav v b r)
             (fun h ch r _ => dmav v b h -> dmav v b r)
             (fun ρ Φ ρ' _ => forall K, env_av v b K ρ -> ogfresh K Φ ->
                               env_av v b (oshift (gm_binders Φ) K) ρ')
             (fun ρ p ups Bks j m r _ => forall K, env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups ->
                                         dav v b m -> dav v b r)
             (fun ρ p ups Bks gs vs ihs _ => forall K, env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups ->
                                       (forall a, In a vs -> dav v b a) -> forall a, In a ihs -> dav v b a)
             (fun ρ p ups Bks t m r _ => forall K, env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups ->
                                         dav v b m -> dav v b r)
             (fun p ups j r _ => (forall u, In u ups -> dav v b u) -> forall a, In a (snd r) -> dav v b a)
             (fun p ups ρ t a _ => forall K, env_av v b K ρ -> ptfresh K t -> (forall u, In u ups -> dav v b u) -> dav v b a)
             (fun ρm As ρ t m a _ => forall Km, env_av v b Km ρm ->
                                    ofresh (oshift (S (List.length (ptyp_ps t))) Km) (List.nth (ptyp_mem t) As a_True) ->
                                    forall K, env_av v b K ρ -> ptfresh K t -> dav v b m -> dav v b a)
             (fun f m r _ => dav v b m -> dav v b r)
             (fun ns m fl pre rs _ => (forall a, In a ns -> dav v b a) -> dav_ne v b m ->
                                     (forall a, In a pre -> dav v b a) -> forall a, In a rs -> dav v b a));
      intros; cbn [ptfresh ptyp_ps ptyp_mem snd] in *.
    all: repeat match goal with
           | H : dav _ _ (_ _) |- _ => inversion_clear H
           | H : dmav _ _ (_ _ _) |- _ => inversion_clear H
           | H : dmav _ _ (_ _ _ _) |- _ => inversion_clear H
           end.
    all: av_fwd.
    (** The uniform arguments of a view, evaluated at the group's. *)
    all: try solve [ match goal with
      | IH : forall K0, env_av _ _ K0 (env_args nil ?ups) -> Forall (ofresh K0) ?Is -> forall a, In a ?cups -> dav _ _ a,
        Hu : forall u, In u ?ups -> dav _ _ u, Ha : In ?a ?cups |- dav _ _ ?a =>
          apply (IH None); [ apply env_av_args_none; [ apply env_av_nil | exact Hu ] | apply Forall_forall; intros; exact I | exact Ha ]
      end ].
    (** Inductive types.  The values are lists, of which evaluation takes
        segments; a branch and the motive are evaluated in an environment
        extended by as many values as they bind. *)
    all: try solve [ lazymatch goal with |- dav _ _ (d_ind _ _ _) => idtac | |- dav _ _ (d_con _ _ _ _) => idtac end;
                     constructor; all_in_with assumption ].
    all: try solve [ match goal with
      | Hf : ofresh ?K (a_elim _ _ _ _ _), IH : _ -> _ -> _ -> dav _ _ ?r |- dav _ _ ?r =>
          apply IH; [ eapply ofresh_elim_blocks; exact Hf | solve [ eauto 3 with mctt avoid ] | assumption ]
      end ].
    all: try solve [ match goal with
      | e : brs_lookup (eb_brs ?bk) ?c = Some (?n, ?B), Hb : List.nth_error ?Bks _ = Some ?bk,
        Hl : List.length ?vs = (im_np ?Dq ?Mk + List.length ?gs)%nat,
        Hn : ?n = _, Hih : eval_ihs _ _ _ _ _ _ ?gs _ ?ihs,
        IHi : (forall x1, In x1 (skipn _ _) -> dav _ _ x1) -> forall x2, In x2 ?ihs -> dav _ _ x2,
        HBk : blocks_ofresh ?K ?Bks,
        Hρ : env_av _ _ ?K ?ρ,
        IHB : forall K0, env_av _ _ K0 (env_args ?ρ ?L) -> ofresh K0 ?B -> dav _ _ ?r |- dav _ _ ?r =>
          let Hi := fresh "Hi" in
          pose proof (IHi ltac:(all_in_with assumption)) as Hi;
          destruct (eval_ihs_length _ _ _ _ _ _ _ Hih) as [_ Hni];
          apply (IHB (oshift (List.length L) K));
            [ apply env_av_args; [ exact Hρ | all_in_with assumption ]
            | rewrite (ind_branch_args_length _ _ _ _ _ Hl), Hni, <- Hn;
              exact (proj2 (HBk _ (List.nth_error_In _ _ Hb)) _ _ _ (brs_lookup_in _ _ _ _ e)) ]
      end ].
    all: try solve [ match goal with
      | Hl : List.length ?as' = im_np ?Dq ?Mk, Hn : eb_nm ?bk = S (im_nn ?Mk), Hb : List.nth_error ?Bks _ = Some ?bk,
        HBk : blocks_ofresh ?K ?Bks, Hρ : env_av _ _ ?K ?ρ,
        IHA : forall K0, env_av _ _ K0 (env_args ?ρ ?L) -> ofresh K0 (eb_motive ?bk) -> dav _ _ ?a
        |- dav _ _ (⇑ ?a (d_elim _ _ _ _ _ _ _)) =>
          constructor;
            [ apply (IHA (oshift (List.length L) K));
                [ apply env_av_args; [ exact Hρ | all_in_with ltac:(constructor; [ constructor; assumption | assumption ]) ]
                | rewrite (ind_motive_args_length _ _ _ _ Hl), <- Hn; exact (proj1 (HBk _ (List.nth_error_In _ _ Hb))) ]
            | eapply dav_elim; eassumption ]
      end ].
    (* the recursive results *)
    all: try solve [ match goal with
      | IH : (forall x1, In x1 ?vs -> dav _ _ x1) -> forall x2, In x2 ?ihs -> dav _ _ x2,
        Hv : forall x3, In x3 (_ :: ?vs) -> dav _ _ x3, Ha : In ?d ?ihs |- dav _ _ ?d =>
          exact (IH (all_in_tail _ _ _ Hv) _ Ha)
      end ].
    all: try solve [ eauto 4 with mctt avoid ].
    (** The types of a function shape's argument and recursive result: a
        [Π] over the family, in an environment that holds only the family. *)
    all: try solve [ lazymatch goal with |- dav _ _ (Πᵈ _ (_ ↦ d_shfam _ _ _ _) _) => idtac end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      eapply dav_pi with (K := None); [ eauto | | exact I ];
      apply env_av_cons_none; [ apply env_av_nil | eapply dav_shfam; eassumption ] ].
    all: try solve [ lazymatch goal with |- dav _ _ (Πᵈ _ (_ ↦ d_ihfam _ _ _ _ _) _) => idtac end;
      match goal with H1 : _ /\ _ |- _ => destruct H1 as [HB Ht] end;
      eapply dav_pi with (K := None); [ eauto | | exact I ];
      apply env_av_cons_none; [ apply env_av_nil | eapply dav_ihfam; eassumption ] ].
    (** The type of the recursive result at a shape's leaf: the motive at
        the leaf's parameters and the argument. *)
    all: try solve [ match goal with
      | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs, IH : forall K0, env_av _ _ K0 (env_args ?ρm (?bs ++ ?v0 :: nil)) -> ofresh K0 ?A -> _,
        Hm : env_av _ _ ?Km ?ρm, HA : ofresh (oshift (S (List.length ?Ps)) ?Km) ?A |- _ =>
          let Hlb := fresh "Hlb" in
          assert (Hlb : List.length bs = List.length Ps) by (clear - e; induction e; cbn; congruence);
          apply (IH (oshift (List.length (bs ++ v0 :: nil)) Km));
            [ apply env_av_args; [ exact Hm | apply dav_args_snoc; assumption ]
            | rewrite List.length_app, Hlb; cbn [List.length]; replace (List.length Ps + 1) with (S (List.length Ps)) by lia; exact HA ]
      end ].
    (** A constructor of a view at the uniform parameters: the container's
        at the view's arguments, closed terms evaluated in an environment of
        the values given. *)
    all: try solve [ apply dav_con;
      match goal with H : forall K0, env_av _ _ K0 (env_args nil _) -> Forall (ofresh K0) _ -> forall a, In a _ -> dav _ _ a |- _ =>
        apply (H None);
          [ apply env_av_args_none; [ apply env_av_nil | first [ intros ? [] | apply dav_args_snoc; assumption ] ]
          | apply List.Forall_forall; intros; exact I ] end ].
    (** The type of a recursive argument: the member at the shape's
        parameters after the uniform ones. *)
    all: try solve [ apply dav_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha]; eauto ].
    (** Records: a type former's arguments, a tuple's fields, a field of a
        tuple, and the projections of a neutral at their types. *)
    all: try solve [ lazymatch goal with |- dav _ _ (d_record _ nil) => apply dav_record; intros ? [] end ].
    all: try solve [ match goal with
      | H : forall y, In y ?vs -> dav _ _ y |- dav _ _ (d_tuple (List.combine _ ?vs)) =>
          apply dav_tuple; intros f y Hin; exact (H _ (List.in_combine_r _ _ _ _ Hin))
      end ].
    all: try solve [ match goal with
      | H : forall f y, In (f, y) ?vs -> dav _ _ y, Hl : field_lookup ?vs _ = Some ?r |- dav _ _ ?r =>
          exact (H _ _ (field_lookup_In _ _ _ Hl))
      end ].
    all: try solve [ match goal with
      | IH : (forall y, In y nil -> dav _ _ y) -> forall z, In z ?rs -> dav _ _ z, Hk : List.nth_error ?rs _ = Some ?r |- dav _ _ ?r =>
          exact (IH (fun _ Hin => match Hin with end) _ (List.nth_error_In _ _ Hk))
      end ].
    all: try solve [ lazymatch goal with |- dav _ _ (⇑ _ (d_proj _ _)) => nflds_head_av end ].
    (** A record type of a global module: its type former, applied to the
        module's arguments. *)
    all: try solve [ match goal with IH : dav _ _ (d_record _ nil) -> _ -> _, Ha : forall a, In a _ -> dav _ _ a |- _ =>
                       apply IH; [ apply dav_record; intros ? [] | exact Ha ] end ].
    all: try solve [ match goal with
      | IH : (forall y, In y (?pre ++ ?x :: nil) -> dav _ _ y) -> forall z, In z ?rs -> dav _ _ z, Hin : In ?d ?rs |- dav _ _ ?d =>
          eapply IH; [ apply dav_args_snoc; [ assumption | nflds_head_av ] | exact Hin ]
      end ].
    (** What is left: the closures the rules build, and the module bodies,
        whose freshness is at the position their parameters and entries
        shift it to. *)
    - (* [efq] on a neutral *)
      apply dav_neut; [ assumption |].
      match goal with Hn : dav _ _ (⇑ _ _) |- _ => inversion Hn; subst end.
      eapply dav_exfalso with (K := K); eassumption.
    - (* an alias lacking no parameter: its target *)
      match goal with IH : omfresh ?K ?E -> _, Hu : oufresh ?K (gu_mk nil (md_alias ?E)) |- _ =>
        apply IH; pose proof (oufresh_alias _ _ _ Hu) as Hx; cbn [List.length] in Hx; rewrite oshift_zero in Hx; exact Hx end.
    - (* a closure given its outermost parameter *)
      match goal with IH : oufresh (oshift 1 ?K) _ -> _, Hu : oufresh ?K (gu_mk (_ ++ _) _) |- _ =>
        exact (IH (oufresh_snoc _ _ _ _ Hu)) end.
    - (* the module of an inductive type, a member of a global module: the
         type former, applied to the module's arguments *)
      match goal with IH : dav _ _ (d_ind _ _ _) -> _ -> _, Ha : forall a, In a _ -> dav _ _ a |- _ =>
        apply IH; [ constructor; intros ? [] | exact Ha ] end.
    - (* a term part of a saturated body, in its expansion *)
      match goal with Hb : kbody _ _ _ ?Φ ?Φx, Hp : gm_prefix_upto ?Φx _ = Some _, HE : entry_tm _ = Some _,
                      Hu : oufresh ?K (gu_mk nil (md_body _ ?Φ)),
                      IHb : ogfresh ?K _ -> _, IHM : forall K0, _ -> ofresh K0 _ -> _ |- _ =>
        pose proof (oufresh_body _ _ _ _ Hu) as HΦ; cbn [List.length] in HΦ; rewrite oshift_zero in HΦ;
        pose proof (ofresh_prefix_upto _ _ _ _ Hp (kbody_ogfresh _ _ _ _ _ _ Hb HΦ)) as HΦ';
        exact (IHM _ (IHb (ogfresh_ext_prefix _ _ _ _ HΦ')) (ogfresh_tm_body _ _ _ _ _ _ HE HΦ')) end.
    - (* a module part of a saturated body, in its expansion *)
      match goal with Hb : kbody _ _ _ ?Φ ?Φx, Hp : gm_prefix_upto ?Φx _ = Some _, HE : entry_unit _ = Some _,
                      Hu : oufresh ?K (gu_mk nil (md_body _ ?Φ)),
                      IHb : ogfresh ?K _ -> _, IHM : forall K0, _ -> oufresh K0 _ -> _ |- _ =>
        pose proof (oufresh_body _ _ _ _ Hu) as HΦ; cbn [List.length] in HΦ; rewrite oshift_zero in HΦ;
        pose proof (ofresh_prefix_upto _ _ _ _ Hp (kbody_ogfresh _ _ _ _ _ _ Hb HΦ)) as HΦ';
        exact (IHM _ (IHb (ogfresh_ext_prefix _ _ _ _ HΦ')) (ogfresh_unit_unit _ _ _ _ _ HE HΦ')) end.
    - (* the empty body *)
      cbn [gm_binders]; rewrite oshift_zero; assumption.
    - (* a definition entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- oshift_oshift.
      apply env_av_cons; [ assumption | constructor; assumption ].
    - (* a submodule entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- oshift_oshift.
      apply env_av_cons; [ assumption | constructor; assumption ].
    - (* a definition with a module part entry *)
      cbn [gm_binders]; replace (S (gm_binders Φ)) with (1 + gm_binders Φ) by lia; rewrite <- oshift_oshift.
      apply env_av_cons; [ assumption | constructor; assumption ].
  Qed.
End Eval.

(** A closure, evaluated at one or two more entries. *)
Lemma eval_clo_av : forall Θ Ξ v b K (ρ : env) B c d,
    env_av v b K ρ -> ofresh (oshift 1 K) B -> dav v b c ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ d -> dav v b d.
Proof.
  intros * Hρ HB Hc Hd.
  eapply (proj1 (eval_av Θ Ξ v b)); [ exact Hd | apply env_av_cons; [ exact Hρ | constructor; exact Hc ] | exact HB ].
Qed.

Lemma eval_clo2_av : forall Θ Ξ v b K (ρ : env) B c1 c2 d,
    env_av v b K ρ -> ofresh (oshift 2 K) B -> dav v b c1 -> dav v b c2 ->
    ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ d -> dav v b d.
Proof.
  intros * Hρ HB Hc1 Hc2 Hd.
  eapply (proj1 (eval_av Θ Ξ v b) _ _ _ Hd (oshift 1 (oshift 1 K))).
  - apply env_av_cons; [ apply env_av_cons; [ exact Hρ | constructor; exact Hc1 ] | constructor; exact Hc2 ].
  - rewrite oshift_oshift; exact HB.
Qed.

Lemma app_av : forall Θ Ξ v b m n r, $| m & n | Θ ⍮ Ξ ↘ r -> dav v b m -> dav v b n -> dav v b r.
Proof. intros * H; exact (proj1 (proj2 (eval_av Θ Ξ v b)) _ _ _ H). Qed.

Lemma shty_av : forall Θ Ξ v b p ups ρ t a K, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
    env_av v b K ρ -> ptfresh K t -> (forall u, In u ups -> dav v b u) -> dav v b a.
Proof.
  intros * H; destruct (eval_av Θ Ξ v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
  exact (Hs _ _ _ _ _ H K).
Qed.

Lemma ihty_av : forall Θ Ξ v b ρm As ρ t m a Km K, ⟦ihty m of t under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
    env_av v b Km ρm -> ofresh (oshift (S (List.length (ptyp_ps t))) Km) (List.nth (ptyp_mem t) As a_True) ->
    env_av v b K ρ -> ptfresh K t -> dav v b m -> dav v b a.
Proof.
  intros * H; destruct (eval_av Θ Ξ v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy & _).
  intros; eapply Hy; eassumption.
Qed.

Lemma proj_av : forall Θ Ξ v b f m r, eval_proj Θ Ξ f m r -> dav v b m -> dav v b r.
Proof.
  intros * H; destruct (eval_av Θ Ξ v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
  exact (Hp _ _ _ H).
Qed.

Lemma ih_av : forall Θ Ξ v b ρ p ups Bks t m r K, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
    env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups -> dav v b m -> dav v b r.
Proof.
  intros * H; destruct (eval_av Θ Ξ v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _).
  intros; eapply Hi; eassumption.
Qed.

Lemma mref_av : forall Θ Ξ v b p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r ->
    (forall u, In u ups -> dav v b u) -> forall a, In a (snd r) -> dav v b a.
Proof.
  intros * H; destruct (eval_av Θ Ξ v b) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _).
  exact (Hm _ _ _ _ H).
Qed.

(** The recursive results a branch is read under, when the eliminator is
    read as its container's: the fresh ones, and the eliminator's at the
    arguments recursive in the group only. *)
Lemma wrap_ihs_eval_av : forall Θ Ξ v b ρ p ups Bks gs' gs vs ihs r K,
    ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
    env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups ->
    (forall a, In a vs -> dav v b a) -> (forall a, In a ihs -> dav v b a) -> forall a, In a r -> dav v b a.
Proof.
  induction 1; intros Hρ HB Ho Hv Hi; [ apply all_in_nil | | |].
  - apply all_in_cons; [ apply Hi; left; reflexivity |].
    apply IHwrap_ihs_eval; [ assumption | assumption | assumption | all_in_with assumption | all_in_with assumption ].
  - apply all_in_cons; [ eapply ih_av; [ eassumption | eassumption | assumption | assumption | apply Hv; left; reflexivity ] |].
    apply IHwrap_ihs_eval; [ assumption | assumption | assumption | all_in_with assumption | assumption ].
  - apply IHwrap_ihs_eval; [ assumption | assumption | assumption | all_in_with assumption | assumption ].
Qed.

Lemma wrap_ihs_eval_length : forall Θ Ξ ρ p ups Bks gs' gs vs ihs r,
    ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> List.length r = cargs_nrec gs /\ List.length vs = List.length gs'.
Proof. induction 1; cbn; intuition congruence. Qed.

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

(** The motives at the recursive arguments, fresh under their binders, from
    the blocks: through the member each shape ends in. *)
Lemma ihs_motives_fresh : forall D Bks K gs, cargs_plen D gs -> blocks_nm_at D None Bks -> blocks_ofresh K Bks ->
    Forall (fun g => match g with
                     | ca_rec t => ofresh (oshift (S (List.length (ptyp_ps t))) K)
                                     (List.nth (ptyp_mem t) (blocks_motives Bks) a_True)
                     | ca_arg _ => True end) gs.
Proof.
  intros * Hpl Hnm HB; pose proof (plen_forall _ _ Hpl) as Hf.
  eapply Forall_impl; [| exact Hf ]; intros [A | t] H; [ exact I |].
  destruct H as (Mj & HMj & Hl).
  pose proof (nth_motives_sel None Bks (ptyp_mem t)) as Hm; cbn [motives_sel elim_src] in Hm.
  destruct Hm as [-> | (b & Hb & ->)]; [ destruct K; exact I |].
  rewrite Hl, <- (Hnm _ _ _ HMj Hb); exact (proj1 (HB _ (List.nth_error_In _ _ Hb))).
Qed.

Lemma dav_mono' : forall v b b' d, b <= b' -> dav v b d -> dav v b' d.
Proof. intros; eapply (proj1 (dav_mono v b)); eassumption. Qed.

Lemma ups_av_mono : forall v b b' ups, b <= b' -> ups_av v b ups -> ups_av v b' ups.
Proof. intros * Hb H a Ha; exact (dav_mono' _ _ _ _ Hb (H a Ha)). Qed.

(** ** Readback Introduces Only Variables Above the Ones in Scope *)

Lemma la_fresh_canon : forall k c xs, all_list (fun a => ne_fresh k (atom_level a)) xs ->
    all_list (fun a => ne_fresh k (atom_level a)) (snd (lvl_canon (c, xs))).
Proof. intros * H; apply la_all_all_list, la_all_canon, la_all_all_list; assumption. Qed.

Section Read.
  Variables (Θ : gdeps) (Ξ : gstack) (v : nat).

  (** A neutral variable at the readback length, at a bound past it. *)
  Lemma dav_fresh_var : forall b s a, v < s -> b <= s -> dav v b a -> dav v (S s) (⇑! a s).
  Proof.
    intros * Hv Hb Ha; constructor; [ eapply (proj1 (dav_mono v b)); [ exact Ha | lia ] | constructor; lia ].
  Qed.

  (** The invariant of a value built during readback: by its constructor, by
      monotonicity, or by the evaluation it came from. *)
  Ltac dav_tac v :=
    first [ eassumption
          | solve [ constructor ]
          | match goal with H : dav v ?b0 ?d |- dav v ?n ?d => eapply (dav_mono' v b0 n d); [ lia | exact H ] end
          | match goal with |- dav v _ (d_neut _ (d_var _)) => constructor; [ dav_tac v | constructor; lia ] end
          | match goal with
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env (extend_env ?ρ ?c1) ?c2 ↘ ?d,
              Hρ : forall x, ?K <> Some x -> deav v ?b0 (env_entry ?ρ x) |- dav v ?n ?d =>
                eapply (eval_clo2_av _ _ v n K ρ B c1 c2 d);
                  [ eapply env_av_mono; [| exact Hρ ]; lia | assumption | dav_tac v | dav_tac v | exact e ]
            end
          | match goal with
            | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ extend_env ?ρ ?c ↘ ?d,
              Hρ : forall x, ?K <> Some x -> deav v ?b0 (env_entry ?ρ x) |- dav v ?n ?d =>
                eapply (eval_clo_av _ _ v n K ρ B c d);
                  [ eapply env_av_mono; [| exact Hρ ]; lia | assumption | dav_tac v | exact e ]
            end
          | match goal with
            | e : $| ?m & ?c | _ ⍮ _ ↘ ?d |- dav v ?n ?d =>
                eapply (app_av _ _ v n m c d); [ exact e | dav_tac v | dav_tac v ]
            end ].

  (** The fresh variables of the telescopes of a declaration are above the
      readback length, and below the length past them.  The types of the
      telescopes are closed, so their environments avoid [v] everywhere. *)
  Lemma fresh_tele_av : forall ρ T s vs, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      forall b, v < s -> b <= s -> env_av v b None ρ -> forall a, In a vs -> dav v (s + List.length T) a.
  Proof.
    induction 1; intros b0 Hv Hb Hρ; [ apply all_in_nil |].
    assert (Ha : dav v b0 a) by (eapply (proj1 (eval_av Θ Ξ v b0)); [ eassumption | exact Hρ | exact I ]).
    cbn [List.length]; replace (s + S (List.length T)) with (S s + List.length T) by lia.
    apply all_in_cons.
    - eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia.
    - apply (IHfresh_tele (S s)); [ lia | lia |].
      change (@None nat) with (oshift 1 None).
      apply env_av_cons; [ eapply env_av_mono; [| exact Hρ ]; lia | constructor; apply (dav_fresh_var b0); assumption ].
  Qed.

  Lemma fresh_cargs_av : forall p ups ρ gs s vs, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      forall b, v < s -> b <= s -> env_av v b None ρ -> (forall a, In a ups -> dav v b a) ->
      forall a, In a vs -> dav v (s + List.length gs) a.
  Proof.
    induction 1; intros b0 Hv Hb Hρ Hu.
    - apply all_in_nil.
    - assert (Ha : dav v b0 a) by (eapply (proj1 (eval_av Θ Ξ v b0)); [ eassumption | exact Hρ | exact I ]).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      apply all_in_cons; [ eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia |].
      apply (IHfresh_cargs (S s)); [ lia | lia | | intros; eapply dav_mono'; [| apply Hu; eassumption ]; lia ].
      change (@None nat) with (oshift 1 None).
      apply env_av_cons; [ eapply env_av_mono; [| exact Hρ ]; lia | constructor; apply (dav_fresh_var b0); assumption ].
    - assert (Ha : dav v b0 a) by (eapply shty_av; [ eassumption | exact Hρ | apply ptfresh_none | exact Hu ]).
      cbn [List.length]; replace (s + S (List.length gs)) with (S s + List.length gs) by lia.
      apply all_in_cons; [ eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia |].
      apply (IHfresh_cargs b0); [ lia | lia | exact Hρ | exact Hu ].
  Qed.

  (** The recursive results are at the motive's instance at the recursive
      argument and its parameters: as many as the motive binds, when each
      recursive argument has as many parameters as the type has non-uniform
      ones. *)
  Lemma fresh_ihs_av : forall ρ As ρa gs' gs vs s ihs, Fihs vs at gs' gs under ρ As in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
      forall b K, v < s -> b <= s -> env_av v b K ρ -> env_av v b None ρa ->
      List.Forall (fun g => match g with
                            | ca_rec t => ofresh (oshift (S (List.length (ptyp_ps t))) K) (List.nth (ptyp_mem t) As a_True)
                            | ca_arg _ => True end) gs ->
      (forall a, In a vs -> dav v b a) ->
      forall a, In a ihs -> dav v (s + cargs_nrec gs') a.
  Proof.
    induction 1; intros b0 K Hv Hb Hρ Hρa Hl Hvs.
    - apply all_in_nil.
    - inversion_clear Hl as [| ? ? _ Hl2].
      apply (IHfresh_ihs b0 K); try assumption.
      + apply env_av_cons_none; [ exact Hρa | exact (all_in_head _ _ _ Hvs) ].
      + exact (all_in_tail _ _ _ Hvs).
    - inversion_clear Hl as [| ? ? Hl1 Hl2]; cbn beta iota in Hl1.
      assert (Ha : dav v b0 a)
        by (eapply ihty_av; [ eassumption | exact Hρ | exact Hl1 | exact Hρa | apply ptfresh_none
                            | exact (all_in_head _ _ _ Hvs) ]).
      cbn [cargs_nrec]; replace (s + S (cargs_nrec gs')) with (S s + cargs_nrec gs') by lia.
      apply all_in_cons.
      + eapply dav_mono'; [| apply (dav_fresh_var b0); assumption ]; lia.
      + apply (IHfresh_ihs b0 K); try assumption; try lia.
        exact (all_in_tail _ _ _ Hvs).
    - inversion_clear Hl as [| ? ? _ Hl2].
      cbn [cargs_nrec]; apply (IHfresh_ihs b0 K); try assumption.
      exact (all_in_tail _ _ _ Hvs).
  Qed.

  (** The motive of a block of a stuck eliminator, at the fresh non-uniform
      parameters and scrutinee, which are above the readback length. *)
  Lemma motive_av : forall ρ K A X pre hd k Mi s ns a b,
      Ftele List.rev (im_nparams Mi) in Θ ⍮ Ξ ⍮ env_args nil X ⍮ s ↘ ns ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mi) :: nil) ↘ a ->
      v < s -> b <= s -> env_av v b K ρ -> ofresh (oshift (S (im_nn Mi)) K) A ->
      (forall x, In x X -> dav v b x) -> (forall x, In x pre -> dav v b x) ->
      dav v (S (s + im_nn Mi)) a.
  Proof.
    intros * f e Hv Hb Hρ HA HX Hp.
    pose proof (fresh_tele_length _ _ _ _ f) as Hlen; rewrite List.length_rev in Hlen.
    change (List.length (im_nparams Mi)) with (im_nn Mi) in Hlen.
    assert (Hns : forall x, In x ns -> dav v (s + im_nn Mi) x).
    { pose proof (fresh_tele_av _ _ _ _ f b Hv Hb ltac:(apply env_av_args_none; [ apply env_av_nil | exact HX ])) as H.
      rewrite List.length_rev in H; exact H. }
    eapply (proj1 (eval_av Θ Ξ v (S (s + im_nn Mi)))); [ exact e | apply env_av_args; [ eapply env_av_mono; [| exact Hρ ]; lia |] |].
    - apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; lia |].
      apply all_in_cons; [| apply all_in_nil ].
      apply (dav_fresh_var (s + im_nn Mi)); [ lia | lia |].
      constructor; apply all_in_app; [ intros; eapply dav_mono'; [| apply Hp; eassumption ]; lia | exact Hns ].
    - rewrite List.length_app, Hlen; cbn [List.length]; replace (im_nn Mi + 1) with (S (im_nn Mi)) by lia; exact HA.
  Qed.

  (** A branch of a block of a stuck eliminator, and the motive's instance
      it is read at: under the fresh non-uniform parameters, arguments and
      recursive results of the group read, as many as the branch binds. *)
  Lemma branch_av : forall ρ K p ups Bks A B X pre hd k c Mi Mv D gs' gs s n0 ns vs ihs wihs bv t b,
      Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ env_args nil X ⍮ s ↘ ns ->
      Fcargs gs of p X in Θ ⍮ Ξ ⍮ env_args nil (X ++ ns) ⍮ (s + im_nn Mi) ↘ vs ->
      Fihs vs at gs' gs under ρ (blocks_motives Bks) in Θ ⍮ Ξ ⍮ env_args nil (X ++ ns) ⍮
        (s + im_nn Mi + List.length gs') ↘ ihs ->
      ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ wihs) ↘ bv ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con hd k c (pre ++ ns ++ vs) :: nil) ↘ t ->
      n0 = (im_nn Mi + List.length gs' + cargs_nrec gs)%nat -> im_nn Mv = im_nn Mi ->
      cargs_plen D gs -> blocks_nm_at D None Bks ->
      v < s -> b <= s -> env_av v b K ρ -> blocks_ofresh K Bks -> ups_av v b ups ->
      ofresh (oshift (S (im_nn Mi)) K) A -> ofresh (oshift n0 K) B ->
      (forall x, In x X -> dav v b x) -> (forall x, In x pre -> dav v b x) ->
      dav v (s + (im_nn Mi + List.length gs' + cargs_nrec gs')) t /\
      dav v (s + (im_nn Mi + List.length gs' + cargs_nrec gs')) bv.
  Proof.
    intros * f f0 f2 fw e0 e1 Hn0 Hnn Hpl Hnm Hv Hb Hρ HBk Ho HA HB HX Hp.
    set (n := (im_nn Mi + List.length gs' + cargs_nrec gs')%nat).
    pose proof (fresh_tele_length _ _ _ _ f) as Hl1; rewrite List.length_rev in Hl1.
    change (List.length (im_nparams Mv)) with (im_nn Mv) in Hl1; rewrite Hnn in Hl1.
    pose proof (fresh_cargs_length _ _ _ _ _ _ f0) as Hl2.
    destruct (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ fw) as [Hl3 Hl4].
    assert (Hns : forall x, In x ns -> dav v (s + im_nn Mi) x).
    { pose proof (fresh_tele_av _ _ _ _ f b Hv Hb ltac:(apply env_av_args_none; [ apply env_av_nil | exact HX ])) as H.
      rewrite List.length_rev in H; change (List.length (im_nparams Mv)) with (im_nn Mv) in H; rewrite Hnn in H; exact H. }
    assert (Hρa : env_av v (s + im_nn Mi) None (env_args nil (X ++ ns)))
      by (apply env_av_args_none; [ apply env_av_nil | apply all_in_app; [ intros; eapply dav_mono'; [| apply HX; eassumption ]; lia | exact Hns ] ]).
    pose proof (fresh_cargs_av _ _ _ _ _ _ f0 (s + im_nn Mi) ltac:(lia) ltac:(lia) Hρa
                  ltac:(intros; eapply dav_mono'; [| apply HX; eassumption ]; lia)) as Hvs.
    assert (Hgl : List.length gs = List.length gs') by congruence.
    rewrite Hgl in Hvs.
    pose proof (fresh_ihs_av _ _ _ _ _ _ _ _ f2 (s + im_nn Mi + List.length gs') K
                  ltac:(lia) ltac:(lia) ltac:(eapply env_av_mono; [| exact Hρ ]; lia)
                  ltac:(eapply env_av_mono; [| exact Hρa ]; lia) (ihs_motives_fresh _ _ _ _ Hpl Hnm HBk) Hvs) as Hihs.
    assert (Hw : forall x, In x wihs -> dav v (s + n) x).
    { eapply wrap_ihs_eval_av; [ exact fw | eapply env_av_mono; [| exact Hρ ]; unfold n; lia | exact HBk |
        eapply ups_av_mono; [| exact Ho ]; unfold n; lia |
        intros; eapply dav_mono'; [| apply Hvs; eassumption ]; unfold n; lia |
        intros; eapply dav_mono'; [| apply Hihs; eassumption ]; unfold n; lia ]. }
    split.
    - eapply (proj1 (eval_av Θ Ξ v (s + n))); [ exact e1 | apply env_av_args; [ eapply env_av_mono; [| exact Hρ ]; unfold n; lia |] |].
      + apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_cons; [| apply all_in_nil ].
        constructor; apply all_in_app; [ intros; eapply dav_mono'; [| apply Hp; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; unfold n; lia
                          | intros; eapply dav_mono'; [| apply Hvs; eassumption ]; unfold n; lia ].
      + rewrite List.length_app, Hl1; cbn [List.length]; replace (im_nn Mi + 1) with (S (im_nn Mi)) by lia; exact HA.
    - eapply (proj1 (eval_av Θ Ξ v (s + n))); [ exact e0 | apply env_av_args; [ eapply env_av_mono; [| exact Hρ ]; unfold n; lia |] |].
      + apply all_in_app; [ intros; eapply dav_mono'; [| apply Hns; eassumption ]; unfold n; lia |].
        apply all_in_app; [ intros; eapply dav_mono'; [| apply Hvs; eassumption ]; unfold n; lia | exact Hw ].
      + rewrite !List.length_app, Hl1, Hl2, Hgl, Hl3, Nat.add_assoc, <- Hn0; exact HB.
  Qed.

  Lemma read_av :
    (forall s m W, Rnf m in Θ ⍮ Ξ ⍮ s ↘ W ->
       forall b, v < s -> b <= s -> dav_nf v b m -> nf_fresh (s - v - 1) W) /\
    (forall s m M, Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
       forall b, v < s -> b <= s -> dav_ne v b m -> ne_fresh (s - v - 1) M) /\
    (forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
       forall b, v < s -> b <= s -> dav v b a -> nf_fresh (s - v - 1) A) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
       forall b, v < s -> b <= s -> dav_la v b xs -> all_list (fun a => ne_fresh (s - v - 1) (atom_level a)) ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall b, v < s -> b <= s -> env_av v b None ρ -> (forall a, In a vs -> dav v b a) ->
       all_list (nf_fresh (s - v - 1)) Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms ->
       forall b, v < s -> b <= s -> env_av v b None ρ -> (forall a, In a ups -> dav v b a) ->
       (forall a, In a vs -> dav v b a) -> all_list (nf_fresh (s - v - 1)) Ms) /\
    (forall s p ups ρ t x X, Rsh x at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ X ->
       forall b, v < s -> b <= s -> env_av v b None ρ -> (forall a, In a ups -> dav v b a) ->
       dav v b x -> nf_fresh (s - v - 1) X) /\
    (forall s ρ p ups Bks sel i Ms NBks, Rblks i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
       forall b K D, v < s -> b <= s -> env_av v b K ρ -> blocks_ofresh K Bks ->
       ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks ->
       (forall a, In a ups -> dav v b a) -> all_list (normal_block_forall (fun n => nf_fresh (n + (s - v - 1)))) NBks) /\
    (forall s ρ p ups Bks Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       forall b K D, v < s -> b <= s -> env_av v b K ρ -> blocks_ofresh K Bks ->
       ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks -> im_nn Mv = im_nn Mi ->
       ofresh (oshift (S (im_nn Mi)) K) A ->
       (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
       (forall a, In a ups -> dav v b a) -> (forall a, In a (snd r) -> dav v b a) -> all_list (fun br => nf_fresh (branch_arity br + (s - v - 1)) (branch_body br)) Bs') /\
    (forall s ρ fl d Fs, Rflds d at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs ->
       forall b, v < s -> b <= s -> env_av v b None ρ -> dav v b d -> all_list (nf_fresh (s - v - 1)) Fs).
  Proof.
    apply (read_mut_ind Θ Ξ
             (fun s m W _ => forall b, v < s -> b <= s -> dav_nf v b m -> nf_fresh (s - v - 1) W)
             (fun s m M _ => forall b, v < s -> b <= s -> dav_ne v b m -> ne_fresh (s - v - 1) M)
             (fun s a A _ => forall b, v < s -> b <= s -> dav v b a -> nf_fresh (s - v - 1) A)
             (fun s xs ys _ => forall b, v < s -> b <= s -> dav_la v b xs -> all_list (fun a => ne_fresh (s - v - 1) (atom_level a)) ys)
             (fun s ρ T vs Ms _ => forall b, v < s -> b <= s -> env_av v b None ρ ->
                                  (forall a, In a vs -> dav v b a) -> all_list (nf_fresh (s - v - 1)) Ms)
             (fun s p ups ρ gs vs Ms _ => forall b, v < s -> b <= s -> env_av v b None ρ ->
                                        (forall a, In a ups -> dav v b a) ->
                                        (forall a, In a vs -> dav v b a) -> all_list (nf_fresh (s - v - 1)) Ms)
             (fun s p ups ρ t x X _ => forall b, v < s -> b <= s -> env_av v b None ρ ->
                                     (forall a, In a ups -> dav v b a) -> dav v b x -> nf_fresh (s - v - 1) X)
             (fun s ρ p ups Bks sel i Ms NBks _ => forall b K D, v < s -> b <= s -> env_av v b K ρ ->
                                                      blocks_ofresh K Bks ->
                                                      ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks ->
                                                      (forall a, In a ups -> dav v b a) -> all_list (normal_block_forall (fun n => nf_fresh (n + (s - v - 1)))) NBks)
             (fun s ρ p ups Bks Mv A Mi r cs Bs Bs' _ => forall b K D, v < s -> b <= s -> env_av v b K ρ ->
                                                            blocks_ofresh K Bks ->
                                                            ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks ->
                                                            im_nn Mv = im_nn Mi ->
                                                            ofresh (oshift (S (im_nn Mi)) K) A ->
                                                            (forall c n B, In (c, n, B) Bs -> ofresh (oshift n K) B) ->
                                                            (forall a, In a ups -> dav v b a) ->
                                                            (forall a, In a (snd r) -> dav v b a) -> all_list (fun br => nf_fresh (branch_arity br + (s - v - 1)) (branch_body br)) Bs')
             (fun s ρ fl d Fs _ => forall b, v < s -> b <= s -> env_av v b None ρ -> dav v b d -> all_list (nf_fresh (s - v - 1)) Fs));
      intros; cbn [snd] in *;
      repeat match goal with
        | H : dav_nf _ _ (_ _ _) |- _ => inversion_clear H
        | H : dav_la _ _ (_ :: _) |- _ => inversion_clear H
        end.
    all: repeat match goal with
      | H : dav _ _ (d_neut _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_lvl _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_suniv _) |- _ => inversion_clear H
      | H : dav _ _ (d_pi _ _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_ind _ _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_con _ _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_app _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_var _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_exfalso _ _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_elim _ _ _ _ _ _ _) |- _ => inversion_clear H
      | H : dav _ _ (d_record _ _) |- _ => inversion_clear H
      | H : dav_ne _ _ (d_proj _ _) |- _ => inversion_clear H
      | H : dav_nf _ _ (_ _ _) |- _ => inversion_clear H
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
      | IH1 : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None nil -> _ -> all_list (nf_fresh _) ?Ps,
        IH2 : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None (env_args nil ?as') -> _ -> _ -> all_list (nf_fresh _) ?Args,
        Hb : ?b <= ?s, Ha : forall a, In a ?as' -> dav v ?b a |- all_list (nf_fresh _) (?Ps ++ ?Args) =>
          apply all_list_app;
            [ apply (IH1 b); [ lia | lia | apply env_av_nil | assumption ]
            | apply (IH2 b); [ lia | lia | apply env_av_args_none; [ apply env_av_nil | assumption ]
                             | all_in_with assumption | all_in_with assumption ] ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None nil -> _ -> all_list (nf_fresh _) ?Ps,
        Hb : ?b <= ?s |- all_list (nf_fresh _) ?Ps =>
          apply (IH b); [ lia | lia | apply env_av_nil | assumption ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> dav_nf v b0 (⇓ ?a ?v0) -> nf_fresh _ ?V |- nf_fresh _ ?V =>
          apply (IH b); [ lia | lia | constructor;
            [ eapply (proj1 (eval_av Θ Ξ v b)); [ exact e | exact Hρ | exact I ] | exact (all_in_head _ _ _ Hv) ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?a, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (?v0 :: _) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None (?ρ ↦ ?v0) -> _ |- all_list (nf_fresh _) _ =>
          apply (IH b); try lia;
            [ apply env_av_cons_none; [ exact Hρ | exact (all_in_head _ _ _ Hv) ] |..]; all_in_with assumption
      end ].
    (** A recursive argument, by its shape. *)
    all: try solve [ match goal with
      | Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> dav v ?b x,
        Hv : forall x, In x (?v0 :: _) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None ?ρ -> (forall a, In a ?ups -> _) -> dav v b0 ?v0 ->
             nf_fresh _ ?V |- nf_fresh _ ?V =>
          apply (IH b); [ lia | lia | exact Hρ | exact Hu | exact (all_in_head _ _ _ Hv) ]
      end ].
    (** The end of a shape: the member at the uniform parameters and the
        shape's own. *)
    all: try solve [ match goal with
      | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ ?ρ ↘ ?bs, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> dav v ?b x, Hx : dav v ?b ?x0,
        IH : forall b0, v < ?s -> b0 <= ?s -> dav_nf v b0 (⇓ (d_ind ?p ?j (?ups ++ ?bs)) ?x0) -> nf_fresh _ ?V
        |- nf_fresh _ ?V =>
          apply (IH b); [ lia | lia | constructor; [| exact Hx ] ];
          apply dav_indty; intros a Ha; apply List.in_app_or in Ha as [Ha | Ha];
            [ exact (Hu _ Ha)
            | exact (proj1 (proj2 (proj2 (eval_av Θ Ξ v b))) _ _ _ e None Hρ
                       (proj2 (List.Forall_forall _ _) (fun _ _ => I)) _ Ha) ]
      end ].
    (** A function shape: under a fresh variable of its domain. *)
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b0, ea : $| ?x0 & ⇑! ?b0 ?s | _ ⍮ _ ↘ ?r,
        Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> dav v ?b x, Hx : dav v ?b ?x0,
        IHA : forall b1, v < ?s -> b1 <= ?s -> dav v b1 ?b0 -> nf_fresh _ ?A |- nf_fresh _ ?A =>
          apply (IHA b); [ lia | lia | eapply (proj1 (eval_av Θ Ξ v b)); [ exact e | exact Hρ | exact I ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?B ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?b0, ea : $| ?x0 & ⇑! ?b0 ?s | _ ⍮ _ ↘ ?r,
        Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hu : forall x, In x ?ups -> dav v ?b x, Hx : dav v ?b ?x0,
        IHV : forall b1, v < S ?s -> b1 <= S ?s -> env_av v b1 None (?ρ ↦ ⇑! ?b0 ?s) -> (forall a, In a ?ups -> _) ->
              dav v b1 ?r -> nf_fresh _ ?V |- nf_fresh _ ?V =>
          let Hb0 := fresh "Hb0" in
          assert (Hb0 : dav v b b0) by (eapply (proj1 (eval_av Θ Ξ v b)); [ exact e | exact Hρ | exact I ]);
          try replace (S (s - v - 1)) with (S s - v - 1) by lia;
          apply (IHV (S s));
            [ lia | lia
            | apply env_av_cons_none; [ eapply env_av_mono; [| exact Hρ ]; lia | eapply dav_fresh_var; eassumption ]
            | intros; eapply dav_mono'; [| apply Hu; eassumption ]; lia
            | eapply app_av; [ exact ea | eapply dav_mono'; [| exact Hx ]; lia | eapply dav_fresh_var; eassumption ] ]
      end ].
    all: try solve [ match goal with
      | Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s,
        Hv : forall x, In x (_ :: ?vs) -> dav v ?b x,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None ?ρ -> _ -> (forall x, In x ?vs -> _) -> all_list (nf_fresh _) ?W
        |- all_list (nf_fresh _) ?W =>
          apply (IH b); [ lia | lia | exact Hρ | assumption | exact (all_in_tail _ _ _ Hv) ]
      end ].
    (** A stuck eliminator: the container's uniform parameters read at
        their telescope; the blocks at the eliminator's uniform
        parameters. *)
    all: try solve [ match goal with
      | em : eval_mref _ _ _ ?ups _ (_, _, ?pre),
        Hu : forall a, In a ?ups -> dav v ?b a, Hb : ?b <= ?s,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None nil -> _ -> all_list (nf_fresh _) ?Ps |- all_list (nf_fresh _) ?Ps =>
          apply (IH b); [ lia | lia | apply env_av_nil | exact (mref_av _ _ _ _ _ _ _ _ em Hu) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_av v b0 K0 ?ρ -> blocks_ofresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_nm_at D0 None ?Bks -> (forall a, In a ?ups -> _) -> all_list _ ?W,
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks,
        Hb : ?b <= ?s, Hρ : forall x, ?K <> Some x -> deav v ?b (env_entry ?ρ x), HBk : blocks_ofresh ?K ?Bks,
        Hu : forall a, In a ?ups -> dav v ?b a |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm | exact Hu ]
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
        IH : forall b0, _ -> _ -> dav v b0 ?a -> nf_fresh _ ?A',
        Hb : ?b <= ?s, Hρ : env_av v ?b ?K ?ρ, HBk : blocks_ofresh ?K ?Bks,
        HX : forall x, In x ?X -> dav v ?b x |- nf_fresh (S (im_nn ?Mi) + _) ?A' =>
          let Hnn := fresh "Hnn" in
          assert (Hnn : im_nn Mv = im_nn Mi) by (pose proof (Hnm _ _ _ HMv Hnth) as Hx; cbn [elim_src] in Hx; congruence);
          replace (S (im_nn Mi) + (s - v - 1)) with (S (s + im_nn Mi) - v - 1) by lia;
          apply (IH (S (s + im_nn Mi))); [ lia | lia |];
          rewrite <- Hnn in e2 |- *;
          eapply motive_av; [ exact f | exact e2 | assumption | exact Hb | exact Hρ
                            | rewrite Hnn, <- Hnmb; exact (proj1 (HBk _ (List.nth_error_In _ _ Hnth))) | exact HX
                            | exact (mref_av _ _ _ _ _ _ _ _ em HX) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_av v b0 K0 ?ρ -> blocks_ofresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_nm_at D0 None ?Bks -> im_nn ?Mv = im_nn ?Mi -> _ -> _ -> _ -> _ ->
               all_list _ ?W,
        Hnth : List.nth_error ?Bks ?ix = Some ?bk, Hnmb : eb_nm ?bk = S (im_nn ?Mi), HMv : ind_member ?D ?ix = Some ?Mv,
        em : eval_mref _ _ _ ?X _ (_, _, ?pre),
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks,
        Hb : ?b <= ?s, Hρ : env_av v ?b ?K ?ρ, HBk : blocks_ofresh ?K ?Bks,
        HX : forall x, In x ?X -> dav v ?b x |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm
                            | pose proof (Hnm _ _ _ HMv Hnth) as Hx; cbn [elim_src] in Hx; congruence
                            | rewrite <- Hnmb; exact (proj1 (HBk _ (List.nth_error_In _ _ Hnth)))
                            | exact (proj2 (HBk _ (List.nth_error_In _ _ Hnth))) | exact HX
                            | exact (mref_av _ _ _ _ _ _ _ _ em HX) ]
      end ].
    all: try solve [ match goal with
      | IH : forall b0 K0 D0, v < ?s -> b0 <= ?s -> env_av v b0 K0 ?ρ -> blocks_ofresh K0 ?Bks ->
               ind_lookup _ _ ?p = Some D0 -> blocks_nm_at D0 None ?Bks -> (forall a, In a ?X -> _) -> all_list _ ?W,
        Hl : ind_lookup _ _ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks,
        Hb : ?b <= ?s, Hρ : env_av v ?b ?K ?ρ, HBk : blocks_ofresh ?K ?Bks,
        HX : forall x, In x ?X -> dav v ?b x |- all_list _ ?W =>
          apply (IH b K D); [ lia | lia | exact Hρ | exact HBk | exact Hl | exact Hnm | exact HX ]
      end ].
    (** A branch: under the fresh non-uniform parameters, arguments and
        recursive results, as many as it binds. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (env_args nil ?X) _ ?s ?ns,
        f0 : fresh_cargs _ _ _ _ _ ?gs _ ?vs,
        f2 : fresh_ihs _ _ ?ρ _ _ ?gs' ?gs ?vs _ ?ihs,
        fw : wrap_ihs_eval _ _ ?ρ _ _ _ ?gs' ?gs ?vs ?ihs ?wihs,
        e0 : ⟦ ?B ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ ?vs ++ ?wihs) ↘ ?bv,
        e1 : ⟦ ?A ⟧ _ ⍮ _ ⍮ env_args ?ρ (?ns ++ _) ↘ ?t,
        Hn0 : ?n0 = _, Hn : ?n = _, Hnn : im_nn _ = im_nn ?Mi,
        Hpl : cargs_plen ?D0 ?gs, Hnm : blocks_nm_at ?D0 None ?Bks,
        IH : forall b0, _ -> _ -> dav_nf v b0 (⇓ ?t ?bv) -> nf_fresh _ ?B',
        Hb : ?b <= ?s, Hρ : env_av v ?b ?K ?ρ, HBk : blocks_ofresh ?K ?Bks,
        HA : ofresh (oshift (S (im_nn ?Mi)) ?K) ?A,
        HB : forall c0 n0 B0, In (c0, n0, B0) (_ :: _) -> ofresh (oshift n0 ?K) B0,
        HX : forall x, In x ?X -> dav v ?b x, Hp : forall x, In x ?pre -> dav v ?b x |- nf_fresh (?n + _) ?B' =>
          let Hbr := fresh "Hbr" in
          pose proof (branch_av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b f f0 f2 fw e0 e1 Hn0 Hnn Hpl Hnm
                        ltac:(assumption) Hb Hρ HBk HX HA (HB _ _ _ (or_introl eq_refl)) HX Hp) as Hbr;
          rewrite <- Hn in Hbr;
          replace (n + (s - v - 1)) with (s + n - v - 1) by lia;
          apply (IH (s + n)); [ lia | lia | constructor; apply Hbr ]
      end ].
    all: try solve [ match goal with
      | IH : context [ all_list _ ?W ], HB : forall c0 n0 B0, In (c0, n0, B0) (_ :: _) -> _ |- all_list _ ?W =>
          eapply IH;
            [ lia | | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
            | intros c1 n1 B1 Hin; exact (HB c1 n1 B1 (or_intror Hin)) | eassumption | eassumption ];
          lia
      end ].
    (** Records: the fields of a tuple read in the environment of the
        parameters; each field projected, at its type evaluated in the
        environment of the fields before it. *)
    all: try solve [ match goal with
      | IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None (env_args nil ?ns) -> dav v b0 ?d -> all_list (nf_fresh _) ?W,
        Hb : ?b <= ?s, Hn : forall a, In a ?ns -> dav v ?b a, Hd : dav v ?b ?d |- all_list (nf_fresh _) ?W =>
          apply (IH b); [ lia | lia | apply env_av_args_none; [ apply env_av_nil | exact Hn ] | exact Hd ]
      end ].
    all: try solve [ match goal with
      | e : eval_proj _ _ _ ?d ?r, e0 : ⟦ ?T ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?t, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s, Hd : dav v ?b ?d,
        IH : forall b0, v < ?s -> b0 <= ?s -> dav_nf v b0 (⇓ ?t ?r) -> nf_fresh _ ?W |- nf_fresh _ ?W =>
          apply (IH b);
            [ lia | lia
            | constructor; [ eapply (proj1 (eval_av Θ Ξ v b)); [ exact e0 | exact Hρ | exact I ] | exact (proj_av _ _ _ _ _ _ _ e Hd) ] ]
      end ].
    all: try solve [ match goal with
      | e : eval_proj _ _ _ ?d ?r, Hρ : env_av v ?b None ?ρ, Hb : ?b <= ?s, Hd : dav v ?b ?d,
        IH : forall b0, v < ?s -> b0 <= ?s -> env_av v b0 None (?ρ ↦ ?r) -> dav v b0 ?d -> all_list (nf_fresh _) ?W |- all_list (nf_fresh _) ?W =>
          apply (IH b); [ lia | lia | apply env_av_cons_none; [ exact Hρ | exact (proj_av _ _ _ _ _ _ _ e Hd) ] | exact Hd ]
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
    all: dav_tac v.
  Qed.
End Read.

(** ** The Initial Environment, and the Corollary *)

(** The initial environment of a context mentions only the levels below its
    length. *)
Lemma initial_env_av : forall Θ Ξ Γ ρ,
    initial_env Θ Ξ Γ ρ ->
    forall v b, List.length Γ <= v -> List.length Γ <= b -> env_av v b None ρ.
Proof.
  induction 1; intros v' b' Hv Hb; cbn [List.length] in *.
  - apply env_av_nil.
  - change None with (oshift 1 None).
    apply env_av_cons; [ apply IHinitial_env; lia |].
    constructor; constructor;
      [ eapply (proj1 (eval_av Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ]
      | constructor; lia ].
  - change None with (oshift 1 None).
    apply env_av_cons; [ apply IHinitial_env; lia |].
    constructor; eapply (proj1 (eval_av Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ].
  - change None with (oshift 1 None).
    apply env_av_cons; [ apply IHinitial_env; lia |].
    constructor; eapply (proj1 (proj2 (proj2 (proj2 (proj2 (eval_av Θ Ξ v' b')))))); [ eassumption | apply IHinitial_env; lia | exact I ].
  - change None with (oshift 1 None).
    apply env_av_cons; [ apply IHinitial_env; lia |].
    constructor;
      [ eapply (proj1 (eval_av Θ Ξ v' b')); [ eassumption | apply IHinitial_env; lia | exact I ]
      | eapply (proj1 (proj2 (proj2 (proj2 (proj2 (eval_av Θ Ξ v' b')))))); [ eassumption | apply IHinitial_env; lia | exact I ] ].
Qed.

(** The environment of [Γ ▹ A] avoids the new variable everywhere except at
    its own position. *)
Lemma initial_env_wk_av : forall Θ Ξ Γ A ρ,
    initial_env Θ Ξ (Γ ▹ A) ρ ->
    env_av (List.length Γ) (S (List.length Γ)) (Some 0) ρ.
Proof.
  intros * Hρ; inversion_clear Hρ.
  apply env_av_cons_bad; eapply initial_env_av; [ eassumption | lia | lia ].
Qed.

(** NbE invents no variables: a weakened term, normalized in the extended
    context at its weakened type, has a normal form fresh at the new
    variable. *)
Theorem nbe_wk_fresh : forall Θ Ξ Γ A M T W,
    nbe Θ Ξ (Γ ▹ A) M[↑]ʷ T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * Hn; inversion_clear Hn as [? ? ? Hρ].
  pose proof (initial_env_wk_av _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  eapply (proj1 (read_av Θ Ξ (List.length Γ))); [ eassumption | cbn; lia | cbn; reflexivity |].
  constructor; eapply (proj1 (eval_av Θ Ξ _ _)); (eassumption || apply exp_shift_fresh).
Qed.

(** The same for the normal form of a weakened type. *)
Theorem nbe_ty_wk_fresh : forall Θ Ξ Γ A T W,
    nbe_ty Θ Ξ (Γ ▹ A) T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * Hn; inversion_clear Hn as [? ? Hρ].
  pose proof (initial_env_wk_av _ _ _ _ _ Hρ).
  replace 0 with (S (List.length Γ) - List.length Γ - 1) by lia.
  eapply (proj1 (proj2 (proj2 (read_av Θ Ξ (List.length Γ))))); [ eassumption | cbn; lia | cbn; reflexivity |].
  eapply (proj1 (eval_av Θ Ξ _ _)); (eassumption || apply exp_shift_fresh).
Qed.
