(** * The Rules with the Redundant Premises Removed

    Every rule carries the premises a presupposition-free formulation
    needs: the [Π]-rules check the domain and the codomain, the
    [⊥]-eliminator checks its type, the congruence rules check the left-hand
    side.  A premise that tells a universe from [Prop] stays: the codomain
    of a [λ] at a [Π] is premised to be of a universe.  Once presupposition
    is available all of those are consequences of the
    remaining premises, and this file restates each rule without them.  The
    primed version is registered as a hint and the rule itself is unregistered,
    so [mauto] searches the small statement and never rediscovers a premise it
    could have presupposed.

    [gen_presups] does all the work; [impl_opt_constructor] is the whole proof of
    most of them.  Where more is needed it is always the same two things: a level
    at which the domain and the codomain of a [Π]-type are both types
    ([lift_exp_pi_common], or [wf_pi_inversion'] when the [Π]-type is already
    known to be one), and cumulativity.

    The rewriting morphisms come first.  Together with [wf_exp_eq_morphism_iff1]
    and [wf_exp_eq_morphism_iff2] from [Definitions] they let [rewrite] replace a
    term by an equal one anywhere in a judgment, including in the type.

    Equations such as [(Π A B)[σ] = Π A[σ] B[q σ]] are not rules but
    equalities of [exp], proved in [Core.Syntactic.Substitution] and used by
    [rewrite] or [simpl_sub], so they need no optimized form.  Neither does
    context equality, which is [Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ] in both directions. *)

From Stdlib Require Import Lia Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CoreInversions.
Import Syntax_Notations Wk_Notations.

(** ** Rewriting the Type of a Judgment *)

Add Parametric Morphism i Θ Ξ Γ : (wf_exp Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ Typeω@i ==> eq ==> iff as wf_exp_morphism_iff3.
Proof.
  intros A A' HAA M; split; intros HM.
  - eapply wf_conv; [ exact HM | exact (presup_exp_eq_right HAA) | exact HAA ].
  - eapply wf_conv; [ exact HM | exact (presup_exp_eq_left HAA) | apply wf_exp_eq_sym; exact HAA ].
Qed.

Add Parametric Morphism i Θ Ξ Γ : (wf_exp_eq Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ Typeω@i ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof.
  split; intros; gen_presups; mautosolve.
Qed.

Add Parametric Morphism Θ Ξ Γ i : (wf_subtyp Θ Ξ Γ)
    with signature (wf_exp_eq Θ Ξ Γ Typeω@i) ==> eq ==> iff as wf_subtyp_morphism_iff1.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 4.
Qed.

Add Parametric Morphism Θ Ξ Γ j : (wf_subtyp Θ Ξ Γ)
    with signature eq ==> (wf_exp_eq Θ Ξ Γ Typeω@j) ==> iff as wf_subtyp_morphism_iff2.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 3.
Qed.

(** ** The Optimized Rules *)

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.

Corollary wf_subtyp_refl' : forall Θ Ξ Γ M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_refl' : mctt.
#[export]
Remove Hints wf_subtyp_refl : mctt.

Corollary wf_conv' : forall Θ Ξ Γ M A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv' : mctt.
#[export]
Remove Hints wf_conv : mctt.

Corollary wf_exp_eq_conv' : forall Θ Ξ Γ M M' A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv' : mctt.
#[export]
Remove Hints wf_exp_eq_conv : mctt.

(** [Prop] is in every small universe. *)
Corollary wf_prop_small : forall Θ Ξ Γ o,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ : Type⟨𝕃ᵒ o⟩.
Proof. intros; eapply (lift_exp_universe_index _ _ _ _ (us ordinal_zero) (us o)); [ cbn; ordinal_solve | apply wf_prop; assumption ]. Qed.

Corollary wf_univ' : forall Θ Ξ Γ o o',
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ordinal_lt o o' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ : Type⟨𝕃ᵒ o'⟩.
Proof.
  intros * ? Hlt; destruct o as [a b].
  eapply (lift_exp_universe_index _ _ _ _ (us (a, S b)) (us o')); [ cbn; ordinal_solve | apply wf_univ_lit; assumption ].
Qed.

Corollary wf_exp_eq_prop_cong_small : forall Θ Ξ Γ o,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ ≈ Propₘ : Type⟨𝕃ᵒ o⟩.
Proof. intros; eapply (lift_exp_eq_universe_index _ _ _ _ _ (us ordinal_zero) (us o)); [ cbn; ordinal_solve | apply wf_exp_eq_prop_cong; assumption ]. Qed.

Corollary wf_exp_eq_univ_cong_small : forall Θ Ξ Γ o o',
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ordinal_lt o o' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ ≈ Type⟨𝕃ᵒ o⟩ : Type⟨𝕃ᵒ o'⟩.
Proof.
  intros * ? Hlt; destruct o as [a b].
  eapply (lift_exp_eq_universe_index _ _ _ _ _ (us (a, S b)) (us o'));
    [ cbn; ordinal_solve | apply wf_exp_eq_univ_cong_lit; assumption ].
Qed.

(** As hints these are guarded on the goal's universe being a small one, and
    fix an open level to [0], exactly as the large forms are: an unguarded
    [Hint Resolve] would make every search in the database try to solve an
    arithmetic side condition. *)
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Propₘ : Type⟨𝕃ᵒ ?n⟩) =>
  fix_open_level n; (apply wf_prop_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Propₘ ≈ Propₘ : Type⟨𝕃ᵒ ?n⟩) =>
  fix_open_level n; (apply wf_exp_eq_prop_cong_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ : Type⟨𝕃ᵒ ?m⟩) =>
  fix_open_level m; (apply wf_univ'; [ assumption | ordinal_solve ]) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ ≈ Type⟨𝕃ᵒ _⟩ : Type⟨𝕃ᵒ ?m⟩) =>
  fix_open_level m; (apply wf_exp_eq_univ_cong_small; [ assumption | ordinal_solve ]) : mctt.

(** [Prop] is a type at every level, not only at [0]. *)
Corollary wf_prop' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ : Typeω@i.
Proof.
  intros; eapply lift_exp_ge; [ | apply wf_prop_large; assumption ]; lia.
Qed.

#[export]
Hint Resolve wf_prop' : mctt.

Corollary wf_exp_eq_prop_cong' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ ≈ Propₘ : Typeω@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | apply wf_exp_eq_refl, wf_prop_large; assumption ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_prop_cong' : mctt.

(** A λ-abstraction at the kinds [pi_kinds κd κc]: its codomain is
    premised to be of the sort of [κc], a function into a type of a
    universe, a proof of a [∀] or a function between levels; the domain's
    sort is read off the context. *)
Corollary wf_fn_at' : forall Θ Ξ Γ κd κc A B M i,
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ M : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : a_pi κd κc A B.
Proof.
  intros * HB Hk HM; destruct (proj2 (ctx_decomp_sort_kind (presup_exp_ctx HB))) as (S & HS & HA).
  eapply wf_fn; [ exact HA | exact HS | exact HB | exact Hk | exact HM ].
Qed.

(** A function, over a domain of any kind. *)
Corollary wf_fn' : forall Θ Ξ Γ κd A B M i,
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ M : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : Π{κd} A B.
Proof. intros * HB HM; exact (wf_fn_at' _ _ _ _ ak_relevant _ _ _ _ HB (pi_kinds_relevant _) HM). Qed.

(** A proof of a [∀], over a domain of any kind. *)
Corollary wf_fn_all' : forall Θ Ξ Γ κd A P M,
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ P : Propₘ ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ M : P ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : ∀ₚ{κd} A P.
Proof. intros * HP HM; exact (wf_fn_at' _ _ _ _ ak_propositional _ _ _ 0 HP (pi_kinds_prop _) HM). Qed.

#[export]
Hint Resolve wf_fn_all' : mctt.

#[export]
Hint Resolve wf_fn' : mctt.
#[export]
Remove Hints wf_fn : mctt.

(** The parts of a [Π] at the kinds [κd κc]: the premises [wf_fn] and
    [wf_app] ask of its domain and codomain. *)
#[warnings="-cannot-define-projection"]
Record pi_parts (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (κd κc : abs_kind) (A B : typ) : Prop := mk_pi_parts
  { (** The sort of the domain *)
    pi_parts_domain_sort : exp
    (** The level of the universe the codomain's sort is next to *)
  ; pi_parts_codomain_level : nat
    (** The domain's sort is a sort of its kind *)
  ; pi_parts_domain_sort_kind : sort_kind pi_parts_domain_sort κd
    (** The domain is of it *)
  ; pi_parts_domain : Θ ⍮ Ξ ⍮ Γ ⊢ A : pi_parts_domain_sort
    (** The codomain is of the sort of its kind *)
  ; pi_parts_codomain : Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@pi_parts_codomain_level
    (** The kinds are those of a [Π] *)
  ; pi_parts_kinds : pi_kinds κd κc }.

(** The parts of a [Π] at the kinds [κd κc] typed at anything.  Whenever a
    [Π]-type is the type of a term this recovers the premises the
    elimination and introduction rules want. *)
Lemma wf_pi_parts_at : forall Θ Ξ Γ κd κc A B C,
    Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κd κc A B : C ->
    pi_parts Θ Ξ Γ κd κc A B.
Proof.
  intros * H; destruct (wf_pi_inversion_at H) as [U HU HA HB Hk _].
  destruct (pi_domain_eq_sort HU HA HA ltac:(apply wf_exp_eq_refl; exact HA)) as (S & HS & HA' & _ & _).
  enough (exists i, Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i) as [i HBi]
    by exact (mk_pi_parts _ _ _ _ _ _ _ S i HS HA' HBi Hk).
  assert (HΓA : ⊢ Θ ⍮ Ξ ⍮ Γ ▹{κd} A) by (eapply wf_ctx_extend; eassumption).
  rewrite abs_kind_sort_wk in HB.
  destruct κc; cbn [abs_kind_sort] in HB |- *; [| exists 0; exact HB | exists 0; exact HB ].
  inversion HU; subst; cbn [exp_wk] in HB; [ eexists; eassumption |].
  assert (Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ʷ ↑ : Γ) by mauto 2.
  match goal with HL : _ ⍮ _ ⍮ _ ⊢ ?L : Level@?n |- _ =>
    assert (Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ (Level@n)); eassumption) end.
  exists 0; eapply wf_exp_suniv_large; eassumption.
Qed.

(** An application at the kinds of the [Π] applied. *)
Corollary wf_app_at' : forall Θ Ξ Γ κd κc A B M N,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : a_pi κd κc A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : B[Id,,N].
Proof.
  intros * HM HN.
  destruct (presup_exp_typ HM) as [S HS HΠ].
  destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HΠ) as [S' i HS' HA HB Hk].
  eapply wf_app; [ exact HA | exact HS' | exact HB | exact Hk | exact HM | exact HN ].
Qed.

Corollary wf_app' : forall Θ Ξ Γ κd A B M N,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Π{κd} A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : B[Id,,N].
Proof. intros; eapply wf_app_at'; eassumption. Qed.

#[export]
Hint Resolve wf_app_at' : mctt.

#[export]
Hint Resolve wf_app' : mctt.
#[export]
Remove Hints wf_app : mctt.

Corollary wf_exp_eq_absurd_cong' : forall Θ Ξ Γ C C' Srt M M',
    Θ ⍮ Ξ ⍮ Γ ⊢ C ≈ C' : Srt ->
    type_sort Srt ->
    level_closed_sort Propₘ Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : ⊥ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ efq M return C ≈ efq M' return C' : C.
Proof.
  intros * HC HS Hl HM HM'; eapply wf_exp_eq_absurd_cong; [ exact (presup_exp_eq_left HC) | exact HS | exact Hl | exact HC | exact HM | exact HM' ].
Qed.

#[export]
Hint Resolve wf_exp_eq_absurd_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_absurd_cong : mctt.

Corollary wf_exp_eq_pi_cong_large' : forall Θ Ξ Γ A A' B B' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ B ≈ B' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{ak_relevant} A B ≈ Π{ak_relevant} A' B' : Typeω@i.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_large' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_cong_large : mctt.

(** The domain and the codomain rarely arrive at the same level; this is the
    congruence that takes them as they come, and the counterpart of
    [wf_pi_max]. *)
Corollary wf_exp_eq_pi_cong_max : forall Θ Ξ Γ A A' B B' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ B ≈ B' : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{ak_relevant} A B ≈ Π{ak_relevant} A' B' : Typeω@(max i j).
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(max i j)) by eauto using lift_exp_eq_max_left.
  assert (Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ B ≈ B' : Typeω@(max i j)) by eauto using lift_exp_eq_max_right.
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mctt.

(** The codomain is premised to be of the sort of its kind, as for
    [wf_fn_at']. *)
Corollary wf_exp_eq_fn_cong' : forall Θ Ξ Γ κd κc A A' B M M' Srt j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt ->
    sort_kind Srt κd ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@j ->
    pi_kinds κd κc ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ M ≈ M' : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M ≈ λ A' M' : a_pi κd κc A B.
Proof.
  intros * HA HS HB Hk HM; eapply wf_exp_eq_fn_cong;
    [ exact (presup_exp_eq_left HA) | exact HS | exact HA | exact HB | exact Hk | exact HM ].
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_cong : mctt.

Corollary wf_exp_eq_app_cong' : forall Θ Ξ Γ κd κc A B M M' N N',
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : a_pi κd κc A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N].
Proof.
  intros * HM HN.
  destruct (presup_exp_typ (presup_exp_eq_left HM)) as [S HS HΠ].
  destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HΠ) as [S' i HS' HA HB Hk].
  eapply wf_exp_eq_app_cong; [ exact HA | exact HS' | exact HB | exact Hk | exact HM | exact HN ].
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_app_cong : mctt.

(** The codomain is premised to be of the sort of its kind, as for
    [wf_fn_at']: at a proposition, the two sides are proofs, equal by
    irrelevance. *)
Corollary wf_exp_eq_pi_beta' : forall Θ Ξ Γ κd κc A B M N i,
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ M : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N].
Proof.
  intros * HB Hk HM HN.
  destruct (proj2 (ctx_decomp_sort_kind (presup_exp_ctx HB))) as (S & HS & HA).
  eapply wf_exp_eq_pi_beta; [ exact HA | exact HS | exact HB | exact Hk | exact HM | exact HN ].
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_beta : mctt.

Corollary wf_exp_eq_fn_eta' : forall Θ Ξ Γ κd κc A B M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : a_pi κd κc A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : a_pi κd κc A B.
Proof.
  intros * HM.
  destruct (presup_exp_typ HM) as [S HS HΠ].
  destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HΠ) as [S' i HS' HA HB Hk].
  eapply wf_exp_eq_fn_eta; [ exact HA | exact HS' | exact HB | exact Hk | exact HM ].
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_eta' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_eta : mctt.

(** A let presupposes its context, which carries the typing of its body; the
    sorts of the annotation and of the body's type stay premises, as they are
    related by [level_closed_sort]. *)
Corollary wf_let' : forall Θ Ξ Γ A M B C Srt SrtC,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ C : SrtC ->
    level_closed_sort Srt SrtC ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : C[Id,,M].
Proof.
  intros * HA HS HC Hl HB; gen_presups.
  match goal with H : ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M |- _ => inversion_clear H end.
  eapply wf_let; [ exact HA | exact HS | eassumption | exact HC | exact Hl | exact HB ].
Qed.

#[export]
Hint Resolve wf_let' : mctt.
#[export]
Remove Hints wf_let : mctt.

Corollary wf_ctx_extend_def' : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M.
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_ctx_extend_def' : mctt.
#[export]
Remove Hints wf_ctx_extend_def : mctt.

(** Congruence for a let, with the sort premises of [wf_let']. *)
Corollary wf_exp_eq_let_cong' : forall Θ Ξ Γ A A' M M' B B' C Srt SrtC,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ C : SrtC ->
    level_closed_sort Srt SrtC ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros * HAA HS HMM HC Hl HBB.
  eapply wf_exp_eq_let_cong; [ exact (presup_exp_eq_left HAA) | exact HS | exact HAA
                             | exact (presup_exp_eq_left HMM) | exact HMM | exact HC | exact Hl | exact HBB ].
Qed.

#[export]
Hint Resolve wf_exp_eq_let_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_let_cong : mctt.

(** [ζ] for a let, with the sort premises of [wf_let']. *)
Corollary wf_exp_eq_let_zeta' : forall Θ Ξ Γ A M B C Srt SrtC,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ C : SrtC ->
    level_closed_sort Srt SrtC ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M].
Proof.
  intros * HA HS HC Hl HB; gen_presups.
  match goal with H : ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M |- _ => inversion_clear H end.
  eapply wf_exp_eq_let_zeta; [ exact HA | exact HS | eassumption | exact HC | exact Hl | exact HB ].
Qed.

#[export]
Hint Resolve wf_exp_eq_let_zeta' : mctt.
#[export]
Remove Hints wf_exp_eq_let_zeta : mctt.

(** A term equation presupposes that both sides are well-typed, so the
    refinement between two contexts extended by equal types needs nothing else. *)
Corollary wf_sub_id_extend_eq' : forall Θ Ξ Γ κ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹{κ} A' ⊢ˢ Id : Γ ▹{κ} A.
Proof.
  intros * H; pose proof (presup_exp_eq_left H); pose proof (presup_exp_eq_right H).
  eapply wf_sub_id_extend_eq; [ eassumption | eassumption | apply sort_kind_abs_kind_sort | exact H ].
Qed.

#[export]
Hint Resolve wf_sub_id_extend_eq' : mctt.
#[export]
Remove Hints wf_sub_id_extend_eq : mctt.

(** Refinement of [Π]-types needs only the equation between the domains and the
    refinement between the codomains; that the four components are types, and at
    a common level, is presupposition and cumulativity.  The codomain [B] is
    checked in [Γ ▹ A'] by the premise and in [Γ ▹ A] by the rule, and the two
    are related by context conversion along the domain equation. *)
Lemma wf_subtyp_pi' : forall Θ Ξ Γ κd A A' B B' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κd Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ⊢ B' : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ⊢ B ⊆ B' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{κd} A B ⊆ Π{κd} A' B'.
Proof.
  intros * HAA HB HB' Hsub.
  pose proof (presup_exp_eq_left HAA) as HA; pose proof (presup_exp_eq_right HAA) as HA'.
  assert (HI : Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ˢ Id : Γ ▹{κd} A')
    by (eapply wf_sub_id_extend_eq; [ exact HA' | exact HA | apply sort_kind_abs_kind_sort | apply wf_exp_eq_sym; exact HAA ]).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB HI) as HBA; rewrite !exp_sub_id in HBA.
  eapply wf_subtyp_pi with (i := max i j);
    [ eapply lift_rel_max_left; exact HA | eapply lift_rel_max_left; exact HA'
    | eapply lift_rel_eq_max_left; exact HAA | eapply lift_exp_max_right; exact HBA
    | eapply lift_exp_max_right; exact HB' | exact Hsub | constructor | constructor ].
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mctt.
#[export]
Remove Hints wf_subtyp_pi : mctt.

(** Conversion along an equation in any universe, large or small: the gluing
    model states every type equation in the ambient universe of its index. *)
Corollary wf_conv_univ : forall Θ Ξ Γ M A A' u,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  intros * HM HA.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(large_level u))
    by (eapply (lift_exp_eq_universe_index _ _ _ _ _ u (large_level u)); [ apply universe_index_le_large_level | exact HA ]).
  eapply wf_exp_subtyp'; [ exact HM | mauto 3 ].
Qed.

Corollary wf_exp_eq_conv_univ : forall Θ Ξ Γ M M' A A' u,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  intros * HM HA.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(large_level u))
    by (eapply (lift_exp_eq_universe_index _ _ _ _ _ u (large_level u)); [ apply universe_index_le_large_level | exact HA ]).
  eapply wf_exp_eq_subtyp'; [ exact HM | mauto 3 ].
Qed.

#[export]
Hint Resolve wf_conv_univ wf_exp_eq_conv_univ : mctt.

(** [Π] and its congruence in any universe, large or small: the two rules
    [wf_pi_large]/[wf_pi_lvl] and [wf_exp_eq_pi_cong_large]/[wf_exp_eq_pi_cong_lvl]
    as one statement over the index. *)
Corollary wf_pi_univ : forall Θ Ξ Γ A B u,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ B : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{ak_relevant} A B : universe_index_term u.
Proof.
  intros * HA HB; destruct u; cbn in *; [ apply wf_pi_small_lit | apply wf_pi_large ]; assumption.
Qed.

(** The principal universe of a [Π] is the join of those of its parts. *)
Corollary wf_pi_universe_index_max : forall Θ Ξ Γ A B u v,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ B : universe_index_term v ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{ak_relevant} A B : universe_index_term (universe_index_max u v).
Proof.
  intros * HA HB; apply wf_pi_univ;
    [ eapply (lift_exp_universe_index _ _ _ _ u); [ apply universe_index_le_universe_index_max_left | exact HA ]
    | eapply (lift_exp_universe_index _ _ _ _ v); [ apply universe_index_le_universe_index_max_right | exact HB ] ].
Qed.

Corollary wf_exp_eq_pi_cong_univ : forall Θ Ξ Γ A A' B B' u,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ B ≈ B' : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{ak_relevant} A B ≈ Π{ak_relevant} A' B' : universe_index_term u.
Proof.
  intros * HA HB; destruct u; cbn in *;
    [ apply wf_exp_eq_pi_cong_small_lit; [ gen_presups; eassumption | assumption | assumption ]
    | apply wf_exp_eq_pi_cong_large'; assumption ].
Qed.

#[export]
Hint Resolve wf_pi_univ wf_pi_universe_index_max wf_exp_eq_pi_cong_univ : mctt.

(** The [λ] congruence with the domain equation in any universe. *)
Corollary wf_exp_eq_fn_cong_univ : forall Θ Ξ Γ A A' B M M' u j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : universe_index_term u ->
    Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ▹{ak_relevant} A ⊢ M ≈ M' : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π{ak_relevant} A B.
Proof.
  intros * HA HB HM.
  eapply wf_exp_eq_fn_cong'; [| apply sort_kind_universe | exact HB | constructor | exact HM ].
  eapply (lift_exp_eq_universe_index _ _ _ _ _ u (large_level u)); [ apply universe_index_le_large_level | exact HA ].
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong_univ : mctt.

(** The same keyed on an equation in any universe, large or small: the gluing
    model rewrites types along equations in the ambient universe of its
    index. *)
Add Parametric Morphism u Θ Ξ Γ : (wf_exp Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ (universe_index_term u) ==> eq ==> iff as wf_exp_morphism_iff_univ.
Proof.
  split; intros; eapply wf_conv_univ; [ eassumption | eassumption | eassumption | symmetry; eassumption ].
Qed.

Add Parametric Morphism u Θ Ξ Γ : (wf_exp_eq Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ (universe_index_term u) ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff_univ.
Proof.
  split; intros; eapply wf_exp_eq_conv_univ; [ eassumption | eassumption | eassumption | symmetry; eassumption ].
Qed.

(** An equation in any universe lifts to the large level the index lives at,
    which is where [wf_subtyp_refl] takes it. *)
#[local] Ltac subtyp_univ_step HAA' :=
  let H := fresh "H" in
  pose proof (lift_exp_eq_universe_index _ _ _ _ _ _ _ (universe_index_le_large_level _) HAA') as H;
  eapply wf_subtyp_refl; cycle 2;
    [ first [ exact H | symmetry; exact H ] | gen_presups; eassumption | cbn; constructor ].

Add Parametric Morphism u Θ Ξ Γ : (wf_subtyp Θ Ξ Γ)
    with signature (wf_exp_eq Θ Ξ Γ (universe_index_term u)) ==> eq ==> iff as wf_subtyp_morphism_iff1_univ.
Proof.
  intros A A' HAA' B; split; intros Hsub;
    ((etransitivity; [ idtac | exact Hsub ]) || (etransitivity; [ exact Hsub | idtac ]));
    subtyp_univ_step HAA'.
Qed.

Add Parametric Morphism u Θ Ξ Γ : (wf_subtyp Θ Ξ Γ)
    with signature eq ==> (wf_exp_eq Θ Ξ Γ (universe_index_term u)) ==> iff as wf_subtyp_morphism_iff2_univ.
Proof.
  intros A B B' HBB'; split; intros Hsub;
    (etransitivity; [ exact Hsub | idtac ]);
    subtyp_univ_step HBB'.
Qed.

