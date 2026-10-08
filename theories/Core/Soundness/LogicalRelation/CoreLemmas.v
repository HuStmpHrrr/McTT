From Stdlib Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Corollaries Substitution.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From Mctt.Core.Soundness.Weakening Require Export Lemmas.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma glu_nat_per_nat : forall Γ M a,
    glu_nat Γ M a ->
    Dom a ≈ a ∈ per_nat.
Proof.
  induction 1; mauto.
Qed.

#[local]
Hint Resolve glu_nat_per_nat : mctt.

Lemma glu_nat_escape : forall Γ M a,
    glu_nat Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : ℕ.
Proof.
  induction 1; intros;
    try match goal with
    | H : _ |- _ => solve [gen_presup H; mauto]
    end.
  assert (Γ ⊢k wk_id : Γ) by mauto 2.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert (Γ ⊢ M[wk_id]ʷ ≈ M' : ℕ) as HM by mauto.
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve glu_nat_escape : mctt.

(** [glu_nat] is stable under context refinement [Δ ⊆ Γ], which is what the
    [ctxsub_*] lemmas need. The other context-transport lemmas below are stated
    in the same refinement form. *)
Lemma glu_nat_resp_ctxsub : forall Γ M a Δ,
    glu_nat Γ M a ->
    Δ ⊆ Γ ->
    glu_nat Δ M a.
Proof.
  induction 1; intros.
  - mauto 4.
  - assert (Δ ⊢ M ≈ succ M' : ℕ) by mauto 3.
    econstructor; [ eassumption | mauto 2 ].
  - econstructor; trivial.
    intros; mauto 4.
Qed.

Hint Resolve glu_nat_resp_ctxsub : mctt.

Lemma glu_nat_resp_exp_eq : forall Γ M a,
    glu_nat Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : ℕ ->
    glu_nat Γ M' a.
Proof.
  induction 1; intros; mauto 4.
  econstructor; trivial.
  intros.
  transitivity M[φ]ʷ; mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_exp_eq : mctt.

Add Parametric Morphism Γ : (glu_nat Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ ℕ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; mauto using glu_nat_resp_exp_eq.
Qed.

Lemma glu_nat_readback : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ M',
      Δ ⊢k φ : Γ ->
      Rnf ⇓ ℕᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : ℕ.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - rewrite <- (exp_wk_zero φ); mauto 4.
  - assert (Δ ⊢ M'[φ]ʷ ≈ M0 : ℕ) by mauto 4.
    assert (Δ ⊢ M[φ]ʷ ≈ (succ M')[φ]ʷ : ℕ) as H' by mauto 4.
    rewrite exp_wk_succ in H'.
    etransitivity; [ eassumption | mauto 3 ].
  - mauto 4.
Qed.

(** The same lemmas for [glu_lvl], which is the readback clause of a neutral at
    [Level]. *)
Lemma glu_lvl_escape : forall Γ M a,
    Dom a ≈ a ∈ per_lvl ->
    glu_lvl Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : Level.
Proof.
  intros * Hper H HΓ.
  assert (Γ ⊢k wk_id : Γ) by mauto 2.
  apply per_lvl_then_per_top in Hper; specialize (Hper (length Γ)) as [M' []].
  clear_dups.
  assert (Γ ⊢ M[wk_id]ʷ ≈ M' : Level) as HM by mauto.
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve glu_lvl_escape : mctt.

Lemma glu_lvl_resp_ctxsub : forall Γ M a Δ,
    glu_lvl Γ M a ->
    Δ ⊆ Γ ->
    glu_lvl Δ M a.
Proof.
  intros * H ? Δ' φ L **; mauto 4.
Qed.

Hint Resolve glu_lvl_resp_ctxsub : mctt.

Lemma glu_lvl_resp_exp_eq : forall Γ M a,
    glu_lvl Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : Level ->
    glu_lvl Γ M' a.
Proof.
  intros * H * ? Δ φ L **.
  transitivity M[φ]ʷ; mauto 4.
Qed.

#[local]
Hint Resolve glu_lvl_resp_exp_eq : mctt.

(** ** Cumulativity of an Element of a Small Universe

    An element of a small universe is a type of that universe [Type⟨t⟩], and
    its type-level gluing is at the ambient large universe.  These two lemmas
    are where the gluing relies on cumulativity ([wf_subtyp_small_large]):
    they move the element's typing and its equations from [Type⟨t⟩] to every
    large universe. *)
Lemma suniv_elem_large : forall Γ M A t j k,
    Γ ⊢ M : A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    Γ ⊢ M : Typeω@k.
Proof.
  intros * HM HA.
  assert (Γ ⊢ Type⟨t⟩ : Typeω@j) by (gen_presups; eassumption).
  assert (Γ ⊢ t : Level) by (eapply wf_univ_lvl_inversion; eassumption).
  eapply wf_exp_subtyp'; [ eapply wf_conv'; eassumption | apply wf_subtyp_small_large; mauto 3 ].
Qed.

Lemma suniv_elem_eq_large : forall Γ M M' A t j k,
    Γ ⊢ M ≈ M' : A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    Γ ⊢ M ≈ M' : Typeω@k.
Proof.
  intros * HM HA.
  assert (Γ ⊢ Type⟨t⟩ : Typeω@j) by (gen_presups; eassumption).
  assert (Γ ⊢ t : Level) by (eapply wf_univ_lvl_inversion; eassumption).
  eapply wf_exp_eq_subtyp';
    [ eapply wf_exp_eq_conv'; eassumption | apply wf_subtyp_small_large; mauto 3 ].
Qed.

(** A glued small universe is the universe at a level term glued to the level
    value.  As an introduction lemma this is what every proof that moves such
    a type needs: the term is kept and the equation composed, and it is a hint
    so that the shared scripts of the gluing lemmas reach it. *)
Lemma suniv_glu_typ_pred_intro : forall l U Γ A t,
    glu_lvl Γ t l ->
    Γ ⊢ A ≈ Type⟨t⟩ : U ->
    suniv_glu_typ_pred l U Γ A.
Proof. intros; eexists; split; eassumption. Qed.

(** It is deliberately not a hint: its conclusion is an existential whose
    witness the search cannot guess, and as a hint it also fires on the goals
    of the other universe clauses, whose predicate is an evar. *)

Lemma glu_lvl_readback : forall Γ M a,
    glu_lvl Γ M a ->
    forall Δ φ M',
      Δ ⊢k φ : Γ ->
      Rnf ⇓ Levelᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : Level.
Proof.
  intros * H; exact H.
Qed.

(** A literal level is glued to its value: its readback is itself. *)
Lemma glu_lvl_lit : forall Γ n,
    ⊢ Γ ->
    glu_lvl Γ (𝕃ᵒ n) (dlvl_lit n).
Proof.
  intros * HΓ Δ φ L Hφ Hr.
  assert (⊢ Δ) by (eapply kripke_dom; eassumption).
  assert (L = nf_lvl_of (lvl_lit n)) as -> by (eapply functional_read_nf; [ exact Hr | apply read_nf_dlvl_lit ]).
  cbn; mauto 3.
Qed.

(** The same lemmas for [glu_False], which is the neutral case of
    [glu_nat] at [⊥]. *)
Lemma glu_False_per_ne : forall Γ M a,
    glu_False Γ M a ->
    Dom a ≈ a ∈ per_ne.
Proof.
  destruct 1; mauto.
Qed.

#[local]
Hint Resolve glu_False_per_ne : mctt.

Lemma glu_False_escape : forall Γ M a,
    glu_False Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : ⊥.
Proof.
  destruct 1; intros.
  assert (Γ ⊢k wk_id : Γ) by mauto 2.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert (Γ ⊢ M[wk_id]ʷ ≈ M' : ⊥) as HM by mauto.
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve glu_False_escape : mctt.

Lemma glu_False_resp_ctxsub : forall Γ M a Δ,
    glu_False Γ M a ->
    Δ ⊆ Γ ->
    glu_False Δ M a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros; mauto 4.
Qed.

Hint Resolve glu_False_resp_ctxsub : mctt.

Lemma glu_False_resp_exp_eq : forall Γ M a,
    glu_False Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : ⊥ ->
    glu_False Γ M' a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros.
  transitivity M[φ]ʷ; mauto.
Qed.

#[local]
Hint Resolve glu_False_resp_exp_eq : mctt.

Lemma glu_False_readback : forall Γ M a,
    glu_False Γ M a ->
    forall Δ φ M',
      Δ ⊢k φ : Γ ->
      Rnf ⇓ ⊥ᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : ⊥.
Proof.
  destruct 1; intros; progressive_inversion; gen_presups.
  mauto 4.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_lvl_escape glu_lvl_resp_ctxsub : mctt.
(** Unlike [glu_nat], [glu_lvl] has one constructor, so [split] breaks a goal
    [glu_lvl Γ M m] into its premises; the readback clause is then
    [glu_lvl_readback], and it is a hint so that the shared scripts reach it. *)
#[local]
Hint Resolve glu_lvl_resp_exp_eq glu_lvl_readback : mctt.
#[export]
Hint Resolve glu_False_escape glu_False_resp_ctxsub : mctt.
#[local]
Hint Resolve glu_False_per_ne glu_False_resp_exp_eq : mctt.
#[export]
Hint Resolve glu_nat_escape : mctt.
#[export]
Hint Resolve glu_nat_resp_ctxsub : mctt.
#[export] Existing Instance glu_ctx_env_sub_morphism_iff2_Proper.
#[local]
Hint Resolve glu_nat_per_nat glu_nat_resp_exp_eq : mctt.
#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  gen_presups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The large level a glued type is a type of.  It is given as an explicit
    argument, with the equation [ulvl i = l], so that the lemma applies to a
    goal [Γ ⊢ A : Typeω@l] whose level is known before the index is. *)
Lemma glu_univ_elem_univ_lvl_gen : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A : Typeω@(ulvl i).
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel; trivial.
Qed.

Lemma glu_univ_elem_univ_lvl : forall i U P El a,
    Typeω@(ulvl i) = U ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A : U.
Proof. intros * <- **; eapply glu_univ_elem_univ_lvl_gen; eassumption. Qed.

Lemma glu_univ_elem_typ_resp_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A A',
      Γ ⊢ A ® P ->
      Γ ⊢ A ≈ A' : Typeω@(ulvl i) ->
      Γ ⊢ A' ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros; simpl_glu_rel;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ destruct_conjs; eexists; split;
                [ eassumption | transitivity A; mauto 4 ] ];
    mauto 4.

  split; [trivial |].
  intros.
  transitivity A[φ]ʷ; mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (P Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> iff as glu_univ_elem_typ_morphism_iff1.
Proof.
  split; intros; eapply glu_univ_elem_typ_resp_exp_eq; mauto 2.
Qed.

Lemma glu_univ_elem_trm_resp_typ_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m A',
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A ≈ A' : Typeω@(ulvl i) ->
      Γ ⊢ M : A' ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel; repeat split; intros;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ eexists; split; [ eassumption | transitivity A; mauto 4 ] ];
    mauto 3.
  all: try solve [ firstorder ].
  all: try solve [ do 2 eexists; split; eassumption ].
  all: try solve [ eapply wf_conv'; eassumption ].
  all: try solve [ transitivity A[φ]ʷ; mauto 4 ].
  (** The readback clauses of a neutral and of an element of a small universe
      move their type by conversion in the ambient universe. *)
  all: try solve [ assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) by mauto 3;
                   eapply wf_exp_eq_conv'; [ eauto | eassumption ] ].
  (** The [Π] case moves the type the same way. *)
  econstructor; mauto 3; eapply wf_conv'; eassumption.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (El Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> eq ==> eq ==> iff as glu_univ_elem_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_typ_resp_ctxsub : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A Δ,
      Γ ⊢ A ® P ->
      Δ ⊆ Γ ->
      Δ ⊢ A ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel;
    (** A small universe: its level term and its equation both move to the
        refined context. *)
    try solve [ eexists; split;
                [ eapply glu_lvl_resp_ctxsub; eassumption | mauto 3 ] ];
    mauto 3.

  - assert (Δ ⊢ IT : Typeω@(ulvl i)) by mauto 3.
    assert (Δ ▹ IT ⊆ Γ ▹ IT) by (eapply ctx_sub_extend; mauto 3 using wf_subtyp_refl_univ).
    econstructor; mauto 3; intros; mauto 4.

  - split; [ mauto 3 | intros; mauto 4 ].
Qed.

Lemma glu_univ_elem_trm_resp_ctxsub : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m Δ,
      Γ ⊢ M : A ® m ∈ El ->
      Δ ⊆ Γ ->
      Δ ⊢ M : A ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel.
  (** An element of a small universe: its type's level term moves to the
      refined context too. *)
  all: try solve [ repeat apply conj;
                   [ mauto 3
                   | eexists; split; [ eapply glu_lvl_resp_ctxsub; eassumption | mauto 3 ]
                   | do 2 eexists; split;
                     [ eassumption | eapply glu_univ_elem_typ_resp_ctxsub; eassumption ]
                   | intros; mauto 4 ] ].
  all: try solve [ repeat apply conj; [ mauto 3 | mauto 3 | ];
                   do 2 eexists; split; [ eassumption | eapply glu_univ_elem_typ_resp_ctxsub; eassumption ] ].
  all: try solve [ split; mauto 3 ].
  (** A [Π]: the context refinement extends over the domain.  A neutral: its
      readback clause is transported along it. *)
  1:{ assert (Δ ⊢ IT : Typeω@(ulvl i)) by mauto 3.
      assert (Δ ▹ IT ⊆ Γ ▹ IT) by (eapply ctx_sub_extend; mauto 3 using wf_subtyp_refl_univ).
      econstructor; mauto 3; intros; mauto 4. }
  1:{ econstructor; [ split | | | ]; mauto 3; intros; mauto 4. }
Qed.

Lemma glu_nat_resp_wk' : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ,
      Γ ⊢ M : ℕ ->
      Δ ⊢k φ : Γ ->
      glu_nat Δ M[φ]ʷ a.
Proof.
  induction 1; intros; gen_presups.
  - econstructor.
    rewrite <- (exp_wk_zero φ); mauto 4.
  - econstructor; [ |mauto].
    rewrite <- (exp_wk_succ φ); mauto 4.
  - econstructor; trivial.
    intros Δ' ψ M' **.
    rewrite exp_wk_wk.
    assert (Δ' ⊢k φ ⊙ ψ : Γ) by mauto 3.
    mauto 4.
Qed.

Lemma glu_nat_resp_wk : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ,
      Δ ⊢k φ : Γ ->
      glu_nat Δ M[φ]ʷ a.
Proof.
  intros * ? * ?.
  assert (⊢ Γ) by (eapply kripke_cod; eassumption).
  mauto using glu_nat_resp_wk'.
Qed.

Hint Resolve glu_nat_resp_wk : mctt.

Lemma glu_lvl_resp_wk : forall Γ M a,
    glu_lvl Γ M a ->
    forall Δ φ,
      Δ ⊢k φ : Γ ->
      glu_lvl Δ M[φ]ʷ a.
Proof.
  intros * H * ? Δ' ψ M' **.
  rewrite exp_wk_wk.
  assert (Δ' ⊢k φ ⊙ ψ : Γ) by mauto 3.
  mauto 4.
Qed.

Hint Resolve glu_lvl_resp_wk : mctt.

Lemma glu_False_resp_wk : forall Γ M a,
    glu_False Γ M a ->
    forall Δ φ,
      Δ ⊢k φ : Γ ->
      glu_False Δ M[φ]ʷ a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros Δ' ψ M' **.
  rewrite exp_wk_wk.
  assert (Δ' ⊢k φ ⊙ ψ : Γ) by mauto 3.
  mauto 4.
Qed.

Hint Resolve glu_False_resp_wk : mctt.

Lemma glu_univ_elem_trm_escape : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M : A.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel; mauto 4.
Qed.

Lemma glu_univ_elem_per_univ : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Dom a ≈ a ∈ per_univ i.
Proof.
  simpl.
  glu_univ_elem_induction1; intros; eexists;
    try solve [per_univ_elem_econstructor; try reflexivity; trivial].

  - subst. eapply per_univ_elem_core_univ'; trivial.
    reflexivity.
  - eapply per_univ_elem_core_suniv'; trivial.
    reflexivity.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    mauto.
Qed.

Hint Resolve glu_univ_elem_per_univ : mctt.

Lemma glu_univ_elem_per_elem : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m R,
      Γ ⊢ M : A ® m ∈ El ->
      DF a ≈ a ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m ∈ R.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H);
    simpl_glu_rel;
    try fold (per_univ j m m); try fold (per_univ (us (dlvl_real l)) m m);
    mauto 4.

  intros.
  destruct_rel_mod_app.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  do_per_univ_elem_irrel_assert.

  econstructor; firstorder eauto.
Qed.

Lemma glu_univ_elem_trm_typ : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel;
    mauto 4.

  econstructor; eauto.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  intros ? ? N n ? ? equiv_n.
  destruct_rel_mod_eval.
  enough (exists mn : domain, $| m & n |↘ mn /\  Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv_n) as [? []]; eauto 3.
Qed.

Lemma glu_univ_elem_trm_univ_lvl : forall i U P El a,
    Typeω@(ulvl i) = U ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A : U.
Proof.
  intros. eapply glu_univ_elem_univ_lvl; [ eassumption | eassumption | eapply glu_univ_elem_trm_typ ]; eassumption.
Qed.

Lemma glu_univ_elem_trm_resp_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m M',
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M ≈ M' : A ->
      Γ ⊢ M' : A ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel;
    repeat split; mauto 3.

  (** The type of the element is unchanged, so a small universe's level term
      and its equation carry over. *)
  all: try solve [ apply suniv_glu_typ_pred_intro; eassumption ].

  - repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_exp_eq;
      [ eassumption | eassumption | eapply wf_exp_eq_conv'; [ eassumption |] ].
    eassumption.

  - (** An element of a small universe: its type-level gluing moves along
        the equation lifted to the ambient [Typeω@0] by cumulativity, and its
        readback clause by transitivity. *)
    repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_exp_eq;
      [ eassumption | eassumption | eapply suniv_elem_eq_large; eassumption ].

  - intros; transitivity M[φ]ʷ; [| eauto ].
    symmetry; mauto 3.

  - econstructor; eauto.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    intros.
    destruct_rel_mod_eval.
    assert (Δ ⊢ N : IT[φ]ʷ) by eauto using glu_univ_elem_trm_escape.
    assert (exists mn : domain, $| m & n |↘ mn /\  Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv_n) as [? []] by intuition.
    eexists; split; eauto.
    enough (Δ ⊢ M[φ]ʷ $ N ≈ M'[φ]ʷ $ N : OT[(ι φ),,N]) by eauto.
    assert (Γ ⊢ M ≈ M' : Π IT OT) as Hty by mauto.
    assert (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : (Π IT OT)[φ]ʷ) as Hty' by mauto 2.
    rewrite exp_wk_pi in Hty'.
    eapply wf_exp_eq_app_cong' with (N := N) (N' := N) in Hty'; [| mauto 2].
    rewrite exp_sub_wk_q_extend in Hty'.
    eassumption.
  - intros.
    enough (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ); mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ T : (El Γ T)
    with signature wf_exp_eq gc_deps gc_stack Γ T ==> eq ==> iff as glu_univ_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_core_univ' : forall j i typ_rel el_rel,
    uidx_lt (ul j) i ->
    (typ_rel <∙> univ_glu_typ_pred j (Typeω@(ulvl i))) ->
    (el_rel <∙> univ_glu_exp_pred j (Typeω@(ulvl i))) ->
    DG 𝕌ω@j ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

Hint Resolve glu_univ_elem_core_univ' : mctt.

Lemma glu_univ_elem_core_suniv' : forall l i typ_rel el_rel,
    Dom l ≈ l ∈ per_lvl ->
    uidx_lt (us (dlvl_real l)) i ->
    (typ_rel <∙> suniv_glu_typ_pred l (Typeω@(ulvl i))) ->
    (el_rel <∙> suniv_glu_exp_pred l (Typeω@(ulvl i))) ->
    DG 𝕌@l ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

Hint Resolve glu_univ_elem_core_suniv' : mctt.

(** The gluing of a universe at either tier, in one statement. *)
Lemma glu_univ_elem_univ_at : forall {u i},
    uidx_lt u i ->
    DG ulvl_val u ∈ glu_univ_elem i ↘ univ_glu_typ_pred_at u (Typeω@(ulvl i)) ↘ univ_glu_exp_pred_at u (Typeω@(ulvl i)).
Proof.
  intros [n | j] * Hlt; cbn [ulvl_val univ_glu_typ_pred_at univ_glu_exp_pred_at].
  - apply glu_univ_elem_core_suniv';
      [ apply per_lvl_lit | exact Hlt | reflexivity | reflexivity ].
  - apply glu_univ_elem_core_univ'; [ exact Hlt | reflexivity | reflexivity ].
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_univ_elem_typ_morphism_iff1_Proper.
#[export] Existing Instance glu_univ_elem_trm_morphism_iff1_Proper.
#[export]
Hint Resolve glu_nat_resp_wk glu_lvl_resp_wk glu_False_resp_wk : mctt.
#[export]
Hint Resolve glu_univ_elem_per_univ : mctt.
#[export] Existing Instance glu_univ_elem_trm_morphism_iff3_Proper.
#[export]
Hint Resolve glu_univ_elem_core_univ' glu_univ_elem_core_suniv' glu_univ_elem_univ_at : mctt.
Ltac glu_univ_elem_econstructor :=
  eapply glu_univ_elem_core_univ' + eapply glu_univ_elem_core_suniv' + basic_glu_univ_elem_econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_univ_elem_univ_simple_constructor : forall {i : nat},
    glu_univ_elem (S i) (univ_glu_typ_pred i Typeω@(S i)) (univ_glu_exp_pred i Typeω@(S i)) 𝕌ω@i.
Proof.
  intros.
  apply glu_univ_elem_core_univ'; [ cbn; lia | reflexivity | reflexivity ].
Qed.

Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.
Ltac rewrite_predicate_equivalence_left :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_predicate_equivalence_right :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_predicate_equivalence :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_predicate_equivalence :=
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_right;
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_left;
  clear_predicate_equivalence.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** *** Simple Morphism instance for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> iff as simple_glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' ? El El'.
  split; intro Horig; [gen El' P' | gen El P];
    glu_univ_elem_induction Horig; unshelve glu_univ_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

(** *** Morphism instances for [neut_glu_*_pred]s *)
Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> eq ==> eq ==> iff as neut_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition.
Qed.

Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> glu_typ_pred_equivalence as neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_typ_pred_morphism_iff; mauto.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> eq ==> eq ==> eq ==> eq ==> iff as neut_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition;
    match_by_head per_bot ltac:(fun H => rewrite H in *); eassumption.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> glu_exp_pred_equivalence as neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_exp_pred_morphism_iff; mauto.
Qed.

(** *** Morphism instances for [pi_glu_*_pred]s *)
Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> glu_typ_pred_equivalence as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Lemma functional_glu_univ_elem : forall i a P P' El El',
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem i ↘ P' ↘ El' ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  glu_univ_elem_induction Ha; intros; basic_invert_glu_univ_elem Ha';
    apply_predicate_equivalence; try solve [split; reflexivity].
  assert ((IP <∙> IP0) /\ (IEl <∙> IEl0)) as [] by mauto.
  apply_predicate_equivalence.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  split; [intros Γ C | intros Γ M C m].
  - split; intros []; econstructor; intuition;
      [rename equiv_m into equiv0_m; assert (equiv_m : in_rel m m) by intuition
      | assert (equiv0_m : in_rel0 m m) by intuition ];
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      assert ((OP m equiv_m <∙> OP0 m equiv0_m) /\ (OEl m equiv_m <∙> OEl0 m equiv0_m)) as [] by mauto 3;
      intuition.
  - split; intros []; econstructor; intuition;
      [rename equiv_n into equiv0_n; assert (equiv_n : in_rel n n) by intuition
      | assert (equiv0_n : in_rel0 n n) by intuition];
      destruct_rel_mod_eval;
      [assert (exists m0n, $| m0 & n |↘ m0n /\ Δ ⊢ M0[φ]ʷ $ N : OT[(ι φ),,N] ® m0n ∈ OEl n equiv_n) by intuition
      | assert (exists m0n, $| m0 & n |↘ m0n /\ Δ ⊢ M0[φ]ʷ $ N : OT[(ι φ),,N] ® m0n ∈ OEl0 n equiv0_n) by intuition];
      destruct_conjs;
      assert ((OP n equiv_n <∙> OP0 n equiv0_n) /\ (OEl n equiv_n <∙> OEl0 n equiv0_n)) as [] by mauto 3;
      eexists; split; intuition.
Qed.

End Fixed_GCtx.

#[export] Existing Instance simple_glu_univ_elem_morphism_iff_Proper.
#[export] Existing Instance neut_glu_typ_pred_morphism_iff_Proper.
#[export] Existing Instance neut_glu_typ_pred_morphism_glu_typ_pred_equivalence_Proper.
#[export] Existing Instance neut_glu_exp_pred_morphism_iff_Proper.
#[export] Existing Instance neut_glu_exp_pred_morphism_glu_exp_pred_equivalence_Proper.
#[export] Existing Instance pi_glu_typ_pred_morphism_iff_Proper.
#[export] Existing Instance pi_glu_typ_pred_morphism_glu_typ_pred_equivalence_Proper.
#[export] Existing Instance pi_glu_exp_pred_morphism_iff_Proper.
#[export] Existing Instance pi_glu_exp_pred_morphism_glu_exp_pred_equivalence_Proper.
Ltac apply_functional_glu_univ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_univ_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (DG ?a ∈ glu_univ_elem ?i ↘ ?P1 ↘ ?El1),
      H2 : DG ?a ∈ glu_univ_elem ?i' ↘ ?P2 ↘ ?El2 |- _ =>
      unify i i';
      assert_fails (unify P1 P2; unify El1 El2);
      match goal with
      | H : P1 <∙> P2, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P1 <∙> P2, H0 : El2 <∙> El1 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El2 <∙> El1 |- _ => fail 1
      | _ => assert ((P1 <∙> P2) /\ (El1 <∙> El2)) as [] by (eapply functional_glu_univ_elem; [apply H1 | apply H2]) || tactic_error P1 P2
      end
  end.

Ltac apply_functional_glu_univ_elem :=
  repeat apply_functional_glu_univ_elem1.

Ltac handle_functional_glu_univ_elem :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_univ_elem;
  apply_predicate_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_univ_elem_pi_clean_inversion1 : forall {i a ρ B in_rel P El},
  DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
  DG Πᵈ a ρ B ∈ glu_univ_elem i ↘ P ↘ El ->
  exists IP IEl (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
     (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred) elem_rel,
      DG a ∈ glu_univ_elem i ↘ IP ↘ IEl /\
        (forall c (equiv_c : Dom c ≈ c ∈ in_rel) b,
            ⟦ B ⟧ ρ ↦ c ↘ b ->
            DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c) /\
        DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel /\
        (P <∙> pi_glu_typ_pred (Typeω@(ulvl i)) in_rel IP IEl OP) /\
        (El <∙> pi_glu_exp_pred (Typeω@(ulvl i)) in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split.
  1,3: eassumption.
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain) Pb Elb,
                          ⟦ B ⟧ ρ ↦ c ↘ b ->
                          DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                          Γ ⊢ M : A ® m ∈ Elb).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          ⟦ B ⟧ ρ ↦ c ↘ b ->
                          DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                          Γ ⊢ A ® Pb).
  2-5: intros []; econstructor; mauto.
  all: intros.
  - assert (Dom c ≈ c ∈ in_rel0) as equiv0_c by intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c) by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_univ_elem; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - assert (Dom m ≈ m ∈ in_rel0) as equiv0_m by intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP m equiv0_m ↘ OEl m equiv0_m) by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    intuition.
  - assert (Dom n ≈ n ∈ in_rel0) as equiv0_n by intuition.
    assert (exists mn : domain, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv0_n) by mauto 3.
    destruct_conjs.
    eexists.
    intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP n equiv0_n ↘ OEl n equiv0_n) by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - assert (exists mn : domain,
               $| m & n |↘ mn /\
                 (forall (b : domain) (Pb : glu_typ_pred) (Elb : glu_exp_pred),
                     ⟦ B ⟧ ρ ↦ n ↘ b ->
                     DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                     Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ Elb)) by intuition.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    eexists.
    intuition.
Qed.

Lemma glu_univ_elem_pi_clean_inversion2 : forall {i a ρ B in_rel IP IEl P El},
  DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
  DG a ∈ glu_univ_elem i ↘ IP ↘ IEl ->
  DG Πᵈ a ρ B ∈ glu_univ_elem i ↘ P ↘ El ->
  exists (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
     (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred) elem_rel,
    (forall c (equiv_c : Dom c ≈ c ∈ in_rel) b,
        ⟦ B ⟧ ρ ↦ c ↘ b ->
        DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c) /\
      DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel /\
      (P <∙> pi_glu_typ_pred (Typeω@(ulvl i)) in_rel IP IEl OP) /\
      (El <∙> pi_glu_exp_pred (Typeω@(ulvl i)) in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hinglu Hglu.
  unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in Hglu; shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]].
  handle_functional_glu_univ_elem.
  do 3 eexists.
  repeat split; try eassumption;
    intros []; econstructor; mauto.
Qed.

End Fixed_GCtx.

Ltac invert_glu_univ_elem H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_univ_elem H.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_lvl_read_left : forall d d' s L, Dom d ≈ d' ∈ per_lvl -> Rnf ⇓ Levelᵈ d' in s ↘ L -> Rnf ⇓ Levelᵈ d in s ↘ L.
Proof.
  intros * Hd%per_lvl_then_per_top Hr; destruct (Hd s) as (L' & HL & HL').
  pose proof (functional_read_nf _ _ _ _ HL' Hr) as ->; exact HL.
Qed.

Lemma glu_lvl_resp_per : forall Γ M m, glu_lvl Γ M m -> forall m', Dom m ≈ m' ∈ per_lvl -> glu_lvl Γ M m'.
Proof.
  intros * H * Hm Δ φ L **.
  eapply H; [ eassumption | eapply per_lvl_read_left; eassumption ].
Qed.

(** Related levels give equivalent small-universe predicates: a level term
    glued to one is glued to the other, and the two have the same realiser,
    which indexes the elements. *)
Lemma suniv_glu_typ_pred_resp_per : forall l l' U,
    Dom l ≈ l' ∈ per_lvl ->
    suniv_glu_typ_pred l U <∙> suniv_glu_typ_pred l' U.
Proof.
  intros * Hl Γ A; cbn; split; intros [t [Ht Heq]]; exists t; split; try assumption;
    eapply glu_lvl_resp_per; [ eassumption | assumption | eassumption | symmetry; assumption ].
Qed.

Lemma suniv_glu_exp_pred_resp_per : forall l l' U,
    Dom l ≈ l' ∈ per_lvl ->
    suniv_glu_exp_pred l U <∙> suniv_glu_exp_pred l' U.
Proof.
  intros * Hl Γ A M m; cbn.
  rewrite (per_lvl_real _ _ Hl).
  pose proof (suniv_glu_typ_pred_resp_per l l' U Hl Γ A) as Ht; cbn in Ht.
  split; intros (? & HA & ? & ?); repeat split; try assumption; apply Ht; assumption.
Qed.

Lemma glu_univ_elem_resp_per_univ : forall i a a' P El,
    Dom a ≈ a' ∈ per_univ i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  simpl.
  intros * [elem_rel Hper] Horig.
  pose proof Hper.
  gen P El.
  per_univ_elem_induction Hper; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Horig; glu_univ_elem_econstructor; try eassumption; mauto;
    handle_per_univ_elem_irrel;
    handle_functional_glu_univ_elem.
  (** A small universe at a related level: the same realiser, and equivalent
      predicates. *)
  all: try match goal with
         | H : per_lvl ?l ?l' |- uidx_lt (us (dlvl_real ?l')) _ =>
             rewrite <- (per_lvl_real _ _ H); assumption
         | H : per_lvl ?l ?l' |- suniv_glu_typ_pred ?l _ <∙> suniv_glu_typ_pred ?l' _ =>
             apply suniv_glu_typ_pred_resp_per; exact H
         | H : per_lvl ?l ?l' |- _ <∙> suniv_glu_exp_pred ?l' _ =>
             exact (suniv_glu_exp_pred_resp_per _ _ _ H)
         end.
  - intros.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
  - reflexivity.
  - apply neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
    eassumption.
  - apply neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
    eassumption.
Qed.

(** *** Morphism instances for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ i ==> iff as glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; eassumption.
Qed.

Add Parametric Morphism i R : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ_elem i R ==> iff as glu_univ_elem_morphism_iff'.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' **.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; mauto.
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_univ_elem_morphism_iff'_Proper.

Ltac saturate_glu_by_per1 :=
  match goal with
  | H : glu_univ_elem ?i ?P ?El ?a,
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a') by (rewrite <- H1; eassumption);
      fail_if_dup
  | H : glu_univ_elem ?i ?P ?El ?a',
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a) by (rewrite H1; eassumption);
      fail_if_dup
  end.

Ltac saturate_glu_by_per :=
  clear_dups;
  repeat saturate_glu_by_per1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_univ_glu_univ_elem : forall i a,
    Dom a ≈ a ∈ per_univ i ->
    exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  simpl.
  (** [per_univ_elem_induction] wants distinct indices; [induction] abstracted
      the right one. *)
  intros i a [R Hper].
  enough (forall a0, DF a0 ≈ a ∈ per_univ_elem i ↘ R -> exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) by eauto.
  clear Hper; intros a0 Hper.
  per_univ_elem_induction Hper; intros;
    try solve [do 2 eexists; unshelve (glu_univ_elem_econstructor; try reflexivity; subst; trivial)].
  (** A small universe at the right-hand level, which has the realiser of the
      left-hand one. *)
  all: try match goal with
         | H : per_lvl ?l ?l' |- exists _ _, glu_univ_elem _ _ _ 𝕌@?l' =>
             do 2 eexists; apply glu_univ_elem_core_suniv';
               [ etransitivity; [ symmetry |]; exact H
               | rewrite <- (per_lvl_real _ _ H); assumption
               | reflexivity | reflexivity ]
         end.

  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A M m =>
                          forall b P El,
                            ⟦ B' ⟧ ρ' ↦ c ↘ b ->
                            glu_univ_elem i P El b ->
                            Γ ⊢ M : A ® m ∈ El).
      instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A =>
                          forall b P El,
                            ⟦ B' ⟧ ρ' ↦ c ↘ b ->
                            glu_univ_elem i P El b ->
                            Γ ⊢ A ® P).
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough (DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel) by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
  - do 2 eexists.
    glu_univ_elem_econstructor; try reflexivity; mauto.
Qed.

Hint Resolve per_univ_glu_univ_elem : mctt.

Corollary per_univ_elem_glu_univ_elem : forall i a R,
    DF a ≈ a ∈ per_univ_elem i ↘ R ->
    exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  intros.
  apply per_univ_glu_univ_elem; mauto.
Qed.

Hint Resolve per_univ_elem_glu_univ_elem : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_glu_univ_elem per_univ_elem_glu_univ_elem : mctt.

Ltac saturate_glu_info1 :=
  match goal with
  | H : glu_univ_elem _ ?P _ _,
      H1 : ?P _ _ |- _ =>
      pose proof (glu_univ_elem_univ_lvl_gen _ _ _ _ H _ _ H1);
      fail_if_dup
  | H : glu_univ_elem _ _ ?El _,
      H1 : ?El _ _ _ _ |- _ =>
      pose proof (glu_univ_elem_trm_escape _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_info :=
  clear_dups;
  repeat saturate_glu_info1.

(** The type-level gluing of a small universe along a weakening [φ]: its level
    term is weakened with the type. *)
Ltac suniv_glu_typ_pred_wk :=
  match goal with
  | H : exists t, glu_lvl ?Γ t ?l /\ _,
      Hφ : ?Δ ⊢k ?φ : ?Γ
    |- exists t, glu_lvl ?Δ t ?l /\ _ =>
      let t := fresh "t" in
      let Heq := fresh "Heq" in
      destruct H as [t [? Heq]]; exists t[φ]ʷ; split;
      [ eapply glu_lvl_resp_wk; eassumption
      | match type of Heq with
        | wf_exp_eq ?T ?X _ ?U ?A _ =>
            assert (wf_exp_eq T X Δ U A[φ]ʷ (Type⟨t⟩)[φ]ʷ) by mauto 2; eassumption
        end ]
  end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Gluing predicates are monotone along Kripke weakenings. Two weakenings
    collapse to a single [[φ ⊙ ψ]ʷ] by [exp_wk_wk], and the [q] of a [Π]
    codomain absorbs the extension of the second weakening by
    [exp_sub_wk_q_extend_wk]. Both are propositional equalities, so each case
    is a [rewrite] away from its hypothesis. *)

Lemma glu_univ_elem_typ_monotone : forall i a P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Δ φ Γ A,
      Γ ⊢ A ® P ->
      Δ ⊢k φ : Γ ->
      Δ ⊢ A[φ]ʷ ® P.
Proof.
  simpl. glu_univ_elem_induction1; intros;
    saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    try solve [mauto 2].
  (** A small universe: the level term weakens with the type. *)
  all: try solve [ suniv_glu_typ_pred_wk ].
  - simpl_glu_rel.
    assert (Δ ⊢ A[φ]ʷ ≈ (Π IT OT)[φ]ʷ : Typeω@(ulvl i)) as HAeq by mauto 2.
    rewrite exp_wk_pi in HAeq.
    econstructor; [ eassumption | mauto 2 | mauto 2 | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.

  - destruct_conjs.
    split; [mauto 2 |].
    intros.
    rewrite exp_wk_wk.
    mauto 4.
Qed.

Lemma glu_univ_elem_exp_monotone : forall i a P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Δ φ Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Δ ⊢k φ : Γ ->
      Δ ⊢ M[φ]ʷ : A[φ]ʷ ® m ∈ El.
Proof.
  simpl. glu_univ_elem_induction1; intros;
    saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all.
  all: try solve [ repeat eexists; mauto 2; eapply glu_univ_elem_typ_monotone; eauto ].
  (** An element of a small universe: its type's level term weakens with it,
      and its readback clause composes the two weakenings. *)
  all: try solve [ repeat apply conj;
                   [ mauto 2
                   | eexists; split; [ eapply glu_lvl_resp_wk; eassumption | mauto 2 ]
                   | do 2 eexists; split;
                     [ eassumption | eapply glu_univ_elem_typ_monotone; eassumption ]
                   | intros; rewrite !exp_wk_wk; mauto 3 ] ].
  all: try solve [ repeat split; mauto 2 ].
  - simpl_glu_rel.
    assert (Δ ⊢ A[φ]ʷ ≈ (Π IT OT)[φ]ʷ : Typeω@(ulvl i)) as HAeq by mauto 2.
    rewrite exp_wk_pi in HAeq.
    econstructor; [ mauto 2 | eassumption | eassumption | mauto 2 | mauto 2 | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.

  - simpl_glu_rel.
    econstructor; [ split; [ mauto 2 | ] | mauto 2 | eassumption | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + do 2 rewrite exp_wk_wk; mauto 4.
Qed.

(** Transport along a context refinement, as in [glu_nat_resp_ctxsub]: a
    Kripke weakening into [Δ] extends to one into [Γ] by [kripke_ctxsub], which
    is all three lemmas need. *)

Lemma glu_elem_bot_resp_ctxsub : forall i a Γ A M m Δ,
    Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
    Δ ⊆ Γ ->
    Δ ⊢ M : A ® m ∈ glu_elem_bot i a.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_elem_top_resp_ctxsub : forall i a Γ A M m Δ,
    Γ ⊢ M : A ® m ∈ glu_elem_top i a ->
    Δ ⊆ Γ ->
    Δ ⊢ M : A ® m ∈ glu_elem_top i a.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_typ_top_resp_ctxsub : forall i a Γ A Δ,
    Γ ⊢ A ® glu_typ_top i a ->
    Δ ⊆ Γ ->
    Δ ⊢ A ® glu_typ_top i a.
Proof.
  intros * [] ?; econstructor; [ mauto 3 | eassumption | intros ]; mauto 4.
Qed.

Hint Resolve glu_elem_bot_resp_ctxsub glu_elem_top_resp_ctxsub glu_typ_top_resp_ctxsub : mctt.

Add Parametric Morphism i a Γ : (glu_elem_bot i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_bot i a Γ A)
    with signature wf_exp_eq gc_deps gc_stack Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ) as HMφM'φ by mauto 4;
    [rewrite <- HMφM'φ | rewrite -> HMφM'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_top i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_top i a Γ A)
    with signature wf_exp_eq gc_deps gc_stack Γ A ==> eq ==> iff as glu_elem_top_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ) as HMφM'φ by mauto 4;
    [rewrite <- HMφM'φ | rewrite -> HMφM'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ : (glu_typ_top i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> iff as glu_typ_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    try (gen_presup HAA'; eassumption);
    intros;
    assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

(** *** Simple Morphism instance for [glu_ctx_env] *)
Add Parametric Morphism : glu_ctx_env
    with signature glu_sub_pred_equivalence ==> eq ==> iff as simple_glu_ctx_env_morphism_iff.
Proof.
  intros Sb Sb' HSbSb' a.
  split; intro Horig; [gen Sb' | gen Sb];
    induction Horig; econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_univ_elem_morphism_iff_Proper.
#[export] Existing Instance glu_elem_bot_morphism_iff2_Proper.
#[export] Existing Instance glu_elem_bot_morphism_iff3_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff2_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff3_Proper.
#[export] Existing Instance glu_typ_top_morphism_iff2_Proper.
#[export] Existing Instance simple_glu_ctx_env_morphism_iff_Proper.
#[export]
Hint Resolve glu_elem_bot_resp_ctxsub glu_elem_top_resp_ctxsub glu_typ_top_resp_ctxsub : mctt.

(** *** Gluing respects the element PER

    A term glued to a value is glued to every value related to it: δ relates
    a member to its expansion by the element PER only. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_bot_read_left : forall d d' s M, Dom d ≈ d' ∈ per_bot -> Rne d' in s ↘ M -> Rne d in s ↘ M.
Proof.
  intros * Hd Hr; destruct (Hd s) as (L & HL & HL').
  pose proof (functional_read_ne _ _ _ _ HL' Hr) as ->; exact HL.
Qed.

(** The same for levels, whose readback is at the type [Level]. *)
(** The same for types: related types read back equally, so a readback of the
    right one is one of the left. *)
Lemma per_top_typ_read_left : forall d d' s W, Dom d ≈ d' ∈ per_top_typ -> Rtyp d' in s ↘ W -> Rtyp d in s ↘ W.
Proof.
  intros * Hd Hr; destruct (Hd s) as (L & HL & HL').
  pose proof (functional_read_typ _ _ _ _ HL' Hr) as ->; exact HL.
Qed.

Lemma glu_nat_resp_per : forall Γ M m, glu_nat Γ M m -> forall m', Dom m ≈ m' ∈ per_nat -> glu_nat Γ M m'.
Proof.
  induction 1 as [| ? ? ? ? HM Hg IH | ? ? ? ? Hb Hrb ]; intros m'' Hm; inversion Hm; subst.
  - constructor; assumption.
  - econstructor; [ eassumption | eapply IH; eassumption ].
  - constructor; [ etransitivity; [ symmetry |]; eassumption |].
    intros * Hk Hr; eapply Hrb; [ eassumption | eapply per_bot_read_left; eassumption ].
Qed.

Lemma glu_False_resp_per : forall Γ M m, glu_False Γ M m -> forall m', Dom m ≈ m' ∈ per_ne -> glu_False Γ M m'.
Proof.
  intros * [? ? ? ? Hb Hrb] m'' Hm; inversion Hm; subst.
  constructor; [ etransitivity; [ symmetry |]; eassumption |].
  intros * Hk Hr; eapply Hrb; [ eassumption | eapply per_bot_read_left; eassumption ].
Qed.

Lemma glu_univ_elem_trm_resp_per_elem : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall R, DF a ≈ a ∈ per_univ_elem i ↘ R ->
    forall Γ A M m m', Γ ⊢ M : A ® m ∈ El -> Dom m ≈ m' ∈ R -> Γ ⊢ M : A ® m' ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  7:{ handle_per_univ_elem_irrel.
      apply_predicate_equivalence.
      destruct_by_head pi_glu_exp_pred.
      assert (PER elem_rel) by (eapply per_elem_PER; eassumption).
      econstructor; try eassumption.
      - etransitivity; [ symmetry |]; eassumption.
      - intros Δ φ N n Hk HN equiv_n.
        destruct (H11 _ _ _ _ Hk HN equiv_n) as (mn & Happ & HO).
        pose proof H6 as H6'.
        invert_per_univ_elem H6'.
        handle_per_univ_elem_irrel.
        destruct_rel_mod_eval.
        destruct (H8 n n equiv_n) as [mn0 mn' Happ0 Happ' Hmn].
        functional_eval_rewrite_clear.
        exists mn'; split; [ exact Happ' |].
        eapply H2; [ eassumption | eassumption | exact HO | exact Hmn ]. }
  all: match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H);
       apply_predicate_equivalence; simpl in *; destruct_conjs.
  - repeat split; try assumption.
    destruct (proj1 (H3 m m') H4) as [R' HR'].
    exists H2, H5; split; [ eapply glu_univ_elem_resp_per_univ; [ exists R'; exact HR' | exact H6 ] | exact H7 ].
  (** A small universe: as the large one, and the readback clause moves along
      the two types, which read back equally. *)
  - match goal with E : elem_rel <~> _, Hm : elem_rel m m' |- _ =>
      destruct (proj1 (E m m') Hm) as [R' HR'] end.
    repeat split; try assumption.
    + eexists; split; eassumption.
    + do 2 eexists; split;
        [ eapply glu_univ_elem_resp_per_univ; [ exists R'; exact HR' | eassumption ] | eassumption ].
    + intros * Hk Hr.
      match goal with Hrb : forall _ _ _, _ -> Rtyp m in _ ↘ _ -> _ |- _ => apply Hrb; [ exact Hk |] end.
      eapply per_top_typ_read_left; [ eapply per_univ_then_per_top_typ; exact HR' | exact Hr ].
  (** [Level]: the readback moves along the level PER. *)
  - assert (Dom m ≈ m' ∈ per_lvl) as Hmm'
      by (match goal with E : _ <~> per_lvl |- _ => apply E; eassumption end).
    repeat split;
      [ assumption
      | eapply per_lvl_trans; [ eapply per_lvl_sym; exact Hmm' | exact Hmm' ]
      | eapply glu_lvl_resp_per; eassumption ].
  (** [ℕ] *)
  - split; [ assumption | eapply glu_nat_resp_per; [ eassumption | apply H1; eassumption ] ].
  - split; assumption.
  - split; [ assumption | eapply glu_False_resp_per; [ eassumption | apply H1; eassumption ] ].
  - destruct_by_head neut_glu_exp_pred.
    match goal with E : _ <~> per_ne, Hm : _ ?x ?y |- _ => apply E in Hm; inversion Hm; subst end.
    econstructor; [ assumption | assumption | etransitivity; [ symmetry |]; eassumption |].
    intros * Hk Hr; eauto using per_bot_read_left.
Qed.

End Fixed_GCtx.
