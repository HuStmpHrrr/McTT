(** * The PER Model along an Extension of the Global Context

    (b)/(c): what is monotone, what is not. *)

From Stdlib Require Import List String Relation_Definitions RelationClasses.
From Equations Require Import Equations.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.
From ExtInv Require Import Ext.
Import Domain_Notations GlobalCtx_Notations.
#[local] Open Scope string_scope.

(** ** The PER lattice below the universes: inclusions *)

Section Incl.
  Variables (G1 G2 : GCtx).
  Hypothesis Hext : gc_ext G1 G2.

  Lemma per_bot_mono : forall m n, @per_bot G1 m n -> @per_bot G2 m n.
  Proof.
    cbn; intros * H s; destruct (H s) as [L [? ?]].
    exists L; split; eapply read_ne_mono; eassumption.
  Qed.

  Lemma per_top_mono : forall m n, @per_top G1 m n -> @per_top G2 m n.
  Proof.
    cbn; intros * H s; destruct (H s) as [L [? ?]].
    exists L; split; eapply read_nf_mono; eassumption.
  Qed.

  Lemma per_top_typ_mono : forall a b, @per_top_typ G1 a b -> @per_top_typ G2 a b.
  Proof.
    cbn; intros * H s; destruct (H s) as [L [? ?]].
    exists L; split; eapply read_typ_mono; eassumption.
  Qed.

  Lemma per_nat_mono : forall m n, @per_nat G1 m n -> @per_nat G2 m n.
  Proof. induction 1; constructor; auto using per_bot_mono. Qed.

  Lemma per_ne_mono : forall m n, @per_ne G1 m n -> @per_ne G2 m n.
  Proof. destruct 1; constructor; auto using per_bot_mono. Qed.

  (** The two cases of [per_univ_elem] that do not quantify over arguments.
      (The [𝕌@j] case needs [per_univ j] at [G1] to be *equivalent* to
      the one at [G2], which it is not — see [per_univ_not_mono] — so the best
      it can give is an inclusion, which needs full monotonicity at [j],
      including its [Π] case.) *)
  Lemma per_univ_elem_mono_nat : forall i R,
      @per_univ_elem G1 i R ℕᵈ ℕᵈ ->
      exists R', @per_univ_elem G2 i R' ℕᵈ ℕᵈ /\ (forall x y, R x y -> R' x y).
  Proof.
    intros * H; simp per_univ_elem in H; inversion H; subst.
    exists (@per_nat G2); split.
    - simp per_univ_elem; apply per_univ_elem_core_nat; reflexivity.
    - intros x y Hxy; apply per_nat_mono, H0, Hxy.
  Qed.
End Incl.

(** ** Counterexamples to the converse inclusions

    [G1] has one open frame with no members; [G2] is [G1] grown by one
    transparent member [c := zero : ℕ].  So [G2] is a grow step (1) of [G1]. *)

Definition p_c : path := p_rel 0 ("c" :: nil).
Definition U_empty : gunit := gu_mk nil ⋄.
Definition U_c : gunit := gu_mk nil (⋄ ⊳ "c" ↦ ge_def true false a_nat (Some a_zero)).

#[local] Instance G1 : GCtx := gc_mk nil (U_empty :: nil).
#[local] Instance G2 : GCtx := gc_mk nil (U_c :: nil).

Lemma G1_G2_ext : gc_ext G1 G2.
Proof.
  unfold gc_ext; cbn.
  apply (gc_ext_grow_member nil nil nil ⋄ "c"); cbn; unfold gm_fresh; cbn; auto.
Qed.

Lemma resolve_c_G2 :
  gc_resolve nil (U_c :: nil) p_c = Some (nil, ge_def true false a_nat (Some a_zero)).
Proof. reflexivity. Qed.

Lemma resolve_c_G1 : gc_resolve nil (U_empty :: nil) p_c = None.
Proof. reflexivity. Qed.

(** A neutral whose *successor branch* mentions [c].  Evaluation never looks at
    it (it is inside a neutral), but readback does. *)
Definition m_bad : domain_ne :=
  d_natrec nil a_nat d_zero (a_glob p_c) (d_var 0).

Lemma eval_c_G2 : forall ρ, eval_exp nil (U_c :: nil) (a_glob p_c) ρ d_zero.
Proof.
  intros; eapply eval_exp_glob_delta; [ exact resolve_c_G2 | cbn; constructor ].
Qed.

Lemma no_eval_c_G1 : forall ρ m, ~ eval_exp nil (U_empty :: nil) (a_glob p_c) ρ m.
Proof.
  intros * H; inversion H; subst;
    match goal with Hr : gc_resolve _ _ _ = Some _ |- _ => rewrite resolve_c_G1 in Hr; discriminate end.
Qed.

Lemma m_bad_per_bot_G2 : @per_bot G2 m_bad m_bad.
Proof.
  cbn; intros s; eexists; split;
    (eapply read_ne_natrec;
     [ constructor | constructor | constructor | constructor
     | constructor | apply eval_c_G2 | constructor | constructor ]).
Qed.

Lemma m_bad_not_per_bot_G1 : ~ @per_bot G1 m_bad m_bad.
Proof.
  cbn; intros H; destruct (H 0) as [L [HL _]].
  inversion HL; subst; eapply no_eval_c_G1; eassumption.
Qed.

Theorem per_bot_not_antimono : exists m, @per_bot G2 m m /\ ~ @per_bot G1 m m.
Proof. exists m_bad; split; [ apply m_bad_per_bot_G2 | apply m_bad_not_per_bot_G1 ]. Qed.

Theorem per_nat_not_antimono : exists m, @per_nat G2 m m /\ ~ @per_nat G1 m m.
Proof.
  exists (⇑ ℕᵈ m_bad); split; [ constructor; apply m_bad_per_bot_G2 |].
  intros H; inversion H; subst; apply m_bad_not_per_bot_G1; assumption.
Qed.

(** A type at [G2] that is no type at [G1]: [per_univ 0] strictly grows. *)
Theorem per_univ_not_antimono :
  exists a, @per_univ G2 0 a a /\ ~ @per_univ G1 0 a a.
Proof.
  exists (⇑ 𝕌@0 m_bad); split.
  - exists (@per_ne G2); simp per_univ_elem.
    apply per_univ_elem_core_neut; [ apply m_bad_per_bot_G2 | reflexivity ].
  - intros [R H]; simp per_univ_elem in H; inversion H; subst.
    apply m_bad_not_per_bot_G1; assumption.
Qed.

(** Hence the [𝕌] case cannot be monotone *as an equivalence of element
    relations*: [per_univ_elem i R 𝕌@0 𝕌@0] pins [R] to [per_univ 0] of its own
    context, and the two differ. *)
Corollary per_univ_elem_univ_rel_changes : forall R1 R2,
    @per_univ_elem G1 1 R1 𝕌@0 𝕌@0 ->
    @per_univ_elem G2 1 R2 𝕌@0 𝕌@0 ->
    ~ (forall a b, R2 a b -> R1 a b).
Proof.
  intros * H1 H2 Hincl.
  simp per_univ_elem in H1, H2; inversion H1; inversion H2; subst.
  destruct per_univ_not_antimono as [a [Ha2 Ha1]].
  apply Ha1.
  (* [a] is in [R2], hence (by the assumed inclusion) in [R1] = per_univ 0 at G1 *)
  match goal with HE : R1 <~> _ |- _ => apply HE end.
  apply Hincl.
  match goal with HE : R2 <~> _ |- _ => apply HE end.
  exact Ha2.
Qed.

(** An environment for [⋅ ▹ ℕ] related at [G2] that is not related at [G1]:
    the judgment [Γ ⊨ M ≈ M' : A] at [G2] quantifies over it, and [G1]'s
    judgment says nothing about it. *)
Theorem env_not_antimono :
  forall R1 R2,
    @per_ctx_env G1 R1 (nil ▹ ℕ) (nil ▹ ℕ) ->
    @per_ctx_env G2 R2 (nil ▹ ℕ) (nil ▹ ℕ) ->
    R2 (⇑ ℕᵈ m_bad :: nil) (⇑ ℕᵈ m_bad :: nil) /\
    ~ R1 (⇑ ℕᵈ m_bad :: nil) (⇑ ℕᵈ m_bad :: nil).
Proof.
  intros * H1 H2; split.
  - inversion H2; subst.
    match goal with
    | Htail : per_ctx_env ?tr nil nil, Hhead : forall ρ ρ' (e : ?tr ρ ρ'), _,
      Henv : R2 <~> _ |- _ =>
        inversion Htail; subst;
        assert (Ht : tr nil nil) by (match goal with HE : tr <~> _ |- _ => apply HE; exact I end);
        apply Henv; cbn; exists Ht;
        destruct (Hhead _ _ Ht) as [a a' Ha Ha' Hpue]
    end.
    inversion Ha; inversion Ha'; subst.
    simp per_univ_elem in Hpue; inversion Hpue; subst.
    match goal with HE : _ <~> per_nat |- _ => apply HE end.
    constructor; apply m_bad_per_bot_G2.
  - inversion H1; subst; intros HR.
    match goal with
    | Hhead : forall ρ ρ' (e : ?tr ρ ρ'), _, Henv : R1 <~> _ |- _ =>
        apply Henv in HR as [Ht Hh]; cbn in Ht, Hh;
        destruct (Hhead _ _ Ht) as [a a' Ha Ha' Hpue]
    end.
    inversion Ha; inversion Ha'; subst.
    simp per_univ_elem in Hpue; inversion Hpue; subst.
    match goal with HE : _ <~> per_nat |- _ => apply HE in Hh end.
    inversion Hh; subst; apply m_bad_not_per_bot_G1; assumption.
Qed.
