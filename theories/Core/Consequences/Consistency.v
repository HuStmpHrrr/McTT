(** * Consistency of the Core

    What completeness and soundness of NbE give together: the inversions
    of conversion and subtyping that normal forms decide (of [Π], of the
    universes and levels, of inductive and record types); canonical forms
    of closed terms of [Π], of a universe and of an inductive type,
    without axioms, through opaque definitions and for every program a
    run files; and the consistency of the core: at a transparent global
    context no closed term inhabits [⊥] ([consistency_False]) nor every
    type of a universe ([consistency]), and likewise at a global context
    with no axiom and at the end of every run.

    It sits in [Core/Consequences/] with [NormalFormWeakening.v] (NbE
    commutes with weakening) and [FiledConstructorTypes.v] (the types of
    filed constructors). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Soundness.
From Mctt.Core.Completeness.Consequences Require Export Types.
From Mctt.Core.Semantic Require Export Transparency Stuck.
From Mctt.Core.Syntactic Require Export Unseal.
From Mctt.Core.Syntactic Require Import CoreInversions.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Semantic Require Import Realizability Levels.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Completeness Require Import UniverseCases ContextCases.
From Mctt.Core.Completeness.Consequences Require Import Rules.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
Require Import Mctt.Core.Syntactic.Command.
From Mctt.Core.Syntactic Require Import Builtin.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma idempotent_nbe_ty : forall {Γ i A B C},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B C ->
    B = C.
Proof.
  intros.
  assert (Γ ⊢ A ≈ B : Typeω@i) as [? []]%completeness_ty by mauto 2 using soundness_ty'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.
Hint Resolve idempotent_nbe_ty : mctt.

(** ** Types at Their Sorts

    A type of a large universe is no proposition ([subtyp_same_relevance]),
    so equations of types at sorts ([type_sort]) compose, and a context
    extended by equal types refines either extension. *)
Lemma typ_prop_absurd : forall {Γ A i},
    Γ ⊢ A : Typeω@i -> Γ ⊢ A : Propₘ -> False.
Proof.
  intros * Hi Hp.
  assert (Hs : Γ ⊢ A ⊆ A) by (eapply wf_subtyp_refl; [ exact Hp | constructor | mauto 3 ]).
  discriminate (subtyp_same_relevance Γ A A relevant propositional i i Hs Hi Hp).
Qed.

(** NbE at [Prop] reads a proposition back as a type. *)
Lemma nbe_prop_to_nbe_ty : forall {Γ T W}, nbe_f Γ T Propₘ W -> nbe_ty_f Γ T W.
Proof.
  intros * [ρ a Hi Ha Hw]; inversion Ha; subst.
  destruct Hw as [Hp | m w Hr Hm Hw]; [ cbn in Hp; discriminate |].
  inversion Hw; subst; try (cbn in *; discriminate).
  econstructor; eassumption.
Qed.

(** The normal form of a type of a sort is its own normal form. *)
Lemma idempotent_nbe_ty_sort : forall {Γ S A B C},
    type_sort S ->
    Γ ⊢ A : S ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B C ->
    B = C.
Proof.
  intros * HS HA HB HC.
  destruct HS as [i |]; [ exact (idempotent_nbe_ty HA HB HC) |].
  pose proof (soundness_ty_at_sort type_sort_prop HA HB) as HE.
  destruct (completeness HE) as (W & H1 & H2).
  apply nbe_prop_to_nbe_ty in H1, H2.
  functional_nbe_rewrite_clear; reflexivity.
Qed.

(** A type of a sort has a normal form. *)
Lemma nbe_ty_exists_sort : forall {Γ S A}, type_sort S -> Γ ⊢ A : S -> exists W, nbe_ty_f Γ A W.
Proof.
  intros * HS HA; destruct HS as [i |]; [ destruct (soundness_ty HA) as (W & HW & _); eauto |].
  destruct (soundness HA) as (W & HW & _); exists W; exact (nbe_prop_to_nbe_ty HW).
Qed.

(** Semantically equal contexts give a type of a sort one normal form. *)
Lemma ctxeq_nbe_ty_eq_sort : forall {Γ Γ' S A W},
    type_sort S -> Γ ⊢ A : S -> ⊨ Γ ≈ Γ' -> nbe_ty_f Γ A W -> nbe_ty_f Γ' A W.
Proof.
  intros * HS HA HΓ HW; destruct HS as [i |]; [ exact (ctxeq_nbe_ty_eq' _ _ _ _ _ HA HΓ HW) |].
  destruct (ctxeq_nbe_eq _ _ _ _ HA HΓ) as (W' & H1 & H2).
  apply nbe_prop_to_nbe_ty in H1, H2.
  functional_nbe_rewrite_clear; exact H2.
Qed.

(** Contexts extended by equal types of a sort are semantically equal. *)
Lemma ctx_extend_sem_eq : forall {Γ S A A'}, type_sort S -> Γ ⊢ A ≈ A' : S -> ⊨ Γ ▹ A ≈ Γ ▹ A'.
Proof.
  intros * HS HAA.
  destruct (rel_type_of_sort HS (completeness_fundamental_exp_eq _ _ _ _ HAA)) as [k Hk].
  eapply per_ctx_extend_type; [| exact Hk ].
  apply rel_ctx_wf_per_ctx, completeness_fundamental_ctx; gen_presups; assumption.
Qed.

(** Types related at an index, of either sort, have one normal form: at
    the initial environment, by the identity substitution, their values
    are related in [per_univ i], so read back equally. *)
Lemma nbe_ty_of_rel_type : forall {Γ A A' i}, Γ ⊨ᵗ A ≈ A' at i -> exists W, nbe_ty_f Γ A W /\ nbe_ty_f Γ A' W.
Proof.
  intros * [R HR Hbody].
  pose proof (per_ctx_then_per_env_initial_env HR) as [ρ [ρ' [Hρi [Hρi' Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (per_ctx_env_proofs _ _ _ HR _ _ Hρρ) as [Hpf _].
  destruct (Hbody _ _ HR _ _ (rel_sub_id (ex_intro _ _ HR)) _ _ _ _ Hρρ (eval_sub_id _ _ Hpf) (eval_sub_id _ _ Hpf))
    as [aσ a a' a'σ' _ Ha Ha' _ Hch].
  cbn in Hch; destruct Hch as (_ & [Rm HRm] & _).
  destruct (per_univ_then_per_top_typ HRm (length Γ)) as (W & HW & HW').
  exists W; split; [ econstructor; [ exact Hρi | exact Ha | exact HW ] | econstructor; [ exact Hρi | exact Ha' | exact HW' ] ].
Qed.

(** A type of a sort is of the sort its value at the initial environment
    is of: a type of a large universe has relevant values, a proposition
    propositional ones ([rel_exp_of_relevance_sort_at]). *)
Lemma typed_at_sort_of_initial_relevance : forall {Γ A S ρ a},
    type_sort S -> Γ ⊢ A : S -> initial_env_f Γ ρ -> ⟦ A ⟧ ρ ↘ a ->
    exists k : nat, Γ ⊢ A : relevance_sort (domain_relevance a) Typeω@k.
Proof.
  intros * HS HA Hρi Ha.
  assert (exists s (i : nat), S = relevance_sort s Typeω@i) as (s & i & ->)
    by (destruct HS as [i |]; [ exists relevant, i | exists propositional, 0 ]; reflexivity).
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  destruct HAs as [R HR _ _].
  pose proof (per_ctx_then_per_env_initial_env HR) as [ρ0 [ρ0' [Hρ0 [_ Hρ]]]].
  functional_initial_env_rewrite_clear.
  destruct (rel_exp_of_relevance_sort_at HR (completeness_fundamental_exp _ _ _ HA) _ _ Hρ) as (a' & Ha' & <-).
  functional_eval_rewrite_clear.
  exists i; exact HA.
Qed.

(** Types each below the other have one normal form
    ([rel_type_of_mutual_subtyp]). *)
Lemma nbe_ty_of_mutual_subtyp : forall {Γ A A'},
    Γ ⊢ A ⊆ A' -> Γ ⊢ A' ⊆ A -> exists W, nbe_ty_f Γ A W /\ nbe_ty_f Γ A' W.
Proof.
  intros * H H'.
  destruct (rel_type_of_mutual_subtyp (completeness_fundamental_subtyp _ _ _ H) (completeness_fundamental_subtyp _ _ _ H'))
    as [i Hi].
  exact (nbe_ty_of_rel_type Hi).
Qed.

(** Completeness for types equal at a sort: one normal form. *)
Lemma completeness_ty_sort : forall {Γ S A B},
    type_sort S -> Γ ⊢ A ≈ B : S -> exists W, nbe_ty_f Γ A W /\ nbe_ty_f Γ B W.
Proof.
  intros * [i |] H; [ exact (completeness_ty H) |].
  destruct (completeness H) as (W & H1 & H2); exists W; split; apply nbe_prop_to_nbe_ty; assumption.
Qed.

(** An equation at a sort, between types one of which is of a large
    universe, is at a large universe. *)
Lemma exp_eq_sort_large : forall {Γ A B S k},
    type_sort S -> Γ ⊢ A ≈ B : S -> Γ ⊢ A : Typeω@k \/ Γ ⊢ B : Typeω@k ->
    exists k', Γ ⊢ A ≈ B : Typeω@k'.
Proof.
  intros * [i |] H Hk; [ eauto |].
  exfalso; assert (Γ ⊢ A : Propₘ /\ Γ ⊢ B : Propₘ) as [] by (gen_presups; split; assumption).
  destruct Hk; eapply typ_prop_absurd; eassumption.
Qed.

(** Two equations of types at sorts compose, at a sort. *)
Lemma exp_eq_trans_sort : forall {Γ A B C S S'},
    type_sort S -> type_sort S' -> Γ ⊢ A ≈ B : S -> Γ ⊢ B ≈ C : S' ->
    exists S'', type_sort S'' /\ Γ ⊢ A ≈ C : S''.
Proof.
  intros * [i |] [j |] H1 H2.
  - eexists; split; [ constructor | eapply exp_eq_trans_typ_max; eassumption ].
  - exfalso; assert (Γ ⊢ B : Typeω@i /\ Γ ⊢ B : Propₘ) as [] by (gen_presups; split; assumption).
    eapply typ_prop_absurd; eassumption.
  - exfalso; assert (Γ ⊢ B : Typeω@j /\ Γ ⊢ B : Propₘ) as [] by (gen_presups; split; assumption).
    eapply typ_prop_absurd; eassumption.
  - exists Propₘ; split; [ constructor | etransitivity; eassumption ].
Qed.

(** A term of a type is one of a type equal to it at a sort. *)
Lemma exp_conv_sort : forall {Γ M A A' S},
    type_sort S -> Γ ⊢ A ≈ A' : S -> Γ ⊢ M : A -> Γ ⊢ M : A'.
Proof.
  intros * HS H HM.
  assert (Γ ⊢ A : S /\ Γ ⊢ A' : S) as [] by (gen_presups; split; assumption).
  eapply wf_exp_subtyp'; [ exact HM | eapply proj1, wf_subtyp_of_exp_eq; eassumption ].
Qed.

(** No type of a large universe is below a proposition. *)
Lemma subtyp_relevant_prop_absurd : forall {Γ A A' i},
    Γ ⊢ A ⊆ A' -> Γ ⊢ A : Typeω@i -> Γ ⊢ A' : Propₘ -> False.
Proof. intros * Hs HA HA'; discriminate (subtyp_same_relevance Γ A A' relevant propositional i 0 Hs HA HA'). Qed.

(** No proposition is below a type of a large universe. *)
Lemma subtyp_prop_relevant_absurd : forall {Γ A A' i},
    Γ ⊢ A ⊆ A' -> Γ ⊢ A : Propₘ -> Γ ⊢ A' : Typeω@i -> False.
Proof. intros * Hs HA HA'; discriminate (subtyp_same_relevance Γ A A' propositional relevant 0 i Hs HA HA'). Qed.

(** [Π] congruence over a domain of a sort ([type_sort]): a type or a
    proposition. *)
Lemma pi_cong_sort : forall {Θ Ξ Γ A A' B B' Sd i},
    type_sort Sd -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Sd -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Sd -> Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Typeω@j.
Proof.
  intros * [k |] HA HAA HB.
  - exists (max k i); eapply wf_exp_eq_pi_cong_large;
      [ eapply lift_exp_max_left; exact HA | eapply lift_exp_eq_max_left; exact HAA | eapply lift_exp_eq_max_right; exact HB ].
  - exists i; change (Typeω@i) with (relevance_sort relevant Typeω@i) at 1.
    eapply wf_exp_eq_pi_cong; [ apply wf_is_univ_large; gen_presups; assumption | exact HA | apply pi_domain_prop
                              | exact HAA | exact HB ].
Qed.

(** [∀ₚ] congruence over a domain of a sort ([type_sort]). *)
Lemma all_cong_sort : forall {Θ Ξ Γ A A' P P' Sd},
    type_sort Sd -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Sd -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Sd -> Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ P ≈ P' : Propₘ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ∀ₚ A P ≈ ∀ₚ A' P' : Propₘ.
Proof.
  intros * HS HA HAA HP.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
  destruct HS as [k |]; [ change Propₘ with (relevance_sort propositional Typeω@k)
                        | change Propₘ with (relevance_sort propositional Typeω@0) ].
  all: eapply wf_exp_eq_pi_cong; [ apply wf_is_univ_large; assumption | exact HA | constructor | exact HAA | exact HP ].
Qed.

(** A [Π] is a type of a large universe: of the universe it is in, or of
    every large one above the small one it is in. *)
Lemma wf_pi_typed_large : forall {Γ A B C}, Γ ⊢ Π A B : C -> exists k, Γ ⊢ Π A B : Typeω@k.
Proof.
  intros * H.
  destruct (wf_pi_inversion H) as [(i & HA & HB & _) | (L & n & HL & HA & HB & _)].
  - exists i; change (Typeω@i) with (relevance_sort relevant Typeω@i).
    assert (⊢ Γ) by (gen_presups; assumption).
    destruct HA; (eapply wf_pi; [ apply wf_is_univ_large; assumption | eassumption | constructor | exact HB ]).
  - exists 0; eapply wf_exp_subtyp'; [| eapply wf_subtyp_small_large; [ gen_presups; assumption | exact HL ] ].
    change (Type⟨L⟩) with (relevance_sort relevant Type⟨L⟩).
    destruct HA; (eapply wf_pi; [ eapply wf_is_univ_small; exact HL | eassumption | constructor | exact HB ]).
Qed.

(** A typed proposition former, [⊤], [⊥], a [∀ₚ] or a [Σₚ], is a
    proposition. *)
Lemma prop_former_typed : forall {Γ A C},
    Γ ⊢ A : C -> (A = ⊤ \/ A = ⊥ \/ (exists B P, A = ∀ₚ B P) \/ (exists P Q, A = Σₚ P Q)) ->
    Γ ⊢ A : Propₘ.
Proof.
  intros * H [-> | [-> | [(B & P & ->) | (P & Q & ->)]]].
  - apply wf_True; gen_presups; assumption.
  - apply wf_False; gen_presups; assumption.
  - destruct (wf_all_inversion _ _ _ _ _ _ H) as [S HS HB HP _].
    assert (⊢ Γ) by (gen_presups; assumption).
    destruct HS as [j |].
    + refine (wf_pi _ _ _ Typeω@j _ _ propositional _ _ HB _ _); [ apply wf_is_univ_large; assumption | constructor | exact HP ].
    + refine (wf_pi _ _ _ Typeω@0 _ _ propositional _ _ HB _ _); [ apply wf_is_univ_large; assumption | constructor | exact HP ].
  - destruct (wf_and_inversion _ _ _ _ _ _ H) as [HP HQ _].
    apply wf_and; assumption.
Qed.

(** A [Π], a type of a large universe, is below no [∀], a proposition
    ([subtyp_same_relevance]). *)
Lemma subtyp_pi_all_absurd : forall {Γ A B X Y},
    Γ ⊢ Π A B ⊆ ∀ₚ X Y -> False.
Proof.
  intros * Hs.
  assert (exists C, Γ ⊢ Π A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_large HC) as [k Hk].
  assert (exists C', Γ ⊢ ∀ₚ X Y : C') as [C' HC'] by (gen_presups; eexists; eassumption).
  pose proof (prop_former_typed HC' ltac:(eauto 6)) as Hp.
  discriminate (subtyp_same_relevance Γ _ _ relevant propositional k k Hs Hk Hp).
Qed.

(** Extended by equal types, a context refines the other extension. *)
Lemma sub_id_extend_of_exp_eq : forall {Γ A A' S},
    type_sort S -> Γ ⊢ A ≈ A' : S -> Γ ▹ A ⊢ˢ Id : Γ ▹ A'.
Proof.
  intros * HS H.
  assert (HId : Γ ⊢ˢ Id : Γ) by (gen_presups; mauto 3).
  assert (Γ ⊢ A : S /\ Γ ⊢ A' : S) as [] by (gen_presups; split; assumption).
  eapply wf_sub_id_extend; [ exact HId | eassumption | exact HS | eassumption | exact HS |].
  eapply proj1, wf_subtyp_of_exp_eq; eassumption.
Qed.

(** Two types, each of [Typeω@i] or of [Prop], with one normal form are
    equal at one of the two sorts: a type of [Typeω@i] and a proposition
    with one normal form would be subtypes of each other, which they are
    not ([subtyp_same_relevance]). *)
Lemma exp_eq_of_nbe_ty_same : forall {Γ A A' i W},
    Γ ⊢ A : Typeω@i \/ Γ ⊢ A : Propₘ ->
    Γ ⊢ A' : Typeω@i \/ Γ ⊢ A' : Propₘ ->
    nbe_ty_f Γ A W ->
    nbe_ty_f Γ A' W ->
    Γ ⊢ A ≈ A' : Typeω@i \/ Γ ⊢ A ≈ A' : Propₘ.
Proof.
  intros * HA HA' Hn Hn'.
  assert (Hcross : forall S S' (r r' : relevance), S = relevance_sort r Typeω@i -> S' = relevance_sort r' Typeω@i ->
            Γ ⊢ A : S -> Γ ⊢ A' : S' -> r = r').
  { intros S S' r r' -> -> HAS HAS'.
    assert (HS : type_sort (relevance_sort r Typeω@i)) by (destruct r; constructor).
    assert (HS' : type_sort (relevance_sort r' Typeω@i)) by (destruct r'; constructor).
    pose proof (soundness_ty_at_sort HS HAS Hn) as E.
    pose proof (soundness_ty_at_sort HS' HAS' Hn') as E'.
    assert (HW : Γ ⊢ W : relevance_sort r Typeω@i) by (gen_presups; assumption).
    assert (HW' : Γ ⊢ W : relevance_sort r' Typeω@i) by (gen_presups; assumption).
    destruct (wf_subtyp_of_exp_eq _ _ _ _ _ _ HAS HW HS E) as [Hs1 _].
    destruct (wf_subtyp_of_exp_eq _ _ _ _ _ _ HAS' HW' HS' E') as [_ Hs2].
    exact (subtyp_same_relevance _ _ _ _ _ _ _ (wf_subtyp_trans _ _ _ _ _ _ Hs1 Hs2) HAS HAS'). }
  destruct HA as [HA | HA], HA' as [HA' | HA'].
  - left; etransitivity; [| symmetry ]; eapply soundness_ty_at_sort; first [ eassumption | constructor ].
  - exfalso; discriminate (Hcross _ _ relevant propositional eq_refl eq_refl HA HA').
  - exfalso; discriminate (Hcross _ _ propositional relevant eq_refl eq_refl HA HA').
  - right; etransitivity; [| symmetry ]; eapply soundness_ty_at_sort; first [ eassumption | constructor ].
Qed.

(** [Π] is injective.  Its domain may be a type or a proposition, so the
    domains are equal at [Typeω@i] or at [Prop] ([wf_pi_inversion']). *)
Lemma exp_eq_pi_inversion : forall {Γ A B A' B' i},
    Γ ⊢ Π A B ≈ Π A' B' : Typeω@i ->
    (Γ ⊢ A ≈ A' : Typeω@i \/ Γ ⊢ A ≈ A' : Propₘ) /\ Γ ▹ A ⊢ B ≈ B' : Typeω@i.
Proof.
  intros * H.
  gen_presups.
  (on_all_hyp: fun H => apply wf_pi_inversion' in H; destruct H).
  (on_all_hyp: fun H => apply completeness_ty in H).
  (on_all_hyp: fun H => pose proof (soundness H)).
  destruct_conjs.
  directed_inversion_clear_by_head nbe.
  directed_inversion_clear_by_head nbe_ty.
  directed_inversion_by_head initial_env; subst.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  directed_inversion_by_head read_typ; subst.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  autoinjections.
  match goal with
  | HA : Γ ⊢ A : Typeω@i \/ Γ ⊢ A : Propₘ, HA' : Γ ⊢ A' : Typeω@i \/ Γ ⊢ A' : Propₘ |- _ =>
      assert (Hdom : Γ ⊢ A ≈ A' : Typeω@i \/ Γ ⊢ A ≈ A' : Propₘ)
        by (eapply exp_eq_of_nbe_ty_same; [ exact HA | exact HA' | econstructor; eassumption | econstructor; eassumption ])
  end.
  (** The codomains, relevant types, read back alike *)
  repeat match goal with Hb : nbe_term _ _ _ _ _ 𝕌ω@_ _ |- _ =>
    let Hp := fresh "Hp" in let Hr := fresh "Hr" in
    destruct Hb as [Hp | ? ? _ ? Hr]; [ cbn in Hp; discriminate |];
    inversion Hr; subst; try (cbn in *; discriminate); clear Hr end.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  split; [ exact Hdom |].
  (** [Γ ▹ A] refines [Γ ▹ A'] because the two heads are equal, and
      [ctxsub_exp_eq] moves the codomain's normal form across. *)
  assert (Γ ▹ A ⊢ˢ Id : Γ ▹ A')
    by (destruct Hdom as [Hd | Hd]; eapply sub_id_extend_of_exp_eq; [ constructor | exact Hd | constructor | exact Hd ]).
  etransitivity; [| symmetry]; mauto 3.
Qed.

(** [∀] is injective: two equal propositions [∀] have domains equal at a
    sort and propositions equal under the left domain.  Their normal forms
    are one [∀ₚⁿ]: its domain is both domains' normal form, its body both
    bodies', the right one moved to the left domain ([ctxeq_nbe_eq]). *)
Lemma exp_eq_all_inversion : forall {Γ A P A' P'},
    Γ ⊢ ∀ₚ A P ≈ ∀ₚ A' P' : Propₘ ->
    (exists S, type_sort S /\ Γ ⊢ A ≈ A' : S) /\ Γ ▹ A ⊢ P ≈ P' : Propₘ.
Proof.
  intros * H.
  assert (Γ ⊢ ∀ₚ A P : Propₘ /\ Γ ⊢ ∀ₚ A' P' : Propₘ) as [H1 H2] by (gen_presups; split; assumption).
  destruct (wf_all_inversion _ _ _ _ _ _ H1) as [SA HS HA HP _].
  destruct (wf_all_inversion _ _ _ _ _ _ H2) as [SA' HS' HA' HP' _].
  destruct (completeness_ty_sort type_sort_prop H) as (W & [ρ a Hi Ha Hr] & [ρ' a' Hi' Ha' Hr']).
  functional_initial_env_rewrite_clear.
  inversion Ha; subst; inversion Ha'; subst.
  inversion Hr; subst; inversion Hr'; subst.
  functional_read_rewrite_clear.
  (** The domains: one normal form, so equal at a sort *)
  match goal with
  | HeA : ⟦ A ⟧ ρ ↘ ?a0, HrA : Rtyp ?a0 in length Γ ↘ ?WA, HeA' : ⟦ A' ⟧ ρ ↘ ?a0', HrA' : Rtyp ?a0' in length Γ ↘ ?WA |- _ =>
      assert (HnA : nbe_ty_f Γ A WA) by (econstructor; eassumption);
      assert (HnA' : nbe_ty_f Γ A' WA) by (econstructor; eassumption)
  end.
  assert (HdA : exists S0, type_sort S0 /\ Γ ⊢ A ≈ A' : S0).
  { destruct HS as [k |], HS' as [k' |].
    - destruct (exp_eq_of_nbe_ty_same (i := max k k') (or_introl ltac:(eapply lift_exp_max_left; exact HA))
                  (or_introl ltac:(eapply lift_exp_max_right; exact HA')) HnA HnA')
        as [Hd | Hd]; eexists; (split; [ constructor | exact Hd ]).
    - destruct (exp_eq_of_nbe_ty_same (i := k) (or_introl HA) (or_intror HA') HnA HnA') as [Hd | Hd];
        eexists; (split; [ constructor | exact Hd ]).
    - destruct (exp_eq_of_nbe_ty_same (i := k') (or_intror HA) (or_introl HA') HnA HnA') as [Hd | Hd];
        eexists; (split; [ constructor | exact Hd ]).
    - destruct (exp_eq_of_nbe_ty_same (i := 0) (or_intror HA) (or_intror HA') HnA HnA') as [Hd | Hd];
        eexists; (split; [ constructor | exact Hd ]). }
  split; [ exact HdA |].
  destruct HdA as (S0 & HS0 & HAA).
  (** The bodies: one normal form, in the left domain's context *)
  assert (HΓA : ⊢ Γ ▹ A) by (gen_presups; assumption).
  assert (HId : Γ ▹ A ⊢ˢ Id : Γ ▹ A') by exact (sub_id_extend_of_exp_eq HS0 HAA).
  assert (HP'A : Γ ▹ A ⊢ P' : Propₘ) by (eapply ctxsub_exp; [ exact HId | exact HP' ]).
  assert (Hsem : ⊨ Γ ▹ A' ≈ Γ ▹ A).
  { destruct (rel_type_of_sort HS0 (completeness_fundamental_exp_eq _ _ _ _ ltac:(symmetry; exact HAA))) as [k Hk].
    eapply per_ctx_extend_type; [| exact Hk ].
    apply rel_ctx_wf_per_ctx, completeness_fundamental_ctx; gen_presups; assumption. }
  destruct (ctxeq_nbe_eq _ _ _ _ HP' Hsem) as (WP' & HWP1 & HWP2).
  apply nbe_prop_to_nbe_ty in HWP1, HWP2.
  match goal with
  | HeP : ⟦ P ⟧ ρ ↦ relevant_value ?a0 ⇑! ?a0 (length Γ) ↘ ?b, HrP : Rtyp ?b in S (length Γ) ↘ ?WP,
    HeA : ⟦ A ⟧ ρ ↘ ?a0,
    HeP' : ⟦ P' ⟧ ρ ↦ relevant_value ?a0' ⇑! ?a0' (length Γ) ↘ ?b', HrP' : Rtyp ?b' in S (length Γ) ↘ ?WP,
    HeA' : ⟦ A' ⟧ ρ ↘ ?a0' |- _ =>
      assert (HnP : nbe_ty_f (Γ ▹ A) P WP) by (econstructor; [ econstructor; eassumption | eassumption | exact HrP ]);
      assert (HnP' : nbe_ty_f (Γ ▹ A') P' WP) by (econstructor; [ econstructor; eassumption | eassumption | exact HrP' ])
  end.
  pose proof (functional_nbe_ty _ _ _ _ HWP1 HnP') as <-.
  etransitivity; [| symmetry ]; eapply soundness_ty_at_sort; first [ constructor | eassumption ].
Qed.

(** ** The Parameters of an Inductive Type

    The normal form of an inductive type is the type former at the normal
    forms of its parameters, each equal to its parameter; so equal
    inductive types have equal parameters. *)
Lemma nbe_ty_ind_params : forall Γ p D k Mk Ms W, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ Γ ->
    List.length Ms = im_np D Mk ->
    (forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T -> Γ ⊢ P : T) ->
    nbe_ty_f Γ (apps (a_ind p k) Ms) W ->
    exists Rs, W = nf_indty p k Rs /\ exps_eq_at Γ (im_params D Mk) Ms (List.map nf_to_exp Rs).
Proof.
  (* PENDING M2: read off the gluing of the parameters (Soundness.Inductives.Args) *)
Admitted.

(** A type whose normal form is an inductive type is equal to the type
    former at typed parameters, whose normal forms the normal form has. *)
Lemma typ_ind_shape : forall Γ T i p k Rs, Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T (nf_indty p k Rs) ->
    exists D Mk Ps, ind_lookup gc_deps gc_stack p = Some D /\ ind_member D k = Some Mk /\ List.length Ps = im_np D Mk /\
      (forall j P A, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some A -> Γ ⊢ P : A) /\
      Γ ⊢ T ≈ apps (a_ind p k) Ps : Typeω@i /\ exps_eq_at Γ (im_params D Mk) Ps (List.map nf_to_exp Rs).
Proof.
  (* PENDING M2: read off the gluing of the inductive type (Soundness.Inductives.Args) *)
Admitted.

Corollary exp_eq_ind_apps_inv : forall Γ p D k Mk X Y i, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    Γ ⊢ apps (a_ind p k) X ≈ apps (a_ind p k) Y : Typeω@i ->
    List.length X = im_np D Mk -> List.length Y = im_np D Mk ->
    (forall j P T, List.nth_error X j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id X) j = Some T -> Γ ⊢ P : T) ->
    (forall j P T, List.nth_error Y j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Y) j = Some T -> Γ ⊢ P : T) ->
    exps_eq_at Γ (im_params D Mk) X Y.
Proof.
  intros * Hl Hk H HXl HYl HXt HYt.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (completeness_ty H) as (W & HWX & HWY).
  destruct (nbe_ty_ind_params _ _ _ _ _ _ _ Hl Hk HΓ HXl HXt HWX) as (Rs & -> & HX).
  destruct (nbe_ty_ind_params _ _ _ _ _ _ _ Hl Hk HΓ HYl HYt HWY) as (Rs' & E & HY).
  injection E as <-.
  destruct HX as [L1 H1]; destruct HY as [L2 H2]; split; [ congruence |].
  eapply (params_eq_trans _ p D k Mk X (List.map nf_to_exp Rs) Y Hl Hk HΓ); [ exact HXl | congruence | congruence | exact H1 |].
  eapply (params_eq_sym _ p D k Mk Y (List.map nf_to_exp Rs) Hl Hk HΓ); [ exact HYl | congruence | exact H2 ].
Qed.

Lemma nf_of_pi : forall {Γ M A B},
    Γ ⊢ M : Π A B ->
    exists W1 W2, nbe_f Γ M (Π A B) λⁿ W1 W2.
Proof.
  intros * HM; destruct (soundness HM) as [W [Hn _]].
  pose proof Hn as Hn0.
  destruct Hn as [ρ a Hi Ha Hr].
  inversion Ha; subst.
  (** A function is relevant, and read back as a [λ] *)
  destruct Hr as [Hp | m w Hrel Hm Hw]; [ cbn in Hp; discriminate |].
  inversion Hw; subst; try (cbn in *; discriminate).
  do 2 eexists; exact Hn0.
Qed.
Hint Resolve nf_of_pi : mctt.

Theorem canonical_form_of_pi : forall {M A B},
    ⋅ ⊢ M : Π A B ->
    exists W1 W2, nbe_f ⋅ M (Π A B) λⁿ W1 W2.
Proof. mauto 3. Qed.
Hint Resolve canonical_form_of_pi : mctt.

(** ** Small Universes Are Injective

    Two small universes are equal only at equal levels: their values are
    related, so their levels are ([per_univ_elem_core_suniv]), so the two
    level terms have the same normal form, and soundness turns that into an
    equation. *)
Lemma exp_eq_suniv_tm_inj : forall {Γ t t' k},
    Γ ⊢ Type⟨t⟩ ≈ Type⟨t'⟩ : Typeω@k ->
    exists n, Γ ⊢ t ≈ t' : Level@n.
Proof.
  intros * H.
  assert (exists n, Γ ⊢ t : Level@n) as [n1 Ht] by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  assert (exists n, Γ ⊢ t' : Level@n) as [n2 Ht'] by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  (** Both level terms move to the larger of their two sorts, where the
      equation is stated. *)
  assert (Γ ⊢ t : Level@(Nat.max n1 n2))
    by (eapply wf_exp_subtyp'; [ exact Ht | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
  assert (Γ ⊢ t' : Level@(Nat.max n1 n2))
    by (eapply wf_exp_subtyp'; [ exact Ht' | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
  exists (Nat.max n1 n2).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  match goal with Hl : per_lvl ?l ?l' |- _ => destruct (Hl (length Γ)) as [W [HW HW']] end.
  assert (Γ ⊢ t ≈ W : Level@(Nat.max n1 n2))
    by (eapply soundness';
        [ eassumption
        | eapply nbe_relevant_intro; [ eassumption | apply eval_exp_level | eassumption
                                     | eapply read_nf_level_sort; eassumption | reflexivity ] ]).
  assert (Γ ⊢ t' ≈ W : Level@(Nat.max n1 n2))
    by (eapply soundness';
        [ eassumption
        | eapply nbe_relevant_intro; [ eassumption | apply eval_exp_level | eassumption
                                     | eapply read_nf_level_sort; eassumption | reflexivity ] ]).
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

(** ** Subtyping of Universe Terms and Level Types

    The three universe rules and the rule for the types of levels, as a
    relation on universe terms and level types: large below large by the
    order on levels, small below small by the order on level terms, small
    below large, and [Level@m] below [Level@n] by the order on sorts. *)
Inductive univ_sub (Γ : ctx) : exp -> exp -> Prop :=
| univ_sub_large : forall i j, i <= j -> univ_sub Γ Typeω@i Typeω@j
| univ_sub_small : forall t t' n,
    Γ ⊢ t : Level@n ->
    Γ ⊢ t' : Level@n ->
    Γ ⊢ maxl t t' ≈ t' : Level@n ->
    univ_sub Γ Type⟨t⟩ Type⟨t'⟩
| univ_sub_small_large : forall t j n,
    Γ ⊢ t : Level@n ->
    univ_sub Γ Type⟨t⟩ Typeω@j
| univ_sub_level : forall m n, m <= n -> univ_sub Γ Level@m Level@n.
Hint Constructors univ_sub : mctt.

(** The two sides of [univ_sub]: a universe term or a type of levels. *)
Inductive sort_term : exp -> Prop :=
| sort_term_univ : forall U, univ_term U -> sort_term U
| sort_term_level : forall n, sort_term Level@n.
Hint Constructors sort_term : mctt.

Lemma univ_sub_sort_term : forall {Γ U V},
    univ_sub Γ U V -> sort_term U /\ sort_term V.
Proof. intros * []; split; first [ apply sort_term_level | apply sort_term_univ; constructor ]. Qed.

(** The types of levels are distinct from the universes and from [Π], and
    [Level@n] determines its sort: in each case the two values are related
    by [per_univ_elem] at the initial environment, which only relates values
    with the same head and, for the types of levels, the same sort. *)
Lemma exp_eq_level_typ_absurd : forall {Γ m i k},
    Γ ⊢ Level@m ≈ Typeω@i : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_suniv_absurd : forall {Γ m t k},
    Γ ⊢ Level@m ≈ Type⟨t⟩ : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_pi_absurd : forall {Γ m A B k},
    Γ ⊢ Level@m ≈ Π A B : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_inj : forall {Γ m n k},
    Γ ⊢ Level@m ≈ Level@n : Typeω@k ->
    m = n.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  reflexivity.
Qed.

(** A [Π] is neither a universe term nor a type of levels. *)
Lemma pi_sort_term_absurd : forall {Γ A B U k},
    sort_term U ->
    Γ ⊢ Π A B ≈ U : Typeω@k ->
    False.
Proof.
  intros * [U' HU | n] H.
  - eapply pi_univ_term_absurd; eassumption.
  - eapply exp_eq_level_pi_absurd; symmetry; exact H.
Qed.

(** Two universe or level-type subtypings compose through an equation
    between the middle ones: the two tiers and the types of levels are
    distinct, the large tier is injective on levels, the small one on level
    terms and the types of levels on sorts. *)
Lemma univ_sub_trans_eq : forall {Γ U V U' W k},
    univ_sub Γ U V ->
    Γ ⊢ V ≈ U' : Typeω@k ->
    univ_sub Γ U' W ->
    univ_sub Γ U W.
Proof.
  intros * H1 Heq H2.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct H1 as [i j Hij | t1 t2 n Ht1 Ht2 H12 | t1 j n Ht1 | m1 m2 Hm12],
           H2 as [i' j' Hij' | t3 t4 n' Ht3 Ht4 H34 | t3 j' n' Ht3 | m3 m4 Hm34].
  (** The middle universes or level types have different heads: impossible. *)
  all: try solve [ exfalso;
                   (eapply exp_eq_typ_suniv_absurd + eapply exp_eq_level_typ_absurd
                    + eapply exp_eq_level_suniv_absurd);
                   (exact Heq + (symmetry; exact Heq)) ].
  - assert (j = i') as -> by mauto 3; constructor; lia.
  - (** The order on level terms through the equation of the middle ones:
        [t1 ≤ t2 ≈ t3 ≤ t4]. *)
    (** The two orders and the equation of the middle terms are at three
        sorts; all four terms move to the largest, where they compose. *)
    destruct (exp_eq_suniv_tm_inj Heq) as [m Heqt].
    set (N := Nat.max (Nat.max n n') m).
    assert (Hup : forall k M, k <= N -> Γ ⊢ M : Level@k -> Γ ⊢ M : Level@N)
      by (intros * ? ?; eapply wf_exp_subtyp'; [ eassumption | apply wf_subtyp_level; assumption ]).
    assert (HupE : forall k M M', k <= N -> Γ ⊢ M ≈ M' : Level@k -> Γ ⊢ M ≈ M' : Level@N)
      by (intros * ? ?; eapply wf_exp_eq_subtyp'; [ eassumption | apply wf_subtyp_level; assumption ]).
    assert (Ht1N : Γ ⊢ t1 : Level@N) by (apply (Hup n); [ subst N; lia | exact Ht1 ]).
    assert (Ht2N : Γ ⊢ t2 : Level@N) by (apply (Hup n); [ subst N; lia | exact Ht2 ]).
    assert (Ht3N : Γ ⊢ t3 : Level@N) by (apply (Hup n'); [ subst N; lia | exact Ht3 ]).
    assert (Ht4N : Γ ⊢ t4 : Level@N) by (apply (Hup n'); [ subst N; lia | exact Ht4 ]).
    assert (H12N : @lvl_sub gc_deps gc_stack N Γ t1 t2)
      by (apply (HupE n); [ subst N; lia | exact H12 ]).
    assert (H34N : @lvl_sub gc_deps gc_stack N Γ t3 t4)
      by (apply (HupE n'); [ subst N; lia | exact H34 ]).
    assert (HeqtN : Γ ⊢ t2 ≈ t3 : Level@N) by (apply (HupE m); [ subst N; lia | exact Heqt ]).
    assert (H23 : @lvl_sub gc_deps gc_stack N Γ t2 t3).
    { unfold lvl_sub.
      transitivity (maxl t3 t3);
        [ apply wf_exp_eq_maxl_cong; [ exact HeqtN | apply wf_exp_eq_refl; exact Ht3N ]
        | apply wf_exp_eq_maxl_idem; exact Ht3N ]. }
    econstructor; [ exact Ht1N | exact Ht4N |].
    change (@lvl_sub gc_deps gc_stack N Γ t1 t4).
    eapply (lvl_sub_trans Ht1N Ht3N Ht4N); [| exact H34N ].
    eapply (lvl_sub_trans Ht1N Ht2N Ht3N); [ exact H12N | exact H23 ].
  - econstructor; eassumption.
  - econstructor; eassumption.
  - assert (m2 = m3) as -> by (eapply exp_eq_level_inj; exact Heq); constructor; lia.
Qed.

(** The three universe rules and the level rule are one disjunct, on
    universe terms and level types: inside a tier it is the order on levels
    or on level terms, from the small tier to the large one it is
    [wf_subtyp_small_large], and between the types of levels it is the order
    on sorts.  An equation of types, and the equation of the domains of two
    [Π]s, is at a sort ([type_sort]): a domain may be a proposition. *)
Lemma subtyp_spec : forall {Γ A B},
    Γ ⊢ A ⊆ B ->
    (exists S, type_sort S /\ Γ ⊢ A ≈ B : S) \/
      (exists U V, (exists k, Γ ⊢ A ≈ U : Typeω@k) /\ (exists k, Γ ⊢ V ≈ B : Typeω@k) /\ univ_sub Γ U V) \/
      (exists A1 A2 B1 B2, (exists k, Γ ⊢ A ≈ Π A1 A2 : Typeω@k) /\ (exists k, Γ ⊢ Π B1 B2 ≈ B : Typeω@k) /\
         (exists S, type_sort S /\ Γ ⊢ A1 ≈ B1 : S) /\ Γ ▹ B1 ⊢ A2 ⊆ B2).
Proof.
  (** The global context is an index of [wf_subtyp], so fix it for the induction. *)
  intros * H.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  induction H; subst;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end.
  - left; eexists; split; eassumption.
  - (** Transitivity: nine combinations of the two cases, of which the mixed
        universe/[Π] ones are impossible.  An equation at a sort next to a
        universe or a [Π] is at a large universe ([exp_eq_sort_large]). *)
    destruct IHwf_subtyp1 as [(S1 & HS1 & Heq1) | [[u [v [[? Hu] [[? Hv] Huv]]]] | (A1 & A2 & B1 & B2 & [? Ha1] & [? Hb1] & (S3 & HS3 & Hab1) & Hsub1)]],
             IHwf_subtyp2 as [(S2 & HS2 & Heq2) | [[u' [v' [[? Hu'] [[? Hv'] Hu'v']]]] | (C1 & C2 & D1 & D2 & [? Hc2] & [? Hd2] & (S4 & HS4 & Hcd2) & Hsub2)]];
      try pose proof (univ_sub_sort_term Huv) as [Hut Hvt];
      try pose proof (univ_sub_sort_term Hu'v') as [Hu't Hv't];
      try (assert (exists k, Γ ⊢ M ≈ M' : Typeω@k) as [? Heq1']
             by (eapply exp_eq_sort_large; [ exact HS1 | exact Heq1 | right; gen_presups; eassumption ]));
      try (assert (exists k, Γ ⊢ M' ≈ M'' : Typeω@k) as [? Heq2']
             by (eapply exp_eq_sort_large; [ exact HS2 | exact Heq2 | left; gen_presups; eassumption ])).
    (** [≈] then [≈]. *)
    + left; exact (exp_eq_trans_sort HS1 HS2 Heq1 Heq2).
    (** [≈] then a universe, and a universe then [≈]. *)
    + right; left; exists u', v'; repeat split; [| | exact Hu'v' ];
        eexists; [ eapply exp_eq_trans_typ_max; eassumption | eassumption ].
    (** [≈] then a [Π]. *)
    + right; right; exists C1, C2, D1, D2; repeat split; [| | | exact Hsub2 ];
        [ eexists; eapply exp_eq_trans_typ_max; eassumption | eexists; eassumption | exists S4; split; assumption ].
    + right; left; exists u, v; repeat split; [| | exact Huv ];
        eexists; [ eassumption | eapply exp_eq_trans_typ_max; eassumption ].
    (** A universe then a universe: the two middle universes are equal, so
        the two subtypings compose. *)
    + assert (Γ ⊢ v ≈ u' : Typeω@(max _ _))
        by (eapply exp_eq_trans_typ_max; [ exact Hv | exact Hu' ]).
      right; left; exists u, v'; repeat split;
        [ eexists; eassumption | eexists; eassumption | eapply univ_sub_trans_eq; eassumption ].
    (** A universe then a [Π], and a [Π] then a universe: impossible. *)
    + exfalso; eapply (pi_sort_term_absurd Hvt), exp_eq_trans_typ_max;
        [ symmetry; exact Hc2 | symmetry; exact Hv ].
    + right; right; exists A1, A2, B1, B2; repeat split; [| | | exact Hsub1 ];
        [ eexists; eassumption | eexists; eapply exp_eq_trans_typ_max; eassumption | exists S3; split; assumption ].
    + exfalso; eapply (pi_sort_term_absurd Hu't), exp_eq_trans_typ_max; [ exact Hb1 | exact Hu' ].
    (** A [Π] then a [Π]: the two middle [Π]s are equal, so the development
        continues with the domain and codomain of the one we keep. *)
    + assert (Γ ⊢ Π B1 B2 ≈ Π C1 C2 : Typeω@(max _ _))
        by (eapply exp_eq_trans_typ_max; [ exact Hb1 | exact Hc2 ]).
      destruct (exp_eq_pi_inversion ltac:(eassumption)) as [Hbc HB2].
      assert (Hbc' : exists S5, type_sort S5 /\ Γ ⊢ B1 ≈ C1 : S5)
        by (destruct Hbc; [ eexists; split; [ constructor | eassumption ] | exists Propₘ; split; [ constructor | eassumption ] ]).
      destruct Hbc' as (S5 & HS5 & Hbc').
      destruct (exp_eq_trans_sort HS5 HS4 Hbc' Hcd2) as (S6 & HS6 & Hbd).
      right; right.
      exists A1, A2, D1, D2; repeat split; [ eexists; eassumption | eexists; eassumption | |].
      * exact (exp_eq_trans_sort HS3 HS6 Hab1 Hbd).
      * (** The two codomain refinements live in contexts extended by the three
            equal domains, so [ctxsub_subtyp] moves both into the one we chose. *)
        assert (HD : Γ ▹ D1 ⊢ˢ Id : Γ ▹ B1) by (eapply sub_id_extend_of_exp_eq; [ exact HS6 | symmetry; exact Hbd ]).
        etransitivity; [| exact Hsub2 ].
        etransitivity; eapply ctxsub_subtyp; [ exact HD | exact Hsub1 | exact HD |].
        eapply proj1, wf_subtyp_of_exp_eq; [ | | constructor | exact HB2 ]; gen_presups; eassumption.
  (** The three universe rules and the level rule, at their own terms. *)
  - right; left; exists Typeω@i, Typeω@j;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; lia ].
  - right; left; exists Type⟨M⟩, Type⟨M'⟩;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | econstructor; eassumption ].
  - right; left; exists Level@m, Level@n;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; lia ].
  - right; left; exists Type⟨M⟩, Typeω@i;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | econstructor; eassumption ].
  - (** The [Π] rule, at its own domains and codomains *)
    right; right; exists A, B, A', B'.
    match goal with Hpd : pi_domain_sort _ ?S |- _ => assert (HS : type_sort S) by (destruct Hpd; constructor) end.
    assert (⊢ Γ) by (gen_presups; assumption).
    repeat split; [ exists i | exists i | eexists; split; [ exact HS | eassumption ] | assumption ];
      apply wf_exp_eq_refl; change (Typeω@i) with (relevance_sort relevant Typeω@i) at 1;
      eapply wf_pi; first [ eassumption | solve [ mauto 3 ] ].
Qed.

Hint Resolve subtyp_spec : mctt.

(** [subtyp_spec] where one side is of a large universe: an equation is at
    a large universe ([exp_eq_sort_large]). *)
Corollary subtyp_spec_large : forall {Γ A B k},
    Γ ⊢ A ⊆ B -> Γ ⊢ A : Typeω@k \/ Γ ⊢ B : Typeω@k ->
    (exists k, Γ ⊢ A ≈ B : Typeω@k) \/
      (exists U V, (exists k, Γ ⊢ A ≈ U : Typeω@k) /\ (exists k, Γ ⊢ V ≈ B : Typeω@k) /\ univ_sub Γ U V) \/
      (exists A1 A2 B1 B2, (exists k, Γ ⊢ A ≈ Π A1 A2 : Typeω@k) /\ (exists k, Γ ⊢ Π B1 B2 ≈ B : Typeω@k) /\
         (exists S, type_sort S /\ Γ ⊢ A1 ≈ B1 : S) /\ Γ ▹ B1 ⊢ A2 ⊆ B2).
Proof.
  intros * H Hk.
  destruct (subtyp_spec H) as [(S & HS & Heq) | Hr]; [ left; exact (exp_eq_sort_large HS Heq Hk) | right; exact Hr ].
Qed.

(** The types of levels are ordered by their sorts. *)
Lemma subtyp_level_inv : forall {Γ m n},
    Γ ⊢ Level@m ⊆ Level@n ->
    m <= n.
Proof.
  intros * H.
  assert (⊢ Γ) by (gen_presups; assumption).
  apply (subtyp_spec_large (k := 0)) in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]];
    [| | | left; apply wf_level_large; assumption ].
  - apply exp_eq_level_inj in Heq; lia.
  - destruct Hs as [i j | t t' ? | t j ? | m' n' Hmn'];
      try solve [ exfalso;
                  (eapply exp_eq_level_typ_absurd + eapply exp_eq_level_suniv_absurd);
                  (exact HU + exact HV + (symmetry; exact HV)) ].
    apply exp_eq_level_inj in HU; symmetry in HV; apply exp_eq_level_inj in HV; lia.
  - exfalso; eapply exp_eq_level_pi_absurd; exact HA.
Qed.

(** An inductive type is neither a [Π] nor a universe nor a type of levels,
    and is below only an equal one. *)
Lemma exp_eq_ind_pi_absurd : forall {Γ p m X A B k},
    Γ ⊢ apps (a_ind p m) X ≈ Π A B : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->].
  inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_ind_sort_absurd : forall {Γ p m X U k},
    sort_term U ->
    Γ ⊢ apps (a_ind p m) X ≈ U : Typeω@k ->
    False.
Proof.
  intros * HU H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->].
  destruct HU as [U' HU' | n]; [ destruct HU' |]; inversion Ha'; subst; invert_per_univ_elem HR.
Qed.

(** An inductive type is below another of the same former only by an
    equation, at its sort: a universe, or [Prop] for a propositional
    one. *)
Lemma subtyp_ind_inv : forall {Γ p m X Y},
    Γ ⊢ apps (a_ind p m) X ⊆ apps (a_ind p m) Y ->
    exists S, type_sort S /\ Γ ⊢ apps (a_ind p m) X ≈ apps (a_ind p m) Y : S.
Proof.
  intros * H.
  apply subtyp_spec in H as [Heq | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]].
  - exact Heq.
  - exfalso; destruct (univ_sub_sort_term Hs) as [HUt _]; eapply exp_eq_ind_sort_absurd; [ exact HUt | exact HU ].
  - exfalso; eapply exp_eq_ind_pi_absurd; exact HA.
Qed.

(** A type below an inductive type normalises to an inductive type, at the
    normal forms of parameters equal to the ones below. *)
Lemma subtyp_ind_nf : forall {Γ T p m D Mm Ps W}, Γ ⊢ T ⊆ apps (a_ind p m) Ps -> ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D m = Some Mm ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some A -> Γ ⊢ P : A) ->
    nbe_ty_f Γ T W ->
    exists Rs, W = nf_indty p m Rs /\ List.length (List.map nf_to_exp Rs) = im_np D Mm /\
      (forall k P R A, List.nth_error Ps k = Some P -> List.nth_error (List.map nf_to_exp Rs) k = Some R ->
         List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some A -> Γ ⊢ P ≈ R : A).
Proof.
  intros * Hs Hl Hm HPl HPt HW.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  apply subtyp_spec in Hs as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & Hsu) | (A1 & A2 & B1 & B2 & _ & [k2 Hb] & _)]].
  - destruct (completeness_ty_sort HS Heq) as (W' & HW1 & HW2).
    functional_nbe_rewrite_clear.
    destruct (nbe_ty_ind_params _ _ _ _ _ _ _ Hl Hm HΓ HPl HPt HW2) as (Rs & -> & [HL HE]).
    exists Rs; split; [ reflexivity | split; [ congruence | exact HE ] ].
  - exfalso; destruct (univ_sub_sort_term Hsu) as [_ HVt].
    eapply exp_eq_ind_sort_absurd; [ exact HVt | symmetry; exact HV ].
  - exfalso; eapply exp_eq_ind_pi_absurd; symmetry; exact Hb.
Qed.

(** ** The Parameters of a Record Type

    As for inductive types: the normal form of a record type is the type
    former at the normal forms of its parameters, each equal to its
    parameter; so equal record types have equal parameters, and a record
    type is neither a [Π] nor a universe nor a type of levels. *)

(** A record found from a well-formed context: typed, closed, and its
    parameters a telescope over the context. *)
Lemma record_params_facts : forall Γ p R, ⊢ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    record_typed gc_deps gc_stack R /\ record_closed R /\ ⊢ record_params R ++ Γ.
Proof.
  intros * HΓ Hl.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl) as Ht.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  split; [ exact Ht | split; [ exact Hc |] ].
  pose proof (record_fctx_app_wf _ _ R 0 Γ ltac:(lia) Hc (typed_params_ass _ _ _ Ht)
                (record_typed_fctx_wf _ _ _ Ht _ (le_n _)) HΓ) as H.
  change (record_fctx R 0) with (@nil centry) in H; exact H.
Qed.

Lemma nbe_ty_record_params : forall Γ p R Ms W, record_lookup gc_deps gc_stack p = Some R -> ⊢ Γ ->
    List.length Ms = List.length (record_params R) ->
    (forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (record_params R) Id Ms) j = Some T -> Γ ⊢ P : T) ->
    nbe_ty_f Γ (apps (a_record p) Ms) W ->
    exists Rs, W = nf_record p Rs /\ exps_eq_at Γ (record_params R) Ms (List.map nf_to_exp Rs).
Proof.
  (* PENDING M2: read off the gluing of the parameters (Soundness.Records.Model) *)
Admitted.

(** A type whose normal form is a record type is equal to the type former
    at typed parameters, whose normal forms the normal form has. *)
Lemma typ_record_shape : forall Γ T i p Rs, Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T (nf_record p Rs) ->
    exists R Ps, record_lookup gc_deps gc_stack p = Some R /\ List.length Ps = List.length (record_params R) /\
      (forall j P A, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (record_params R) Id Ps) j = Some A -> Γ ⊢ P : A) /\
      Γ ⊢ T ≈ apps (a_record p) Ps : Typeω@i /\ exps_eq_at Γ (record_params R) Ps (List.map nf_to_exp Rs).
Proof.
  (* PENDING M2: read off the gluing of the record type (Soundness.Inductives.Args) *)
Admitted.

Corollary exp_eq_record_apps_inv : forall Γ p R X Y i, record_lookup gc_deps gc_stack p = Some R ->
    Γ ⊢ apps (a_record p) X ≈ apps (a_record p) Y : Typeω@i ->
    List.length X = List.length (record_params R) -> List.length Y = List.length (record_params R) ->
    (forall j P T, List.nth_error X j = Some P -> List.nth_error (tele_insts (record_params R) Id X) j = Some T -> Γ ⊢ P : T) ->
    (forall j P T, List.nth_error Y j = Some P -> List.nth_error (tele_insts (record_params R) Id Y) j = Some T -> Γ ⊢ P : T) ->
    exps_eq_at Γ (record_params R) X Y.
Proof.
  intros * Hl H HXl HYl HXt HYt.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (record_params_facts _ _ _ HΓ Hl) as (Ht & Hc & HPΓ).
  pose proof (typed_params_ass _ _ _ Ht) as Hass.
  destruct (completeness_ty H) as (W & HWX & HWY).
  destruct (nbe_ty_record_params _ _ _ _ _ Hl HΓ HXl HXt HWX) as (Rs & -> & HX).
  destruct (nbe_ty_record_params _ _ _ _ _ Hl HΓ HYl HYt HWY) as (Rs' & E & HY).
  injection E as <-.
  destruct HX as [L1 H1]; destruct HY as [L2 H2]; split; [ congruence |].
  eapply (tele_eq_trans _ (record_params R) X (List.map nf_to_exp Rs) Y Hass HPΓ); [ exact HXl | congruence | congruence | exact H1 |].
  eapply (tele_eq_sym _ (record_params R) Y (List.map nf_to_exp Rs) Hass HPΓ); [ exact HYl | congruence | exact H2 ].
Qed.

Lemma exp_eq_record_pi_absurd : forall {Γ p X A B k},
    Γ ⊢ apps (a_record p) X ≈ Π A B : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_record_value _ _ _ _ Ha) as [? ->].
  inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_record_sort_absurd : forall {Γ p X U k},
    sort_term U ->
    Γ ⊢ apps (a_record p) X ≈ U : Typeω@k ->
    False.
Proof.
  intros * HU H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_record_value _ _ _ _ Ha) as [? ->].
  destruct HU as [U' HU' | n]; [ destruct HU' |]; inversion Ha'; subst; invert_per_univ_elem HR.
Qed.

(** A record type is below another of the same former only by an
    equation, at its sort, as for inductive types. *)
Lemma subtyp_record_inv : forall {Γ p X Y},
    Γ ⊢ apps (a_record p) X ⊆ apps (a_record p) Y ->
    exists S, type_sort S /\ Γ ⊢ apps (a_record p) X ≈ apps (a_record p) Y : S.
Proof.
  intros * H.
  apply subtyp_spec in H as [Heq | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]].
  - exact Heq.
  - exfalso; destruct (univ_sub_sort_term Hs) as [HUt _]; eapply exp_eq_record_sort_absurd; [ exact HUt | exact HU ].
  - exfalso; eapply exp_eq_record_pi_absurd; exact HA.
Qed.

(** A type below a record type normalises to that record type, at the
    normal forms of parameters equal to the ones below. *)
Lemma subtyp_record_nf : forall {Γ T p R Ps W}, Γ ⊢ T ⊆ apps (a_record p) Ps -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ps = List.length (record_params R) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (record_params R) Id Ps) k = Some A -> Γ ⊢ P : A) ->
    nbe_ty_f Γ T W ->
    exists Rs, W = nf_record p Rs /\ List.length (List.map nf_to_exp Rs) = List.length (record_params R) /\
      (forall k P Q A, List.nth_error Ps k = Some P -> List.nth_error (List.map nf_to_exp Rs) k = Some Q ->
         List.nth_error (tele_insts (record_params R) Id Ps) k = Some A -> Γ ⊢ P ≈ Q : A).
Proof.
  intros * Hs Hl HPl HPt HW.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  apply subtyp_spec in Hs as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & Hsu) | (A1 & A2 & B1 & B2 & _ & [k2 Hb] & _)]].
  - destruct (completeness_ty_sort HS Heq) as (W' & HW1 & HW2).
    functional_nbe_rewrite_clear.
    destruct (nbe_ty_record_params _ _ _ _ _ Hl HΓ HPl HPt HW2) as (Rs & -> & [HL HE]).
    exists Rs; split; [ reflexivity | split; [ congruence | exact HE ] ].
  - exfalso; destruct (univ_sub_sort_term Hsu) as [_ HVt].
    eapply exp_eq_record_sort_absurd; [ exact HVt | symmetry; exact HV ].
  - exfalso; eapply exp_eq_record_pi_absurd; symmetry; exact Hb.
Qed.

(** A literal of type [Level@n] is of a tier at most [n], and so is the
    constant of a level of type [Level@n]. *)
Lemma wf_llit_sort : forall {Γ o n},
    Γ ⊢ 𝕃ᵒ o : Level@n ->
    fst o <= n.
Proof.
  intros * H; destruct (wf_llit_inversion_sort _ _ _ _ _ H) as (m & Hm & Hs).
  apply subtyp_level_inv in Hs; lia.
Qed.

Lemma lvl_fold_hd_sort : forall {Γ} (l : list (nat * exp)) hd n,
    Γ ⊢ lvl_fold hd l : Level@n ->
    Γ ⊢ hd : Level@n.
Proof.
  intros Γ l; induction l as [| [k a] r IH]; cbn; intros hd n H; [ exact H |].
  apply IH in H; apply wf_maxl_inversion in H as (m & Hhd & _ & Hs).
  eapply wf_exp_subtyp'; [ exact Hhd | exact Hs ].
Qed.

Lemma lvl_exp_of_const_sort : forall {Γ c} {l : list (nat * exp)} {n},
    Γ ⊢ lvl_exp_of c l : Level@n ->
    fst c <= n.
Proof.
  intros * H.
  destruct l as [| [k a] r]; cbn in H; [ exact (wf_llit_sort H) |].
  destruct c as [[| c1] [| c2]]; try (cbn; lia);
    apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m & Hc & _ & Hs);
    apply subtyp_level_inv in Hs; apply wf_llit_sort in Hc; cbn in *; lia.
Qed.

(** The large tier is never below the small one. *)
Lemma subtyp_large_small_absurd : forall {Γ i t},
    Γ ⊢ Typeω@i ⊆ Type⟨t⟩ ->
    False.
Proof.
  intros * H.
  assert (⊢ Γ) by (gen_presups; assumption).
  apply (subtyp_spec_large (k := S i)) in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]];
    [| | | left; mauto 3 ].
  - eapply exp_eq_typ_suniv_absurd; exact Heq.
  - destruct Hs; solve [ eapply exp_eq_typ_suniv_absurd; eassumption | eapply exp_eq_level_suniv_absurd; eassumption ].
  - eapply pi_univ_term_absurd; [ apply univ_term_typ | symmetry; exact HA ].
Qed.

End Fixed_GCtx.

(** ** The Normal Forms of Small Types

    A small type's normal form is a type constructor of the small tier:
    [Prop], the placeholder type, [Level], a [Π], or a small universe at a
    literal level below the one the type lives in.  It is never a large
    universe (the large tier is not below the small one), never a
    proposition (a proposition is in no universe), and never a small
    universe at a level with an atom: such a universe is in no small
    universe at a literal level, since an atom is unbounded under some
    assignment. *)
Inductive small_typ_nf (n : nat) : nf -> Prop :=
(** The universe of propositions *)
| small_typ_nf_prop : small_typ_nf n Propⁿ
(** The placeholder type *)
| small_typ_nf_placeholder : small_typ_nf n nf_placeholder_type
(** A type of levels *)
| small_typ_nf_level : forall m, small_typ_nf n Levelⁿ@m
(** A [Π] *)
| small_typ_nf_pi : forall A B, small_typ_nf n (Πⁿ A B)
(** A small universe at a literal level below [n] *)
| small_typ_nf_univ : forall m, m < n -> small_typ_nf n Typeⁿ@m
(** An inductive type applied to its parameters.  Its sort is not
    recorded: the shape says only that it is an inductive type. *)
| small_typ_nf_indty : forall p k Ms, small_typ_nf n (nf_indty p k Ms)
(** A record type applied to its parameters; its sort is not recorded
    either. *)
| small_typ_nf_record : forall p Ms, small_typ_nf n (nf_record p Ms).
#[export]
Hint Constructors small_typ_nf : mctt.

(** ** The Normal Forms of the Types of a Universe

    The normal forms of the types of a universe [u], when they are not
    neutral: [Prop], the placeholder type, the types of levels, the [Π]s,
    the small universes whose successor level is below [u] (every small
    universe when [u] is large), and the large universes below [u].  A
    literal small universe's instance is [small_typ_nf]
    ([typ_nf_below_lit]); a large one's gives the type constructors
    ([typ_nf_below_large]). *)
Inductive typ_nf_below : universe_nf -> nf -> Prop :=
(** The universe of propositions *)
| typ_nf_below_prop : forall u, typ_nf_below u Propⁿ
(** The placeholder type *)
| typ_nf_below_placeholder : forall u, typ_nf_below u nf_placeholder_type
(** A type of levels *)
| typ_nf_below_level : forall u m, typ_nf_below u Levelⁿ@m
(** A [Π] *)
| typ_nf_below_pi : forall u A B, typ_nf_below u (Πⁿ A B)
(** A small universe whose successor level is below [u] *)
| typ_nf_below_univ : forall u c xs,
    universe_nf_le (universe_small (lvl_suc (c, xs))) u ->
    typ_nf_below u (univⁿ c xs)
(** A large universe below [u] *)
| typ_nf_below_typ : forall i j, j < i -> typ_nf_below (universe_large i) Typeωⁿ@j
(** An inductive type at its parameters *)
| typ_nf_below_indty : forall u p k Ms, typ_nf_below u (nf_indty p k Ms)
(** A record type at its parameters *)
| typ_nf_below_record : forall u p Ms, typ_nf_below u (nf_record p Ms).
#[export]
Hint Constructors typ_nf_below : mctt.

(** Below the literal [Type@n], a universe has no atom (an atom is
    unbounded below a finite literal, [lvl_le_lit_closed]) and a finite
    level below [n]. *)
Lemma typ_nf_below_lit : forall n W,
    typ_nf_below (universe_small (lvl_lit (ordinal_of_nat n))) W ->
    small_typ_nf n W.
Proof.
  intros * H; inversion H as [| | | | ? c xs Hle | | |]; subst; try constructor.
  cbn [universe_nf_le] in Hle.
  pose proof (lvl_le_lit_closed _ _ Hle) as Hxs.
  destruct xs as [| [k s a] r]; cbn in Hxs; [| discriminate ].
  rewrite lvl_le_correct in Hle; specialize (Hle _ lvl_adm_zero).
  rewrite lvl_eval_suc in Hle; unfold lvl_eval, lvl_lit in Hle; cbn in Hle.
  destruct c as [a m]; assert (a = 0) as -> by ordinal_solve.
  constructor; ordinal_solve.
Qed.

(** Below a large universe, a type constructor that is not neutral. *)
Lemma typ_nf_below_large : forall i W,
    typ_nf_below (universe_large i) W ->
    is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof.
  intros * H; inversion H; subst; (split; [ cbn; constructor | intros ? Heq; discriminate Heq ]).
Qed.

Section Small_Typ.
  Context {GC : GCtx}.

(** A small universe below another: the canonical level of its level term
    is below the other's.  Read off the semantic subtyping at the initial
    environment, where [per_subtyp_suniv] orders the readbacks. *)
Lemma subtyp_suniv_bound : forall {Γ M N L L'},
    Γ ⊢ Type⟨M⟩ ⊆ Type⟨N⟩ ->
    nbe_f Γ M Level (nf_lvl_of L) ->
    nbe_f Γ N Level (nf_lvl_of L') ->
    lvl_le L L'.
Proof.
  intros * Hs Hn Hn'.
  apply completeness_fundamental_subtyp in Hs as [R HR i Hg].
  destruct (per_ctx_then_per_env_initial_env HR) as (ρ & ρ' & Hρ & Hρ' & Hrel).
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (⊨ Γ ≈ Γ) as HsΓ by (eexists; exact HR).
  destruct (per_ctx_env_proofs _ _ _ HR _ _ Hrel) as [Hpf _].
  destruct (Hg _ _ HR _ _ (rel_sub_id HsΓ) _ _ _ _ Hrel (eval_sub_id _ _ Hpf) (eval_sub_id _ _ Hpf))
    as [aσ a a'σ' a' Ha1 Ha2 Ha3 Ha4 _ _ Hsub].
  inversion Hn; subst.
  inversion Hn'; subst.
  directed_inversion_by_head eval_exp; subst.
  invert_nbe_term.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  inversion Hsub; subst;
    (** universes are no propositions *)
    [| match goal with Hp : per_prop _ _ |- _ => destruct Hp; cbn in *; discriminate end ].
  match goal with Hl : per_sublvl _ _ |- _ =>
    destruct (Hl (length Γ)) as [L0 L1 HL0 HL1 Hle] end.
  functional_read_rewrite_clear.
  repeat match goal with H : nf_lvl_of _ = nf_lvl_of _ |- _ => apply nf_lvl_of_inj in H; subst end.
  exact Hle.
Qed.

(** The instance at a literal. *)
Corollary subtyp_suniv_lit_bound : forall {Γ M n L},
    Γ ⊢ Type⟨M⟩ ⊆ Type@n ->
    nbe_f Γ M Level (nf_lvl_of L) ->
    lvl_le L (lvl_lit (ordinal_of_nat n)).
Proof.
  intros * Hs Hn; eapply subtyp_suniv_bound; [ exact Hs | exact Hn |].
  inversion Hn; subst.
  eapply nbe_relevant_intro; [ eassumption | eassumption | apply eval_exp_llit | | directed_inversion_by_head eval_exp; reflexivity ].
  directed_inversion_by_head eval_exp; subst; mauto 3.
Qed.

(** The normal form of a small universe is the universe at the normal form of
    its level. *)
Lemma nbe_ty_univ_level : forall {Γ t L n},
    nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L) ->
    nbe_f Γ t Level@n (nf_lvl_of L).
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  match goal with H1 : fst ?L0 = fst L, H2 : snd ?L0 = snd L |- _ =>
    assert (L0 = L) as -> by (destruct L0, L; cbn in *; congruence) end.
  eapply nbe_relevant_intro; [ eassumption | apply eval_exp_level | eassumption | eapply read_nf_level_sort; eassumption | reflexivity ].
Qed.

(** The level of a small universe in normal form is a canonical level of a
    sort its level term has: its constant is of a tier at most that sort, and
    each atom is a level of its own sort ([soundness_lvl_well_scoped]). *)
Lemma univ_nf_well_scoped : forall {Γ c xs A},
    Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : A ->
    nbe_ty_f Γ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ (univⁿ c xs) ->
    exists n, Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@n /\ fst c <= n /\ @level_atoms_well_scoped gc_deps gc_stack n Γ xs.
Proof.
  intros * HA Hn.
  destruct (wf_univ_lvl_inversion HA) as [n Ht].
  pose proof (nbe_ty_univ_level (L := (c, xs)) (n := n) Hn) as Hl.
  pose proof (soundness_lvl_well_scoped Ht Hl) as Hws; cbn in Hws.
  exists n; split; [ exact Ht | exact Hws ].
Qed.

(** NbE at a small universe reads the term back as a type. *)
Lemma nbe_suniv_to_nbe_ty : forall {Γ M t W},
    nbe_f Γ M Type⟨t⟩ W ->
    nbe_ty_f Γ M W.
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  invert_nbe_term.
  match goal with Hr : Rnf ⇓ _ _ in _ ↘ _ |- _ => inversion Hr; subst; try (cbn in *; discriminate) end.
  econstructor; eassumption.
Qed.

(** A small universe at a literal level reads back as itself. *)
Lemma nbe_ty_suniv_lit : forall {Γ n W},
    nbe_ty_f Γ Type⟨𝕃ᵒ n⟩ W ->
    W = nf_univ n nil.
Proof.
  intros * Hn.
  directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst.
  match goal with H : eval_exp _ _ (a_llit _) _ _ |- _ => inversion H; subst end.
  directed_inversion_by_head read_typ; subst.
  match goal with H : Rnf ⇓ Levelᵈ (domain_level_lit n) in _ ↘ _ |- _ =>
    pose proof (read_nf_domain_level_lit n (length Γ)) as Hk;
    assert (L = lvl_lit n) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption) end.
  reflexivity.
Qed.

(** The large universes are ordered by their indices. *)
Lemma subtyp_large_inv : forall {Γ i j},
    Γ ⊢ Typeω@i ⊆ Typeω@j ->
    i <= j.
Proof.
  intros * H.
  assert (⊢ Γ) by (gen_presups; assumption).
  apply (subtyp_spec_large (k := S i)) in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]];
    [| | | left; mauto 3 ].
  - apply exp_eq_typ_implies_eq_level in Heq; lia.
  - destruct Hs as [i' j' Hij | t t' ? | t j' ? | m' n' Hmn'].
    + apply exp_eq_typ_implies_eq_level in HU; symmetry in HV; apply exp_eq_typ_implies_eq_level in HV; lia.
    + exfalso; eapply exp_eq_typ_suniv_absurd; exact HU.
    + exfalso; eapply exp_eq_typ_suniv_absurd; exact HU.
    + exfalso; eapply exp_eq_level_typ_absurd; symmetry; exact HU.
  - exfalso; eapply pi_univ_term_absurd; [ apply univ_term_typ | symmetry; exact HA ].
Qed.

(** The normal form of a universe term is a universe normal form: [Typeω@i]
    is its own, and [Type⟨t⟩]'s is the universe at the normal form of [t]. *)
Lemma nbe_ty_univ_term : forall {Γ T W},
    univ_term T ->
    nbe_ty_f Γ T W ->
    exists u, W = universe_nf_to_nf u.
Proof.
  intros * HT Hn; inversion HT; subst;
    directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst;
    directed_inversion_by_head read_typ; subst.
  - exists (universe_large i); reflexivity.
  - exists (universe_small L); reflexivity.
Qed.

Lemma nbe_ty_typ_univ_nf : forall {Γ i u},
    nbe_ty_f Γ Typeω@i (universe_nf_to_nf u) ->
    u = universe_large i.
Proof.
  intros * Hn; directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst.
  destruct u; cbn in *; match goal with H : Rtyp _ in _ ↘ _ |- _ => inversion H; subst end; congruence.
Qed.

Lemma nbe_ty_suniv_univ_nf : forall {Γ t u},
    nbe_ty_f Γ Type⟨t⟩ (universe_nf_to_nf u) ->
    exists L, u = universe_small L /\ nbe_f Γ t Level (nf_lvl_of L).
Proof.
  intros * Hn; destruct u as [L | i].
  - exists L; split; [ reflexivity | exact (nbe_ty_univ_level Hn) ].
  - exfalso; directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst.
    cbn in *; match goal with H : Rtyp _ in _ ↘ _ |- _ => inversion H end.
Qed.

Lemma nbe_ty_lit_univ_nf : forall {Γ n u},
    nbe_ty_f Γ Type@n (universe_nf_to_nf u) ->
    u = universe_small (lvl_lit (ordinal_of_nat n)).
Proof.
  intros * Hn; apply nbe_ty_suniv_lit in Hn.
  destruct u as [[c xs] | i]; cbn in Hn; inversion Hn; reflexivity.
Qed.

(** NbE at a universe term reads the term back as a type. *)
Lemma nbe_univ_term_to_nbe_ty : forall {Γ T M W},
    univ_term T ->
    nbe_f Γ M T W ->
    nbe_ty_f Γ M W.
Proof. intros * [] Hn; [ eapply nbe_type_to_nbe_ty; exact Hn | eapply nbe_suniv_to_nbe_ty; exact Hn ]. Qed.

(** A type of a universe term is a type of a large universe. *)
Lemma univ_term_large : forall {Γ T M},
    univ_term T ->
    Γ ⊢ M : T ->
    exists k, Γ ⊢ M : Typeω@k.
Proof.
  intros * [i | t] HM; [ eauto |].
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (exists C, Γ ⊢ Type⟨t⟩ : C) as [C Hk] by (gen_presups; eexists; eassumption).
  destruct (wf_univ_lvl_inversion Hk) as [n Ht].
  exists 0; eapply wf_exp_subtyp'; [ exact HM | eapply wf_subtyp_small_large; eassumption ].
Qed.

(** A universe term with a term is a type of a large universe. *)
Lemma univ_term_typed_large : forall {Γ T M},
    univ_term T ->
    Γ ⊢ M : T ->
    exists k, Γ ⊢ T : Typeω@k.
Proof.
  intros * [i | t] HM; assert (⊢ Γ) by (gen_presups; assumption).
  - exists (S i); apply wf_typ; assumption.
  - assert (exists C, Γ ⊢ Type⟨t⟩ : C) as [C Hk] by (gen_presups; eexists; eassumption).
    destruct (wf_univ_lvl_inversion Hk) as [n Ht].
    exists 0; eapply wf_univ_large_tm; eassumption.
Qed.

(** The shape of the normal form of a type of a universe term, when it is
    not neutral.  A large universe [Typeω@j] in [Typeω@i] has [j < i], and is
    in no small universe; a small universe [Type⟨l⟩] in [Type⟨t⟩] has the
    successor of [l] below the normal form of [t] ([subtyp_suniv_bound]). *)
Lemma typ_nf_below_of_nbe : forall {Γ M T u W},
    univ_term T ->
    Γ ⊢ M : T ->
    nbe_ty_f Γ T (universe_nf_to_nf u) ->
    nbe_f Γ M T W ->
    (forall V, W <> ⇑ⁿ V) ->
    typ_nf_below u W.
Proof.
  intros * HT HM HnT Hn Hne.
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (HMW : Γ ⊢ M ≈ W : T) by (eapply soundness'; eassumption).
  assert (HW : Γ ⊢ W : T) by (gen_presups; assumption).
  destruct (univ_term_large HT HM) as [k HMl].
  destruct (univ_term_large HT HW) as [k' HWl].
  pose proof (nbe_univ_term_to_nbe_ty HT Hn) as Hty.
  (** A normal form is its own normal form. *)
  assert (HWW : nbe_ty_f Γ W W).
  { destruct (soundness_ty HWl) as (C & HC & _).
    assert (W = C) as <- by (exact (idempotent_nbe_ty HMl Hty HC)).
    exact HC. }
  inversion Hty; subst.
  match goal with Hr : Rtyp _ in _ ↘ W |- _ => inversion Hr; subst end.
  all: try solve [ constructor | exfalso; eapply Hne; reflexivity ].
  (** A proposition is in no universe *)
  all: try solve [ exfalso; cbn [nf_to_exp] in HWl; eapply (typ_prop_absurd HWl), (prop_former_typed HWl); eauto 6 ].
  - destruct HT as [i0 | t].
    + apply nbe_ty_typ_univ_nf in HnT as ->.
      cbn in HW; apply wf_typ_inversion, subtyp_large_inv in HW.
      constructor; lia.
    + exfalso; cbn in HW; apply wf_typ_inversion in HW; eapply subtyp_large_small_absurd; exact HW.
  - destruct L as [c xs]; unfold nf_univ_of in *; cbn [fst snd] in *.
    constructor.
    destruct HT as [i | t].
    + apply nbe_ty_typ_univ_nf in HnT as ->; exact I.
    + destruct (nbe_ty_suniv_univ_nf HnT) as (L' & -> & HL').
      cbn [universe_nf_le nf_to_exp] in *.
      set (E := lvl_exp_of c (List.map atom_exp xs)) in *.
      apply wf_univ_inversion in HW.
      assert (HL : nbe_f Γ E Level (nf_lvl_of (c, xs))) by (apply (nbe_ty_univ_level (L := (c, xs))); exact HWW).
      inversion HL; subst.
      directed_inversion_by_head eval_exp; subst.
      invert_nbe_term.
      match goal with Hr : Rnf ⇓ Levelᵈ ?l in _ ↘ _, HE : ⟦ E ⟧ _ ↘ ?l |- _ =>
        destruct (domain_level_canon_of_read _ _ _ Hr) as [Hsh [L0 [HL0 Hc]]] end.
      apply nf_lvl_of_inj in HL0; subst L0.
      (** The universe above has the successor level, whose canonical form
          is the canonical successor of [(c, xs)]. *)
      pose proof (domain_level_canon_suc _ _ _ Hc) as Hc'.
      assert (Hn' : nbe_f Γ (succl E) Level (nf_lvl_of (lvl_canon (lvl_suc (c, xs))))).
      { eapply nbe_relevant_intro; [ eassumption | eassumption | apply eval_exp_succl; eassumption
                                   | apply domain_level_canon_read; [ apply domain_level_shape_suc | exact Hc' ] | reflexivity ]. }
      pose proof (subtyp_suniv_bound HW Hn' HL') as Hle.
      rewrite lvl_le_correct in *; intros ν Hν; specialize (Hle ν Hν).
      rewrite lvl_canon_eval in Hle by exact Hν; exact Hle.
Qed.

End Small_Typ.

#[export]
Hint Resolve idempotent_nbe_ty : mctt.
#[export]
Hint Resolve nf_of_pi : mctt.
#[export]
Hint Resolve canonical_form_of_pi : mctt.
#[export]
Hint Resolve subtyp_spec : mctt.

(** In the empty context, a neutral without a global head has no type: its
    head would be a variable. *)
Lemma no_closed_neutral : forall {Θ Ξ A} {W : ne},
    ne_clean W ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A).
Proof.
  intros * HWc HW.
  dependent induction HW; try (destruct W; simpl in *; congruence);
    try solve [ eauto ].
  all: destruct W; simpl in *; try congruence; autoinjections; destruct_all;
    try contradiction; eauto.
  all: try solve [ match_by_head ctx_lookup ltac:(fun H => inversion H) ].
  (* PENDING M3: a neutral ex falso [efq ⋆ⁿ] carries the proof [⋆] of [⊥],
     typed exactly when [⊥] is proved ([wf_true_inversion]), so this case
     is consistency itself, from the model *)
  admit.
Admitted.

(** ** Canonical Forms and Consistency

    These hold only at a transparent global context: otherwise an axiom
    [c : Nat] is a closed neutral, and an axiom of type [Π Typeω@i #0] refutes
    consistency.  At a transparent context a normal form has no global head
    ([nbe_clean]), and a neutral without one has no head in the empty local
    context ([no_closed_neutral]). *)

Section Transparent_GCtx.
  Context {GC : GCtx}.
  Hypothesis Htr : gc_transparent gc_deps gc_stack.

(** There is no closed proof of [⊥]. *)
Theorem consistency_False : forall M,
    ~ ⋅ ⊢ M : ⊥.
Proof.
  (* PENDING M3: a proof of [⊥] normalises to [⋆ⁿ], which says nothing;
     consistency comes from the model, where [⊥] has no element *)
Admitted.

(** Canonicity at a universe.  A closed type of a universe term [T] has a
    normal form of the shape [typ_nf_below u], where [u] is the normal form
    of [T] ([typ_nf_below_of_nbe]): it is not neutral, since at a
    transparent context a closed neutral has no type.  At [Typeω@i] this is
    [canonical_form_of_large_typ], at [Type@n] [canonical_form_of_typ_lit]. *)
Theorem canonical_form_of_typ : forall {T M},
    univ_term T ->
    ⋅ ⊢ M : T ->
    exists u W, nbe_ty_f ⋅ T (universe_nf_to_nf u) /\ nbe_f ⋅ M T W /\ typ_nf_below u W.
Proof.
  intros * HT HM.
  destruct (soundness HM) as (W & Hn & HMW).
  destruct (univ_term_typed_large HT HM) as [k Hk].
  destruct (soundness_ty Hk) as (U & HU & _).
  destruct (nbe_ty_univ_term HT HU) as [u ->].
  exists u, W; split; [ exact HU | split; [ exact Hn |] ].
  eapply typ_nf_below_of_nbe; [ exact HT | exact HM | exact HU | exact Hn |].
  intros V ->.
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hn) as Hc; cbn in Hc.
  assert (⋅ ⊢ V : T) by (gen_presups; assumption).
  eapply no_closed_neutral; eassumption.
Qed.

Corollary canonical_form_of_large_typ : forall {i M},
    ⋅ ⊢ M : Typeω@i ->
    exists W, nbe_f ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof.
  intros * HM; destruct (canonical_form_of_typ (univ_term_typ i) HM) as (u & W & Hu & Hn & Hb).
  apply nbe_ty_typ_univ_nf in Hu as ->; exists W; split; [ exact Hn | exact (typ_nf_below_large _ _ Hb) ].
Qed.
Hint Resolve canonical_form_of_large_typ : mctt.

Corollary canonical_form_of_typ_lit : forall {n M},
    ⋅ ⊢ M : Type@n ->
    exists W, nbe_f ⋅ M Type@n W /\ small_typ_nf n W.
Proof.
  intros * HM; destruct (canonical_form_of_typ (univ_term_suniv _) HM) as (u & W & Hu & Hn & Hb).
  apply nbe_ty_lit_univ_nf in Hu as ->; exists W; split; [ exact Hn | exact (typ_nf_below_lit _ _ Hb) ].
Qed.

(** Consistency at a universe: there is no closed inhabitant of [Π T #0]
    for a universe term [T].  At [Typeω@i] this is [consistency_large], at
    [Type@n] [consistency_lit].  [⊥] is a proposition, no type of a
    universe, so this is no longer [consistency_False] at [M $ ⊥]. *)
Theorem consistency : forall T M,
    univ_term T ->
    ~ ⋅ ⊢ M : Π T #0.
Proof.
  (* PENDING M3: ⊥ is in Prop only; read the normal form λ W1 W2 of M
     ([canonical_form_of_pi]): W2 is a normal form of type #0 under one
     type variable, which has none *)
Admitted.

Corollary consistency_large : forall {i} M,
    ~ ⋅ ⊢ M : Π Typeω@i #0.
Proof. intros; apply consistency, univ_term_typ. Qed.

Corollary consistency_lit : forall {n} M,
    ~ ⋅ ⊢ M : Π Type@n #0.
Proof. intros; apply consistency, univ_term_suniv. Qed.

(** ** Canonical Forms of Inductive Types

    A closed term of an inductive type normalises to one of its
    constructors, applied to normal forms of its parameters and arguments:
    a neutral would be closed. *)
Theorem canonical_form_of_ind : forall {M p k Ps},
    ⋅ ⊢ M : apps (a_ind p k) Ps ->
    exists W, nbe_f ⋅ M (apps (a_ind p k) Ps) W /\
      exists D Mk c gs Vs, ind_lookup gc_deps gc_stack p = Some D /\ ind_member D k = Some Mk /\
        ind_con Mk c = Some gs /\ W = nf_con p k c Vs.
Proof.
  intros * HM.
  destruct (soundness HM) as (W & Hn & HMW).
  exists W; split; [ exact Hn |].
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hn) as Hc.
  assert (HW : ⋅ ⊢ W : apps (a_ind p k) Ps) by (gen_presups; assumption).
  inversion Hn as [? a Hi Ha Hnt]; subst.
  inversion Hi; subst.
  destruct (eval_ind_value _ _ _ _ _ Ha) as [ms ->].
  (** An inductive type is relevant: its terms are read back *)
  destruct Hnt as [Hp | m ? _ Hm Hr]; [ cbn in Hp; discriminate |].
  inversion Hr; subst; try (cbn in *; discriminate).
  1,2: do 5 eexists; split; [ eassumption | split; [ eassumption | split; [ eassumption | reflexivity ] ] ].
  (* a record view's value: its one constructor *)
  - do 5 eexists; split; [ eassumption | split; [ eassumption | split; [| reflexivity ] ] ].
    match goal with Hc : im_cons ?Mj = ((?c, ?gs) :: nil)%list |- ind_con ?Mj _ = _ =>
      unfold ind_con; rewrite Hc; cbn; rewrite String.eqb_refl; reflexivity end.
  - exfalso; cbn in Hc, HW; eapply no_closed_neutral; eassumption.
Qed.

(** The member of a group of the shape of the natural numbers
    ([nat_shape]), whose constructors are [z] and [s]: declared, without
    non-uniform parameters, and with the constructors [z], without
    arguments, and [s], with one recursive argument of the member itself. *)
Record nat_member_shape (z s : String.string) (Mn : imember) : Prop := mk_nat_member_shape
  { (** The member is declared *)
    nat_member_shape_decl : im_is_decl Mn = true
    (** It has no non-uniform parameter *)
  ; nat_member_shape_nparams : im_nparams Mn = nil
    (** Its constructors are [z], without arguments, and [s], with one
        recursive argument of itself *)
  ; nat_member_shape_cons : forall c gs, ind_con Mn c = Some gs -> (c = z /\ gs = nil) \/ (c = s /\ gs = ca_rec (pt_self 0 nil) :: nil) }.

Lemma nat_shape_inv : forall D z s, nat_shape D = Some (z, s) ->
    ind_uparams D = nil /\ (forall k Mk, ind_member D k = Some Mk -> k = 0 /\ nat_member_shape z s Mk).
Proof.
  intros [Δ S ms] z s H; unfold nat_shape in H; cbn in H.
  destruct Δ; [| discriminate ].
  destruct ms as [| [[pm | ? ? ? ? | ? ? ?] [|] cs] [|]]; try discriminate.
  split; [ reflexivity |].
  intros [| k] Mk Hk; cbn in Hk; [| destruct k; discriminate ].
  injection Hk as <-; split; [ reflexivity |].
  constructor; [ reflexivity | reflexivity |].
  intros c gs Hc; unfold ind_con in Hc; cbn in Hc; unfold nat_cons_shape in H.
  repeat (match type of H with context [match ?x with _ => _ end] => destruct x; try discriminate end).
  all: injection H as <- <-; cbn in Hc.
  all: repeat (match type of Hc with context [String.eqb ?a ?b] => destruct (String.eqb_spec a b) as [-> | ?]; [ injection Hc as <-; auto | ] end); discriminate.
Qed.

(** A term of the domain of a [Π] is one of the domain of a [Π] below. *)
Lemma subtyp_pi_dom_conv : forall {Γ A' B' A B N},
    Γ ⊢ Π A' B' ⊆ Π A B -> Γ ⊢ N : A -> Γ ⊢ N : A'.
Proof.
  intros * H HN.
  assert (exists C, Γ ⊢ Π A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_large HC) as [k0 Hk0].
  apply (subtyp_spec_large (k := k0)) in H
    as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & [k2 HB] & (S3 & HS3 & H13) & _)]];
    [| | | right; exact Hk0 ].
  - apply exp_eq_pi_inversion in Heq as [Hd _].
    destruct Hd; (eapply exp_conv_sort; [| symmetry; eassumption | exact HN ]); constructor.
  - exfalso; destruct (univ_sub_sort_term Hs) as [HUt _]; eapply pi_sort_term_absurd; [ exact HUt | exact HU ].
  - apply exp_eq_pi_inversion in HA as [HA _]; apply exp_eq_pi_inversion in HB as [HB _].
    assert (Γ ⊢ N : B1) by (destruct HB; (eapply exp_conv_sort; [| symmetry; eassumption | exact HN ]); constructor).
    assert (Γ ⊢ N : A1) by (eapply exp_conv_sort; [ exact HS3 | symmetry; exact H13 | assumption ]).
    destruct HA; (eapply exp_conv_sort; [| symmetry; eassumption | eassumption ]); constructor.
Qed.

(** The normal forms of a type shaped as the natural numbers
    ([nat_shape]), its constructors [z] and [s]: chains of [s] ending in
    [z]. *)
Inductive nat_chain_nf (p : qname) (z s : String.string) : nf -> Prop :=
(** The constructor [z] *)
| nat_chain_nf_zero : nat_chain_nf p z s (nf_con p 0 z nil)
(** The constructor [s] at a chain *)
| nat_chain_nf_succ : forall W, nat_chain_nf p z s W -> nat_chain_nf p z s (nf_con p 0 s (cons W nil)).

(** The number of constructors of one argument heading a normal form: the
    number a chain of [s] ending in [z] stands for. *)
Definition nf_succ_depth (W : nf) : nat :=
  (fix go (W : nf) : nat :=
     match W with
     | nf_con _ _ _ (cons V nil) => S (go V)
     | _ => 0
     end) W.

(** The readback of a value of a type of the shape of the natural numbers
    at that type, one step: the constructor [z], the constructor [s] at the
    readback of a value of the same type, or a neutral. *)
Inductive nat_read_step (p : qname) (z s : String.string) : nf -> Prop :=
(** The constructor [z] *)
| nat_read_step_zero : nat_read_step p z s (nf_con p 0 z nil)
(** The constructor [s] at the readback of a value of the same type *)
| nat_read_step_succ : forall v V, Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ V ->
    nat_read_step p z s (nf_con p 0 s (cons V nil))
(** A neutral *)
| nat_read_step_neut : forall M, nat_read_step p z s ⇑ⁿ M.

Lemma nat_read_step_of_read : forall p D z s W v, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ W -> nat_read_step p z s W.
Proof.
  intros * Hl Hs Hr; destruct (nat_shape_inv _ _ _ Hs) as (Hnu & Hms).
  inversion Hr; subst; try (cbn in *; discriminate); [| | | constructor ].
  all: match goal with H : ind_lookup _ _ _ = Some ?D0 |- _ => assert (D0 = D) as -> by congruence end.
  all: match goal with H : ind_member _ 0 = Some _ |- _ => destruct (Hms _ _ H) as [_ [Hdec Hnp Hcs]] end.
  (** A view, or a record view, is not a declared member. *)
  2: match goal with H : im_head _ = mh_view _ _ _ _ |- _ => unfold im_is_decl in Hdec; rewrite H in Hdec; discriminate end.
  2: match goal with H : im_head _ = mh_record _ _ _ |- _ => unfold im_is_decl in Hdec; rewrite H in Hdec; discriminate end.
  match goal with H : ind_con _ _ = Some _ |- _ => destruct (Hcs _ _ H) as [[-> ->] | [-> ->]] end.
  all: unfold im_params, im_np, im_nn, ind_nu in *; rewrite Hnu, Hnp in *; cbn in *.
  all: match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  all: match goal with H : Rcargs _ at _ of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  1: constructor.
  match goal with H : Rcargs _ at nil of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  match goal with H : Rsh _ at _ of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  match goal with H : ⟦ nil ⟧* _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  cbn; econstructor; eassumption.
Qed.

(** An inductive type is below no [Π]. *)
Lemma subtyp_ind_pi_absurd : forall {Γ p m X A B},
    Γ ⊢ apps (a_ind p m) X ⊆ Π A B -> False.
Proof.
  intros * H.
  assert (exists C, Γ ⊢ Π A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_large HC) as [k0 Hk0].
  apply (subtyp_spec_large (k := k0)) in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]];
    [| | | right; exact Hk0 ].
  - eapply exp_eq_ind_pi_absurd; exact Heq.
  - destruct (univ_sub_sort_term Hs) as [HUt _]; eapply exp_eq_ind_sort_absurd; [ exact HUt | exact HU ].
  - eapply exp_eq_ind_pi_absurd; exact HA.
Qed.

(** A proposition is below no inductive type: at an environment of the
    context the proposition's value is propositional, the inductive type's
    relevant, and a subtyping keeps relevance ([per_subtyp_relevance]). *)
Lemma subtyp_prop_ind_absurd : forall {Γ A p k Ps},
    Γ ⊢ A ⊆ apps (a_ind p k) Ps -> Γ ⊢ A : Propₘ -> False.
Proof.
  intros * Hs HA.
  pose proof (completeness_fundamental_subtyp _ _ _ Hs) as [R HR k' Hsub].
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  pose proof (per_ctx_then_per_env_initial_env HR) as [ρ [ρ' [_ [_ Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (per_ctx_env_proofs _ _ _ HR _ _ Hρρ) as [Hpf _].
  destruct (Hsub _ _ HR _ _ (rel_sub_id (ex_intro _ _ HR)) _ _ _ _ Hρρ (eval_sub_id _ _ Hpf) (eval_sub_id _ _ Hpf))
    as [aσ a a'σ' a' _ Ha _ Ha' _ _ Hsa].
  pose proof (per_subtyp_relevance _ _ _ Hsa) as Hr.
  destruct (eval_ind_value _ _ _ _ _ Ha') as [ms ->].
  destruct (rel_exp_of_prop_inversion_simple_at HR HAs _ _ Hρρ) as (x' & _ & Hx' & _ & [Hl _ _]).
  functional_eval_rewrite_clear.
  rewrite Hl in Hr; discriminate Hr.
Qed.

(** A record type is no proposition: at an environment of the context its
    value is a record type, which is relevant. *)
Lemma typ_prop_record_absurd : forall {Γ p Ms}, Γ ⊢ apps (a_record p) Ms : Propₘ -> False.
Proof.
  intros * HA.
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  destruct (rel_exp_of_prop_inversion HAs) as [R [HR _]].
  pose proof (per_ctx_then_per_env_initial_env HR) as [ρ [ρ' [_ [_ Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (rel_exp_of_prop_inversion_simple_at HR HAs _ _ Hρρ) as (x & _ & Hx & _ & [Hl _ _]).
  destruct (eval_record_value _ _ _ _ Hx) as [ms ->].
  discriminate Hl.
Qed.

(** The argument of the constructor [s] of a closed term of a type of the
    shape of the natural numbers is of that type. *)
Lemma nat_succ_arg_typed : forall p D z s V, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    ⋅ ⊢ nf_con p 0 s (cons V nil) : a_ind p 0 -> ⋅ ⊢ V : a_ind p 0.
Proof.
  intros * Hl Hs HT; destruct (nat_shape_inv _ _ _ Hs) as (Hnu & Hms).
  cbn [nf_to_exp List.map apps_exp] in HT.
  apply wf_app_inversion in HT as [A B [Hf | Hf] HV HBs].
  (** A constructor is no proof of a [∀]: its codomain is a proposition,
      below no inductive type *)
  2:{ exfalso; apply (subtyp_prop_ind_absurd (Ps := nil) HBs).
      assert (Hall : ⋅ ⊢ ∀ₚ A B : Propₘ) by (gen_presups; eapply prop_former_typed; [ eassumption | eauto 6 ]).
      destruct (wf_all_inversion _ _ _ _ _ _ Hall) as [S HS HA HB _].
      change Propₘ with (Propₘ[Id,,nf_to_exp V]); mauto 3. }
  apply wf_con_inversion in Hf as [D' Mk gs Hl' Hk Hc Hsub].
  rewrite Hl in Hl'; injection Hl' as <-.
  destruct (Hms _ _ Hk) as [_ [Hdec Hnp Hcs]].
  unfold im_is_decl in Hdec; destruct (im_head Mk) eqn:Eh; [| discriminate | discriminate ].
  destruct (Hcs _ _ Hc) as [[_ ->] | [_ ->]].
  all: unfold con_ty, im_params, cargs_ctx, im_nn in Hsub; rewrite Hnu, Hnp in Hsub; cbn in Hsub.
  all: unfold ind_mty in Hsub; rewrite Hk in Hsub.
  all: unfold im_ty_at, im_ref, im_pre in Hsub; rewrite Eh in Hsub.
  all: unfold ind_uvars, vars_from, ind_nu in Hsub; rewrite Hnu in Hsub; cbn in Hsub.
  - (** [s] without arguments is no function. *)
    exfalso; exact (subtyp_ind_pi_absurd (X := nil) Hsub).
  - exact (subtyp_pi_dom_conv Hsub HV).
Qed.

Lemma nat_chain_of_read : forall p D z s, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    forall W v, Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ W -> nf_clean W -> ⋅ ⊢ W : a_ind p 0 -> nat_chain_nf p z s W.
Proof.
  intros p D z s Hl Hs W; remember (nf_succ_depth W) as k eqn:Ek; revert W Ek.
  induction k as [| k IH]; intros W Ek v Hr Hc HT.
  all: destruct (nat_read_step_of_read _ _ _ _ _ _ Hl Hs Hr) as [| v' V Hr' | M].
  all: try (exfalso; cbn in Hc, HT; eapply no_closed_neutral; eassumption).
  - constructor.
  - cbn in Ek; discriminate.
  - constructor.
  - constructor.
    cbn in Hc; destruct_conjs.
    unfold nf_succ_depth in Ek; cbn in Ek; injection Ek as Ek.
    exact (IH V Ek v' Hr' ltac:(assumption) (nat_succ_arg_typed _ _ _ _ _ Hl Hs HT)).
Qed.

Lemma nat_chain_nf_numeral : forall p z s W, nat_chain_nf p z s W -> exists n, nf_to_exp W = nat_chain p z s n.
Proof. induction 1 as [| W _ [n IH]]; [ exists 0; reflexivity | exists (S n); cbn; rewrite IH; reflexivity ]. Qed.

(** A closed term of a type shaped as the natural numbers is a numeral:
    its normal form is the chain of constructors [nat_chain p z s n] a
    numeral stands for where the type is bound as the natural numbers. *)
Corollary canonical_form_of_ind_nat : forall {M p D z s},
    ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    ⋅ ⊢ M : a_ind p 0 ->
    exists W n, nbe_f ⋅ M (a_ind p 0) W /\ nat_chain_nf p z s W /\ nf_to_exp W = nat_chain p z s n.
Proof.
  intros * Hl Hs HM.
  destruct (soundness HM) as (W & Hn & HMW).
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hn) as Hc.
  assert (HW : ⋅ ⊢ W : a_ind p 0) by (gen_presups; assumption).
  assert (Hch : nat_chain_nf p z s W).
  { inversion Hn as [? a Hi Ha Hnt]; subst.
    inversion Hi; subst; inversion Ha; subst.
    destruct Hnt as [Hp | m ? _ Hm Hr]; [ cbn in Hp; discriminate |].
    eapply nat_chain_of_read; eassumption. }
  destruct (nat_chain_nf_numeral _ _ _ _ Hch) as [n Hnum].
  exists W, n; auto.
Qed.

End Transparent_GCtx.

#[export]
Hint Resolve canonical_form_of_large_typ : mctt.

(** The canonical forms of inductive types, with the global context
    explicit. *)
Corollary canonical_form_of_ind_gctx : forall Θ Ξ M p k Ps,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : apps (a_ind p k) Ps ->
    exists W, nbe Θ Ξ ⋅ M (apps (a_ind p k) Ps) W /\
      exists D Mk c gs Vs, ind_lookup Θ Ξ p = Some D /\ ind_member D k = Some Mk /\
        ind_con Mk c = Some gs /\ W = nf_con p k c Vs.
Proof. intros * Htr HM; exact (@canonical_form_of_ind (gc_mk Θ Ξ) Htr M p k Ps HM). Qed.

Corollary canonical_form_of_ind_nat_gctx : forall Θ Ξ M p D z s,
    gc_transparent Θ Ξ ->
    ind_lookup Θ Ξ p = Some D -> nat_shape D = Some (z, s) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : a_ind p 0 ->
    exists W n, nbe Θ Ξ ⋅ M (a_ind p 0) W /\ nat_chain_nf p z s W /\ nf_to_exp W = nat_chain p z s n.
Proof. intros * Htr Hl Hs HM; exact (@canonical_form_of_ind_nat (gc_mk Θ Ξ) Htr M p D z s Hl Hs HM). Qed.

(** The theorems above, with the global context explicit. *)
Corollary canonical_form_of_typ_gctx : forall Θ Ξ T M,
    gc_transparent Θ Ξ ->
    univ_term T ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : T ->
    exists u W, nbe_ty Θ Ξ ⋅ T (universe_nf_to_nf u) /\ nbe Θ Ξ ⋅ M T W /\ typ_nf_below u W.
Proof. intros * Htr HT HM; exact (@canonical_form_of_typ (gc_mk Θ Ξ) Htr T M HT HM). Qed.

Corollary canonical_form_of_large_typ_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof. intros * Htr HM; exact (@canonical_form_of_large_typ (gc_mk Θ Ξ) Htr i M HM). Qed.

Corollary canonical_form_of_typ_lit_gctx : forall Θ Ξ n M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ small_typ_nf n W.
Proof. intros * Htr HM; exact (@canonical_form_of_typ_lit (gc_mk Θ Ξ) Htr n M HM). Qed.

Corollary consistency_gctx : forall Θ Ξ T M,
    gc_transparent Θ Ξ ->
    univ_term T ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π T #0).
Proof. intros * Htr; exact (@consistency (gc_mk Θ Ξ) Htr T M). Qed.

Corollary consistency_large_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Typeω@i #0).
Proof. intros * Htr; exact (@consistency_large (gc_mk Θ Ξ) Htr i M). Qed.

Corollary consistency_lit_gctx : forall Θ Ξ n M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@n #0).
Proof. intros * Htr; exact (@consistency_lit (gc_mk Θ Ξ) Htr n M). Qed.

Corollary consistency_False_gctx : forall Θ Ξ M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Htr; exact (@consistency_False (gc_mk Θ Ξ) Htr M). Qed.

(** ** Opaque Definitions

    With [abstract] definitions allowed, a closed normal form of a type
    shaped as the natural numbers can be stuck: an opaque global applied to
    arguments, as [c] is in [abstract c : Nat := 3].  What survives is:

    - at the global context itself, every closed normal form of such a type
      is a chain of its constructors, or one wrapped around a neutral headed
      by a global that does not unfold ([canonical_form_of_ind_nat_stuck]),
      with no hypothesis at all;
    - without axioms that global is an opaque definition with a body, and
      after unsealing every definition the term computes to a chain, equal
      in the unsealed context to the sealed normal form
      ([canonical_form_of_ind_nat_no_axioms]);
    - without axioms there is no closed proof of [⊥]
      ([consistency_False_no_axioms]): unsealing preserves typing
      ([unseal_exp]) and produces a transparent context
      ([gc_no_axioms_unseal_transparent]). *)

(** The global at the head of a neutral, if any.  Ex falso holds no
    proof, so it has none. *)
Fixpoint ne_head (W : ne) : option qname :=
  match W with
  | ne_elim _ _ _ _ W | ne_app W _ | ne_proj _ W => ne_head W
  | ne_absurd _ | ne_var _ => None
  | ne_glob p => Some p
  end.

(** In the empty context, a neutral is headed by a global. *)
Lemma no_closed_neutral_head : forall {Θ Ξ A} {W : ne},
    ne_head W = None ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A).
Proof.
  intros * HWc HW.
  dependent induction HW; try (destruct W; simpl in *; congruence);
    try solve [ eauto ].
  all: destruct W; simpl in *; try congruence; autoinjections; destruct_all;
    try contradiction; eauto.
  all: try solve [ match_by_head ctx_lookup ltac:(fun H => inversion H) ].
  (* PENDING M3: a neutral ex falso [efq ⋆ⁿ] carries the proof [⋆] of [⊥],
     typed exactly when [⊥] is proved ([wf_true_inversion]), so this case
     is consistency itself, from the model *)
  admit.
Admitted.

Lemma closed_neutral_head : forall {Θ Ξ A} {W : ne},
    Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A ->
    exists p, ne_head W = Some p.
Proof.
  intros * HW; destruct (ne_head W) as [p |] eqn:Hh; [ eauto |].
  exfalso; exact (no_closed_neutral_head Hh HW).
Qed.

(** A chain of the constructors [z] and [s] of [p], possibly around a
    neutral whose globals satisfy [G], headed by one. *)
Inductive nat_chain_stuck (G : qname -> Prop) (p : qname) (z s : String.string) : nf -> Prop :=
(** The constructor [z] *)
| nat_chain_stuck_zero : nat_chain_stuck G p z s (nf_con p 0 z nil)
(** The constructor [s] at a chain *)
| nat_chain_stuck_succ : forall W, nat_chain_stuck G p z s W -> nat_chain_stuck G p z s (nf_con p 0 s (cons W nil))
(** A neutral headed by a global, its globals satisfying [G] *)
| nat_chain_stuck_neut : forall W h, ne_head W = Some h -> ne_stuck G W -> nat_chain_stuck G p z s ⇑ⁿ W.
#[export]
Hint Constructors nat_chain_stuck : mctt.

(** A global that is an opaque definition with a body. *)
Definition gopaque (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop :=
  exists pv r A M, gc_resolve Θ Ξ p = Some (ge_def false pv r A (Some M)).

Lemma gstuck_gopaque : forall Θ Ξ p, gc_no_axioms Θ Ξ -> gstuck Θ Ξ p -> gopaque Θ Ξ p.
Proof.
  intros * Hna [b pv r A B Hr Hb].
  pose proof (gc_no_axioms_resolve _ _ _ _ _ _ _ _ Hna Hr) as HB.
  destruct B as [M |]; [| congruence ].
  destruct Hb as [-> | ?]; [| discriminate ].
  unfold gopaque; eauto.
Qed.

Lemma nf_ne_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    (forall W, nf_stuck G W -> nf_stuck G' W) /\ (forall W, ne_stuck G W -> ne_stuck G' W).
Proof.
  intros G G' HG; apply nf_ne_ind; intros; cbn in *; destruct_all; repeat split; eauto.
  (** The lists, element by element; a block by its motive and its
      branches. *)
  all: nested_elements; cbn in *; destruct_all; eauto.
  all: split; eauto; nested_elements; cbn in *; eauto.
Qed.

Lemma nf_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall W, nf_stuck G W -> nf_stuck G' W.
Proof. intros * HG; apply (nf_ne_stuck_mono _ _ HG). Qed.

Lemma ne_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall W, ne_stuck G W -> ne_stuck G' W.
Proof. intros * HG; apply (nf_ne_stuck_mono _ _ HG). Qed.

Lemma nat_chain_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall p z s W, nat_chain_stuck G p z s W -> nat_chain_stuck G' p z s W.
Proof.
  intros * HG; induction 1; econstructor; eauto using ne_stuck_mono.
Qed.
Section Stuck_GCtx.
  Context {GC : GCtx}.

(** The normal forms of a closed term of a type shaped as the natural
    numbers, read at any global context: a chain of its constructors, possibly
    around a neutral headed by a stuck global. *)
Lemma nat_chain_stuck_of_read : forall G p D z s, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    forall W v, Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ W -> nf_stuck G W -> ⋅ ⊢ W : a_ind p 0 ->
      nat_chain_stuck G p z s W.
Proof.
  intros G p D z s Hl Hs W; remember (nf_succ_depth W) as k eqn:Ek; revert W Ek.
  induction k as [| k IH]; intros W Ek v Hr Hc HT.
  all: destruct (nat_read_step_of_read _ _ _ _ _ _ Hl Hs Hr) as [| v' V Hr' | M].
  all: try (cbn in Hc, HT; destruct (closed_neutral_head HT) as [h Hh]; eapply nat_chain_stuck_neut; eassumption).
  - constructor.
  - cbn in Ek; discriminate.
  - constructor.
  - constructor.
    cbn in Hc; destruct_conjs.
    unfold nf_succ_depth in Ek; cbn in Ek; injection Ek as Ek.
    exact (IH V Ek v' Hr' ltac:(assumption) (nat_succ_arg_typed _ _ _ _ _ Hl Hs HT)).
Qed.

(** A closed term of a type shaped as the natural numbers, at any global
    context: its normal form is a chain of the type's constructors, possibly
    around a neutral headed by a global that does not unfold. *)
Theorem canonical_form_of_ind_nat_stuck : forall {M p D z s},
    ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    ⋅ ⊢ M : a_ind p 0 ->
    exists W, nbe_f ⋅ M (a_ind p 0) W /\ nat_chain_stuck (gstuck gc_deps gc_stack) p z s W.
Proof.
  intros * Hl Hs HM.
  destruct (soundness HM) as (W & Hn & HMW).
  pose proof (nbe_stuck _ _ _ _ _ _ Hn) as Hc.
  assert (HW : ⋅ ⊢ W : a_ind p 0) by (gen_presups; assumption).
  exists W; split; [ exact Hn |].
  inversion Hn as [? a Hi Ha Hnt]; subst.
  inversion Hi; subst; inversion Ha; subst.
  destruct Hnt as [Hp | m ? _ Hm Hr]; [ cbn in Hp; discriminate |].
  eapply nat_chain_stuck_of_read; eassumption.
Qed.

(** Canonicity at a universe, at any global context: the normal form is of
    the shape [typ_nf_below u], or a neutral headed by a stuck global. *)
Theorem canonical_form_of_typ_stuck : forall {T M},
    univ_term T ->
    ⋅ ⊢ M : T ->
    exists u W, nbe_ty_f ⋅ T (universe_nf_to_nf u) /\ nbe_f ⋅ M T W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      (typ_nf_below u W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * HT HM.
  destruct (soundness HM) as (W & Hn & HMW).
  destruct (univ_term_typed_large HT HM) as [k Hk].
  destruct (soundness_ty Hk) as (U & HU & _).
  destruct (nbe_ty_univ_term HT HU) as [u ->].
  exists u, W; split; [ exact HU | split; [ exact Hn | split; [ exact (nbe_stuck _ _ _ _ _ _ Hn) |] ] ].
  assert (Hd : (exists V, W = ⇑ⁿ V) \/ (forall V, W <> ⇑ⁿ V))
    by (destruct W; try (right; intros ? Heq; discriminate Heq); left; eexists; reflexivity).
  destruct Hd as [[V ->] | Hne].
  - right; assert (HV : ⋅ ⊢ V : T) by (gen_presups; assumption).
    destruct (closed_neutral_head HV) as [p Hp]; eauto.
  - left; eapply typ_nf_below_of_nbe; eassumption.
Qed.

Corollary canonical_form_of_large_typ_stuck : forall {i M},
    ⋅ ⊢ M : Typeω@i ->
    exists W, nbe_f ⋅ M Typeω@i W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * HM; destruct (canonical_form_of_typ_stuck (univ_term_typ i) HM) as (u & W & Hu & Hn & Hs & Hc).
  apply nbe_ty_typ_univ_nf in Hu as ->; exists W; split; [ exact Hn | split; [ exact Hs |] ].
  destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_large _ _ Hb) | right; exact Hneu ].
Qed.

Corollary canonical_form_of_typ_lit_stuck : forall {n M},
    ⋅ ⊢ M : Type@n ->
    exists W, nbe_f ⋅ M Type@n W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * HM; destruct (canonical_form_of_typ_stuck (univ_term_suniv _) HM) as (u & W & Hu & Hn & Hs & Hc).
  apply nbe_ty_lit_univ_nf in Hu as ->; exists W; split; [ exact Hn | split; [ exact Hs |] ].
  destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_lit _ _ Hb) | right; exact Hneu ].
Qed.

End Stuck_GCtx.

Corollary canonical_form_of_ind_nat_stuck_gctx : forall Θ Ξ M p D z s,
    ind_lookup Θ Ξ p = Some D -> nat_shape D = Some (z, s) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : a_ind p 0 ->
    exists W, nbe Θ Ξ ⋅ M (a_ind p 0) W /\ nat_chain_stuck (gstuck Θ Ξ) p z s W.
Proof. intros * Hl Hs HM; exact (@canonical_form_of_ind_nat_stuck (gc_mk Θ Ξ) M p D z s Hl Hs HM). Qed.
Corollary canonical_form_of_typ_stuck_gctx : forall Θ Ξ T M,
    univ_term T ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : T ->
    exists u W, nbe_ty Θ Ξ ⋅ T (universe_nf_to_nf u) /\ nbe Θ Ξ ⋅ M T W /\ nf_stuck (gstuck Θ Ξ) W /\
      (typ_nf_below u W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HT HM; exact (@canonical_form_of_typ_stuck (gc_mk Θ Ξ) T M HT HM). Qed.

Corollary canonical_form_of_large_typ_stuck_gctx : forall Θ Ξ i M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ nf_stuck (gstuck Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_large_typ_stuck (gc_mk Θ Ξ) i M HM). Qed.

Corollary canonical_form_of_typ_lit_stuck_gctx : forall Θ Ξ n M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ nf_stuck (gstuck Θ Ξ) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_typ_lit_stuck (gc_mk Θ Ξ) n M HM). Qed.

(** *** Without Axioms *)

Theorem consistency_no_axioms : forall Θ Ξ T M,
    gc_no_axioms Θ Ξ ->
    univ_term T ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π T #0).
Proof.
  intros * Hna HT HM.
  exact (consistency_gctx _ _ _ _ (gc_no_axioms_unseal_transparent _ _ Hna) HT (unseal_exp _ _ _ _ _ HM)).
Qed.

Corollary consistency_large_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Typeω@i #0).
Proof. intros * Hna; apply consistency_no_axioms; [ exact Hna | apply univ_term_typ ]. Qed.

Corollary consistency_lit_no_axioms : forall Θ Ξ n M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@n #0).
Proof. intros * Hna; apply consistency_no_axioms; [ exact Hna | apply univ_term_suniv ]. Qed.

Theorem consistency_False_no_axioms : forall Θ Ξ M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof.
  intros * Hna HM.
  exact (consistency_False_gctx _ _ _ (gc_no_axioms_unseal_transparent _ _ Hna) (unseal_exp _ _ _ _ _ HM)).
Qed.

(** The sealed normal form of a closed term of a type shaped as the natural
    numbers is a chain of its constructors around a neutral headed by an
    opaque definition; unsealed, the term computes to a numeral's chain,
    which is equal to the sealed normal form once the definitions unfold. *)
Theorem canonical_form_of_ind_nat_no_axioms : forall Θ Ξ M p D z s,
    gc_no_axioms Θ Ξ ->
    ind_lookup Θ Ξ p = Some D -> nat_shape D = Some (z, s) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : a_ind p 0 ->
    exists W, nbe Θ Ξ ⋅ M (a_ind p 0) W /\ nat_chain_stuck (gopaque Θ Ξ) p z s W /\
      exists V n, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M (a_ind p 0) V /\ nat_chain_nf p z s V /\
        nf_to_exp V = nat_chain p z s n /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : a_ind p 0.
Proof.
  intros * Hna Hl Hs HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_ind_nat_stuck_gctx _ _ _ _ _ _ _ Hl Hs HM) as (W & HW & Hc).
  assert (Hl' : ind_lookup (gds_unseal Θ) (gs_unseal Ξ) p = Some D) by (rewrite ind_lookup_unseal; exact Hl).
  destruct (canonical_form_of_ind_nat_gctx _ _ _ _ _ _ _ Htr Hl' Hs HM') as (V & n & HV & HcV & Hn).
  exists W; split; [ exact HW | split ].
  - eapply nat_chain_stuck_mono; [| exact Hc ]; intros; apply gstuck_gopaque; assumption.
  - exists V, n; repeat split; [ exact HV | exact HcV | exact Hn |].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness' HM HW)).
    pose proof (soundness' HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

(** At a universe term [T]: sealed, the normal form is of the shape
    [typ_nf_below u] or a neutral headed by an opaque definition; unsealed,
    it is of the shape [typ_nf_below u'], where [u] and [u'] are the normal
    forms of [T] sealed and unsealed; and the two normal forms are equal once
    the definitions unfold. *)
Theorem canonical_form_of_typ_no_axioms : forall Θ Ξ T M,
    gc_no_axioms Θ Ξ ->
    univ_term T ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : T ->
    exists u W, nbe_ty Θ Ξ ⋅ T (universe_nf_to_nf u) /\ nbe Θ Ξ ⋅ M T W /\ nf_stuck (gopaque Θ Ξ) W /\
      (typ_nf_below u W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists u' V, nbe_ty (gds_unseal Θ) (gs_unseal Ξ) ⋅ T (universe_nf_to_nf u') /\
        nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M T V /\ typ_nf_below u' V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : T.
Proof.
  intros * Hna HT HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_typ_stuck_gctx _ _ _ _ HT HM) as (u & W & Hu & HW & Hs & Hc).
  destruct (canonical_form_of_typ_gctx _ _ _ _ Htr HT HM') as (u' & V & Hu' & HV & HcV).
  exists u, W; split; [ exact Hu | split; [ exact HW | split; [| split; [ exact Hc |] ] ] ].
  - apply (nf_stuck_mono (gstuck Θ Ξ)); [ intros; apply gstuck_gopaque; assumption | exact Hs ].
  - exists u', V; split; [ exact Hu' | split; [ exact HV | split; [ exact HcV |] ] ].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness' HM HW)).
    pose proof (soundness' HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

Corollary canonical_form_of_large_typ_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ nf_stuck (gopaque Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Typeω@i V /\ is_typ_constr V /\ (forall V', V <> ⇑ⁿ V') /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Typeω@i.
Proof.
  intros * Hna HM.
  destruct (canonical_form_of_typ_no_axioms _ _ _ _ Hna (univ_term_typ i) HM)
    as (u & W & Hu & HW & Hs & Hc & u' & V & Hu' & HV & HcV & HWV).
  apply (@nbe_ty_typ_univ_nf (gc_mk Θ Ξ)) in Hu as ->.
  apply (@nbe_ty_typ_univ_nf (gc_mk (gds_unseal Θ) (gs_unseal Ξ))) in Hu' as ->.
  exists W; split; [ exact HW | split; [ exact Hs | split ] ].
  - destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_large _ _ Hb) | right; exact Hneu ].
  - destruct (typ_nf_below_large _ _ HcV) as [HcV' HnV].
    exists V; split; [ exact HV | split; [ exact HcV' | split; [ exact HnV | exact HWV ] ] ].
Qed.

Corollary canonical_form_of_typ_lit_no_axioms : forall Θ Ξ n M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ nf_stuck (gopaque Θ Ξ) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Type@n V /\ small_typ_nf n V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Type@n.
Proof.
  intros * Hna HM.
  destruct (canonical_form_of_typ_no_axioms _ _ _ _ Hna (univ_term_suniv _) HM)
    as (u & W & Hu & HW & Hs & Hc & u' & V & Hu' & HV & HcV & HWV).
  apply (@nbe_ty_lit_univ_nf (gc_mk Θ Ξ)) in Hu as ->.
  apply (@nbe_ty_lit_univ_nf (gc_mk (gds_unseal Θ) (gs_unseal Ξ))) in Hu' as ->.
  exists W; split; [ exact HW | split; [ exact Hs | split ] ].
  - destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_lit _ _ Hb) | right; exact Hneu ].
  - exists V; split; [ exact HV | split; [ exact (typ_nf_below_lit _ _ HcV) | exact HWV ] ].
Qed.

(** *** Every Program

    A run of commands that declare no axiom, loading units that declare
    none, files no axiom ([run_no_axioms]), so the theorems above hold at
    every global context it reaches, and at what such a program files. *)

Section Programs.
  Variables (load_path : path -> option String.string) (read : String.string -> option Cst.prog)
            (to_core : Cst.prog -> option core_unit).
  Hypothesis Hload : forall prg u, to_core prg = Some u -> unit_no_axioms u.

Corollary consistency_False_run : forall ch B Rb cs B' Rb' Θ Ξ M,
    Mctt.Core.Syntactic.System.Command.run_cmds load_path read to_core ch B Rb nil nil cs B' Rb' Θ Ξ ->
    cmds_no_axioms cs ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Hr Hc; apply consistency_False_no_axioms; eapply run_cmds_no_axioms; [ exact Hload | exact Hr | exact Hc ]. Qed.

Corollary consistency_False_prog : forall prg B Θ U M,
    Mctt.Core.Syntactic.System.Command.prog_sem load_path read to_core prg B Θ U ->
    ~ (((prog_path prg, U) :: Θ) ⍮ nil ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Hp; apply consistency_False_no_axioms; eapply prog_sem_no_axioms; [ exact Hload | exact Hp ]. Qed.

(** A program's bound natural numbers: the type a program binds as the
    natural numbers is read at its end ([prog_sem_builtins_wf]), and a
    closed term of it computes, once its definitions unfold, to the chain
    of constructors a numeral stands for ([nat_chain]). *)
Corollary canonical_form_of_bound_nat_prog : forall prg B Θ U M p,
    Mctt.Core.Syntactic.System.Command.prog_sem load_path read to_core prg B Θ U ->
    let Θ' := ((prog_path prg, U) :: Θ) in
    builtins_nat B = Some p ->
    Θ' ⍮ nil ⍮ ⋅ ⊢ M : a_ind p 0 ->
    exists z s V n, nat_view Θ' nil B = Some (p, z, s) /\
      nbe (gds_unseal Θ') nil ⋅ M (a_ind p 0) V /\ nf_to_exp V = nat_chain p z s n.
Proof.
  intros * Hp Θ' Hb HM.
  pose proof (prog_sem_no_axioms _ _ _ Hload _ _ _ _ Hp) as Hna.
  pose proof (Mctt.Core.Syntactic.System.Command.prog_sem_builtins_wf _ _ _ _ _ _ _ Hp) as Hw.
  destruct (Hw _ Hb) as [D z s Hl Hs _].
  exists z, s.
  destruct (canonical_form_of_ind_nat_no_axioms _ _ _ _ _ _ _ Hna Hl Hs HM) as (_ & _ & _ & V & n & HV & _ & Hn & _).
  exists V, n; split; [ unfold nat_view, Θ'; rewrite Hb, Hl, Hs; reflexivity | split; assumption ].
Qed.

End Programs.
