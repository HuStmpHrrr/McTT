(** * The Set Model of Propositions

    The set judgments of the rules of [Prop], [⊤], [⊥] and [tt]: [Prop]
    is a relevant code of the first small universe, a proposition a
    proposition code, a proof the empty set. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Export Universes.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import ListNotations.

Section Props.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_denotes_prop : forall Γ, set_denotes T γ Γ a_prop (fun _ => prop_universe_code).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_True : forall Γ, set_denotes T γ Γ a_True (fun _ => prop_code True).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_False : forall Γ, set_denotes T γ Γ a_False (fun _ => prop_code False).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_tt : forall Γ, set_denotes T γ Γ a_tt (fun _ => empty_set).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma prop_code_mem_prop_universe : forall P, set_mem (prop_code P) (code_carrier prop_universe_code).
Proof.
  intros. unfold prop_universe_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  exists P. apply set_eq_refl.
Qed.

(** A term of [Prop]'s carrier is a proposition code. *)
Lemma is_prop_code_of_prop_universe : forall C, set_mem C (code_carrier prop_universe_code) -> is_prop_code C.
Proof.
  intros C HC. unfold prop_universe_code in HC. eapply set_mem_eq_r in HC; [| apply code_carrier_type_code].
  destruct HC as [P E]. exists P. exact E.
Qed.

(** ** Ex Falso, Conjunctions and Tagged Proofs *)

(** A type of [Prop] denotes a proposition's code. *)
Lemma set_prop_is_prop_code : forall Γ P FPr FP FP2 ρ, set_exp_eq_with T γ Γ a_prop P P FPr FP FP2 ->
    set_env_in T γ Γ ρ -> is_prop_code (FP ρ).
Proof.
  intros * [HPr _ _ _ HPm] Hρ. apply is_prop_code_of_prop_universe.
  eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HPr (set_denotes_prop _) Hρ) |].
  apply HPm. exact Hρ.
Qed.

(** A proposition with a proof is true. *)
Lemma prop_true_of_mem : forall C z, is_prop_code C -> set_mem z (code_carrier C) -> prop_true C.
Proof. intros * HC Hz. unfold prop_true. eapply set_mem_eq_l; [exact (prop_code_carrier_empty _ _ HC Hz) | exact Hz]. Qed.

Section Conjunctions.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** The code of a conjunction: both components true, the second at the
    proof of the first. *)
Definition and_denotation (FP FQ : set_env -> aczel_set) (ρ : set_env) : aczel_set :=
  prop_code (prop_true (FP ρ) /\ prop_true (FQ (set_env_extend ρ (set_entry_term ak_propositional empty_set)))).

Lemma set_denotes_and : forall Γ P Q FP FQ, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_propositional P :: Γ ->
    set_denotes T γ Γ P FP -> set_denotes T γ (ce_ass ak_propositional P :: Γ) Q FQ ->
    set_denotes T γ Γ (a_and P Q) (and_denotation FP FQ).
Proof.
  intros * HΓ Hc HP HQ. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  pose proof (set_denotes_exists _ _ _ _ _ HP _ Hρ) as Hp.
  apply (set_interp_and T γ Γ ρ P Q (FP ρ) (fun x => FQ (set_env_extend ρ (set_entry_term ak_propositional x)))); [exact Hc | exact Hp |].
  intros x Hx. apply (set_denotes_exists _ _ _ _ _ HQ). exact (set_env_in_extend_ass T γ Γ ρ _ P _ x Hρ Hp Hx).
Qed.

(** A proof of a conjunction makes both components true. *)
Lemma and_denotation_true : forall Γ P Q FS FP FQ FM ρ, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_propositional P :: Γ ->
    set_denotes T γ Γ P FP -> set_denotes T γ (ce_ass ak_propositional P :: Γ) Q FQ ->
    set_denotes T γ Γ (a_and P Q) FS -> set_env_in T γ Γ ρ -> set_mem (FM ρ) (code_carrier (FS ρ)) ->
    prop_true (FP ρ) /\ prop_true (FQ (set_env_extend ρ (set_entry_term ak_propositional empty_set))).
Proof.
  intros * HΓ Hc HP HQ HS Hρ Hm.
  eapply set_mem_eq_r in Hm; [| apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HS (set_denotes_and _ _ _ _ _ HΓ Hc HP HQ) Hρ)].
  apply prop_true_prop_code. eapply prop_true_of_mem; [eexists; apply set_eq_refl | exact Hm].
Qed.

(** A proof of [Q] at a proof of [P]: the proposition at the empty set. *)
Lemma set_prop_at_proof : forall Γ P Q M FP FQ FM FQM ρ, ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_propositional P :: Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp M) : ce_ass ak_propositional P :: Γ ->
    set_denotes T γ Γ P FP -> set_denotes T γ (ce_ass ak_propositional P :: Γ) Q FQ -> set_denotes T γ Γ M FM ->
    set_denotes T γ Γ (exp_sub Q (sb_extend sb_id (se_exp M))) FQM ->
    set_env_in T γ Γ ρ -> is_prop_code (FP ρ) -> set_mem (FM ρ) (code_carrier (FP ρ)) ->
    set_eq (FQM ρ) (FQ (set_env_extend ρ (set_entry_term ak_propositional empty_set))).
Proof.
  intros * Hc Hσ HP HQ HM HQM Hρ HPc Hm. pose proof (set_denotes_exists _ _ _ _ _ HP _ Hρ) as Hp.
  pose proof (prop_code_carrier_empty _ _ HPc Hm) as Em.
  assert (Hin : set_env_in T γ (ce_ass ak_propositional P :: Γ) (set_env_extend ρ (set_entry_term ak_propositional (FM ρ))))
    by exact (set_env_in_extend_ass T γ Γ ρ _ P _ _ Hρ Hp Hm).
  eapply set_eq_trans.
  - apply set_eq_sym. apply (set_denotes_unique _ _ _ _ _ HQM ρ ρ); [exact Hρ |].
    apply (set_interp_single_sub T γ Γ ρ ak_propositional P M (FM ρ)); [exact Hc | exact Hσ | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
    exact (set_denotes_exists _ _ _ _ _ HQ _ Hin).
  - exact (set_denotes_unique _ _ _ _ _ HQ _ _ _
             (set_env_rel_extend_ass T γ Γ ρ ρ _ P _ _ _ Hρ Hp (prop_true_of_mem _ _ HPc Hm) (set_eq_sym _ _ Em))
             (set_denotes_exists _ _ _ _ _ HQ _ Hin)).
Qed.

End Conjunctions.

End Props.

(** ** The Rules *)

Section Rules.
  Variables (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation).














End Rules.
