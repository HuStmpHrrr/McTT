(** * The Extracted Checker Refines the Reference Checker

    [Extraction.TypeCheck] is the checker that is extracted;
    [Reference.TypeCheck] is the direct one it was refined from (see the
    head of [Extraction.TypeCheck] for the two refinements).  Both decide
    the same judgments with the same specification, so they compute the
    same result on every input: the same decision, and the same inferred
    normal form ([functional_alg_type_infer]).  These are the
    input–output equalities of the refinement. *)

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Extraction Require Import TypeCheckBase.
From Mctt.Extraction Require TypeCheck.
From Mctt.Reference Require TypeCheck.
Import Domain_Notations Fixed_Notations.

(** The computational content of a decision, and of an inference. *)
Definition sumbool_result {P Q : Prop} (s : {P} + {Q}) : bool := if s then true else false.

Definition sumor_result {A} {P : A -> Prop} {Q : Prop} (s : {x | P x} + {Q}) : option A :=
  match s with
  | inleft (exist _ x _) => Some x
  | inright _ => None
  end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  Lemma sumbool_result_iff : forall {P Q Q' : Prop} (s : {P} + {Q}) (s' : {P} + {Q'}),
      (Q -> ~ P) -> (Q' -> ~ P) -> sumbool_result s = sumbool_result s'.
  Proof. intros * HQ HQ'; destruct s, s'; cbn; firstorder. Qed.

  Theorem type_check_in_refines : forall G A HA P M H H',
      sumbool_result (Extraction.TypeCheck.type_check_in G A HA P M H) =
      sumbool_result (Reference.TypeCheck.type_check_in G A HA P M H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.

  Theorem type_infer_in_refines : forall G HG P M H H',
      sumor_result (Extraction.TypeCheck.type_infer_in G HG P M H) =
      sumor_result (Reference.TypeCheck.type_infer_in G HG P M H').
  Proof.
    intros.
    destruct (Extraction.TypeCheck.type_infer_in G HG P M H) as [[A HA] | HN],
             (Reference.TypeCheck.type_infer_in G HG P M H') as [[A' HA'] | HN']; cbn;
      destruct_conjs;
      [ f_equal; eapply functional_alg_type_infer; eassumption
      | exfalso; eapply HN'; eassumption
      | exfalso; eapply HN; eassumption
      | reflexivity ].
  Qed.

  Theorem ext_check_refines : forall G HG Ψ H H',
      sumbool_result (Extraction.TypeCheck.ext_check G HG Ψ H) =
      sumbool_result (Reference.TypeCheck.ext_check G HG Ψ H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.

  Theorem unit_check_refines : forall G HG U H H',
      sumbool_result (Extraction.TypeCheck.unit_check G HG U H) =
      sumbool_result (Reference.TypeCheck.unit_check G HG U H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.

  Theorem modexp_check_refines : forall G HG M H H',
      sumbool_result (Extraction.TypeCheck.modexp_check G HG M H) =
      sumbool_result (Reference.TypeCheck.modexp_check G HG M H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.
End Fixed_GCtx.
