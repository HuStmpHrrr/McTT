From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString ExtrOcamlZInt.

From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Completeness Soundness.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Extraction Require Import NbE TypeCheck.
From Mctt.Frontend Require Import Elaborator Parser.
Import MenhirLibParser.Inter.
Import Syntax_Notations.

(** A compilation unit elaborates to one closed expression per [eval] command,
    each with the type it was ascribed if it was ascribed one; see
    [Frontend.Elaborator]. *)
Variant eval_result :=
  | EvalGood : forall A M W,
      ⋅ ⊢ M : A ->
      nbe ⋅ M A W ->
      eval_result
  | TypeCheckingFailure : forall A M, ~ ⋅ ⊢ M : A -> eval_result
  | TypeInferenceFailure : forall M, (forall A, ~ ⋅ ⊢a M ⟹ A) -> eval_result
.

Definition inspect {A} (x : A) : { y | x = y } := exist _ x eq_refl.
Extraction Inline inspect.

#[local]
Ltac impl_obl_tac :=
  try reflexivity;
  try eassumption;
  try apply user_exp_all;
  try (on_all_hyp: fun H => apply soundness in H as [? []]);
  try (eapply nbe_order_sound; eassumption).

#[tactic="impl_obl_tac"]
Equations run_eval (e : (option typ * exp)%type) : eval_result :=
| (Some A, M) with type_check_closed A _ M _ => {
  | left  _ with nbe_impl ⋅ M A _ => {
    | exist _ W _ => EvalGood A M W _ _
    }
  | right _ => TypeCheckingFailure A M _
  }
| (None, M) with type_infer_closed M _ => {
  | inleft (exist _ A _) with nbe_impl ⋅ M A _ => {
    | exist _ W _ => EvalGood A M W _ _
    }
  | inright _ => TypeInferenceFailure M _
  }
.
Next Obligation.
  intros.
  (on_all_hyp: fun H => apply soundness in H as [? []]).
  eapply nbe_order_sound.
  eassumption.
Qed.

Variant main_result :=
  | AllGood : forall cst es rs,
      elaborate_prog cst = Some es ->
      rs = List.map run_eval es ->
      main_result
  | ElaborationFailure : forall cst, elaborate_prog cst = None -> main_result
  | ParserFailure : Aut.state -> Aut.Gram.token -> main_result
  | ParserTimeout : nat -> main_result
.

#[tactic="impl_obl_tac"]
Equations main (log_fuel : nat) (buf : buffer) : main_result :=
| log_fuel, buf with Parser.prog log_fuel buf => {
  | Parsed_pr cst _ with inspect (elaborate_prog cst) => {
    | exist _ (Some es) _ => AllGood cst es (List.map run_eval es) _ _
    | exist _ None      _ => ElaborationFailure cst _
    }
  | Fail_pr_full s t               => ParserFailure s t
  | Timeout_pr                     => ParserTimeout log_fuel
  }
.

Extraction Language OCaml.

Set Extraction Flag 1007.
Set Extraction Output Directory "../driver/extracted".
