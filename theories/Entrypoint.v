From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString ExtrOcamlZInt.

From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Completeness Soundness.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Extraction Require Import NbE TypeCheck GlobalCheck.
From Mctt.Frontend Require Import Elaborator Parser.
Import MenhirLibParser.Inter.
Import Syntax_Notations.

(** A compilation unit elaborates to its unit and one obligation per [eval]:
    a closed expression, the type it was ascribed if it was, and the stack of
    frames it stands on; see [Frontend.Elaborator].  The unit is the first to
    be filed, so it is elaborated against no other.  Nothing proves the
    elaborator's stacks well formed, so each is checked before the expression
    is. *)
Variant eval_result :=
  | EvalGood : forall Ξ A M W,
      nil ⍮ Ξ ⍮ ⋅ ⊢ M : A ->
      nbe nil Ξ ⋅ M A W ->
      eval_result
  | StackFailure : forall Ξ (M : exp), ~ ⊢g nil ⍮ Ξ -> eval_result
  | TypeCheckingFailure : forall Ξ A M, ~ nil ⍮ Ξ ⍮ ⋅ ⊢ M : A -> eval_result
  | TypeInferenceFailure : forall Ξ M,
      (forall A, ~ @alg_type_infer (gc_mk nil Ξ) ⋅ A M) -> eval_result
.

Definition inspect {A} (x : A) : { y | x = y } := exist _ x eq_refl.
Extraction Inline inspect.

#[local]
Ltac impl_obl_tac :=
  try reflexivity;
  try eassumption;
  try apply user_exp_all;
  try (on_all_hyp: fun H => apply (@soundness (gc_mk nil _)) in H as [? []]);
  try (eapply nbe_order_sound; eassumption).

#[tactic="impl_obl_tac"]
Equations run_eval (e : eval_obl) : eval_result :=
| (Ξ, M, oA) with check_gctx_closed Ξ => {
  | right _ => StackFailure Ξ M _
  | left Hg with oA => {
    | Some A with @type_check_closed (gc_mk nil Ξ) Hg A _ M _ => {
      | left _ with nbe_impl nil Ξ ⋅ M A _ => {
        | exist _ W _ => EvalGood Ξ A M W _ _
        }
      | right _ => TypeCheckingFailure Ξ A M _
      }
    | None with @type_infer_closed (gc_mk nil Ξ) Hg M _ => {
      | inleft (exist _ A _) with nbe_impl nil Ξ ⋅ M A _ => {
        | exist _ W _ => EvalGood Ξ A M W _ _
        }
      | inright _ => TypeInferenceFailure Ξ M _
      }
    }
  }
.
Next Obligation. (* nbe_order nil Ξ ⋅ M A, from the inferred type *)
  match goal with
  | HM : wf_exp _ _ ⋅ _ ?M |- nbe_order nil ?Ξ ⋅ ?M _ =>
      apply (@soundness (gc_mk nil Ξ)) in HM as [? []]
  end.
  eapply nbe_order_sound; eassumption.
Qed.

(** The definitions that follow the last [eval] are seen by no obligation, so
    the unit itself is checked as well. *)
Variant unit_result :=
  | UnitGood : forall U, nil ⍮ nil ⊢u U -> unit_result
  | UnitFailure : forall U, ~ nil ⍮ nil ⊢u U -> unit_result
.

Definition check_unit (U : gunit) : unit_result :=
  match check_gunit_closed U with
  | left H => UnitGood U H
  | right H => UnitFailure U H
  end.

Variant main_result :=
  | AllGood : forall cst fp U es ur rs,
      elaborate_prog nil cst = eok ((fp, U), es) ->
      ur = check_unit U ->
      rs = List.map run_eval es ->
      main_result
  | ElaborationFailure : forall cst msg, elaborate_prog nil cst = eerr msg -> main_result
  | ParserFailure : Aut.state -> Aut.Gram.token -> main_result
  | ParserTimeout : nat -> main_result
.

#[tactic="impl_obl_tac"]
Equations main (log_fuel : nat) (buf : buffer) : main_result :=
| log_fuel, buf with Parser.prog log_fuel buf => {
  | Parsed_pr cst _ with inspect (elaborate_prog nil cst) => {
    | exist _ (eok ((fp, U), es)) _ => AllGood cst fp U es (check_unit U) (List.map run_eval es) _ _ _
    | exist _ (eerr msg) _ => ElaborationFailure cst msg _
    }
  | Fail_pr_full s t               => ParserFailure s t
  | Timeout_pr                     => ParserTimeout log_fuel
  }
.

Extraction Language OCaml.

Set Extraction Flag 1007.
Set Extraction Output Directory "../driver/extracted".
