From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.

(** * What the Implementations Look Up

    The declarations the evaluator and readback keep ([lk_cache]), and the
    data a command computes once for the implementations it runs
    ([FCtx]). *)

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

Definition qname_dec : forall (x y : qname), {x = y} + {x <> y}.
Proof. decide equality; apply list_eq_dec, string_dec. Defined.

Section Cache.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A declaration looked up already: the eliminator keeps the one of the
      constructor it takes apart for the recursive results, whose arguments
      are of the same type, and compares names instead of looking up
      again. *)
  Definition lk_cache : Set := option {x : qname * ind_decl | ind_lookup Θ Ξ (fst x) = Some (snd x)}.

  Definition cache_lookup (ck : lk_cache) (p : qname) : { o | ind_lookup Θ Ξ p = o } :=
    match ck with
    | Some (exist _ (pc, D) E) =>
        match qname_dec pc p with
        | left Hq => exist _ (Some D) (eq_rect pc (fun r => ind_lookup Θ Ξ r = Some D) E p Hq)
        | right _ => inspect (ind_lookup Θ Ξ p)
        end
    | None => inspect (ind_lookup Θ Ξ p)
    end.

End Cache.

(** ** What a Command Looks Up Once

    The data the implementations look global names up in, computed once by
    the command that runs them ([Extraction.Command]) rather than once per
    lookup.  It is a class, so that the reference checker
    ([Reference.TypeCheck]) and the statements about the implementations
    ([Reference.Refinement]) get the default, [fctx_none], without naming
    it; any instance gives the same results, since every lookup it
    provides is proved equal to the one of the global context.

    - [fc_seed]: a declaration the evaluator and readback start from, as if
      they had looked it up already: the eliminator of the type bound as
      the natural numbers then looks nothing up. *)
Class FCtx (Θ : gdeps) (Ξ : gstack) : Set := mk_fctx { fc_seed : lk_cache Θ Ξ }.

Arguments mk_fctx {Θ Ξ}.

#[global] Instance fctx_none Θ Ξ : FCtx Θ Ξ | 100 := mk_fctx None.


(** The cache that holds the declaration at [p], if [p] names one. *)
Definition cache_at (Θ : gdeps) (Ξ : gstack) (op : option qname) : lk_cache Θ Ξ :=
  match op with
  | Some p =>
      match inspect (ind_lookup Θ Ξ p) with
      | exist _ (Some D) E => Some (exist _ (p, D) E)
      | exist _ None _ => None
      end
  | None => None
  end.
