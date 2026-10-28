From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import FastContext.

(** * The Core Context of a Fast Context

    The Core global context a fast context stands for, behind a sealed
    module: it is the decoding of the fast data ([fc_gctx_eq]), but no
    tactic can reduce it into the decoding functions.  [firstorder]
    reduces through any transparent definition whatever its [Opaque]
    status, and through the type of a [Qed] constant, and took about ten
    seconds per call on a goal mentioning the decoding, two minutes in the
    obligations of [TypeCheck].  The field [fc_gctx_eq] of the signature is
    implemented by a proof ([FcDecoding.fc_gctx_eq]): it is no axiom, and
    the theorems using it stay closed under the global context.

    The module has a file of its own so that no extracted code has it:
    the extracted functions take the fast data and read no Core context,
    so extraction needs nothing of this file, and the decoding functions
    of [Extraction.FastGlobal] are not extracted either. *)
Module Type FcDecodingSig.
  (** The Core global context a fast context stands for *)
  Parameter fc_gctx : FCtx -> GCtx.
  (** It is the decoding of the fast data. *)
  Parameter fc_gctx_eq : forall F, fc_gctx F = gc_mk (view_deps (fc_view F)) (dec_stack (fc_frames F)).
End FcDecodingSig.

(** The implementation of [FcDecodingSig]: the decoding itself *)
Module FcDecoding : FcDecodingSig.
  (** The decoding of the fast data *)
  Definition fc_gctx (F : FCtx) : GCtx := gc_mk (view_deps (fc_view F)) (dec_stack (fc_frames F)).
  (** By definition *)
  Lemma fc_gctx_eq : forall F, fc_gctx F = gc_mk (view_deps (fc_view F)) (dec_stack (fc_frames F)).
  Proof. reflexivity. Qed.
End FcDecoding.
