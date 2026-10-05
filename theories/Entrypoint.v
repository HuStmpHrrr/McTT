From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString ExtrOcamlZInt.
From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Semantic Require Import NbE.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import Command.
From Mctt.Frontend Require Import Elaborator Parser.
Import MenhirLibParser.Inter.
Import Syntax_Notations GlobalCtx_Notations.

(** * The Driver's Entry Point

    The program on the command line is parsed, elaborated into core commands,
    and run by the verified interpreter of [Extraction.Command], which loads
    every unit it imports.  The driver supplies two functions:

    - [load_path], the file IO that finds a unit under the search root;
    - [read], which lexes (in OCaml) and parses what was found.

    Termination of the loader is a [Prop] argument, erased by extraction; it
    holds when the search root has finitely many units ([load_step_wf]). *)

Variant main_result :=
  | AllGood : Cst.prog -> gctx -> gunit -> list eval_entry -> main_result
  | ElaborationFailure : Cst.prog -> string -> main_result
  | RunFailure : Cst.prog -> run_error -> main_result
  | ParserFailure : Aut.state -> Aut.Gram.token -> main_result
  | ParserTimeout : nat -> main_result
.

Section Main.
  Variable load_path : list string -> option string.
  Variable read : string -> option Cst.prog.
  Hypothesis Hwf : well_founded (load_step load_path).

  (** The program is elaborated here only to report the error message, since
      the interpreter's [to_core] returns an option. *)
  Definition main (log_fuel : nat) (buf : buffer) : main_result :=
    match Parser.prog log_fuel buf with
    | Parsed_pr prg _ =>
        match elaborate_core prg with
        | eerr msg => ElaborationFailure prg msg
        | eok _ =>
            match prog_impl load_path read to_core prg (Hwf _) with
            | rok (Θ, U, log) => AllGood prg Θ U log
            | rerr e => RunFailure prg e
            end
        end
    | Fail_pr_full s t => ParserFailure s t
    | Timeout_pr => ParserTimeout log_fuel
    end.

  (** What [AllGood] certifies: the program denotes the computed global
      context and unit, which are well formed, and every reported [eval] is
      well typed, in the context of its enclosing frames, with the normal
      form shown. *)
  Theorem main_sound : forall log_fuel buf prg Θ U log,
      main log_fuel buf = AllGood prg Θ U log ->
      (prog_sem load_path read to_core prg Θ U /\ ⊢g Θ /\ Θ ⍮ ⋅ ⊢ᵘ U ≈ U) /\
      (forall e, In e log ->
         ⊢ ev_gctx e ⍮ ev_ctx e /\ ev_gctx e ⍮ ev_ctx e ⊢ ev_exp e : ev_typ e /\
         nbe (ev_gctx e) (ev_ctx e) (ev_exp e) (ev_typ e) (ev_nf e)).
  Proof.
    intros * H; unfold main in H.
    destruct (Parser.prog log_fuel buf); try discriminate.
    destruct (elaborate_core _); try discriminate.
    destruct (prog_impl load_path read to_core _ _) as [[[Θ' U'] log'] |] eqn:Hr; try discriminate.
    injection H as <- <- <- <-.
    destruct (prog_impl_sound _ _ _ _ _ _ _ _ Hr) as [Hsem Hlog].
    split; [| exact Hlog ].
    destruct (prog_sem_wf _ _ _ _ _ _ Hsem) as [HΘ HU].
    tauto.
  Qed.

  (** A program that has a meaning runs to completion, with that meaning. *)
  Theorem main_complete : forall log_fuel buf prg buf' Θ U,
      Parser.prog log_fuel buf = Parsed_pr prg buf' ->
      prog_sem load_path read to_core prg Θ U ->
      (forall msg, elaborate_core prg <> eerr msg) ->
      exists log, main log_fuel buf = AllGood prg Θ U log.
  Proof.
    intros * Hp Hsem Hel; unfold main; rewrite Hp.
    destruct (elaborate_core prg) eqn:He; [| exfalso; eapply Hel; reflexivity ].
    destruct (prog_impl_complete _ _ _ _ _ _ Hsem (Hwf _)) as (log & Hr).
    rewrite Hr; eauto.
  Qed.
End Main.

Extraction Language OCaml.

Set Extraction Flag 1007.
Set Extraction Output Directory "../driver/extracted".
