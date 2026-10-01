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
    every unit it imports.  Two things come from the driver: [load_path], the
    file IO that finds a unit under the search root, and [read], which lexes and
    parses what it found — the lexer being OCaml.  The termination proof of the
    loader is a [Prop] argument, erased by extraction: it holds when the search
    root has finitely many units ([load_step_wf]). *)

Variant main_result :=
  | AllGood : Cst.prog -> gdeps -> gunit -> list eval_entry -> main_result
  | ElaborationFailure : Cst.prog -> string -> main_result
  | RunFailure : Cst.prog -> run_error -> main_result
  | ParserFailure : Aut.state -> Aut.Gram.token -> main_result
  | ParserTimeout : nat -> main_result
.

Section Main.
  Variable load_path : list string -> option string.
  Variable read : string -> option Cst.prog.
  Hypothesis Hwf : well_founded (load_step load_path).

  (** Elaborated once more only to report its message: the interpreter's
      [to_core] keeps the option. *)
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

  (** What [AllGood] certifies: the program means a well-formed global
      context, the one computed up to the order of units within a level, and
      every reported [eval] is well typed, in the context of the parameters of
      the frames it stands in, with the normal form shown. *)
  Theorem main_sound : forall log_fuel buf prg Θ U log,
      main log_fuel buf = AllGood prg Θ U log ->
      (exists ΘR, prog_sem load_path read to_core prg ΘR U /\ gds_equiv ΘR Θ /\
                  wf_gdeps ΘR /\ wf_gunit ΘR nil (p_abs (prog_path prg) nil) U) /\
      (forall e, In e log ->
         ⊢g ev_deps e ⍮ ev_stack e /\ ev_deps e ⍮ ev_stack e ⍮ gs_tele (ev_stack e) ⊢ ev_exp e : ev_typ e /\
         nbe (ev_deps e) (ev_stack e) (gs_tele (ev_stack e)) (ev_exp e) (ev_typ e) (ev_nf e)).
  Proof.
    intros * H; unfold main in H.
    destruct (Parser.prog log_fuel buf); try discriminate.
    destruct (elaborate_core _); try discriminate.
    destruct (prog_impl load_path read to_core _ _) as [[[Θ' U'] log'] |] eqn:Hr; try discriminate.
    injection H as <- <- <- <-.
    destruct (prog_impl_sound _ _ _ _ _ _ _ _ Hr) as [(ΘR & Hsem & Heq) Hlog].
    split; [| exact Hlog ].
    destruct (prog_sem_wf _ _ _ _ _ _ Hsem) as [HΘ HU].
    exists ΘR; tauto.
  Qed.

  (** And a program that has a meaning is run to completion. *)
  Theorem main_complete : forall log_fuel buf prg buf' ΘR U,
      Parser.prog log_fuel buf = Parsed_pr prg buf' ->
      prog_sem load_path read to_core prg ΘR U ->
      (forall msg, elaborate_core prg <> eerr msg) ->
      exists Θ log, main log_fuel buf = AllGood prg Θ U log /\ gds_equiv ΘR Θ.
  Proof.
    intros * Hp Hsem Hel; unfold main; rewrite Hp.
    destruct (elaborate_core prg) eqn:He; [| exfalso; eapply Hel; reflexivity ].
    destruct (prog_impl_complete _ _ _ _ _ _ Hsem (Hwf _)) as (Θ & log & Hr & Heq).
    rewrite Hr; eauto.
  Qed.
End Main.

Extraction Language OCaml.

Set Extraction Flag 1007.
Set Extraction Output Directory "../driver/extracted".
