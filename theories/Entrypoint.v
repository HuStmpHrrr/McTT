From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString ExtrOcamlZInt.
From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Semantic Require Import NbE.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import FastGlobal Command.
From Mctt.Extraction Require ViewsFound.
From Mctt.Frontend Require Import Elaborator Parser.
Import MenhirLibParser.Inter.
Import Syntax_Notations GlobalCtx_Notations.

(** * The Driver's Entry Point

    The program on the command line is parsed, elaborated into core commands,
    and run by the verified interpreter of [Extraction.Command], which loads
    every unit it imports.  The interpreter finds the views of a group with
    [ViewsFound.views_search], proved to terminate.  The driver supplies two
    functions:

    - [load_path], the file IO that finds a unit under the search root;
    - [read], which lexes (in OCaml) and parses what was found.

    Termination of the loader is a [Prop] argument, erased by extraction; it
    holds when the search roots have finitely many units ([load_step_wf],
    given a thunk [all_files : unit -> list path] enumerating them).

    The run returns the filed units and the program's unit fast
    ([Extraction.FastGlobal]); the statements read them in Core
    ([dec_units], [dec_unit]), and [main_rep] says the fast results are the
    translations of their readings. *)

Variant main_result :=
  (** The program, the builtin bindings it ends with, every unit filed,
      fast, the program's own unit, fast, and the log of its evals *)
  | AllGood : Cst.prog -> builtins -> funits -> funit -> list eval_entry -> main_result
  | ElaborationFailure : Cst.prog -> string -> main_result
  | RunFailure : Cst.prog -> run_error -> main_result
  | ParserFailure : Aut.state -> Aut.Gram.token -> main_result
  | ParserTimeout : nat -> main_result
.

Section Main.
  Variable load_path : list string -> option string.
  Variable read : string -> option Cst.prog.
  Hypothesis Hwf : well_founded (load_step load_path).

  (** The program is elaborated here, to report the error message, since
      the interpreter's [to_core] returns an option; its unit is then run
      as it is ([unit_run]), so it is elaborated once. *)
  Definition main (log_fuel : nat) (buf : buffer) : main_result :=
    match Parser.prog log_fuel buf with
    | Parsed_pr prg _ =>
        match elaborate_core prg with
        | elab_failure msg => ElaborationFailure prg msg
        | elab_success u0 =>
            match unit_run load_path read to_core ViewsFound.views_search prg u0 (Hwf _) with
            | run_success (B, s, u, log) => AllGood prg B s u log
            | run_failure e => RunFailure prg e
            end
        end
    | Fail_pr_full s t => ParserFailure s t
    | Timeout_pr => ParserTimeout log_fuel
    end.

  (** Running the unit the program elaborates to is running the program. *)
  Lemma main_unit_run : forall prg u, elaborate_core prg = elab_success u ->
      unit_run load_path read to_core ViewsFound.views_search prg u (Hwf _) =
      prog_impl load_path read to_core ViewsFound.views_search prg (Hwf _).
  Proof.
    intros * He; symmetry; apply prog_impl_unit_run; unfold to_core; rewrite He; reflexivity.
  Qed.

  (** What [AllGood] certifies: the program denotes a well-formed global
      context, equal to the computed one up to the order of units within a
      level, with the builtin bindings shown, and every reported [eval] is
      well typed, in the context of the parameters of its enclosing frames,
      with the normal form shown.  The computed context and unit are read
      off the fast ones. *)
  Theorem main_sound : forall log_fuel buf prg B s u log,
      main log_fuel buf = AllGood prg B s u log ->
      (exists ΘR, prog_sem load_path read to_core prg B ΘR (dec_unit u) /\ gds_equiv ΘR (dec_units s) /\
                  ⊢ᵍ ΘR ⍮ nil /\ ΘR ⍮ nil ⍮ q_abs (prog_path prg) nil ⍮ fk_module ⊢ᵍᵘ dec_unit u) /\
      (forall e, In e log ->
         ⊢ᵍ eval_entry_deps e ⍮ eval_entry_stack e /\ eval_entry_deps e ⍮ eval_entry_stack e ⍮ gs_tele (eval_entry_stack e) ⊢ eval_entry_exp e : eval_entry_typ e /\
         nbe (eval_entry_deps e) (eval_entry_stack e) (gs_tele (eval_entry_stack e)) (eval_entry_exp e) (eval_entry_typ e) (eval_entry_nf e)).
  Proof.
    intros * H; unfold main in H.
    destruct (Parser.prog log_fuel buf); try discriminate.
    destruct (elaborate_core _) as [u0 |] eqn:He; try discriminate.
    rewrite (main_unit_run _ _ He) in H.
    destruct (prog_impl load_path read to_core ViewsFound.views_search _ _) as [[[[B' s'] u'] log'] |] eqn:Hr;
      try discriminate.
    injection H as <- <- <- <- <-.
    destruct (prog_impl_sound _ _ _ _ _ _ _ _ _ _ Hr) as [(ΘR & Hsem & Heq) Hlog].
    split; [| exact Hlog ].
    destruct (prog_sem_wf _ _ _ _ _ _ _ Hsem) as [HΘ HU].
    exists ΘR; tauto.
  Qed.

  (** The fast results of [AllGood] are the translations of their
      readings: the filed units refine [dec_units s], and [u] is the
      translation of [dec_unit u]. *)
  Theorem main_rep : forall log_fuel buf prg B s u log,
      main log_fuel buf = AllGood prg B s u log -> units_rep s (dec_units s) /\ u = tr_unit (dec_unit u).
  Proof.
    intros * H; unfold main in H.
    destruct (Parser.prog log_fuel buf); try discriminate.
    destruct (elaborate_core _) as [u0 |] eqn:He; try discriminate.
    rewrite (main_unit_run _ _ He) in H.
    destruct (prog_impl load_path read to_core ViewsFound.views_search _ _) as [[[[B' s'] u'] log'] |] eqn:Hr;
      try discriminate.
    injection H as <- <- <- <- <-.
    exact (prog_impl_rep _ _ _ _ _ _ _ _ _ _ Hr).
  Qed.

  (** A program that has a meaning runs to completion. *)
  Theorem main_complete : forall log_fuel buf prg buf' B ΘR U,
      Parser.prog log_fuel buf = Parsed_pr prg buf' ->
      prog_sem load_path read to_core prg B ΘR U ->
      (forall msg, elaborate_core prg <> elab_failure msg) ->
      exists s u log, main log_fuel buf = AllGood prg B s u log /\ dec_unit u = U /\ gds_equiv ΘR (dec_units s).
  Proof.
    intros * Hp Hsem Hel; unfold main; rewrite Hp.
    destruct (elaborate_core prg) eqn:He; [| exfalso; eapply Hel; reflexivity ].
    rewrite (main_unit_run _ _ He).
    destruct (prog_impl_complete _ _ _ _ ViewsFound.views_search_complete _ _ _ _ Hsem (Hwf _))
      as (s & u & log & Hr & HU & Heq).
    rewrite Hr; exists s, u, log; split; [ reflexivity | split; assumption ].
  Qed.
End Main.

Extraction Language OCaml.

Set Extraction Flag 1007.
Set Extraction Output Directory "../driver/extracted".

(** [String.compare], which orders the keys of the fast tables
    ([Extraction.FastGlobal]), runs as OCaml's.  Strings are OCaml's native
    strings ([ExtrOcamlNativeString]), and the two orders agree: Rocq's
    compares two strings character by character, a character by its code
    ([Ascii.compare], on [N]), the first difference deciding and a proper
    prefix coming first; OCaml's [String.compare] is lexicographic on the
    bytes as unsigned codes, a proper prefix coming first.  The directive
    replaces a linear walk over the string as a list of characters by the
    native comparison; the comparison it returns is mapped onto Rocq's
    [comparison]. *)
Extract Inlined Constant String.compare =>
  "(fun a b -> let c = Stdlib.String.compare a b in if c = 0 then Eq else if c < 0 then Lt else Gt)".
