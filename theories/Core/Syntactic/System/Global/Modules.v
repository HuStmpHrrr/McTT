(** * Reading the Modules of a Global Context

    A body module is read in its body: its definitions and submodules are the
    entries of that body, at the module's telescope.  In a well-formed global
    context every entry is stored over the telescope of the module it is filed
    in ([gm_coh]): a definition's type is generalized over it, a submodule
    adds parameters to it, and an alias's parameters extend it. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Export Presup.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

