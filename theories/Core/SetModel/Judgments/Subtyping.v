(** * The Set Model of Subtyping

    A subtype's carriers are in the supertype's: universes grow with their
    indices, types of levels with their sorts, small universes are in the
    large ones, and a [Π] into an evaluated kind is covariant in its
    codomain.  A term of a subtype is a term of the supertype. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Export Levels.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import ListNotations.

Section Subtyping.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** Subsumption at one context: a term of a subtype, or two equal ones, at
    the supertype. *)
Lemma set_exp_eq_at_supertype {GC : GCtx} : forall Γ A A' M M' FA FM FM' FA0 FA', set_exp_eq_with T γ Γ A M M' FA FM FM' ->
    set_subtyp_with T γ Γ A A' FA0 FA' -> set_rel_exp_eq T γ Γ A' M M'.
Proof.
  intros * [HA HM HM' E Hm] [HA0 HA' Hs]. exists FA', FM, FM'. constructor; try assumption.
  intros ρ Hρ. apply Hs; [exact Hρ |]. eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HA HA0 Hρ) |].
  apply Hm. exact Hρ.
Qed.






(** A universe's carrier: the relevant codes of its universe of sets. *)
Lemma set_mem_universe_code : forall l U z, set_mem z (code_carrier (universe_code l U)) <-> set_mem z U /\ is_relevant_code z.
Proof.
  intros. unfold universe_code. split; intros Hz.
  - eapply set_mem_eq_r in Hz; [| apply code_carrier_type_code]. apply set_mem_separation in Hz; [exact Hz | exact is_relevant_code_resp].
  - eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |]. apply set_mem_separation; [exact is_relevant_code_resp | exact Hz].
Qed.

Lemma universe_code_sub : forall l l' U U', set_sub U U' -> set_sub (code_carrier (universe_code l U)) (code_carrier (universe_code l' U')).
Proof. intros * H z Hz. apply set_mem_universe_code in Hz as [Hz Hr]. apply set_mem_universe_code. split; [apply H; exact Hz | exact Hr]. Qed.

(** [Typeω@i ⊆ Typeω@j], [i < j], at one context. *)
Lemma set_subtyp_typ_lt {GC : GCtx} : forall Γ i j, i < j -> set_rel_subtyp T γ Γ (a_typ i) (a_typ j).
Proof.
  intros * H. exists (fun _ => large_universe_code T i), (fun _ => large_universe_code T j).
  constructor; [apply set_denotes_typ .. |]. intros ρ _. apply universe_code_sub. apply tower_sub. cbn. lia.
Qed.






End Subtyping.
