(** * The Set Rules of Universes and Propositions

    The set judgments of the rules of the large universes, [Prop], [⊤],
    [⊥] and [tt]: each term denotes a constant, of its type's carrier. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Universes.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** A term every derivation gives the value [c] denotes [c]. *)
Lemma set_denotes_const : forall Γ M c, (forall ρ, set_interp T γ Γ ρ M c) ->
    (forall ρ v, set_interp T γ Γ ρ M v -> set_eq v c) -> set_denotes T γ Γ M (fun _ => c).
Proof. intros * Hex Hun. constructor; [intros ρ _; apply Hex | intros ρ ρ' v _ Hv; exact (Hun _ _ Hv)]. Qed.

(** The code of the large universe [Typeω@i]. *)
Definition large_universe_code (i : nat) : aczel_set := universe_code (large_ordinal_set i) (tower T (ul i)).

Lemma set_denotes_typ : forall Γ i, set_denotes T γ Γ (a_typ i) (fun _ => large_universe_code i).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

(** A universe code of a member of a universe of sets is relevant and a
    member. *)
Lemma universe_code_mem : forall l U V, grothendieck V -> set_mem l V -> set_mem U V ->
    set_mem (universe_code l U) V /\ is_relevant_code (universe_code l U).
Proof.
  intros * HV Hl HU. split.
  - apply (grothendieck_type_code _ HV); [exact Hl | apply (grothendieck_separation _ HV); exact HU].
  - do 3 eexists. split; [apply set_eq_refl | discriminate].
Qed.

(** [Typeω@i : Typeω@(S i)]. *)
Lemma set_rule_typ : forall Γ i, set_exp_eq T γ Γ (a_typ (S i)) (a_typ i) (a_typ i).
Proof.
  intros. exists (fun _ => large_universe_code (S i)), (fun _ => large_universe_code i).
  constructor; [apply set_denotes_typ .. |]. intros ρ _.
  unfold large_universe_code at 1, universe_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  pose proof (tower_grothendieck T (ul (S i))) as HV.
  destruct (universe_code_mem (large_ordinal_set i) (tower T (ul i)) _ HV
              (grothendieck_universe_index_set _ HV (ul i)) (tower_increasing T (ul i) (ul (S i)) ltac:(cbn; lia))) as [Hm Hr].
  apply set_mem_separation; [exact is_relevant_code_resp |]. split; assumption.
Qed.

End Universes.
