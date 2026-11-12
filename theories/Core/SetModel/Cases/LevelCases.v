(** * The Set Rules of Levels

    A level is an ordinal below [ω²]; a type of levels [Level@n] the set
    of those below [ω·(n+1)], a member of every universe of sets.  The
    successor of a level is its successor ordinal, the join of two levels
    their union, the larger. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Cases Require Export FunctionCases.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Levels.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_mem_level_type : forall n z, set_mem z (code_carrier (level_type_code n)) <->
    exists o, fst o <= n /\ set_eq z (pair_ordinal_set o).
Proof.
  intros n z. unfold level_type_code. split.
  - intros Hz. eapply set_mem_eq_r in Hz; [| apply code_carrier_type_code]. destruct Hz as [[o Ho] E]. exists o. auto.
  - intros [o [Ho E]]. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |]. exists (exist _ o Ho). exact E.
Qed.

Lemma set_denotes_level : forall Γ n, set_denotes T γ Γ (a_level n) (fun _ => level_type_code n).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_llit : forall Γ o, set_denotes T γ Γ (a_llit o) (fun _ => pair_ordinal_set o).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_succl : forall Γ M FM, set_denotes T γ Γ M FM -> set_denotes T γ Γ (a_succl M) (fun ρ => successor_set (FM ρ)).
Proof.
  intros * HM. constructor; [intros ρ Hρ; constructor; exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
  intros ρ ρ' v Hr Hv. inversion Hv; subst. apply successor_set_resp.
  exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)).
Qed.

Lemma set_denotes_maxl : forall Γ M N FM FN, set_denotes T γ Γ M FM -> set_denotes T γ Γ N FN ->
    set_denotes T γ Γ (a_maxl M N) (fun ρ => union_set (unordered_pair_set (FM ρ) (FN ρ))).
Proof.
  intros * HM HN. constructor; [intros ρ Hρ; constructor; [exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | exact (set_denotes_exists _ _ _ _ _ HN _ Hρ)] |].
  intros ρ ρ' v Hr Hv. inversion Hv; subst. apply union_set_resp. apply unordered_pair_set_resp;
    [exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)) | exact (set_denotes_unique _ _ _ _ _ HN _ _ _ Hr ltac:(eassumption))].
Qed.

(** A term of [Level@n] is an ordinal below [ω·(n+1)]. *)
Lemma level_value : forall Γ n M FL FM FM' ρ, set_exp_eq_with T γ Γ (a_level n) M M FL FM FM' -> set_env_in T γ Γ ρ ->
    exists o, fst o <= n /\ set_eq (FM ρ) (pair_ordinal_set o).
Proof.
  intros * [HL HM _ _ Hm] Hρ. apply set_mem_level_type.
  eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HL (set_denotes_level _ n) Hρ) | exact (Hm ρ Hρ)].
Qed.

(** [Level@n : LevelSort]. *)
Lemma set_rule_level : forall Γ n, set_exp_eq T γ Γ a_level_sort (a_level n) (a_level n).
Proof.
  intros. exists (fun _ => level_sort_code (level_types_universe T)), (fun _ => level_type_code n), (fun _ => level_type_code n).
  constructor; [apply set_denotes_level_sort | apply set_denotes_level | apply set_denotes_level | intros; apply set_eq_refl |].
  intros ρ _. unfold level_sort_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  apply set_mem_separation; [exact is_level_type_code_resp |]. split; [| eapply is_level_type_code_level; apply set_eq_refl].
  apply set_mem_union. exists (tower T (us (0, 0))). split; [exists (0, 0); apply set_eq_refl |].
  apply grothendieck_level_type_code. apply tower_grothendieck.
Qed.

(** A level literal [𝕃ᵒ o : Level@n], [o]'s tier at most [n]. *)
Lemma set_rule_llit : forall Γ o n, fst o <= n -> set_exp_eq T γ Γ (a_level n) (a_llit o) (a_llit o).
Proof.
  intros * Ho. exists (fun _ => level_type_code n), (fun _ => pair_ordinal_set o), (fun _ => pair_ordinal_set o).
  constructor; [apply set_denotes_level | apply set_denotes_llit .. | intros; apply set_eq_refl |].
  intros ρ _. apply set_mem_level_type. exists o. split; [exact Ho | apply set_eq_refl].
Qed.

(** [M ≈ M' : Level@n] gives [succl M ≈ succl M' : Level@n]. *)
Lemma set_rule_succl : forall Γ n M M' FL FM FM', set_exp_eq_with T γ Γ (a_level n) M M' FL FM FM' ->
    set_exp_eq T γ Γ (a_level n) (a_succl M) (a_succl M').
Proof.
  intros * H. pose proof H as [HL HM HM' E Hm].
  exists (fun _ => level_type_code n), (fun ρ => successor_set (FM ρ)), (fun ρ => successor_set (FM' ρ)).
  constructor; [apply set_denotes_level | apply set_denotes_succl; assumption .. | intros ρ Hρ; apply successor_set_resp; exact (E ρ Hρ) |].
  intros ρ Hρ.
  destruct (level_value _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL HM HM (fun _ _ => set_eq_refl _) Hm) Hρ)
    as [[a b] [Ho Eo]].
  apply set_mem_level_type. exists (a, S b). split; [exact Ho |]. apply successor_set_resp. exact Eo.
Qed.

(** [M ≈ M'] and [N ≈ N'] at [Level@n] give [maxl M N ≈ maxl M' N']. *)
Lemma set_rule_maxl : forall Γ n M M' N N' FL FM FM' FL' FN FN', set_exp_eq_with T γ Γ (a_level n) M M' FL FM FM' ->
    set_exp_eq_with T γ Γ (a_level n) N N' FL' FN FN' -> set_exp_eq T γ Γ (a_level n) (a_maxl M N) (a_maxl M' N').
Proof.
  intros * HMe HNe. pose proof HMe as [HL HM HM' EM Hm]. pose proof HNe as [HL' HN HN' EN Hn].
  exists (fun _ => level_type_code n), (fun ρ => union_set (unordered_pair_set (FM ρ) (FN ρ))),
    (fun ρ => union_set (unordered_pair_set (FM' ρ) (FN' ρ))).
  constructor; [apply set_denotes_level | apply set_denotes_maxl; assumption .. |
                intros ρ Hρ; apply union_set_resp; apply unordered_pair_set_resp; [exact (EM ρ Hρ) | exact (EN ρ Hρ)] |].
  intros ρ Hρ.
  destruct (level_value _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL HM HM (fun _ _ => set_eq_refl _) Hm) Hρ) as [x [Hx Ex]].
  destruct (level_value _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL' HN HN (fun _ _ => set_eq_refl _) Hn) Hρ) as [y [Hy Ey]].
  apply set_mem_level_type. exists (pair_max x y). split.
  - destruct (pair_max_cases x y) as [[_ ->] | [_ ->]]; assumption.
  - eapply set_eq_trans; [| apply union_pair_ordinal_set]. apply union_set_resp. apply unordered_pair_set_resp; assumption.
Qed.

End Levels.
