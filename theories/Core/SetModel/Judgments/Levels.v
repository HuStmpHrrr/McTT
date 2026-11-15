(** * The Set Model of Levels

    A level is an ordinal below [ω²]; a type of levels [Level@n] the set
    of those below [ω·(n+1)], a member of every universe of sets.  The
    successor of a level is its successor ordinal, the join of two levels
    their union, the larger. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Export Functions.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Levels.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_denotes_llit {GC : GCtx} : forall Γ o, set_denotes T γ Γ (a_llit o) (fun _ => pair_ordinal_set o).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_succl {GC : GCtx} : forall Γ M FM, set_denotes T γ Γ M FM -> set_denotes T γ Γ (a_succl M) (fun ρ => successor_set (FM ρ)).
Proof.
  intros * HM. constructor; [intros ρ Hρ; constructor; exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
  intros ρ ρ' v Hr Hv. inversion Hv; subst. apply successor_set_resp.
  exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)).
Qed.

Lemma set_denotes_maxl {GC : GCtx} : forall Γ M N FM FN, set_denotes T γ Γ M FM -> set_denotes T γ Γ N FN ->
    set_denotes T γ Γ (a_maxl M N) (fun ρ => union_set (unordered_pair_set (FM ρ) (FN ρ))).
Proof.
  intros * HM HN. constructor; [intros ρ Hρ; constructor; [exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | exact (set_denotes_exists _ _ _ _ _ HN _ Hρ)] |].
  intros ρ ρ' v Hr Hv. inversion Hv; subst. apply union_set_resp. apply unordered_pair_set_resp;
    [exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)) | exact (set_denotes_unique _ _ _ _ _ HN _ _ _ Hr ltac:(eassumption))].
Qed.

(** A term of [Level@n] is an ordinal below [ω·(n+1)]. *)
Lemma level_value {GC : GCtx} : forall Γ n M FL FM FM' ρ, set_exp_eq_with T γ Γ (a_level n) M M FL FM FM' -> set_env_in T γ Γ ρ ->
    exists o, fst o <= n /\ set_eq (FM ρ) (pair_ordinal_set o).
Proof.
  intros * [HL HM _ _ Hm] Hρ. apply set_mem_level_type.
  eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HL (set_denotes_level T γ _ n) Hρ) | exact (Hm ρ Hρ)].
Qed.





(** ** Universes *)



(** ** The Level Equations *)

Lemma set_level_eq_of_values {GC : GCtx} : forall Γ n L R FL FR, set_denotes T γ Γ L FL -> set_denotes T γ Γ R FR ->
    (forall ρ, set_env_in T γ Γ ρ -> set_eq (FL ρ) (FR ρ)) ->
    (forall ρ, set_env_in T γ Γ ρ -> set_mem (FL ρ) (code_carrier (level_type_code n))) ->
    set_rel_exp_eq T γ Γ (a_level n) L R.
Proof. intros * HL HR E Hm. exists (fun _ => level_type_code n), FL, FR. constructor; [apply set_denotes_level | assumption ..]. Qed.

Lemma pair_ordinal_level : forall o n, fst o <= n -> set_mem (pair_ordinal_set o) (code_carrier (level_type_code n)).
Proof. intros. apply set_mem_level_type. exists o. split; [assumption | apply set_eq_refl]. Qed.

Lemma set_sub_eq_l : forall x x' y, set_eq x x' -> set_sub x' y -> set_sub x y.
Proof. intros * E H z Hz. apply H. eapply set_mem_eq_r; [exact E | exact Hz]. Qed.

Lemma union_pair_comm : forall x y, set_eq (union_set (unordered_pair_set x y)) (union_set (unordered_pair_set y x)).
Proof.
  intros. apply set_eq_intro; intros z Hz; apply set_mem_union in Hz as [w [Hw Hz]]; apply set_mem_union; exists w;
    (split; [apply set_mem_unordered_pair in Hw; apply set_mem_unordered_pair; tauto | exact Hz]).
Qed.

Lemma set_mem_union_pair : forall z x y, set_mem z (union_set (unordered_pair_set x y)) <-> set_mem z x \/ set_mem z y.
Proof.
  intros. rewrite set_mem_union. split.
  - intros [w [Hw Hz]]. apply set_mem_unordered_pair in Hw as [E | E]; [left | right]; eapply set_mem_eq_r; eauto.
  - intros [Hz | Hz]; [exists x | exists y]; (split; [apply set_mem_unordered_pair; auto using set_eq_refl | exact Hz]).
Qed.

Lemma union_pair_assoc : forall x y z, set_eq (union_set (unordered_pair_set (union_set (unordered_pair_set x y)) z))
                                              (union_set (unordered_pair_set x (union_set (unordered_pair_set y z)))).
Proof. intros. apply set_eq_intro; intros w Hw; rewrite !set_mem_union_pair in *; tauto. Qed.

Lemma union_pair_idem : forall x, set_eq (union_set (unordered_pair_set x x)) x.
Proof. intros. apply set_eq_intro; intros w Hw; rewrite ?set_mem_union_pair in *; tauto. Qed.

Lemma union_pair_sub : forall x y, set_sub x y -> set_eq (union_set (unordered_pair_set x y)) y.
Proof. intros x y H. apply set_eq_intro; intros w Hw; rewrite ?set_mem_union_pair in *; [destruct Hw; auto | auto]. Qed.







(** The successor of the larger is the larger of the successors. *)
Lemma pair_max_succ : forall a b a' b', pair_max (a, S b) (a', S b') = (fst (pair_max (a, b) (a', b')), S (snd (pair_max (a, b) (a', b')))).
Proof.
  intros. unfold pair_max; cbn [fst snd]. destruct (Nat.ltb a a'); [reflexivity |]. destruct (Nat.ltb a' a); [reflexivity |].
  cbn [fst snd]. f_equal.
Qed.



End Levels.
