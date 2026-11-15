(** * The Set Rules of Levels

    The rules of the types of levels in the set model: [Level@n], the
    literals, [succl], [maxl], their congruences and the equations of
    levels.  The lemmas they rest on are in [Judgments/Levels.v]. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Import Levels.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Levels.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** [Level@n : LevelSort]. *)
Lemma set_rule_level : forall Γ n, set_exp_eq Θ Ξ T γ Γ a_level_sort (a_level n) (a_level n).
Proof.
  intros. set_open. exists (fun _ => level_sort_code (level_types_universe T)), (fun _ => level_type_code n), (fun _ => level_type_code n).
  constructor; [apply set_denotes_level_sort | apply set_denotes_level | apply set_denotes_level | intros; apply set_eq_refl |].
  intros ρ _. unfold level_sort_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  apply set_mem_separation; [exact is_level_type_code_resp |]. split; [| eapply is_level_type_code_level; apply set_eq_refl].
  apply set_mem_union. exists (tower T (us (0, 0))). split; [exists (0, 0); apply set_eq_refl |].
  apply grothendieck_level_type_code. apply tower_grothendieck.
Qed.

(** A level literal [𝕃ᵒ o : Level@n], [o]'s tier at most [n]. *)
Lemma set_rule_llit : forall Γ o n, fst o <= n -> set_exp_eq Θ Ξ T γ Γ (a_level n) (a_llit o) (a_llit o).
Proof.
  intros * Ho. set_open. exists (fun _ => level_type_code n), (fun _ => pair_ordinal_set o), (fun _ => pair_ordinal_set o).
  constructor; [apply set_denotes_level | apply set_denotes_llit .. | intros; apply set_eq_refl |].
  intros ρ _. apply set_mem_level_type. exists o. split; [exact Ho | apply set_eq_refl].
Qed.

(** [M ≈ M' : Level@n] gives [succl M ≈ succl M' : Level@n]. *)
Lemma set_rule_succl : forall Γ n M M', set_exp_eq Θ Ξ T γ Γ (a_level n) M M' ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_succl M) (a_succl M').
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [HL HM HM' E Hm].
  exists (fun _ => level_type_code n), (fun ρ => successor_set (FM ρ)), (fun ρ => successor_set (FM' ρ)).
  constructor; [apply set_denotes_level | apply set_denotes_succl; assumption .. | intros ρ Hρ; apply successor_set_resp; exact (E ρ Hρ) |].
  intros ρ Hρ.
  destruct (level_value T γ _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL HM HM (fun _ _ => set_eq_refl _) Hm) Hρ)
    as [[a b] [Ho Eo]].
  apply set_mem_level_type. exists (a, S b). split; [exact Ho |]. apply successor_set_resp. exact Eo.
Qed.

(** [M ≈ M'] and [N ≈ N'] at [Level@n] give [maxl M N ≈ maxl M' N']. *)
Lemma set_rule_maxl : forall Γ n M M' N N', set_exp_eq Θ Ξ T γ Γ (a_level n) M M' ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) N N' -> set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl M N) (a_maxl M' N').
Proof.
  intros * HMe HNe. set_open. destruct HMe as (FL & FM & FM' & HMe). destruct HNe as (FL' & FN & FN' & HNe). pose proof HMe as [HL HM HM' EM Hm]. pose proof HNe as [HL' HN HN' EN Hn].
  exists (fun _ => level_type_code n), (fun ρ => union_set (unordered_pair_set (FM ρ) (FN ρ))),
    (fun ρ => union_set (unordered_pair_set (FM' ρ) (FN' ρ))).
  constructor; [apply set_denotes_level | apply set_denotes_maxl; assumption .. |
                intros ρ Hρ; apply union_set_resp; apply unordered_pair_set_resp; [exact (EM ρ Hρ) | exact (EN ρ Hρ)] |].
  intros ρ Hρ.
  destruct (level_value T γ _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL HM HM (fun _ _ => set_eq_refl _) Hm) Hρ) as [x [Hx Ex]].
  destruct (level_value T γ _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL' HN HN (fun _ _ => set_eq_refl _) Hn) Hρ) as [y [Hy Ey]].
  apply set_mem_level_type. exists (pair_max x y). split.
  - destruct (pair_max_cases x y) as [[_ ->] | [_ ->]]; assumption.
  - eapply set_eq_trans; [| apply union_pair_ordinal_set]. apply union_set_resp. apply unordered_pair_set_resp; assumption.
Qed.

(** [𝕃(a, S b) ≈ succl 𝕃(a, b)]. *)
Lemma set_rule_llit_succl : forall Γ a b n, a <= n ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_llit (a, S b)) (a_succl (a_llit (a, b))).
Proof.
  intros * Ha. set_open. apply (set_level_eq_of_values T γ _ _ _ _ _ _ (set_denotes_llit T γ _ _) (set_denotes_succl T γ _ _ _ (set_denotes_llit T γ _ _)));
    [intros; apply set_eq_refl | intros; apply pair_ordinal_level; exact Ha].
Qed.

(** [maxl M 𝕃(S n, 0) ≈ 𝕃(S n, 0) : Level@(S n)]. *)
Lemma set_rule_maxl_absorb : forall Γ n M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_level (S n)) (a_maxl M (a_llit (S n, 0))) (a_llit (S n, 0)).
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ _].
  apply (set_level_eq_of_values T γ _ _ _ _ _ _ (set_denotes_maxl T γ _ _ _ _ _ HM (set_denotes_llit T γ _ _)) (set_denotes_llit T γ _ _)).
  - intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
    apply union_pair_sub. eapply set_sub_eq_l; [exact Ex |].
    apply pair_ordinal_set_sub. left. destruct x as [a b]. unfold pair_lt. cbn in *. lia.
  - intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
    eapply set_mem_eq_l; [apply set_eq_sym; apply union_pair_sub |].
    + eapply set_sub_eq_l; [exact Ex |]. apply pair_ordinal_set_sub. left. destruct x as [a b]. unfold pair_lt. cbn in *. lia.
    + apply pair_ordinal_level. cbn. lia.
Qed.

(** [maxl 𝕃@0 M ≈ M]. *)
Lemma set_rule_maxl_zero : forall Γ n M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl (a_llit (0, 0)) M) M.
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ Hm].
  apply (set_level_eq_of_values T γ _ _ _ _ _ _ (set_denotes_maxl T γ _ _ _ _ _ (set_denotes_llit T γ _ _) HM) HM).
  - intros ρ Hρ. apply union_pair_sub. intros z Hz. destruct (set_mem_empty _ Hz).
  - intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
    eapply set_mem_eq_l; [apply set_eq_sym; apply union_pair_sub; intros z Hz; destruct (set_mem_empty _ Hz) |].
    eapply set_mem_eq_l; [apply set_eq_sym; exact Ex | apply pair_ordinal_level; exact Hx].
Qed.

(** The join is associative, commutative and idempotent. *)
Lemma set_rule_maxl_assoc : forall Γ n M N P,
    set_exp_eq Θ Ξ T γ Γ (a_level n) M M -> set_exp_eq Θ Ξ T γ Γ (a_level n) N N ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) P P ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl (a_maxl M N) P) (a_maxl M (a_maxl N P)).
Proof.
  intros * HMe HNe HPe. set_open. destruct HMe as (FL & FM & FM' & HMe). destruct HNe as (FL' & FN & FN' & HNe).
  destruct HPe as (FL'' & FP & FP' & HPe). pose proof HMe as [_ HM _ _ _]. pose proof HNe as [_ HN _ _ _]. pose proof HPe as [_ HP _ _ _].
  apply (set_level_eq_of_values T γ _ _ _ _ _ _ (set_denotes_maxl T γ _ _ _ _ _ (set_denotes_maxl T γ _ _ _ _ _ HM HN) HP)
           (set_denotes_maxl T γ _ _ _ _ _ HM (set_denotes_maxl T γ _ _ _ _ _ HN HP))); [intros; apply union_pair_assoc |].
  intros ρ Hρ.
  destruct (level_value T γ _ _ _ _ _ _ _ HMe Hρ) as [x [Hx Ex]]. destruct (level_value T γ _ _ _ _ _ _ _ HNe Hρ) as [y [Hy Ey]].
  destruct (level_value T γ _ _ _ _ _ _ _ HPe Hρ) as [z [Hz Ez]].
  eapply set_mem_eq_l; [| apply (pair_ordinal_level (pair_max (pair_max x y) z) n)].
  - apply set_eq_sym. eapply set_eq_trans; [| apply union_pair_ordinal_set]. apply union_set_resp. apply unordered_pair_set_resp; [| exact Ez].
    eapply set_eq_trans; [| apply union_pair_ordinal_set]. apply union_set_resp. apply unordered_pair_set_resp; assumption.
  - destruct (pair_max_cases (pair_max x y) z) as [[_ ->] | [_ ->]]; [exact Hz |].
    destruct (pair_max_cases x y) as [[_ ->] | [_ ->]]; assumption.
Qed.

Lemma set_rule_maxl_comm : forall Γ n M N,
    set_exp_eq Θ Ξ T γ Γ (a_level n) M M -> set_exp_eq Θ Ξ T γ Γ (a_level n) N N ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl M N) (a_maxl N M).
Proof.
  intros * HMe HNe. pose proof (set_rule_maxl _ _ _ _ _ _ HMe HNe) as Hmax. set_open.
  destruct HMe as (FL & FM & FM' & HMe). destruct HNe as (FL' & FN & FN' & HNe).
  destruct Hmax as (FA & FL0 & _ & [HA HL0 _ _ Hm0]).
  pose proof HMe as [_ HM _ _ _]. pose proof HNe as [_ HN _ _ _].
  exists FA, FL0, (fun ρ => union_set (unordered_pair_set (FN ρ) (FM ρ))).
  constructor; [exact HA | exact HL0 | apply set_denotes_maxl; assumption | | exact Hm0].
  intros ρ Hρ. eapply set_eq_trans; [exact (set_denotes_agree _ _ _ _ _ _ _ HL0 (set_denotes_maxl T γ _ _ _ _ _ HM HN) Hρ) |].
  apply union_pair_comm.
Qed.

Lemma set_rule_maxl_idem : forall Γ n M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl M M) M.
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ Hm].
  apply (set_level_eq_of_values T γ _ _ _ _ _ _ (set_denotes_maxl T γ _ _ _ _ _ HM HM) HM); [intros; apply union_pair_idem |].
  intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
  eapply set_mem_eq_l; [apply set_eq_sym; apply union_pair_idem |].
  eapply set_mem_eq_l; [apply set_eq_sym; exact Ex | apply pair_ordinal_level; exact Hx].
Qed.

Lemma set_rule_succl_maxl : forall Γ n M N,
    set_exp_eq Θ Ξ T γ Γ (a_level n) M M -> set_exp_eq Θ Ξ T γ Γ (a_level n) N N ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_succl (a_maxl M N)) (a_maxl (a_succl M) (a_succl N)).
Proof.
  intros * HMe HNe. set_open. destruct HMe as (FL & FM & FM' & HMe). destruct HNe as (FL' & FN & FN' & HNe). pose proof HMe as [_ HM _ _ _]. pose proof HNe as [_ HN _ _ _].
  apply (set_level_eq_of_values T γ _ _ _ _ _ _ (set_denotes_succl T γ _ _ _ (set_denotes_maxl T γ _ _ _ _ _ HM HN))
           (set_denotes_maxl T γ _ _ _ _ _ (set_denotes_succl T γ _ _ _ HM) (set_denotes_succl T γ _ _ _ HN))).
  - intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ HMe Hρ) as [[a b] [Hx Ex]]. destruct (level_value T γ _ _ _ _ _ _ _ HNe Hρ) as [[a' b'] [Hy Ey]].
    eapply set_eq_trans; [apply successor_set_resp; eapply set_eq_trans;
                          [apply union_set_resp; apply unordered_pair_set_resp; [exact Ex | exact Ey] | apply union_pair_ordinal_set] |].
    eapply set_eq_trans; [| apply set_eq_sym; apply union_set_resp; apply unordered_pair_set_resp;
                             [apply successor_set_resp; exact Ex | apply successor_set_resp; exact Ey]].
    change (set_eq (successor_set (pair_ordinal_set (pair_max (a, b) (a', b'))))
                   (union_set (unordered_pair_set (pair_ordinal_set (a, S b)) (pair_ordinal_set (a', S b'))))).
    eapply set_eq_trans; [| apply set_eq_sym; apply union_pair_ordinal_set]. rewrite pair_max_succ.
    destruct (pair_max (a, b) (a', b')). apply set_eq_refl.
  - intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ HMe Hρ) as [[a b] [Hx Ex]]. destruct (level_value T γ _ _ _ _ _ _ _ HNe Hρ) as [[a' b'] [Hy Ey]].
    apply set_mem_level_type. exists (fst (pair_max (a, b) (a', b')), S (snd (pair_max (a, b) (a', b')))). split.
    + cbn [fst]. destruct (pair_max_cases (a, b) (a', b')) as [[_ ->] | [_ ->]]; assumption.
    + apply successor_set_resp. eapply set_eq_trans; [apply union_set_resp; apply unordered_pair_set_resp; [exact Ex | exact Ey] |].
      eapply set_eq_trans; [apply union_pair_ordinal_set |]. destruct (pair_max (a, b) (a', b')). apply set_eq_refl.
Qed.

(** [maxl M (succl M) ≈ succl M]. *)
Lemma set_rule_maxl_succl : forall Γ n M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl M (a_succl M)) (a_succl M).
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ _].
  apply (set_level_eq_of_values T γ _ _ _ _ _ _ (set_denotes_maxl T γ _ _ _ _ _ HM (set_denotes_succl T γ _ _ _ HM)) (set_denotes_succl T γ _ _ _ HM));
    [intros; apply union_pair_sub; apply set_sub_successor |].
  intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ H Hρ) as [[a b] [Hx Ex]].
  eapply set_mem_eq_l; [apply set_eq_sym; apply union_pair_sub; apply set_sub_successor |].
  apply set_mem_level_type. exists (a, S b). split; [exact Hx | apply successor_set_resp; exact Ex].
Qed.

End Levels.
