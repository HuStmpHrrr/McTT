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
  destruct (level_value _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL HM HM (fun _ _ => set_eq_refl _) Hm) Hρ)
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
  destruct (level_value _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL HM HM (fun _ _ => set_eq_refl _) Hm) Hρ) as [x [Hx Ex]].
  destruct (level_value _ _ _ _ _ _ ρ (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HL' HN HN (fun _ _ => set_eq_refl _) Hn) Hρ) as [y [Hy Ey]].
  apply set_mem_level_type. exists (pair_max x y). split.
  - destruct (pair_max_cases x y) as [[_ ->] | [_ ->]]; assumption.
  - eapply set_eq_trans; [| apply union_pair_ordinal_set]. apply union_set_resp. apply unordered_pair_set_resp; assumption.
Qed.

(** ** Universes *)

(** A large universe is a universe. *)
Lemma set_rule_is_univ_large : forall Γ i, set_ctx_slots Θ Ξ T γ Γ -> set_universe Θ Ξ T γ Γ (a_typ i).
Proof.
  intros Γ i HΓ. set_open. destruct HΓ as [HΓ _]. exists (fun _ => large_universe_code T i).
  constructor; [exact HΓ | apply set_denotes_typ |].
  intros ρ _. exists (tower T (ul i)). split; [apply tower_grothendieck |]. exists (large_ordinal_set i). apply set_eq_refl.
Qed.

(** A universe at a level is a universe. *)
Lemma set_rule_is_univ_small : forall Γ n L, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ (a_level n) L L ->
    set_universe Θ Ξ T γ Γ (a_univ L).
Proof.
  intros * HΓ HL. set_open. destruct HΓ as [HΓ _]. destruct HL as (FL & FM & FM' & HL). pose proof HL as [_ HM _ _ _].
  exists (fun ρ => level_universe_code T (FM ρ)). constructor; [exact HΓ | exact (set_denotes_univ T γ _ _ _ HM) |].
  intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ HL Hρ) as (o & _ & Eo).
  exists (tower T (us o)). split; [apply tower_grothendieck |]. exists (FM ρ).
  unfold level_universe_code, universe_code. apply type_code_resp; [apply set_eq_refl |].
  apply separation_set_resp; [exact is_relevant_code_resp | exact is_relevant_code_resp | apply small_universe_set_eq; exact Eo | tauto].
Qed.

(** ** The Level Equations *)

Lemma set_rule_level_eq {GC : GCtx} : forall Γ n L R FL FR, set_denotes T γ Γ L FL -> set_denotes T γ Γ R FR ->
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

(** [𝕃(a, S b) ≈ succl 𝕃(a, b)]. *)
Lemma set_rule_llit_succl : forall Γ a b n, a <= n ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_llit (a, S b)) (a_succl (a_llit (a, b))).
Proof.
  intros * Ha. set_open. apply (set_rule_level_eq _ _ _ _ _ _ (set_denotes_llit _ _) (set_denotes_succl _ _ _ (set_denotes_llit _ _)));
    [intros; apply set_eq_refl | intros; apply pair_ordinal_level; exact Ha].
Qed.

(** [maxl M 𝕃(S n, 0) ≈ 𝕃(S n, 0) : Level@(S n)]. *)
Lemma set_rule_maxl_absorb : forall Γ n M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_level (S n)) (a_maxl M (a_llit (S n, 0))) (a_llit (S n, 0)).
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ _].
  apply (set_rule_level_eq _ _ _ _ _ _ (set_denotes_maxl _ _ _ _ _ HM (set_denotes_llit _ _)) (set_denotes_llit _ _)).
  - intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
    apply union_pair_sub. eapply set_sub_eq_l; [exact Ex |].
    apply pair_ordinal_set_sub. left. destruct x as [a b]. unfold pair_lt. cbn in *. lia.
  - intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
    eapply set_mem_eq_l; [apply set_eq_sym; apply union_pair_sub |].
    + eapply set_sub_eq_l; [exact Ex |]. apply pair_ordinal_set_sub. left. destruct x as [a b]. unfold pair_lt. cbn in *. lia.
    + apply pair_ordinal_level. cbn. lia.
Qed.

(** [maxl 𝕃@0 M ≈ M]. *)
Lemma set_rule_maxl_zero : forall Γ n M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl (a_llit (0, 0)) M) M.
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ Hm].
  apply (set_rule_level_eq _ _ _ _ _ _ (set_denotes_maxl _ _ _ _ _ (set_denotes_llit _ _) HM) HM).
  - intros ρ Hρ. apply union_pair_sub. intros z Hz. destruct (set_mem_empty _ Hz).
  - intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
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
  apply (set_rule_level_eq _ _ _ _ _ _ (set_denotes_maxl _ _ _ _ _ (set_denotes_maxl _ _ _ _ _ HM HN) HP)
           (set_denotes_maxl _ _ _ _ _ HM (set_denotes_maxl _ _ _ _ _ HN HP))); [intros; apply union_pair_assoc |].
  intros ρ Hρ.
  destruct (level_value _ _ _ _ _ _ _ HMe Hρ) as [x [Hx Ex]]. destruct (level_value _ _ _ _ _ _ _ HNe Hρ) as [y [Hy Ey]].
  destruct (level_value _ _ _ _ _ _ _ HPe Hρ) as [z [Hz Ez]].
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
  intros ρ Hρ. eapply set_eq_trans; [exact (set_denotes_agree _ _ _ _ _ _ _ HL0 (set_denotes_maxl _ _ _ _ _ HM HN) Hρ) |].
  apply union_pair_comm.
Qed.

Lemma set_rule_maxl_idem : forall Γ n M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl M M) M.
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ Hm].
  apply (set_rule_level_eq _ _ _ _ _ _ (set_denotes_maxl _ _ _ _ _ HM HM) HM); [intros; apply union_pair_idem |].
  intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ H Hρ) as [x [Hx Ex]].
  eapply set_mem_eq_l; [apply set_eq_sym; apply union_pair_idem |].
  eapply set_mem_eq_l; [apply set_eq_sym; exact Ex | apply pair_ordinal_level; exact Hx].
Qed.

(** The successor of the larger is the larger of the successors. *)
Lemma pair_max_succ : forall a b a' b', pair_max (a, S b) (a', S b') = (fst (pair_max (a, b) (a', b')), S (snd (pair_max (a, b) (a', b')))).
Proof.
  intros. unfold pair_max; cbn [fst snd]. destruct (Nat.ltb a a'); [reflexivity |]. destruct (Nat.ltb a' a); [reflexivity |].
  cbn [fst snd]. f_equal.
Qed.

Lemma set_rule_succl_maxl : forall Γ n M N,
    set_exp_eq Θ Ξ T γ Γ (a_level n) M M -> set_exp_eq Θ Ξ T γ Γ (a_level n) N N ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_succl (a_maxl M N)) (a_maxl (a_succl M) (a_succl N)).
Proof.
  intros * HMe HNe. set_open. destruct HMe as (FL & FM & FM' & HMe). destruct HNe as (FL' & FN & FN' & HNe). pose proof HMe as [_ HM _ _ _]. pose proof HNe as [_ HN _ _ _].
  apply (set_rule_level_eq _ _ _ _ _ _ (set_denotes_succl _ _ _ (set_denotes_maxl _ _ _ _ _ HM HN))
           (set_denotes_maxl _ _ _ _ _ (set_denotes_succl _ _ _ HM) (set_denotes_succl _ _ _ HN))).
  - intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ HMe Hρ) as [[a b] [Hx Ex]]. destruct (level_value _ _ _ _ _ _ _ HNe Hρ) as [[a' b'] [Hy Ey]].
    eapply set_eq_trans; [apply successor_set_resp; eapply set_eq_trans;
                          [apply union_set_resp; apply unordered_pair_set_resp; [exact Ex | exact Ey] | apply union_pair_ordinal_set] |].
    eapply set_eq_trans; [| apply set_eq_sym; apply union_set_resp; apply unordered_pair_set_resp;
                             [apply successor_set_resp; exact Ex | apply successor_set_resp; exact Ey]].
    change (set_eq (successor_set (pair_ordinal_set (pair_max (a, b) (a', b'))))
                   (union_set (unordered_pair_set (pair_ordinal_set (a, S b)) (pair_ordinal_set (a', S b'))))).
    eapply set_eq_trans; [| apply set_eq_sym; apply union_pair_ordinal_set]. rewrite pair_max_succ.
    destruct (pair_max (a, b) (a', b')). apply set_eq_refl.
  - intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ HMe Hρ) as [[a b] [Hx Ex]]. destruct (level_value _ _ _ _ _ _ _ HNe Hρ) as [[a' b'] [Hy Ey]].
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
  apply (set_rule_level_eq _ _ _ _ _ _ (set_denotes_maxl _ _ _ _ _ HM (set_denotes_succl _ _ _ HM)) (set_denotes_succl _ _ _ HM));
    [intros; apply union_pair_sub; apply set_sub_successor |].
  intros ρ Hρ. destruct (level_value _ _ _ _ _ _ _ H Hρ) as [[a b] [Hx Ex]].
  eapply set_mem_eq_l; [apply set_eq_sym; apply union_pair_sub; apply set_sub_successor |].
  apply set_mem_level_type. exists (a, S b). split; [exact Hx | apply successor_set_resp; exact Ex].
Qed.

End Levels.
