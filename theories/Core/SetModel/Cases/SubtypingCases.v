(** * The Set Rules of Subtyping

    A subtype's carriers are in the supertype's: universes grow with their
    indices, types of levels with their sorts, small universes are in the
    large ones, and a [Π] into an evaluated kind is covariant in its
    codomain.  A term of a subtype is a term of the supertype. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Cases Require Export LevelCases.
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

(** Subsumption. *)
Lemma set_rule_exp_eq_subtyp : forall Γ A A' M M', set_exp_eq Θ Ξ T γ Γ A M M' ->
    set_subtyp Θ Ξ T γ Γ A A' -> set_exp_eq Θ Ξ T γ Γ A' M M'.
Proof.
  intros * HM HA. set_open. destruct HM as (FA & FM & FM' & HM). destruct HA as (FA0 & FA' & HA).
  exact (set_exp_eq_at_supertype _ _ _ _ _ _ _ _ _ _ HM HA).
Qed.

(** Equality of terms is symmetric. *)
Lemma set_rule_exp_eq_sym : forall Γ A M M', set_exp_eq Θ Ξ T γ Γ A M M' -> set_exp_eq Θ Ξ T γ Γ A M' M.
Proof.
  intros * HM. set_open. destruct HM as (FA & FM & FM' & [HA HM HM' E Hm]). exists FA, FM', FM. constructor; try assumption.
  - intros ρ Hρ. apply set_eq_sym. exact (E _ Hρ).
  - intros ρ Hρ. exact (set_mem_eq_l _ _ _ (E _ Hρ) (Hm _ Hρ)).
Qed.

(** And transitive. *)
Lemma set_rule_exp_eq_trans : forall Γ A M M' M'', set_exp_eq Θ Ξ T γ Γ A M M' -> set_exp_eq Θ Ξ T γ Γ A M' M'' ->
    set_exp_eq Θ Ξ T γ Γ A M M''.
Proof.
  intros * H1 H2. set_open. destruct H1 as (FA & FM & FM' & [HA HM HM' E Hm]). destruct H2 as (GA & GM & GM' & [_ HGM HGM' E' _]).
  exists FA, FM, GM'.
  constructor; try assumption.
  intros ρ Hρ. eapply set_eq_trans; [exact (E _ Hρ) |]. eapply set_eq_trans; [exact (set_denotes_agree _ _ _ _ _ _ _ HM' HGM Hρ) |].
  exact (E' _ Hρ).
Qed.

(** Equal types are subtypes. *)
Lemma set_rule_subtyp_refl : forall Γ S M M', set_exp_eq Θ Ξ T γ Γ S M M' -> set_subtyp Θ Ξ T γ Γ M M'.
Proof.
  intros * H. set_open. destruct H as (FS & FM & FM' & [_ HM HM' E _]). exists FM, FM'. constructor; [exact HM | exact HM' |]. intros ρ Hρ z Hz.
  eapply set_mem_eq_r; [apply code_carrier_resp; exact (E ρ Hρ) | exact Hz].
Qed.

Lemma set_rule_subtyp_trans : forall Γ A A' A'', set_subtyp Θ Ξ T γ Γ A A' -> set_subtyp Θ Ξ T γ Γ A' A'' ->
    set_subtyp Θ Ξ T γ Γ A A''.
Proof.
  intros * Hs1 Hs2. set_open. destruct Hs1 as (FA & FA' & [HA HA' H1]). destruct Hs2 as (FB & FB' & [HB HB' H2]). exists FA, FB'. constructor; [exact HA | exact HB' |].
  intros ρ Hρ z Hz. apply H2; [exact Hρ |]. eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HA' HB Hρ) |].
  apply H1; assumption.
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

(** [Typeω@i ⊆ Typeω@j], [i < j]. *)
Lemma set_rule_subtyp_univ : forall Γ i j, i < j -> set_subtyp Θ Ξ T γ Γ (a_typ i) (a_typ j).
Proof. intros * H. set_open. exact (set_subtyp_typ_lt _ _ _ H). Qed.

(** [Level@m ⊆ Level@n], [m ≤ n]. *)
Lemma set_rule_subtyp_level : forall Γ m n, m <= n -> set_subtyp Θ Ξ T γ Γ (a_level m) (a_level n).
Proof.
  intros * H. set_open. exists (fun _ => level_type_code m), (fun _ => level_type_code n).
  constructor; [apply set_denotes_level .. |]. intros ρ _ z Hz.
  apply set_mem_level_type in Hz as [o [Ho E]]. apply set_mem_level_type. exists o. split; [lia | exact E].
Qed.

(** A small universe is below every large one. *)
Lemma set_rule_subtyp_small_large : forall Γ n i M, set_exp_eq Θ Ξ T γ Γ (a_level n) M M ->
    set_subtyp Θ Ξ T γ Γ (a_univ M) (a_typ i).
Proof.
  intros * H. set_open. destruct H as (FL & FM & FM' & H). pose proof H as [_ HM _ _ _]. exists (fun ρ => level_universe_code T (FM ρ)), (fun _ => large_universe_code T i).
  constructor; [apply set_denotes_univ; exact HM | apply set_denotes_typ |]. intros ρ Hρ.
  destruct (level_value _ _ _ _ _ _ _ _ _ H Hρ) as [o [_ Eo]]. apply universe_code_sub. intros z Hz.
  eapply set_mem_eq_r in Hz; [| apply small_universe_set_eq; exact Eo]. apply (tower_sub T (us o) (ul i)); [exact I | exact Hz].
Qed.

(** [Type⟨M⟩ ⊆ Type⟨M'⟩] when [maxl M M' ≈ M']. *)
Lemma set_rule_subtyp_suniv : forall Γ n M M',
    set_exp_eq Θ Ξ T γ Γ (a_level n) M M -> set_exp_eq Θ Ξ T γ Γ (a_level n) M' M' ->
    set_exp_eq Θ Ξ T γ Γ (a_level n) (a_maxl M M') M' ->
    set_subtyp Θ Ξ T γ Γ (a_univ M) (a_univ M').
Proof.
  intros * HMe HM'e HXe. set_open. destruct HMe as (FL & FM & FM2 & HMe). destruct HM'e as (FL' & FM' & FM'2 & HM'e).
  destruct HXe as (FA & FX & FX' & [_ HX HX' EX _]). pose proof HMe as [_ HM _ _ _]. pose proof HM'e as [_ HM' _ _ _].
  exists (fun ρ => level_universe_code T (FM ρ)), (fun ρ => level_universe_code T (FM' ρ)).
  constructor; [apply set_denotes_univ; assumption .. |]. intros ρ Hρ.
  destruct (level_value _ _ _ _ _ _ _ _ _ HMe Hρ) as [o [_ Eo]]. destruct (level_value _ _ _ _ _ _ _ _ _ HM'e Hρ) as [o' [_ Eo']].
  assert (Emax : set_eq (pair_ordinal_set (pair_max o o')) (pair_ordinal_set o')).
  { eapply set_eq_trans; [apply set_eq_sym; apply union_pair_ordinal_set |].
    eapply set_eq_trans; [apply union_set_resp; apply unordered_pair_set_resp; [apply set_eq_sym; exact Eo | apply set_eq_sym; exact Eo'] |].
    eapply set_eq_trans; [apply set_eq_sym; exact (set_denotes_agree _ _ _ _ _ _ _ HX (set_denotes_maxl _ _ _ _ _ _ _ HM HM') Hρ) |].
    eapply set_eq_trans; [exact (EX ρ Hρ) |]. eapply set_eq_trans; [exact (set_denotes_agree _ _ _ _ _ _ _ HX' HM' Hρ) | exact Eo']. }
  apply pair_ordinal_set_inj in Emax.
  apply universe_code_sub. intros z Hz.
  eapply set_mem_eq_r in Hz; [| apply small_universe_set_eq; exact Eo].
  eapply set_mem_eq_r; [apply set_eq_sym; apply small_universe_set_eq; exact Eo' |].
  apply (tower_sub T (us o) (us o')); [| exact Hz]. cbn.
  destruct (pair_max_cases o o') as [[[Hlt | ->] _] | [[Hlt | ->] Hm]]; unfold ordinal_le, pair_lt in *.
  - destruct Hlt as [Hlt | [Ha Hb]]; [left; exact Hlt | right; split; [exact Ha | lia]].
  - right; split; [reflexivity | lia].
  - rewrite Hm in Emax. subst o'. right; split; [reflexivity | lia].
  - right; split; [reflexivity | lia].
Qed.

(** A [Π] into an evaluated kind is covariant in its codomain. *)
Lemma set_rule_subtyp_pi : forall Γ κd κc i A A' B B', set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ -> ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A' :: Γ ->
    Θ ⍮ Ξ ⍮ ce_ass κd A' :: Γ ⊢ˢ sb_id : ce_ass κd A :: Γ -> κc <> ak_propositional ->
    set_exp_eq Θ Ξ T γ Γ (abs_kind_sort κd (a_typ i)) A A' ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A' :: Γ) (abs_kind_sort κc (a_typ i)) B' B' ->
    set_subtyp Θ Ξ T γ (ce_ass κd A' :: Γ) B B' ->
    set_subtyp Θ Ξ T γ Γ (a_pi κd κc A B) (a_pi κd κc A' B').
Proof.
  intros * HΓ Hc Hc' Hσ Hκ HAe HBe HB'e HXe. set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS & FA & FA' & [_ HA HA' EA _]). destruct HBe as (FS1 & FB & FB1 & [_ HB _ _ _]).
  destruct HB'e as (FS2 & FB' & FB'2 & [_ HB' _ _ _]). destruct HXe as (FX & FX' & [HX HX' Hsub]).
  pose proof (set_denotes_ctx_conv_ass _ _ _ _ _ _ _ _ _ _ Hfn Hmods HΓ Hc Hσ HA HA' EA HB) as HBc.
  exists (pi_denotation κd κc FA FB), (pi_denotation κd κc FA' FB').
  constructor; [apply set_denotes_pi; assumption .. |]. intros ρ Hρ.
  pose proof (set_denotes_exists _ _ _ _ _ HA' _ Hρ) as Ha'.
  assert (Hx : forall x, set_mem x (code_carrier (FA' ρ)) -> set_env_in T γ (ce_ass κd A' :: Γ) (set_env_extend ρ (set_entry_term κd x)))
    by (intros x Hx; exact (set_env_in_extend_ass T γ Γ ρ κd A' _ x Hρ Ha' Hx)).
  assert (Hpt : forall x, set_mem x (code_carrier (FA' ρ)) ->
            set_sub (code_carrier (body_function κd FB ρ x)) (code_carrier (body_function κd FB' ρ x))).
  { intros x Hxa z Hz. unfold body_function in *.
    eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HX' HB' (Hx x Hxa)) |].
    apply Hsub; [exact (Hx x Hxa) |].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HBc HX (Hx x Hxa)) | exact Hz]. }
  assert (HrB : respects_on (code_carrier (FA ρ)) (fun x => code_carrier (body_function κd FB ρ x)))
    by (intros x y Hxa E; apply code_carrier_resp; exact (body_function_respects _ _ _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hxa E)).
  assert (HrB' : respects_on (code_carrier (FA' ρ)) (fun x => code_carrier (body_function κd FB' ρ x)))
    by (intros x y Hxa E; apply code_carrier_resp; exact (body_function_respects _ _ _ _ _ _ _ _ _ HΓ HA' HB' Hρ _ _ Hxa E)).
  pose proof (code_carrier_resp _ _ (EA ρ Hρ)) as Ec.
  assert (Hfs : set_sub (function_set (code_carrier (FA ρ)) (fun x => code_carrier (body_function κd FB ρ x)))
                        (function_set (code_carrier (FA' ρ)) (fun x => code_carrier (body_function κd FB' ρ x)))).
  { intros g Hg. eapply set_mem_eq_r in Hg.
    - revert g Hg. apply function_set_mono_on; [| exact HrB' | exact Hpt].
      intros x y Hxa E. apply HrB; [eapply set_mem_eq_r; [apply set_eq_sym; exact Ec | exact Hxa] | exact E].
    - apply function_set_resp_on; [exact Ec |]. intros x x' Hxa E. apply HrB; assumption. }
  destruct κc; [| contradiction |]; cbn [pi_denotation]; unfold pi_code; intros g Hg.
  all: eapply set_mem_eq_r in Hg; [| apply code_carrier_type_code].
  all: eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code | apply Hfs; exact Hg].
Qed.

End Subtyping.
