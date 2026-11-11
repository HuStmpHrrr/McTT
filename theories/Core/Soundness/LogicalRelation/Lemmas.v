From Stdlib Require Import Lia List PeanoNat Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import ContextCases FundamentalTheorem UniverseCases UnitCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Soundness.LogicalRelation Require Export Realizability.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Semantic Require Import RecordPER.
From Mctt.Core.Completeness.Consequences Require Import AnnotatedUpto.
From Mctt.Core.Soundness Require Import KeptProofs.
From Mctt.Core.Syntactic.System Require Import LetPeeling.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** An equation at the sort of a kind next to a large universe holds next
    to a larger one. *)
Lemma wf_exp_eq_kind_sort_max_left : forall Γ κ X Y n m,
    Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@n -> Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@(max n m).
Proof. intros * H; destruct κ; cbn in *; [ mauto 3 using lift_exp_eq_max_left | exact H | exact H ]. Qed.

Lemma wf_exp_eq_kind_sort_max_right : forall Γ κ X Y n m,
    Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@m -> Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@(max n m).
Proof. intros * H; destruct κ; cbn in *; [ mauto 3 using lift_exp_eq_max_right | exact H | exact H ]. Qed.

(** Two types glued at the same value are equal: both are equal to its
    annotated readback. *)
Lemma glu_typ_top_unique : forall i j a Γ A A',
    Γ ⊢ A ® glu_typ_top i a -> Γ ⊢ A' ® glu_typ_top j a ->
    Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(max (large_level i) (large_level j)).
Proof.
  intros * [HA Hp Hr] [_ _ Hr'].
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  destruct (Hp (length Γ)) as [V V0 HV _ _].
  pose proof (Hr _ _ _ Hid HV) as H1; pose proof (Hr' _ _ _ Hid HV) as H2; unfold glu_nf_eq in H1, H2.
  rewrite exp_wk_id in H1, H2.
  apply wf_exp_eq_kind_sort_max_left with (m := large_level j) in H1.
  apply wf_exp_eq_kind_sort_max_right with (n := large_level i) in H2.
  etransitivity; [ exact H1 | symmetry; exact H2 ].
Qed.

Lemma glu_univ_elem_typ_unique_upto_exp_eq : forall {i j : universe_index} {a P P' El El' Γ A A'},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(max (large_level i) (large_level j)).
Proof.
  intros * Hi Hj Hn HA HA'; apply glu_typ_top_unique; eapply realize_glu_typ_top; eassumption.
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq : mctt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq_ge : forall {i j : universe_index} {a P P' El El' Γ A A'},
    universe_index_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level j).
Proof.
  intros.
  replace (large_level j) with (max (large_level i) (large_level j))
    by (pose proof (universe_index_le_large_level_le _ _ ltac:(eassumption)); lia).
  eapply glu_univ_elem_typ_unique_upto_exp_eq; eassumption.
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq_ge : mctt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq' : forall {i : universe_index} {a P El Γ A A'},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P ->
    Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i).
Proof.
  intros; rewrite <- (PeanoNat.Nat.max_id (large_level i)).
  eapply glu_univ_elem_typ_unique_upto_exp_eq; eassumption.
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq' : mctt.

Lemma glu_univ_elem_per_univ_elem_typ_escape : forall {i : universe_index} {a a' elem_rel P P' El El' Γ A A'},
    DF a ≈ a' ∈ per_univ_elem i ↘ elem_rel ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i).
Proof.
  intros * Hper Hglu Hglu' Hn HA HA'; exact (glu_univ_elem_typ_unique _ _ _ _ _ _ _ _ Hglu Hglu' Hper Hn _ _ _ HA HA').
Qed.

Hint Resolve glu_univ_elem_per_univ_elem_typ_escape : mctt.

Lemma glu_univ_elem_per_univ_typ_escape : forall {i : universe_index} {a a' P P' El El' Γ A A'},
    Dom a ≈ a' ∈ per_univ i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i).
Proof.
  intros * [] **.
  eapply glu_univ_elem_per_univ_elem_typ_escape; eassumption.
Qed.

Hint Resolve glu_univ_elem_per_univ_typ_escape : mctt.

Corollary glu_univ_elem_cumu_ge : forall {i : nat} {j : nat} {a P El},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem j ↘ P' ↘ El'.
Proof.
  intros.
  assert (Dom a ≈ a ∈ per_univ i) as [R] by mauto.
  assert (DF a ≈ a ∈ per_univ_elem j ↘ R) by mauto.
  mauto.
Qed.

Hint Resolve glu_univ_elem_cumu_ge : mctt.

(** The same along the order of universe indices: in particular, a small type
    is glued at every large index. *)
Corollary glu_univ_elem_cumu_ge_universe_index : forall {i j : universe_index} {a P El},
    universe_index_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem j ↘ P' ↘ El'.
Proof.
  intros.
  assert (Dom a ≈ a ∈ per_univ i) as [R] by mauto 2.
  assert (DF a ≈ a ∈ per_univ_elem j ↘ R) by (eapply per_univ_elem_cumu_universe_index; eassumption).
  mauto 2.
Qed.

Corollary glu_univ_elem_cumu_max_left : forall {i : nat} {j : nat} {a P El},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El'.
Proof.
  intros.
  assert (i <= max i j) by lia.
  mauto.
Qed.

Corollary glu_univ_elem_cumu_max_right : forall {i : nat} {j : nat} {a P El},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El'.
Proof.
  intros.
  assert (j <= max i j) by lia.
  mauto.
Qed.

(** ** Inductive Types Across Universes

    The gluing of an inductive type at two universes differs in the gluings
    of the types of its telescopes; the components in its type predicate
    move an element down, as the domain and codomains of a [Π] do. *)

Lemma ind_components_lower_n : forall p D ups NP NEl AP AEl DP DEl (NEl' : nat -> nat -> list domain -> glu_exp_pred) Γ Us,
    ind_glu_components p D ups NP NEl AP AEl DP DEl Γ Us ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ A M n, NP m j vs Γ A -> NEl' m j vs Γ A M n -> NEl m j vs Γ A M n) ->
    forall m Mm, ind_member D m = Some Mm ->
    forall n Ns ns, n <= im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) n ns ns ->
      (forall j N T' v, j < n -> List.nth_error Ns j = Some N ->
         List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T' ->
         List.nth_error ns j = Some v -> Γ ⊢ N : T' ® v ∈ NEl' m j (List.firstn j ns)) ->
      (forall j N T' v, j < n -> List.nth_error Ns j = Some N ->
         List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T' ->
         List.nth_error ns j = Some v -> Γ ⊢ N : T' ® v ∈ NEl m j (List.firstn j ns)).
Proof.
  intros * [HCN _ _] HNl m Mm HM n Ns ns Hn Hp H'.
  assert (Hl : List.length ns = n) by (destruct Hp; assumption).
  enough (forall k, k <= n -> forall j N T' v, j < k -> List.nth_error Ns j = Some N ->
            List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T' ->
            List.nth_error ns j = Some v -> Γ ⊢ N : T' ® v ∈ NEl m j (List.firstn j ns)) as Hm
    by (intros; eapply (Hm n); eauto).
  induction k as [| k IH]; intros Hk j N T' v Hj HN HT Hv; [ lia |].
  destruct (Nat.eq_dec j k) as [-> | Hne]; [| eapply IH; eauto; lia ].
  assert (Hpm : tele_prefix_rel (canon_nparams_rel D ups m) k (List.firstn k ns) (List.firstn k ns))
    by (eapply tele_prefix_rel_of_pre; [ exact Hp | lia ]).
  eapply HNl; [ exact HM | lia | exact Hpm | | eapply H'; eauto; lia ].
  eapply (HCN m Mm k Ns (List.firstn k ns) T'); [ exact HM | rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
  intros j' N' T'' v' Hj' HN' HT' Hv'.
  rewrite List.firstn_firstn, Nat.min_l by lia.
  rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec j' k); [| discriminate ].
  eapply IH; eauto; lia.
Qed.

Lemma ind_components_lower_a : forall p D ups NP NEl AP AEl DP DEl
    (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred) Γ Us m Mm Ns ns c gs gs1 gs2 As vs,
    ind_glu_components p D ups NP NEl AP AEl DP DEl Γ Us ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       forall Γ A M n, AP m ms c j vs Γ A -> AEl' m ms c j vs Γ A M n -> AEl m ms c j vs Γ A M n) ->
    ind_member D m = Some Mm ->
    glu_nparams m Mm NEl Γ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
    ind_con Mm c = Some gs -> gs = gs1 ++ gs2 -> List.length vs = List.length gs1 ->
    tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
      (nonrec_arg_vals gs1 vs) ->
    (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
       List.nth_error vs (List.length hs1) = Some v ->
       Γ ⊢ N : T' ® v ∈ AEl' m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
    (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
       List.nth_error vs (List.length hs1) = Some v ->
       Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
Proof.
  intros * [_ HCA _] HAl HM Hnp Hns Hc Heq Hvl Hp H'.
  enough (forall k, forall hs1 rB B hs2 N T' v, List.length hs1 < k -> gs1 = hs1 ++ ca_arg rB B :: hs2 ->
            List.nth_error As (List.length hs1) = Some N ->
            List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
            List.nth_error vs (List.length hs1) = Some v ->
            Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1))
                                (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) as Hm
    by (intros; eapply (Hm (S (List.length hs1))); eauto).
  induction k as [| k IH]; intros hs1 rB B hs2 N T' v Hlt Heq1 HN HT Hv; [ lia |].
  destruct (Nat.eq_dec (List.length hs1) k) as [Hlm | Hne]; [| eapply IH; eauto; lia ].
  assert (Hl1 : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
  assert (HK : List.length (cargs_nonrec hs1) < List.length (cargs_nonrec gs))
    by (rewrite Heq, Heq1, !cargs_nonrec_app, !List.length_app; cbn; lia).
  assert (Hpre : tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec hs1))
                   (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
  { pose proof (tele_prefix_rel_of_pre _ _ _ _ (List.length (cargs_nonrec hs1)) Hp
                  ltac:(rewrite Heq1, cargs_nonrec_app, List.length_app; cbn; lia)) as Hq.
    rewrite (nonrec_firstn _ _ _ _ _ Heq1 Hvl) in Hq; exact Hq. }
  eapply HAl; [ exact HM | exact Hns | exact Hc | exact HK | exact Hpre | | eapply H'; eauto ].
  eapply (HCA m Mm c gs hs1 rB B (hs2 ++ gs2) Ns ns As (List.firstn (List.length hs1) vs) T');
    [ exact HM | exact Hc | rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact Hnp | exact Hns
    | rewrite List.length_firstn; lia | exact HT | | exact Hpre ].
  intros hs1' rB' B' hs2' N' T'' v' Heq2 HN' HT' Hv'.
  assert (Hlt' : List.length hs1' < List.length hs1) by (rewrite Heq2, List.length_app; cbn; lia).
  rewrite List.firstn_firstn, Nat.min_l by lia.
  rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1') (List.length hs1)); [| discriminate ].
  eapply (IH hs1' rB' B' (hs2' ++ ca_arg rB B :: hs2));
    [ lia | rewrite Heq1, Heq2, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ].
Qed.

Lemma glu_nparams_lower : forall p D ups NP NEl AP AEl DP DEl (NEl' : nat -> nat -> list domain -> glu_exp_pred) Γ Us k Mk Ns ns,
    ind_glu_components p D ups NP NEl AP AEl DP DEl Γ Us ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ A M n, NP m j vs Γ A -> NEl' m j vs Γ A M n -> NEl m j vs Γ A M n) ->
    ind_member D k = Some Mk ->
    tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
    glu_nparams k Mk NEl' Γ Us Ns ns -> glu_nparams k Mk NEl Γ Us Ns ns.
Proof.
  intros * Hc HNl HMk Hns [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
  intros j N A n HN HA Hn.
  assert (Hj : j < im_nn Mk) by (rewrite <- L2; apply List.nth_error_Some; congruence).
  eapply (ind_components_lower_n _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl _ _ HMk (im_nn Mk) Ns ns);
    [ lia | | | exact Hj | exact HN | exact HA | exact Hn ].
  - destruct Hns as [_ Hns]; split; [ exact L2 | exact Hns ].
  - intros; eapply H; eassumption.
Qed.

Lemma ind_glu_components_cumu : forall p D ups NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' Γ Us,
    group_structure D -> ind_canon_props D ups ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\
       (forall Γ T N n, NP m j vs Γ T -> NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ T N n, NEl m j vs Γ T N n -> NEl' m j vs Γ T N n) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
       (forall Γ T N n, AP m ms c j vs Γ T -> AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       (forall Γ A, DP m (ms ++ ws ++ ys) Ts B Γ A -> DP' m (ms ++ ws ++ ys) Ts B Γ A) /\
       (forall Γ A M n, DP m (ms ++ ws ++ ys) Ts B Γ A -> DEl' m (ms ++ ws ++ ys) Ts B Γ A M n -> DEl m (ms ++ ws ++ ys) Ts B Γ A M n)) ->
    ind_glu_components p D ups NP NEl AP AEl DP DEl Γ Us -> ind_glu_components p D ups NP' NEl' AP' AEl' DP' DEl' Γ Us.
Proof.
  intros * Hass Hcp HN HN' HA HD Hc.
  assert (HNl : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             forall Γ A M n, NP m j vs Γ A -> NEl' m j vs Γ A M n -> NEl m j vs Γ A M n)
    by (intros * HM Hj Hp; exact (proj2 (HN _ _ _ _ HM Hj Hp))).
  assert (HAl : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
             j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             forall Γ A M n, AP m ms c j vs Γ A -> AEl' m ms c j vs Γ A M n -> AEl m ms c j vs Γ A M n)
    by (intros * HM Hm Hc0 Hj Hp; exact (proj2 (HA _ _ _ _ _ _ _ HM Hm Hc0 Hj Hp))).
  pose proof Hc as [HCN HCA HCR]; constructor.
  - intros m Mm k Ns ns T HM Hl Hk HT Hpre Hp.
    apply (proj1 (HN m Mm k ns HM Hk Hp)).
    apply (HCN m Mm k Ns ns T HM Hl Hk HT); [| exact Hp ].
    intros j N T' n Hj HN0 HT' Hn.
    eapply (ind_components_lower_n _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl _ _ HM k Ns ns);
      [ lia | exact Hp | | exact Hj | exact HN0 | exact HT' | exact Hn ].
    exact Hpre.
  - intros m Mm c gs gs1 r0 A0 gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    assert (HK : List.length (cargs_nonrec gs1) < List.length (cargs_nonrec gs))
      by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
    apply (proj1 (HA _ _ _ _ _ _ _ HM Hns Hcon HK Hp)).
    pose proof (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl HM Hns Hnp) as Hnp'.
    eapply HCA; [ exact HM | exact Hcon | exact Heq | exact Hnp' | exact Hns | exact Hvl | exact HT | | exact Hp ].
    intros hs1 rB B hs2 N T' v Heq1 HN0 HT' Hv.
    eapply (ind_components_lower_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gs1 (ca_arg r0 A0 :: gs2) As vs Hc HAl HM Hnp' Hns Hcon Heq Hvl
              Hp Hpre); eassumption.
  - intros m Mm c gs gs1 t gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl HM Hns Hnp) as Hnp'.
    pose proof (HCR m Mm c gs gs1 t gs2 Ns ns As vs T HM Hcon Heq Hnp' Hns Hvl HT
                  (ind_components_lower_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gs1 (ca_rec t :: gs2) As vs Hc HAl HM Hnp' Hns Hcon Heq
                     Hvl Hp Hpre)
                  Hp) as H.
    subst gs.
    (** The end of the shape: the parameters' gluings grow *)
    assert (HSE : forall Γ0 Us0 pre Ts j Ps T0, glu_self_params p D ups NEl Γ0 Us0 pre Ts j Ps T0 ->
                  glu_self_params p D ups NEl' Γ0 Us0 pre Ts j Ps T0).
    { intros * HS Mj Q bsr HMj HT0 Hb; destruct (HS Mj Q bsr HMj HT0 Hb) as [Hr Hn Ht].
      constructor; [ exact Hr | | exact Ht ].
      eapply (glu_nparams_mono D ups NEl); [ exact HN' | exact HMj | exact Hr | exact Hn ]. }
    exact (glu_shape_typ_change p D ups ups m Mm (DP m) (DP' m) (DEl m) (DEl' m) _ _ Hass Hcp HM HSE ltac:(intros; reflexivity)
             (fun ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 Hm0 Hc0 Heq0 Hw0 HB0 Hy0 =>
                HD m Mm ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 HM Hm0 Hc0 Heq0 Hw0 HB0 Hy0)
             t Γ _ _ _ T H ns c gs1 t gs2 (nonrec_arg_vals gs1 vs) 0 nil ltac:(rewrite List.app_nil_r; reflexivity)
             ltac:(cbn [List.firstn]; rewrite List.app_nil_r; reflexivity)
             Hns Hcon Hp eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
Qed.


(** The right side of equal parameters is typed at its own telescope. *)
Lemma exps_eq_at_typed_r : forall p D k Mk Δ Xs Ys, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ Δ ->
    List.length Xs = im_np D Mk -> exps_eq_at Δ (im_params D Mk) Xs Ys ->
    forall j Y A, List.nth_error Ys j = Some Y -> List.nth_error (tele_insts (im_params D Mk) Id Ys) j = Some A -> Δ ⊢ Y : A.
Proof.
  intros * Hl HMk HΔ HXl [HlXY HXY] j Y A HY HA.
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
  destruct (nth_error_lt_some Xs j ltac:(rewrite HlXY; apply List.nth_error_Some; congruence)) as [X HX].
  destruct (nth_error_lt_some (tele_insts (im_params D Mk) Id Xs) j) as [T0 HT0].
  { rewrite length_tele_insts_params by (try (eapply decl_closed_params_ass; eassumption); exact HXl).
    apply List.nth_error_Some; congruence. }
  pose proof (HXY _ _ _ _ HX HY HT0) as HXY0.
  destruct (params_types_cong _ _ _ _ _ _ _ Hl HMk HΔ HXl ltac:(rewrite <- HlXY; exact HXl) HXY _ _ _ HT0 HA) as (S & HS & HTT).
  eapply wf_conv_sort; [ gen_presups; eassumption | exact (presup_exp_eq_right HTT) | exact HS | exact HTT ].
Qed.

Lemma map_wk_id : forall Ps, List.map (fun P => P[wk_id]ʷ) Ps = Ps.
Proof. intros; rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; reflexivity. Qed.


Lemma ind_rps_of_per : forall i R p D k Mk as1 as2, DF d_ind p k as1 ≈ d_ind p k as2 ∈ per_univ_elem i ↘ R ->
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    forall n, exists Ms, Rps as1 at List.rev (im_params D Mk) in gc_deps ⍮ gc_stack ⍮ nil ⍮ n ↘ Ms.
Proof.
  intros * H Hl HMk n.
  destruct (per_univ_then_per_top_typ H n) as [W W' Hr _ _].
  inversion Hr; subst.
  match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
  match goal with H : ind_member D k = Some ?M1 |- _ => assert (M1 = Mk) as -> by congruence end.
  eauto.
Qed.

(** Two lists of parameters glued to the same values are equal. *)
Lemma glu_params_top_eq : forall p D k Mk Δ Ps Qs as',
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ Δ ->
    (exists Ms, Rps as' at List.rev (im_params D Mk) in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms) ->
    glu_params_top D Mk Δ Ps as' -> glu_params_top D Mk Δ Qs as' -> exps_eq_at Δ (im_params D Mk) Ps Qs.
Proof.
  intros * Hl HMk HΔ (Ms & HMs) HP HQ.
  assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
  pose proof (proj2 (decl_of_lookup _ _ _ _ _ HΔ Hl)) as Hc.
  pose proof (glu_params_top_read _ _ _ _ _ HP _ _ _ Hid HMs) as H1.
  pose proof (glu_params_top_read _ _ _ _ _ HQ _ _ _ Hid HMs) as H2.
  rewrite !map_wk_id_exp in H1, H2.
  exact (tele_eq_annotate_upto _ _ _ _ _ _ (decl_closed_params_ass _ _ _ Hc HMk) (params_ctx_wf _ _ _ _ _ Hl HMk HΔ)
           ltac:(rewrite length_im_params; exact (glu_params_top_len _ _ _ _ _ HP))
           ltac:(rewrite length_im_params; exact (glu_params_top_len _ _ _ _ _ HQ)) H1 H2 ltac:(reflexivity)).
Qed.

Lemma ind_typ_at_cumu : forall p D ups ns NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' k Mk a b Γ A Ps,
    group_structure D -> ind_canon_props D ups -> ind_member D k = Some Mk ->
    tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
    a <= b ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\
       (forall Γ T N n, NP m j vs Γ T -> NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ T N n, NEl m j vs Γ T N n -> NEl' m j vs Γ T N n) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
       (forall Γ T N n, AP m ms c j vs Γ T -> AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       (forall Γ A, DP m (ms ++ ws ++ ys) Ts B Γ A -> DP' m (ms ++ ws ++ ys) Ts B Γ A) /\
       (forall Γ A M n, DP m (ms ++ ws ++ ys) Ts B Γ A -> DEl' m (ms ++ ws ++ ys) Ts B Γ A M n -> DEl m (ms ++ ws ++ ys) Ts B Γ A M n)) ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@a Γ A Ps ->
    ind_typ_at p D ups ns NP' NEl' AP' AEl' DP' DEl' k Mk Typeω@b Γ A Ps.
Proof.
  intros * Hass Hcp HMk Hns Hab HN HN' HA HD (HA0 & Hk); split; [ eapply lift_exp_eq_ge; eassumption |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hpt Hs Hc Hnp].
  constructor; [ exact Hpt | | |].
  - destruct (Nat.eq_dec a b) as [<- | Hne]; [ exact Hs |].
    eapply wf_subtyp_trans; [ exact Hs | apply wf_subtyp_univ; [ eapply kripke_dom; eassumption | lia ] ].
  - intros Ps' HPs'; eapply ind_glu_components_cumu; [ exact Hass | exact Hcp | exact HN | exact HN' | exact HA | exact HD
                                                     | exact (Hc _ HPs') ].
  - eapply (glu_nparams_mono D ups NEl); [ exact HN' | exact HMk | exact Hns | exact Hnp ].
Qed.


(** The case of an inductive type in the cumulativity of the gluing, from
    the one of its telescopes' types. *)
Lemma glu_univ_elem_cumu_ind : forall (i j : universe_index) p D k Mk pm ups ns NP NEl AP AEl DP DEl elem_rel
    NP' NEl' AP' AEl' DP' DEl' elem_rel',
    universe_index_le i j -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    List.length ups = ind_nu D -> group_structure D ->
    DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
    DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem j ↘ elem_rel' ->
    (forall m Mm j κ A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
       tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b) ->
    (forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b) ->
    (forall m Mm j κ A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
       tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\ (forall Γ T N n, NEl m j vs Γ T N n -> NEl' m j vs Γ T N n) /\
       (forall Γ T N n, NP m j vs Γ T -> NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
    (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b ->
       (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
       (forall Γ T N n, AEl m ms c j vs Γ T N n -> AEl' m ms c j vs Γ T N n) /\
       (forall Γ T N n, AP m ms c j vs Γ T -> AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       exists b, ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                         (ms ++ ws ++ ys) ↘ b) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ b ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       (forall Γ T, DP m (ms ++ ws ++ ys) Ts B Γ T -> DP' m (ms ++ ws ++ ys) Ts B Γ T) /\
       (forall Γ T N n, DEl m (ms ++ ws ++ ys) Ts B Γ T N n -> DEl' m (ms ++ ws ++ ys) Ts B Γ T N n) /\
       (forall Γ T N n, DP m (ms ++ ws ++ ys) Ts B Γ T -> DEl' m (ms ++ ws ++ ys) Ts B Γ T N n -> DEl m (ms ++ ws ++ ys) Ts B Γ T N n)) ->
    (forall Γ A, ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@(large_level i) Γ A ->
       ind_glu_typ_pred p D ups ns NP' NEl' AP' AEl' DP' DEl' k Mk Typeω@(large_level j) Γ A) /\
    (forall Γ A M m, ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk elem_rel Typeω@(large_level i) Γ A M m ->
       ind_glu_exp_pred p D ups ns NP' NEl' AP' AEl' DP' DEl' k Mk elem_rel' Typeω@(large_level j) Γ A M m) /\
    (forall Γ A M m, ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@(large_level i) Γ A ->
       ind_glu_exp_pred p D ups ns NP' NEl' AP' AEl' DP' DEl' k Mk elem_rel' Typeω@(large_level j) Γ A M m ->
       ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk elem_rel Typeω@(large_level i) Γ A M m).
Proof.
  intros * Hge Hl HMk Hh Hu Hass Hper Hper' HeN HeA HN3 HA3 HeD HD3.
  assert (HN : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\ (forall Γ T N n, NEl m j vs Γ T N n -> NEl' m j vs Γ T N n) /\
             (forall Γ T N n, NP m j vs Γ T -> NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)).
  { intros m Mm j0 vs HM Hj Hp.
    destruct (nparams_lt_ass D m Mm j0 Hass HM ltac:(rewrite List.length_rev; exact Hj)) as (κ & A & HA).
    destruct (HeN _ _ _ _ _ _ HM HA Hp) as [b Hb]; exact (HN3 _ _ _ _ _ _ _ HM HA Hp Hb). }
  assert (HA : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
             j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
             (forall Γ T N n, AEl m ms c j vs Γ T N n -> AEl' m ms c j vs Γ T N n) /\
             (forall Γ T N n, AP m ms c j vs Γ T -> AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)).
  { intros m Mm ms c gs j0 vs HM Hm Hc Hj Hp.
    destruct (nth_error_lt_some' _ _ Hj) as [A HA].
    destruct (HeA _ _ _ _ _ _ _ _ HM Hm Hc HA Hp) as [b Hb]; exact (HA3 _ _ _ _ _ _ _ _ _ HM Hm Hc HA Hp Hb). }
  assert (HN2 : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\
             (forall Γ T N n, NP m j vs Γ T -> NEl' m j vs Γ T N n -> NEl m j vs Γ T N n))
    by (intros m Mm j0 vs HM Hj Hp; destruct (HN m Mm j0 vs HM Hj Hp) as (E1 & _ & E3); split; assumption).
  assert (HA2 : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
             j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
             (forall Γ T N n, AP m ms c j vs Γ T -> AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n))
    by (intros m Mm ms c gs j0 vs HM Hm Hc Hj Hp; destruct (HA m Mm ms c gs j0 vs HM Hm Hc Hj Hp) as (E1 & _ & E3);
        split; assumption).
  assert (HD : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t)
               j ys ys ->
             let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
             (forall Γ T, DP m (ms ++ ws ++ ys) Ts B Γ T -> DP' m (ms ++ ws ++ ys) Ts B Γ T) /\
             (forall Γ T N n, DEl m (ms ++ ws ++ ys) Ts B Γ T N n -> DEl' m (ms ++ ws ++ ys) Ts B Γ T N n) /\
             (forall Γ T N n, DP m (ms ++ ws ++ ys) Ts B Γ T -> DEl' m (ms ++ ws ++ ys) Ts B Γ T N n ->
                DEl m (ms ++ ws ++ ys) Ts B Γ T N n)).
  { intros * HM Hm Hc Heq Hw HB Hy.
    destruct (HeD _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy) as [b Hb];
      exact (HD3 _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy Hb). }
  assert (HD2 : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t)
               j ys ys ->
             let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
             (forall Γ T, DP m (ms ++ ws ++ ys) Ts B Γ T -> DP' m (ms ++ ws ++ ys) Ts B Γ T) /\
             (forall Γ T N n, DP m (ms ++ ws ++ ys) Ts B Γ T -> DEl' m (ms ++ ws ++ ys) Ts B Γ T N n ->
                DEl m (ms ++ ws ++ ys) Ts B Γ T N n))
    by (intros * HM Hm Hc Heq Hw HB Hy; destruct (HD _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy) as (E1 & _ & E3);
        split; assumption).
  pose proof (ind_canon_of_per _ _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as Hcp.
  pose proof (ind_rps_of_per _ _ _ _ _ _ _ _ Hper Hl HMk) as Hrb.
  pose proof (universe_index_le_large_level_le _ _ Hge) as Hij.
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hper Hper') as Hrel.
  destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as [_ _ _ Hfam Hadm _ Hns0 _].
  assert (Hns : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns)
    by (rewrite <- (member_nparams_eq _ _ _ HMk); exact Hns0).
  assert (HNu : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             forall Γ T N n, NEl m j vs Γ T N n -> NEl' m j vs Γ T N n)
    by (intros m Mm j0 vs HM Hj Hp; exact (proj1 (proj2 (HN m Mm j0 vs HM Hj Hp)))).
  split; [| split ].
  - intros Γ A (Ps & HPs); exists Ps; eapply ind_typ_at_cumu;
      [ exact Hass | exact Hcp | exact HMk | exact Hns | exact Hij | exact HN2 | exact HNu | exact HA2 | exact HD2 | exact HPs ].
  - intros Γ A M m [HM Hm Ps HPs Hk].
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Ps _ _);
      [ apply Hrel; exact Hm
      | eapply ind_typ_at_cumu; [ exact Hass | exact Hcp | exact HMk | exact Hns | exact Hij | exact HN2 | exact HNu | exact HA2
                                | exact HD2 | exact HPs ] |].
    intros Δ φ Ps' Hφ HPs'; eapply (ind_glu_elem_mono p D ups NEl AEl DP DEl Hass Hcp); [| | | exact (Hk _ _ _ Hφ HPs') ].
    + exact HNu.
    + intros m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp; apply (proj1 (proj2 (HA m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp))).
    + exact HD2.
  - (** Down: the element moves to the smaller gluings, where its type is
        glued, at the same uniform parameters *)
    intros Γ A M m HPs HMe.
    eapply ind_glu_exp_move; [ exact Hl | exact HMk | exact Hass | exact Hcp | exact Hfam | exact Hadm | | | | | | exact HMe
                             | exact HPs ].
    + intros m0 Mm j0 vs HM0 Hj Hp Γ0 T N n HN0 HT0; exact (proj2 (proj2 (HN m0 Mm j0 vs HM0 Hj Hp)) _ _ _ _ HT0 HN0).
    + intros m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp Γ0 T N n HN0 HT0;
        exact (proj2 (proj2 (HA m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp)) _ _ _ _ HT0 HN0).
    + intros * HM0 Hm' Hc Heq Hw HB Hy Ts Γ0 T N n HN0 _; exact (proj1 (proj2 (HD _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hc Heq Hw HB Hy)) _ _ _ _ HN0).
    + intros v Hv; apply Hrel; exact Hv.
    + intros Δ Xs Ys HΔ HX HY; exact (glu_params_top_eq _ _ _ _ _ _ _ _ Hl HMk HΔ (Hrb _) HX HY).
Qed.

(** ** Records along the Cumulativity of the Gluing

    The fields of a record type glue at families that grow along the
    universes: the types of the fields, each after projections glued at
    the smaller family, are glued at the bigger one. *)

(** What the families of a record's fields do along the cumulativity, at
    every field and prefix of related values: types move up, elements of
    a type glued below move down. *)
Definition record_fams_cumu (R : record_decl) (ns : list domain)
    (FP FP' : nat -> list domain -> glu_typ_pred) (FEl FEl' : nat -> list domain -> glu_exp_pred) : Prop :=
  forall k f T vs, List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel (canon_fields_rel R ns) k vs vs ->
    (forall Δ A, FP k vs Δ A -> FP' k vs Δ A) /\ (forall Δ A M m, FP k vs Δ A -> FEl' k vs Δ A M m -> FEl k vs Δ A M m).

Lemma record_fields_glu_cumu : forall R ns FP FEl FP' FEl' Γ Ns,
    record_fams_cumu R ns FP FP' FEl FEl' ->
    record_fields_glu R ns FP FEl Γ Ns -> record_fields_glu R ns FP' FEl' Γ Ns.
Proof.
  intros * HF Hg k f T Ms ms Hk HMl Hml HMs Hp.
  apply (proj1 (HF _ _ _ _ Hk Hp)).
  apply (Hg k f T Ms ms Hk HMl Hml); [| exact Hp ].
  (* the terms before, glued at the smaller family, field by field *)
  assert (Hlow : forall n, n <= k -> forall j g T' M m, j < n -> List.nth_error (record_fields R) j = Some (g, T') ->
             List.nth_error Ms j = Some M -> List.nth_error ms j = Some m ->
             Γ ⊢ M : T'[sb_of_list Id (Ns ++ List.firstn j Ms)] ® m ∈ FEl j (List.firstn j ms)).
  { induction n as [| n IH]; intros Hn j g T' M m Hj Hfj HM Hm; [ lia |].
    destruct (Nat.lt_ge_cases j n) as [Hlt | Hge]; [ exact (IH ltac:(lia) _ _ _ _ _ Hlt Hfj HM Hm) |].
    assert (j = n) as -> by lia.
    pose proof (tele_prefix_rel_of_pre _ _ _ _ n Hp ltac:(lia)) as Hpn.
    apply (proj2 (HF _ _ _ _ Hfj Hpn)); [| exact (HMs _ _ _ _ _ Hfj HM Hm) ].
    apply (Hg n g T' (List.firstn n Ms) (List.firstn n ms) Hfj);
      [ rewrite List.length_firstn; lia | rewrite List.length_firstn; lia | | exact Hpn ].
    intros j' g' T'' M' m' Hfj' HM' Hm'.
    assert (Hj' : j' < n) by (pose proof (proj1 (List.nth_error_Some _ _) ltac:(rewrite HM'; discriminate)) as Hlt;
                              rewrite List.length_firstn in Hlt; lia).
    rewrite nth_error_firstn_lt in HM' by exact Hj'; rewrite nth_error_firstn_lt in Hm' by exact Hj'.
    rewrite !List.firstn_firstn, !Nat.min_l by lia.
    exact (IH ltac:(lia) _ _ _ _ _ Hj' Hfj' HM' Hm'). }
  intros j g T' M m Hfj HM Hm.
  assert (Hj : j < k) by (rewrite <- HMl; apply List.nth_error_Some; congruence).
  exact (Hlow k (le_n _) _ _ _ _ _ Hj Hfj HM Hm).
Qed.

Lemma record_typ_at_cumu : forall p R ns FP FEl FP' FEl' a b Γ A Ns,
    a <= b -> record_fams_cumu R ns FP FP' FEl FEl' ->
    record_typ_at p R ns FP FEl Typeω@a Γ A Ns -> record_typ_at p R ns FP' FEl' Typeω@b Γ A Ns.
Proof.
  intros * Hab HF [HA Hk]; constructor; [ eapply lift_exp_eq_ge; eassumption |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hp Hs Hf]; constructor; [ exact Hp | |].
  - destruct (Nat.eq_dec a b) as [<- | Hne]; [ exact Hs |].
    eapply wf_subtyp_trans; [ exact Hs | apply wf_subtyp_univ; [ eapply kripke_dom; eassumption | lia ] ].
  - intros Ns' HNs'; exact (record_fields_glu_cumu _ _ _ _ _ _ _ _ HF (Hf Ns' HNs')).
Qed.

(** Two lists of parameters of a record glued to the same values are
    equal. *)
Lemma record_params_glu_eq : forall (R : record_decl) Δ Ps Qs ns, all_assumptions (record_params R) -> ⊢ record_params R ++ Δ ->
    (exists Ms, Rps ns at List.rev (record_params R) in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms) ->
    params_glu_top (record_params R) Δ Ps ns -> params_glu_top (record_params R) Δ Qs ns ->
    exps_eq_at Δ (record_params R) Ps Qs.
Proof.
  intros * Hass HC (Ms & HMs) [HPl _ HPr] [HQl _ HQr].
  assert (HΔ : ⊢ Δ) by (eapply ctx_app_wf_tail; exact HC).
  assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
  pose proof (HPr _ _ _ Hid HMs) as HPMs; pose proof (HQr _ _ _ Hid HMs) as HQMs.
  rewrite (map_wk_id Ps) in HPMs; rewrite (map_wk_id Qs) in HQMs.
  eapply tele_eq_annotate_upto; [ exact Hass | exact HC | exact HPl | exact HQl | exact HPMs | exact HQMs | reflexivity ].
Qed.

(** A type of a record at parameters [Ps] is one at parameters [Qs] glued
    to the same values. *)
Lemma record_typ_at_params_change : forall p R ns FP FEl a Γ A Ps Qs,
    record_lookup gc_deps gc_stack p = Some R ->
    (forall n, exists Ms, Rps ns at List.rev (record_params R) in gc_deps ⍮ gc_stack ⍮ nil ⍮ n ↘ Ms) ->
    (forall Δ φ, Δ ⊢ᵏ φ : Γ -> params_glu_top (record_params R) Δ (List.map (fun P => P[φ]ʷ) Qs) ns) ->
    record_typ_at p R ns FP FEl Typeω@a Γ A Ps -> record_typ_at p R ns FP FEl Typeω@a Γ A Qs.
Proof.
  intros * Hl Hrb HQ [HA0 Hk].
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (Hrt : Γ ⊢ a_record p : record_ty R) by (gen_presups; eapply wf_record_own_apps; eassumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HSu HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  assert (HCw : forall Δ, ⊢ Δ -> ⊢ record_params R ++ Δ).
  { intros Δ HΔ; pose proof (record_fctx_app_wf _ _ R 0 Δ ltac:(lia) Hc Hass HF HΔ) as H.
    change (record_fctx R 0) with (@nil centry) in H; exact H. }
  assert (Heq : forall Δ φ, Δ ⊢ᵏ φ : Γ ->
                  exps_eq_at Δ (record_params R) (List.map (fun P => P[φ]ʷ) Ps) (List.map (fun P => P[φ]ʷ) Qs)).
  { intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hpt _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    eapply record_params_glu_eq; [ exact Hass | exact (HCw _ HΔ) | apply Hrb | exact Hpt | exact (HQ _ _ Hφ) ]. }
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  constructor.
  - destruct (Hk _ _ Hid) as [[HPl _ _] Hs _].
    destruct (Heq _ _ Hid) as [_ HPQ]; destruct (HQ _ _ Hid) as [HQl _ _].
    rewrite (map_wk_id Ps) in HPl, Hs, HPQ; rewrite (map_wk_id Qs) in HPQ, HQl.
    etransitivity; [ exact HA0 |].
    eapply wf_exp_eq_subtyp'; [| exact Hs ].
    eapply wf_exp_eq_record_apps; [ exact Hrt | exact Hl | exact HPl | exact HQl | exact HPQ ].
  - intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [[HPl HPt HPr] Hs Hf].
    pose proof (Heq _ _ Hφ) as [HlPQ HPQ]; pose proof (HQ _ _ Hφ) as HQt.
    pose proof HQt as [HQl _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    constructor; [ exact HQt | |].
    + destruct (record_sort_inst_cong _ _ _ R _ _ Hc Hass HSu HΔ HPl HQl HPQ) as [n Hk'].
      eapply wf_subtyp_trans; [ eapply wf_subtyp_refl'; symmetry; exact Hk' | exact Hs ].
    + intros Ns' [HlQN HQN]; apply Hf; split; [ congruence |].
      exact (tele_eq_trans _ (record_params R) _ _ _ Hass (HCw _ HΔ) HPl HQl (eq_trans (eq_sym HlQN) HQl) HPQ HQN).
Qed.

(** The case of a record type in the cumulativity of the gluing, from the
    one of its fields' types. *)
Lemma glu_univ_elem_cumu_record : forall (i j : universe_index) p R ns FP FEl elem_rel FP' FEl' elem_rel',
    universe_index_le i j -> record_lookup gc_deps gc_stack p = Some R ->
    DF d_record p ns ≈ d_record p ns ∈ per_univ_elem i ↘ elem_rel ->
    DF d_record p ns ≈ d_record p ns ∈ per_univ_elem j ↘ elem_rel' ->
    (forall k f T vs, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs -> exists b, ⟦ T ⟧ record_fields_env R ns vs ↘ b) ->
    (forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ record_fields_env R ns vs ↘ b ->
       (forall Γ A, FP k vs Γ A -> FP' k vs Γ A) /\ (forall Γ A M m, FEl k vs Γ A M m -> FEl' k vs Γ A M m) /\
       (forall Γ A M m, FP k vs Γ A -> FEl' k vs Γ A M m -> FEl k vs Γ A M m)) ->
    (forall Γ A, record_glu_typ_pred p R ns FP FEl Typeω@(large_level i) Γ A ->
       record_glu_typ_pred p R ns FP' FEl' Typeω@(large_level j) Γ A) /\
    (forall Γ A M m, record_glu_exp_pred p R ns FP FEl elem_rel Typeω@(large_level i) Γ A M m ->
       record_glu_exp_pred p R ns FP' FEl' elem_rel' Typeω@(large_level j) Γ A M m) /\
    (forall Γ A M m, record_glu_typ_pred p R ns FP FEl Typeω@(large_level i) Γ A ->
       record_glu_exp_pred p R ns FP' FEl' elem_rel' Typeω@(large_level j) Γ A M m ->
       record_glu_exp_pred p R ns FP FEl elem_rel Typeω@(large_level i) Γ A M m).
Proof.
  intros * Hge Hl Hper Hper' HeT HT3.
  assert (HF : record_fams_cumu R ns FP FP' FEl FEl').
  { intros k f T vs Hk Hp; destruct (HeT _ _ _ _ Hk Hp) as [b Hb].
    destruct (HT3 _ _ _ _ _ Hk Hp Hb) as (E1 & _ & E3); split; assumption. }
  pose proof (universe_index_le_large_level_le _ _ Hge) as Hij.
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hper Hper') as Hrel.
  pose proof (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hper) as Hcf.
  split; [| split ].
  - intros Γ A (Ns & HNs); exists Ns; exact (record_typ_at_cumu _ _ _ _ _ _ _ _ _ _ _ _ Hij HF HNs).
  - intros Γ A M m [HM Hm Ns HNs vs Hvs Hk].
    refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ (proj1 (Hrel _ _) Hm) Ns
              (record_typ_at_cumu _ _ _ _ _ _ _ _ _ _ _ _ Hij HF HNs) vs Hvs _); [ exact HM |].
    intros Δ φ Ns' Hφ HNs' k f T r Hfk Hr.
    assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
    pose proof (record_projs_prefix_diag _ _ _ _ k (proj1 (record_canon_facts_elem _ _ _ _ _ Hcf _ _) Hm) Hvs ltac:(lia)) as Hpre.
    destruct (HeT _ _ _ _ Hfk Hpre) as [b Hb].
    apply (proj1 (proj2 (HT3 _ _ _ _ _ Hfk Hpre Hb))).
    exact (Hk Δ φ Ns' Hφ HNs' k f T r Hfk Hr).
  - intros Γ A M m (Ps & HPs) [HM Hm Qs HQs vs Hvs Hk].
    assert (HPQ : record_typ_at p R ns FP FEl Typeω@(large_level i) Γ A Qs).
    { eapply record_typ_at_params_change; [ exact Hl | | | exact HPs ].
      - intros n; destruct (record_canon_facts_top _ _ _ _ _ Hcf n) as [Ms Ms' HMs _ _]; eauto.
      - intros Δ φ Hφ; destruct HQs as [_ HQk]; destruct (HQk _ _ Hφ) as [HQp _ _]; exact HQp. }
    refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ (proj2 (Hrel _ _) Hm) Qs HPQ vs Hvs _); [ exact HM |].
    intros Δ φ Ns' Hφ HNs'.
    destruct HPQ as [_ HPk]; destruct (HPk _ _ Hφ) as [_ _ HPf].
    assert (Hlv : List.length vs = List.length (record_fields R)) by (symmetry; exact (List.Forall2_length Hvs)).
    assert (Hpre : forall k, k <= List.length (record_fields R) ->
               tele_prefix_rel (canon_fields_rel R ns) k (List.firstn k vs) (List.firstn k vs))
      by (intros k Hk0; exact (record_projs_prefix_diag _ _ _ _ k (proj1 (record_canon_facts_elem _ _ _ _ _ Hcf _ _) (proj2 (Hrel _ _) Hm)) Hvs Hk0)).
    (* the projections, field by field, after the ones before glued below *)
    intros k; induction k as [k IHk] using (well_founded_induction lt_wf).
    intros f T r Hfk Hr.
    assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
    apply (proj2 (HF _ _ _ _ Hfk (Hpre k ltac:(lia)))); [| exact (Hk Δ φ Ns' Hφ HNs' k f T r Hfk Hr) ].
    apply (HPf Ns' HNs' k f T (record_pre R k M[φ]ʷ) (List.firstn k vs) Hfk);
      [ apply length_record_pre; lia | rewrite List.length_firstn; lia | | exact (Hpre k ltac:(lia)) ].
    intros j0 g T' N' n' Hfj HN' Hn'.
    assert (Hjk : j0 < k) by (pose proof (proj1 (List.nth_error_Some _ _) ltac:(rewrite Hn'; discriminate)) as H0;
                              rewrite List.length_firstn in H0; lia).
    unfold record_pre in HN'; rewrite List.nth_error_map, nth_error_firstn_lt in HN' by exact Hjk.
    rewrite Hfj in HN'; cbn in HN'; injection HN' as <-.
    rewrite nth_error_firstn_lt in Hn' by exact Hjk.
    replace (List.firstn j0 (record_pre R k M[φ]ʷ)) with (record_pre R j0 M[φ]ʷ)
      by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
    rewrite List.firstn_firstn, Nat.min_l by lia.
    exact (IHk j0 Hjk g T' n' Hfj Hn').
Qed.

(** A neutral type glued in [Typeω@i] is glued in every larger universe:
    its typing and its readback equations lift along [i <= j]. *)
Lemma neut_glu_typ_pred_lift_ge : forall {i j b Γ A},
    i <= j ->
    Γ ⊢ A ® neut_glu_typ_pred Typeω@i b ->
    Γ ⊢ A ® neut_glu_typ_pred Typeω@j b.
Proof.
  intros * Hij [HA HR]; split; [ eapply lift_exp_ge; eassumption |].
  intros * Hφ Hr; pose proof (HR _ _ _ Hφ Hr) as Heq; unfold glu_ne_eq in *.
  eapply lift_exp_eq_ge; eassumption.
Qed.

(** An element of a neutral type glued in [Typeω@i] is one in every larger
    universe. *)
Lemma neut_glu_exp_pred_lift_ge : forall {i j b Γ A M m},
    i <= j ->
    Γ ⊢ M : A ® m ∈ neut_glu_exp_pred Typeω@i b ->
    Γ ⊢ M : A ® m ∈ neut_glu_exp_pred Typeω@j b.
Proof.
  intros * Hij []; econstructor; [ eapply neut_glu_typ_pred_lift_ge |..]; eassumption.
Qed.

(** An element of a neutral type in any universe is one in [Typeω@i] at a
    type glued there. *)
Lemma neut_glu_exp_pred_lower : forall {i j b Γ A M m},
    Γ ⊢ A ® neut_glu_typ_pred Typeω@i b ->
    Γ ⊢ M : A ® m ∈ neut_glu_exp_pred Typeω@j b ->
    Γ ⊢ M : A ® m ∈ neut_glu_exp_pred Typeω@i b.
Proof.
  intros * HA HM; inversion HM; subst; econstructor; eassumption.
Qed.

(** An element glued at one type of a gluing is glued at every other type
    the gluing holds of: the two types are equal ([glu_univ_elem_typ_unique_upto_exp_eq']),
    or both are [LevelSort], the only type the gluing of [LevelSortᵈ] holds of. *)
Lemma glu_univ_elem_trm_resp_glu_typ : forall {i P El a Γ A A' M m},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El.
Proof.
  intros * Hglu HA HA' HM.
  assert (Hls : a = LevelSortᵈ \/ not_level_sort a)
    by (destruct a; first [ left; reflexivity | right; discriminate ]).
  destruct Hls as [-> | Hls].
  - basic_invert_glu_univ_elem Hglu.
    apply_predicate_equivalence.
    destruct HA as [-> _], HA' as [-> _]; exact HM.
  - eapply glu_univ_elem_trm_resp_typ_exp_eq; [ eassumption | eassumption |].
    eapply glu_univ_elem_typ_unique_upto_exp_eq'; eassumption.
Qed.

Section glu_univ_elem_cumulativity.
  (** The record case of the cumulativity: [glu_univ_elem_cumu_record] at
      the families of both indices. *)
  #[local]
  Ltac record_cumu_case :=
    match goal with Hl : record_lookup _ _ ?p = Some ?R, Hl' : record_lookup _ _ ?p = Some ?R' |- _ =>
      assert_fails constr_eq R R'; assert (R' = R) by congruence; subst R' end;
    match goal with
    | Hge : universe_index_le ?i ?j, Hl : record_lookup _ _ ?p = Some ?R,
      Hper : per_univ_elem ?i ?er (d_record ?p ?ns) (d_record ?p ?ns),
      Hper' : per_univ_elem ?j ?er' (d_record ?p ?ns) (d_record ?p ?ns) |- _ =>
        let L1 := fresh "L1" in let L2 := fresh "L2" in let L3 := fresh "L3" in
        edestruct (glu_univ_elem_cumu_record i j p R ns) as (L1 & L2 & L3);
          [ exact Hge | exact Hl | exact Hper | exact Hper' | eassumption
          | match goal with
            | IH : forall k f T vs b, _ -> _ -> _ -> forall j0, universe_index_le i j0 -> _,
              Hg : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
                intros k0 f0 T0 vs0 b0 Hk0 Hp0 Hb0; eapply IH;
                  [ exact Hk0 | exact Hp0 | exact Hb0 | exact Hge | eapply Hg; eassumption ]
            end
          | ]
    end.

  #[local]
  Lemma glu_univ_elem_cumulativity_ge : forall {i j : universe_index} {a P P' El El'},
      universe_index_le i j ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El ->
      DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
      (forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® P') /\
        (forall Γ A M m, Γ ⊢ M : A ® m ∈ El -> Γ ⊢ M : A ® m ∈ El') /\
        (forall Γ A M m, Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El' -> Γ ⊢ M : A ® m ∈ El).
  Proof.
    simpl.
    intros * Hge Hglu Hglu'. gen El' P' j.
    glu_univ_elem_induction Hglu; repeat split; intros;
      try assert (DF a ≈ a ∈ per_univ_elem j ↘ in_rel) by (eapply per_univ_elem_cumu_universe_index; eassumption);
      invert_glu_univ_elem Hglu';
      handle_functional_glu_univ_elem;
      simpl in *; destruct_glu_records;
      (** Every equation of a glued type is in the ambient universe of its
          index, the large universe [Typeω@(large_level u)], so each is lifted along
          the order on large levels ([universe_index_le_large_level_le]). *)
      try match goal with Hge : universe_index_le ?u ?v |- _ =>
        let Hl := fresh "Hl" in
        pose proof (universe_index_le_large_level_le _ _ Hge) as Hl;
        repeat match goal with H : _ ⍮ _ ⍮ _ ⊢ ?A ≈ ?B : Typeω@(large_level u) |- _ =>
          let T := constr:(_ ⊢ A ≈ B : Typeω@(large_level v)) in
          assert_fails (assert T by assumption);
          pose proof (lift_exp_eq_ge _ _ _ _ _ _ _ Hl H) end;
        repeat match goal with H : _ ⍮ _ ⍮ _ ⊢ ?A : Typeω@(large_level u) |- _ =>
          let T := constr:(_ ⊢ A : Typeω@(large_level v)) in
          assert_fails (assert T by assumption);
          pose proof (lift_exp_ge _ _ _ _ _ _ Hl H) end end.
    all: try solve [repeat split; intros; destruct_conjs; mauto 2 | intuition mauto 3].
    (** A small universe: only the ambient universe of its type-level gluing
        changes between the two indices; the level term, the element's gluing
        at the realiser of the level and its readback clause carry over. *)
    all: try solve
      [ econstructor;
        [ eassumption | econstructor; [ eassumption | eapply lift_exp_eq_ge; eassumption ]
        | econstructor; eassumption | eassumption ] ].
    (** A neutral type: its equations are lifted, or kept at a type glued
        at the smaller index. *)
    all: try solve [ eapply neut_glu_typ_pred_lift_ge; eassumption
                   | eapply neut_glu_exp_pred_lift_ge; eassumption
                   | eapply neut_glu_exp_pred_lower; eassumption ].
    (** An inductive type: by its components' families ([glu_univ_elem_cumu_ind]). *)
    all: try solve [ assert (D0 = D) by congruence; subst D0;
      assert (M0 = M) by congruence; subst M0;
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->];
      edestruct (glu_univ_elem_cumu_ind i j p D k M pm ups ns NP NEl AP AEl DP DEl elem_rel NP0 NEl0 AP0 AEl0 DP0 DEl0 elem_rel0)
        as (L1 & L2 & L3);
        [ exact Hge | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
        | eassumption | eassumption
        | intros m0 Mm j0 κ A0 vs b HM0 HA0 Hp Hb;
          eapply H8; [ exact HM0 | exact HA0 | exact Hp | exact Hb | exact Hge | eauto ]
        | intros m0 Mm ms c gs j0 A0 vs b HM0 Hm Hc HA0 Hp Hb;
          eapply H10; [ exact HM0 | exact Hm | exact Hc | exact HA0 | exact Hp | exact Hb | exact Hge | eauto ]
        | eassumption
        | intros m0 Mm ms c gs gs1 t gs2 ws j0 B ys b HM0 Hm Hc Heq Hw HB Hy Hb;
          eapply H13; [ exact HM0 | exact Hm | exact Hc | exact Heq | exact Hw | exact HB | exact Hy | exact Hb | exact Hge | eauto ]
        | first [ eapply L1 | eapply L2 | eapply L3 ]; eassumption ] ].
    (** A record type: by its fields' families ([glu_univ_elem_cumu_record]). *)
    all: try solve [ record_cumu_case; first [ eapply L1 | eapply L2 | eapply L3 ]; eassumption ].
    (** A Π type: the domain and codomain gluings move by the induction
        hypotheses; the equations of the type are lifted along the order. *)
    - destruct H7 as [? ? IT OT HA HIT HOT HIP HOP].
      econstructor;
        [ eapply lift_rel_eq_ge; eassumption | eapply lift_rel_ge; eassumption | eapply lift_rel_ge; eassumption | | ].
      + intros Δ φ Hφ. eapply (proj1 (IHHglu j Hge _ _ H9)); eauto.
      + intros Δ φ M m Hφ HM em.
        assert (HMi : Δ ⊢ M : IT[φ]ʷ ® m ∈ IEl) by (eapply (proj2 (proj2 (IHHglu j Hge _ _ H9))); eauto).
        match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        apply_relation_equivalence.
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        eapply (proj1 (H2 m em a0 H6 j Hge _ _ (H10 m em a0 H6))); eauto.
    - destruct H7 as [? ? ? ? IT OT HM Hm HA HIT HOT HIP HOEl].
      assert (DF d_pi κd κc a ρ B ≈ d_pi κd κc a ρ B ∈ per_univ_elem j ↘ elem_rel)
        by (eapply per_univ_elem_cumu_universe_index; eassumption).
      handle_per_univ_elem_irrel.
      econstructor;
        [ eassumption | eassumption | eapply lift_rel_eq_ge; eassumption | eapply lift_rel_ge; eassumption
        | eapply lift_rel_ge; eassumption | | ].
      + intros Δ φ Hφ. eapply (proj1 (IHHglu j Hge _ _ H9)); eauto.
      + intros Δ φ N n Hφ HN en.
        assert (HNi : Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl) by (eapply (proj2 (proj2 (IHHglu j Hge _ _ H9))); eauto).
        destruct (HOEl _ _ _ _ Hφ HNi en) as (mn & Happ & Hmn).
        exists mn; split; [ exact Happ |].
        match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        apply_relation_equivalence.
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        eapply (proj1 (proj2 (H2 n en a0 H7 j Hge _ _ (H10 n en a0 H7)))); eauto.
    (** Down: the type at [i] fixes the domain and codomain; an argument is
        moved to the domain at [j], where both domains are glued, and the
        application back to the codomain at [i] ([glu_univ_elem_trm_resp_glu_typ]). *)
    - destruct H7 as [? ? IT OT HA HIT HOT HIP HOP].
      destruct H8 as [? ? ? ? IT0 OT0 HM Hm HA0 HIT0 HOT0 HIP0 HOEl0].
      handle_per_univ_elem_irrel.
      econstructor; [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | ].
      intros Δ φ N n Hφ HN en.
      assert (HNj : Δ ⊢ N : IT[φ]ʷ ® n ∈ x0) by (eapply (proj1 (proj2 (IHHglu j Hge _ _ H10))); eauto).
      assert (HNj0 : Δ ⊢ N : IT0[φ]ʷ ® n ∈ x0)
        by (eapply glu_univ_elem_trm_resp_glu_typ;
            [ exact H10 | eapply (proj1 (IHHglu j Hge _ _ H10)); eauto | eauto | exact HNj ]).
      destruct (HOEl0 _ _ _ _ Hφ HNj0 en) as (mn & Happ & Hmn).
      exists mn; split; [ exact Happ |].
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      apply_relation_equivalence.
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      pose proof (H11 n en a0 H7) as Hbj.
      pose proof (H2 n en a0 H7 j Hge _ _ Hbj) as (HbP & _ & HbEl).
      eapply HbEl; [ eauto |].
      eapply glu_univ_elem_trm_resp_glu_typ; [ exact Hbj | eapply glu_univ_elem_trm_typ; eassumption | eauto | exact Hmn ].
  Qed.

  (** The two instances the development uses: along the levels of the large
      tier, and from a small universe into every large one. *)
  Lemma glu_univ_elem_cumulativity_nat : forall {i j : nat} {a P P' El El'},
      i <= j ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El ->
      DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
      (forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® P') /\
        (forall Γ A M m, Γ ⊢ M : A ® m ∈ El -> Γ ⊢ M : A ® m ∈ El') /\
        (forall Γ A M m, Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El' -> Γ ⊢ M : A ® m ∈ El).
  Proof. intros; eapply (glu_univ_elem_cumulativity_ge (i := ul i) (j := ul j)); [ cbn; lia | eassumption | eassumption ]. Qed.

End glu_univ_elem_cumulativity.

(** The third part of cumulativity along the order of indices: an element
    of the larger gluing at a type of the smaller one is an element of the
    smaller one. *)
Corollary glu_univ_elem_exp_lower_universe_index : forall {i j : universe_index} {a P P' El El' Γ A M m},
    universe_index_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ M : A ® m ∈ El' ->
    Γ ⊢ M : A ® m ∈ El.
Proof.
  intros * Hle Hi Hj HA HM.
  destruct (glu_univ_elem_cumulativity_ge Hle Hi Hj) as (_ & _ & Hl); exact (Hl _ _ _ _ HA HM).
Qed.

(** The index-order instances of cumulativity for a type and an element. *)
Corollary glu_univ_elem_typ_cumu_ge_universe_index : forall {i j : universe_index} {a P P' El El' Γ A},
    universe_index_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros * Hle Hi Hj HA.
  destruct (glu_univ_elem_cumulativity_ge Hle Hi Hj) as (Htyp & _); exact (Htyp _ _ HA).
Qed.

Corollary glu_univ_elem_exp_cumu_ge_universe_index : forall {i j : universe_index} {a P P' El El' Γ A M m},
    universe_index_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros * Hle Hi Hj HM.
  destruct (glu_univ_elem_cumulativity_ge Hle Hi Hj) as (_ & Hexp & _); exact (Hexp _ _ _ _ HM).
Qed.

Corollary glu_univ_elem_typ_cumu_ge : forall {i : nat} {j : nat} {a P P' El El' Γ A},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros.
  eapply glu_univ_elem_cumulativity_nat; mauto 4.
Qed.

Corollary glu_univ_elem_typ_cumu_max_left : forall {i : nat} {j : nat} {a P P' El El' Γ A},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_typ_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_typ_cumu_max_right : forall {i : nat} {j : nat} {a P P' El El' Γ A},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_typ_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_ge : forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros. gen m M A Γ.
  eapply glu_univ_elem_cumulativity_nat; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_max_left : forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_exp_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_max_right : forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_exp_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower :  forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ M : A ® m ∈ El' ->
    Γ ⊢ M : A ® m ∈ El.
Proof.
  intros * ? ? ?. gen m M A Γ.
  eapply glu_univ_elem_cumulativity_nat; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower_max_left :  forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ M : A ® m ∈ El' ->
    Γ ⊢ M : A ® m ∈ El.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_exp_lower; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower_max_right :  forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ M : A ® m ∈ El' ->
    Γ ⊢ M : A ® m ∈ El.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_exp_lower; mauto 4.
Qed.

(** An element moves to the gluing of a related type at any index, given
    the type's gluing there: both gluings lifted to a common index, the
    element moves there ([glu_univ_elem_transfer]) at the target type,
    lifted, and back down at the target type. *)
Lemma universe_index_le_ul_max : forall (u : universe_index) n, large_level u <= n -> universe_index_le u (ul n).
Proof. intros u0 n0 H; destruct u0; cbn in *; [ exact I | lia ]. Qed.

Lemma glu_univ_elem_exp_conv_universe_index : forall {i j k : universe_index} {a a' P P' El El' Γ A M m},
    Dom a ≈ a' ∈ per_univ k ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ A ® P' ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros * [R HR] Hi Hj HM HA.
  set (n := Nat.max (large_level i) (Nat.max (large_level j) (large_level k))).
  assert (Hin : universe_index_le i (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
  assert (Hjn : universe_index_le j (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
  assert (Hkn : universe_index_le k (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_universe_index Hin Hi) as (Pn & Eln & Hn).
  destruct (glu_univ_elem_cumu_ge_universe_index Hjn Hj) as (Pn' & Eln' & Hn').
  assert (HMn : Γ ⊢ M : A ® m ∈ Eln) by (eapply glu_univ_elem_exp_cumu_ge_universe_index; [ exact Hin | exact Hi | exact Hn | exact HM ]).
  assert (HAn : Γ ⊢ A ® Pn') by (eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hjn | exact Hj | exact Hn' | exact HA ]).
  assert (HRn : DF a ≈ a' ∈ per_univ_elem (ul n) ↘ R) by (eapply per_univ_elem_cumu_universe_index; eassumption).
  pose proof (glu_univ_elem_transfer _ _ _ _ _ _ _ _ Hn Hn' HRn _ _ _ _ HMn HAn) as HMn'.
  eapply glu_univ_elem_exp_lower_universe_index; [ exact Hjn | exact Hj | exact Hn' | exact HA | exact HMn' ].
Qed.

Lemma glu_univ_elem_exp_conv : forall {i : nat} {j : nat} {k : nat} {a a' P P' El El' Γ A M m},
    Dom a ≈ a' ∈ per_univ k ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ A ® P' ->
    Γ ⊢ M : A ® m ∈ El'.
Proof. intros; eapply glu_univ_elem_exp_conv_universe_index; eassumption. Qed.

(** ** The Order on Levels, Syntactically

    Two level terms glued to levels in the canonical order ([per_sublvl]) are
    in the syntactic order [maxl t t' ≈ t'].  Each is equal to its readback,
    and the readbacks are canonical levels in [lvl_le], which the level
    equations turn into the equation ([lvl_exp_of_le]).  This is the
    syntactic content of a semantic subtyping between small universes. *)

(** The atoms of a level normal form without proofs hold no proofs. *)
Lemma level_atoms_proof_free_In : forall c xs j s a,
    nf_proof_free (nf_lvl c xs) -> List.In (mk_level_atom j s a) xs -> ne_proof_free a.
Proof.
  intros c xs; cbn [nf_proof_free]; induction xs as [| x xs IH]; intros * Hp Hin; [ destruct Hin |].
  destruct Hp as [Hx Hxs]; destruct Hin as [-> | Hin]; [ exact Hx | exact (IH _ _ _ Hxs Hin) ].
Qed.

(** The atoms of a level of sort [n] read off its well scoped normal form
    ([level_atoms_well_scoped]) are levels of their sorts. *)
Lemma level_atoms_well_scoped_In : forall n Γ xs j s a,
    @level_atoms_well_scoped gc_deps gc_stack n Γ xs -> List.In (mk_level_atom j s a) xs -> Γ ⊢ (a : exp) : Level@s.
Proof.
  intros n Γ xs; induction xs as [| [k t b] xs IH]; intros * Hw Hin; [ destruct Hin |].
  destruct Hw as [[_ Hb] Hxs]; destruct Hin as [Heq | Hin];
    [ injection Heq as -> -> ->; exact Hb | exact (IH _ _ _ Hxs Hin) ].
Qed.

(** Atoms without proofs, each a level of its sort, are coherent: two of
    them equal up to proofs are the same neutral ([ne_proof_free_eq]). *)
Lemma level_atoms_coherent_of_proof_free : forall {Γ} xs,
    (forall j s a, List.In (mk_level_atom j s a) xs -> ne_proof_free a /\ Γ ⊢ (a : exp) : Level@s) ->
    @level_atoms_coherent gc_deps gc_stack Γ xs.
Proof.
  intros * Hxs j s a j' b Ha Hb Hab.
  destruct (Hxs _ _ _ Ha) as [Hpf Ht].
  rewrite <- (ne_proof_free_eq _ _ Hpf Hab); exact (wf_exp_eq_refl Ht).
Qed.

Lemma glu_lvl_sublvl_eq : forall {Γ t t' l l' n},
    ⊢ Γ ->
    Dom l ≈ l ∈ per_lvl ->
    Dom l' ≈ l' ∈ per_lvl ->
    per_sublvl l l' ->
    glu_lvl n Γ t l ->
    glu_lvl n Γ t' l' ->
    Γ ⊢ maxl t t' ≈ t' : Level@n.
Proof.
  intros * HΓ Hl Hl' Hle Ht Ht'.
  destruct (Hle (length Γ)) as [[c xs] [d ys] HL HL' HLL' Hpf Hpf'].
  assert (Γ ⊢ t ≈ nf_lvl_of (c, xs) : Level@n) as Htc
    by (rewrite <- (exp_wk_id t); eapply glu_lvl_readback; mauto 3).
  assert (Γ ⊢ t' ≈ nf_lvl_of (d, ys) : Level@n) as Htd
    by (rewrite <- (exp_wk_id t'); eapply glu_lvl_readback; mauto 3).
  (** The readbacks are canonical levels of sort [n], their atoms typed at
      their own sorts, which the absorption step of [lvl_exp_of_le] needs. *)
  assert (nf_lvl_well_scoped n Γ (nf_lvl_of (c, xs))) as [Hc Hxs]
    by (eapply glu_lvl_well_scoped_readback; [ exact Ht | mauto 3 | exact HL ]).
  assert (nf_lvl_well_scoped n Γ (nf_lvl_of (d, ys))) as [Hd Hys]
    by (eapply glu_lvl_well_scoped_readback; [ exact Ht' | mauto 3 | exact HL' ]).
  unfold nf_lvl_of in *; cbn [nf_to_exp fst snd] in *.
  (** The atoms of both readbacks hold no proofs: they are coherent. *)
  assert (Hcoh : @level_atoms_coherent gc_deps gc_stack Γ (xs ++ ys)).
  { apply level_atoms_coherent_of_proof_free; intros j s a Hin.
    apply in_app_or in Hin as [Hin | Hin]; split.
    - exact (level_atoms_proof_free_In _ _ _ _ _ Hpf Hin).
    - exact (level_atoms_well_scoped_In _ _ _ _ _ _ Hxs Hin).
    - exact (level_atoms_proof_free_In _ _ _ _ _ Hpf' Hin).
    - exact (level_atoms_well_scoped_In _ _ _ _ _ _ Hys Hin). }
  transitivity (maxl (lvl_exp_of c (List.map atom_exp xs)) (lvl_exp_of d (List.map atom_exp ys)));
    [ apply wf_exp_eq_maxl_cong; assumption |].
  transitivity (lvl_exp_of d (List.map atom_exp ys));
    [ apply lvl_exp_of_le; assumption | symmetry; assumption ].
Qed.

(** An equation in a sort of types is a subtyping. *)
Lemma wf_subtyp_of_sort_eq : forall {Γ S A A'},
    Γ ⊢ A ≈ A' : S -> type_sort S -> Γ ⊢ A ⊆ A'.
Proof.
  intros * Heq HS; eapply wf_subtyp_refl; [ exact (presup_exp_eq_right Heq) | exact HS | exact Heq ].
Qed.

Lemma wf_subtyp_of_kind_sort_eq : forall {Γ κ i A A'},
    Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i -> Γ ⊢ A ⊆ A'.
Proof.
  intros * Heq; eapply wf_subtyp_of_sort_eq; [ exact Heq | apply type_sort_abs_kind; constructor ].
Qed.

(** Two types glued at related values other than [LevelSortᵈ] are subtypes:
    they are equal ([glu_univ_elem_per_univ_elem_typ_escape]). *)
Lemma glu_univ_elem_per_univ_elem_subtyp : forall {i a a' R P P' El El' Γ A A'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ⊆ A'.
Proof.
  intros; eapply wf_subtyp_of_kind_sort_eq, glu_univ_elem_per_univ_elem_typ_escape; eassumption.
Qed.

(** [A ⊆ A'] through the types the two are equal to: leaves the subtyping
    of those two. *)
#[local]
Ltac subtyp_through HA HA' :=
  eapply wf_subtyp_trans;
    [ eapply wf_subtyp_of_sort_eq; [ exact HA | first [ constructor | apply type_sort_abs_kind; constructor ] ]
    | eapply wf_subtyp_trans;
      [ | eapply wf_subtyp_of_sort_eq; [ symmetry; exact HA' | first [ constructor | apply type_sort_abs_kind; constructor ] ] ] ].

(** A semantic subtyping between glued types, other than [LevelSortᵈ], is a
    syntactic one.  [LevelSort] is in no sort ([level_sort_untyped]), so no
    subtyping is about it. *)
Lemma glu_univ_elem_per_subtyp_typ_escape : forall {i : universe_index} {a a' P P' El El' Γ A A'},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ⊆ A'.
Proof.
  intros * Hsubtyp Hglu Hglu' Hnl HA HA'.
  gen A' A Γ. gen El' El P' P.
  induction Hsubtyp; intros; subst.
  (** [LevelSortᵈ] is excluded *)
  all: try (exfalso; apply Hnl; reflexivity).
  (** Related types: equal ([glu_univ_elem_per_univ_elem_subtyp]) — two
      inductive types, two records, two neutrals, two propositions, [Prop]. *)
  all: try solve [ eapply glu_univ_elem_per_univ_elem_subtyp;
                   [ eassumption | exact Hglu | exact Hglu' | exact Hnl | exact HA | exact HA' ] ].
  all: try solve [ eapply glu_univ_elem_per_univ_elem_subtyp; [ | exact Hglu | exact Hglu' | exact Hnl | exact HA | exact HA' ];
                   basic_per_univ_elem_econstructor; try eassumption; try reflexivity ].
  (** [Level@m] below [Level@n], [m <= n] *)
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *.
    subtyp_through HA HA'; mauto 3. }
  (** A universe below a larger one, in either tier, and a small one below a
      large one.  Two small universes are below each other by the syntactic
      order on their glued level terms ([glu_lvl_sublvl_eq]); a small one is
      below a large one because its level term is a level. *)
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *.
    subtyp_through HA HA'; mauto 3. }
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *;
       destruct_conjs; destruct_glu_records.
    subtyp_through suniv_glu_typ_eq0 suniv_glu_typ_eq.
    (** The two level terms are glued at their own sorts; both move to
        the larger of the two, where the order on levels is stated. *)
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    set (nt := suniv_glu_typ_sort0); set (nt' := suniv_glu_typ_sort).
    assert (Γ ⊢ suniv_glu_typ_lvl0 : Level@(Nat.max nt nt'))
      by (eapply glu_lvl_escape; [ exact H1 | eapply glu_lvl_sort_le; [ | exact suniv_glu_typ_glu0 ] | exact HΓ ]; lia).
    assert (Γ ⊢ suniv_glu_typ_lvl : Level@(Nat.max nt nt'))
      by (eapply glu_lvl_escape; [ exact H4 | eapply glu_lvl_sort_le; [ | exact suniv_glu_typ_glu ] | exact HΓ ]; lia).
    eapply wf_subtyp_suniv; [ assumption | eassumption | eassumption |].
    eapply glu_lvl_sublvl_eq;
      [ exact HΓ | exact H1 | exact H4 | exact H
      | eapply glu_lvl_sort_le; [ | exact suniv_glu_typ_glu0 ]
      | eapply glu_lvl_sort_le; [ | exact suniv_glu_typ_glu ] ]; lia. }
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *;
       destruct_conjs; destruct_glu_records.
    match goal with Heq : _ ⊢ A ≈ Type⟨?t⟩ : _, Heq' : _ ⊢ A' ≈ Typeω@_ : _ |- _ =>
      subtyp_through Heq Heq';
      assert (exists k, Γ ⊢ t : Level@k) as [? ?] by (eapply wf_univ_lvl_inversion; gen_presups; eassumption)
    end.
    mauto 3. }
  (** A [Π]: the domains are equal, the codomains at the fresh variables
      subtypes by the induction hypothesis, under the right domain. *)
  basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence.
  destruct HA as [? ? IT OT HA HIT HOT HIP HOP], HA' as [? ? IT' OT' HA' HIT' HOT' HIP' HOP'].
  handle_functional_glu_univ_elem.
  (** The kinds, the codomains' evaluations and their kinds, of both sides *)
  pose proof H3 as Hpi; basic_invert_per_univ_elem Hpi.
  match goal with H : forall c c' (e : _ c c'), rel_mod_eval _ B _ _ _ _ |- _ => rename H into Hout end.
  match goal with H : forall c c', _ c c' -> value_not_level_sort B _ |- _ => rename H into Hnb end.
  match goal with H : forall c c', _ c c' -> rel_typ_kind B _ _ |- _ => rename H into Hkd end.
  match goal with H : not_level_sort a |- _ => rename H into Hna end.
  match goal with H : per_univ_elem i ?R a a, H' : PER ?R |- _ => rename H into Hpa end.
  pose proof H4 as Hpi'; basic_invert_per_univ_elem Hpi'.
  match goal with H : forall c c' (e : _ c c'), rel_mod_eval _ B' _ _ _ _ |- _ => rename H into Hout' end.
  match goal with H : forall c c', _ c c' -> rel_typ_kind B' _ _ |- _ => rename H into Hkd' end.
  match goal with H : not_level_sort a' |- _ => rename H into Hna' end.
  match goal with H : per_univ_elem i ?R a' a', H' : PER ?R |- _ => rename H into Hpa' end.
  match goal with H : domain_kind a' = domain_kind a |- _ => rename H into Hka' end.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  pose proof (HIP _ _ Hid) as HITg; pose proof (HIP' _ _ Hid) as HITg'; rewrite exp_wk_id in HITg, HITg'.
  assert (HITeq : Γ ⊢ IT ≈ IT' : abs_kind_sort (domain_kind a) Typeω@(large_level i))
    by (eapply glu_univ_elem_per_univ_elem_typ_escape; [ exact H0 | exact H5 | exact H12 | exact Hna | exact HITg | exact HITg' ]).
  (** The fresh variables, related in each domain relation *)
  set (c := ⇑! a (length Γ)); set (c' := ⇑! a' (length Γ)).
  pose proof (var_per_elem (length Γ) H0 Hna) as Hcc'.
  pose proof (var_per_elem (length Γ) Hpa Hna) as Hc2.
  pose proof (var_per_elem (length Γ) H6 Hna) as Hc0.
  pose proof (var_per_elem (length Γ) H13 Hna') as Hc1'.
  pose proof (var_per_elem (length Γ) Hpa' Hna') as Hc3'.
  (** The codomains there, of the kind [κc] and not [LevelSortᵈ] *)
  destruct (Hout c c Hc2) as [b ? Eb ? ?].
  destruct (Hout' c' c' Hc3') as [b' ? Eb' ? ?].
  destruct (Hnb c c Hc2) as (b0 & Eb0 & Hnbb).
  assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
  destruct (Hkd c c Hc2) as (b1 & Eb1 & Hkb).
  assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
  destruct (Hkd' c' c' Hc3') as (b2 & Eb2 & Hkb').
  assert (b2 = b') as -> by (eapply functional_eval_exp; eassumption).
  pose proof (H7 c Hc0 b Eb) as HGb.
  pose proof (H14 c' Hc1' b' Eb') as HGb'.
  assert (HΓIT : ⊢ Γ ▹{domain_kind a} IT) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
  assert (HΓIT' : ⊢ Γ ▹{domain_kind a} IT') by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
  (** The left codomain is glued under the left domain, so under the right one *)
  assert (HOTg : (Γ ▹{domain_kind a} IT') ⊢ OT ® OP c Hc0).
  { pose proof (var0_glu_elem H5 Hna HITg) as Hv.
    assert (Hwk : Γ ▹{domain_kind a} IT ⊢ᵏ ↑ : Γ) by mauto 3.
    pose proof (HOP _ _ _ _ Hwk Hv Hc0) as HO.
    assert (HO' : (Γ ▹{domain_kind a} IT) ⊢ OT ® OP c Hc0)
      by (eapply glu_univ_elem_typ_resp_exp_eq;
          [ exact HGb | exact HO | rewrite Hkb; eapply (shift_var_eq _ _ _ _ _ (ul (large_level i))); [ exact HOT | exact HIT ] ]).
    eapply glu_univ_elem_typ_resp_ctxsub; [ exact HGb | exact HO' | mauto 4 ]. }
  assert (HOTg' : (Γ ▹{domain_kind a} IT') ⊢ OT' ® OP0 c' Hc1').
  { pose proof (var0_glu_elem H12 Hna' HITg') as Hv; rewrite Hka' in Hv.
    assert (Hwk : Γ ▹{domain_kind a} IT' ⊢ᵏ ↑ : Γ) by mauto 3.
    pose proof (HOP' _ _ _ _ Hwk Hv Hc1') as HO.
    eapply glu_univ_elem_typ_resp_exp_eq;
      [ exact HGb' | exact HO | rewrite Hkb'; eapply (shift_var_eq _ _ _ _ _ (ul (large_level i))); [ exact HOT' | exact HIT' ] ]. }
  pose proof (H2 _ _ _ _ Hcc' Eb Eb' Hnbb _ _ _ HGb _ HGb' _ _ HOTg _ HOTg') as HOTsub.
  subtyp_through HA HA'.
  eapply wf_subtyp_pi; eassumption.
Qed.

Hint Resolve glu_univ_elem_per_subtyp_typ_escape : mctt.

(** An element at a glued type is one at a type glued at a related value:
    the two types are equal ([glu_univ_elem_typ_unique]), so the element
    is at the second type, where it moves to the second gluing
    ([glu_univ_elem_transfer]); [LevelSortᵈ] is related only to itself. *)
Lemma glu_univ_elem_per_univ_elem_trm : forall {i a a' R P P' El El' Γ A A' M m},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * HR Hglu Hglu' HA HM.
  assert (HAt : Γ ⊢ A ® P) by (eapply glu_univ_elem_trm_typ; eassumption).
  assert (Hls : a = LevelSortᵈ \/ not_level_sort a) by (destruct a; first [ left; reflexivity | right; discriminate ]).
  destruct Hls as [-> | Hn].
  - basic_invert_per_univ_elem HR.
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP HEE].
    apply HEE; eapply glu_univ_elem_trm_resp_glu_typ; [ exact Hglu | exact HAt | apply HPP; exact HA | exact HM ].
  - pose proof (glu_univ_elem_typ_unique _ _ _ _ _ _ _ _ Hglu Hglu' HR Hn _ _ _ HAt HA) as HAA.
    pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hglu _ _ _ _ _ HM HAA) as HM'.
    exact (glu_univ_elem_transfer _ _ _ _ _ _ _ _ Hglu Hglu' HR _ _ _ _ HM' HA).
Qed.

Lemma glu_univ_elem_per_subtyp_trm_if : forall {i : universe_index} {a a' P P' El El' Γ A A' M m},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  gen m M A' A. gen Γ. gen El' El P' P.
  induction Hsubtyp; intros; subst.
  (** Related types have the same gluing ([glu_univ_elem_per_univ_elem_trm]):
      two inductive types, two records, two neutrals, two propositions,
      [Prop], [LevelSort]. *)
  all: try solve [ eapply glu_univ_elem_per_univ_elem_trm; [ eassumption | exact Hglu | exact Hglu' | exact HA | exact HA' ] ].
  all: try solve [ eapply glu_univ_elem_per_univ_elem_trm; [ | exact Hglu | exact Hglu' | exact HA | exact HA' ];
                   basic_per_univ_elem_econstructor; try eassumption; try reflexivity ].
  (** Otherwise the types are subtypes ([glu_univ_elem_per_subtyp_typ_escape]) *)
  all: assert (HAt : Γ ⊢ A ® P) by (eapply glu_univ_elem_trm_typ; eassumption).
  all: lazymatch type of Hglu with glu_univ_elem ?k _ _ ?x => lazymatch type of Hglu' with glu_univ_elem _ _ _ ?y =>
         assert (Hs : Sub x <: y at k) by (econstructor; eassumption) end end.
  all: assert (HAA : Γ ⊢ A ⊆ A')
         by (eapply glu_univ_elem_per_subtyp_typ_escape; [ exact Hs | exact Hglu | exact Hglu' | intro; discriminate | exact HAt | exact HA ]).
  (** A type of levels below one of a larger sort: the element is a level of
      the larger sort, and its readback equation moves there
      ([glu_lvl_sort_le]). *)
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *.
       destruct HA' as [_ Hper Hlvl].
       econstructor; [ exact HA | eapply per_lvl_at_mono; eassumption | eapply glu_lvl_sort_le; eassumption ]. }
  (** A universe below a larger one: the element is glued at the larger
      index, by cumulativity. *)
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *.
    destruct HA' as [HM _ [Pm Elm Hgm Hpm]].
    assert (Hij : universe_index_le (ul i) (ul j)) by (cbn; lia).
    destruct (glu_univ_elem_cumu_ge_universe_index Hij Hgm) as (Pj & Elj & Hj).
    econstructor; [ mauto 3 | exact HA |].
    econstructor; [ exact Hj | eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hij | exact Hgm | exact Hj | exact Hpm ] ]. }
  (** Small universe below small universe: the element is glued at the larger
      realiser by cumulativity (the order on levels bounds the realisers), and
      its readback moves by subsumption along [A ⊆ A']. *)
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *.
    destruct HA' as [HM HAs [Pm Elm Hgm Hpm] Hrd].
    assert (Hll : universe_index_le (us (domain_level_real l)) (us (domain_level_real l'))) by (cbn; apply per_sublvl_real; exact H).
    destruct (glu_univ_elem_cumu_ge_universe_index Hll Hgm) as (Pj & Elj & Hj).
    econstructor;
      [ mauto 3 | exact HA
      | econstructor; [ exact Hj | eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hll | exact Hgm | exact Hj | exact Hpm ] ] |].
    intros Δ φ W Hφ Hr; pose proof (Hrd _ _ _ Hφ Hr) as Heq; unfold glu_nf_eq in *.
    eapply wf_exp_eq_subtyp'; [ exact Heq | mauto 3 ]. }
  (** Small universe below a large one: the element is glued at the large
      index, by cumulativity across the tiers. *)
  1: { basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence; simpl in *.
    destruct HA' as [HM HAs [Pm Elm Hgm Hpm] Hrd].
    assert (Hll : universe_index_le (us (domain_level_real l)) (ul j)) by exact I.
    destruct (glu_univ_elem_cumu_ge_universe_index Hll Hgm) as (Pj & Elj & Hj).
    econstructor; [ mauto 3 | exact HA |].
    econstructor; [ exact Hj | eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hll | exact Hgm | exact Hj | exact Hpm ] ]. }
  (** A [Π]: an argument glued at the right domain is glued at the left
      one (the domains are related, so glued alike); the application moves
      from the left codomain to the right one by the induction hypothesis. *)
  basic_invert_glu_univ_elem Hglu; basic_invert_glu_univ_elem Hglu'; apply_predicate_equivalence.
  destruct HA as [? ? IT' OT' HA HIT' HOT' HIP' HOP'].
  destruct HA' as [? ? ? ? IT OT HM Hm HAe HIT HOT HIP HOEl].
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  econstructor;
    [ mauto 3 | eapply per_elem_subtyping; [ exact Hs | exact H8 | exact H15 | exact Hm ]
    | exact HA | exact HIT' | exact HOT' | exact HIP' |].
  intros Δ φ N n Hφ HN en.
  assert (en0 : in_rel0 n n) by (apply H10; exact en).
  (** The argument, at the right domain's gluing, at the left one: the
      domain values are related *)
  assert (HN1 : Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl)
    by (eapply glu_univ_elem_per_univ_elem_trm; [ exact (proj1 (per_univ_elem_sym _ _ _ _ H0)) | exact H12 | exact H5
                                                | exact (HIP _ _ Hφ) | exact HN ]).
  destruct (HOEl _ _ _ _ Hφ HN1 en0) as (mn & Happ & Hmn).
  exists mn; split; [ exact Happ |].
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  apply_relation_equivalence.
  destruct_rel_mod_eval.
  handle_per_univ_elem_irrel.
  match goal with Eb : ⟦ B ⟧ ρ ↦ n ⦂ _ ↘ ?b, Eb' : ⟦ B' ⟧ ρ' ↦ n ⦂ _ ↘ ?b' |- _ =>
    eapply (H2 n n b b' en0 Eb Eb' _ _ _ (H7 n en0 b Eb) _ (H14 n en b' Eb'));
      [ exact (HOP' _ _ _ _ Hφ HN en) | exact Hmn ] end.
Qed.

Lemma glu_univ_elem_per_subtyp_trm_conv : forall {i : nat} {j : nat} {k : nat} {a a' P P' El El' Γ A A' M m},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem k ↘ P' ↘ El' ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros.
  assert (Sub a <: a' at (max i (max j k))) by mauto using per_subtyp_cumu_left.
  assert (j <= max i (max j k)) by lia.
  assert (exists P El, DG a ∈ glu_univ_elem (max i (max j k)) ↘ P ↘ El) as [Ptop [Eltop]] by mauto using glu_univ_elem_cumu_ge.
  assert (k <= max i (max j k)) by lia.
  assert (exists P El, DG a' ∈ glu_univ_elem (max i (max j k)) ↘ P ↘ El) as [Ptop' [Eltop']] by mauto using glu_univ_elem_cumu_ge.
  assert (Γ ⊢ A' ® Ptop') by (eapply glu_univ_elem_typ_cumu_ge; mauto).
  assert (Γ ⊢ M : A ® m ∈ Eltop) by (eapply @glu_univ_elem_exp_cumu_ge with (i := j); mauto).
  assert (Γ ⊢ M : A' ® m ∈ Eltop') by (eapply glu_univ_elem_per_subtyp_trm_if; mauto).
  eapply glu_univ_elem_exp_lower; mauto.
Qed.

(** *** Lemmas for [glu_rel_typ_with_sub] and [glu_rel_exp_with_sub] *)

Lemma mk_glu_rel_typ_with_sub' : forall {i : nat} {Δ A σ ρ a},
    ⟦ A ⟧ ρ ↘ a ->
    (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

Hint Resolve mk_glu_rel_typ_with_sub' : mctt.

Lemma mk_glu_rel_typ_with_sub'' : forall {i : nat} {Δ A σ ρ a},
    ⟦ A ⟧ ρ ↘ a ->
    Dom a ≈ a ∈ per_univ i ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * ? [] ?.
  assert (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) as [? []] by mauto.
  eapply mk_glu_rel_typ_with_sub'; mauto.
Qed.

Hint Resolve mk_glu_rel_typ_with_sub'' : mctt.

(** The term's value is given at the kind of the type's value
    ([glu_term_value]): kept at a proposition. *)
Lemma mk_glu_rel_exp_with_sub' : forall {i : nat} {Δ A M σ ρ a m},
    ⟦ A ⟧ ρ ↘ a ->
    glu_term_value M ρ (domain_kind a) m ->
    (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ] : A[σ] ® m ∈ El) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * Ha Hm (P & El & Hglu) HEl.
  econstructor; [ exact Ha | exact Hm | exact Hglu | exact (HEl _ _ Hglu) ].
Qed.

Hint Resolve mk_glu_rel_exp_with_sub' : mctt.

Lemma mk_glu_rel_exp_with_sub'' : forall {i : nat} {Δ A M σ ρ a m},
    ⟦ A ⟧ ρ ↘ a ->
    glu_term_value M ρ (domain_kind a) m ->
    Dom a ≈ a ∈ per_univ i ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ] : A[σ] ® m ∈ El) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * Ha Hm Hper HEl.
  destruct (per_univ_glu_univ_elem _ _ Hper) as (P & El & Hglu).
  eapply mk_glu_rel_exp_with_sub'; [ exact Ha | exact Hm | eauto | exact HEl ].
Qed.

Hint Resolve mk_glu_rel_exp_with_sub'' : mctt.

(** A type that is a term of a universe: its value is evaluated (a
    universe's kind is relevant) and glued at the universe's index. *)
Lemma glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : forall {i : nat} {Δ A} {j : nat} {σ ρ},
  glu_rel_exp_with_sub i Δ A Typeω@j σ ρ ->
  glu_rel_typ_with_sub j Δ A σ ρ.
Proof.
  intros * [a m P El Ha Hm Hglu HA].
  simplify_evals; cbn [domain_kind glu_term_value] in Hm.
  basic_invert_glu_univ_elem Hglu.
  apply_predicate_equivalence.
  destruct HA as [_ _ [Pm Elm Hgm Hpm]].
  econstructor; [ exact Hm | exact Hgm | exact Hpm ].
Qed.

Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mctt.

(** A type glued at [j], of the universe [Typeω@j], is a term of it. *)
Lemma glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : forall {Δ A} {j : nat} {σ Γ ρ},
  Δ ⊢ˢ σ : Γ ->
  Δ ⊢ A[σ] : Typeω@j ->
  glu_rel_typ_with_sub j Δ A σ ρ ->
  glu_rel_exp_with_sub (S j) Δ A Typeω@j σ ρ.
Proof.
  intros * Hσ HAt [a P El Ha Hglu HA].
  assert (Hu : exists P El, DG 𝕌ω@j ∈ glu_univ_elem (S j) ↘ P ↘ El) by (eapply per_univ_glu_univ_elem; mauto 3).
  destruct Hu as (Pu & Elu & Hu).
  econstructor; [ mauto 3 | cbn; exact Ha | exact Hu |].
  basic_invert_glu_univ_elem Hu; apply_predicate_equivalence.
  econstructor; [ exact HAt | mauto 3 | econstructor; [ exact Hglu | exact HA ] ].
Qed.

Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mctt.

(** *** Lemmas for [glu_ctx_env] *)

(** A term glued at a type under a substitution is glued under an equal
    one, given the term's typing at a type of the sort of a kind. *)
Lemma glu_univ_elem_trm_resp_sub_eq : forall {i : nat} {Γ' κ B N Δ σ σ' a P El m},
    Γ' ⊢ B : abs_kind_sort κ Typeω@i ->
    Γ' ⊢ N : B ->
    Δ ⊢ˢ σ ≈ σ' : Γ' ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ N[σ] : B[σ] ® m ∈ El ->
    Δ ⊢ N[σ'] : B[σ'] ® m ∈ El.
Proof.
  intros * HB HN Heq Hglu HNg.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Heq) as Hσ.
  assert (HBt : Δ ⊢ B[σ] ® P) by (eapply glu_univ_elem_trm_typ; eassumption).
  assert (HBs : Δ ⊢ B[σ] : abs_kind_sort κ Typeω@i)
    by (replace (abs_kind_sort κ Typeω@i) with ((abs_kind_sort κ Typeω@i)[σ]) by (rewrite abs_kind_sort_sub; reflexivity); mauto 3).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu HBt HBs) as [Hk _].
  eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hglu | eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hglu | exact HNg | mauto 3 ] |].
  cbn [large_level]; rewrite Hk.
  replace (abs_kind_sort κ Typeω@i) with ((abs_kind_sort κ Typeω@i)[σ]) by (rewrite abs_kind_sort_sub; reflexivity); mauto 3.
Qed.

Lemma wf_exp_kind_sort_max_right : forall Γ κ X n m,
    Γ ⊢ X : abs_kind_sort κ Typeω@m -> Γ ⊢ X : abs_kind_sort κ Typeω@(max n m).
Proof. intros * H; destruct κ; cbn in *; [ mauto 3 using lift_exp_max_right | exact H | exact H ]. Qed.

(** A glued term typed in [Γ0] moves along [σ ≈ σ'], at a gluing of the
    same type value at a large enough index: its type is of a sort of a
    kind next to a large universe, or [LevelSort], which no substitution
    changes. *)
Lemma glu_typed_resp_sub_eq : forall {i : nat} {a P El Γ0 M A Δ σ σ' m},
    Γ0 ⊢ M : A ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M[σ] : A[σ] ® m ∈ El ->
    Δ ⊢ˢ σ ≈ σ' : Γ0 ->
    exists (i' : nat) P' El', DG a ∈ glu_univ_elem i' ↘ P' ↘ El' /\ Δ ⊢ A[σ'] ® P' /\ Δ ⊢ M[σ'] : A[σ'] ® m ∈ El'.
Proof.
  intros * HM Hglu HMg Heq.
  destruct (presup_exp_typ_cases HM) as [A S HS HA | HΓ0 _].
  - assert (HSk : exists κ (j : nat), S = abs_kind_sort κ Typeω@j)
      by (destruct HS as [j | |]; [ exists ak_relevant, j | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity).
    destruct HSk as (κ & j & ->).
    destruct (glu_univ_elem_cumu_max_left (j := j) Hglu) as (Pm & Elm & Hgm).
    pose proof (glu_univ_elem_exp_cumu_max_left Hglu Hgm HMg) as HMm.
    pose proof (glu_univ_elem_trm_resp_sub_eq (wf_exp_kind_sort_max_right _ _ _ i _ HA) HM Heq Hgm HMm) as HM'.
    exists (max i j), Pm, Elm; split; [ exact Hgm | split; [ eapply glu_univ_elem_trm_typ; eassumption | exact HM' ] ].
  - (** [LevelSort]: unchanged *)
    exists i, P, El; split; [ exact Hglu |].
    pose proof (glu_univ_elem_trm_typ _ _ _ _ Hglu _ _ _ _ HMg) as HT; cbn in HT |- *.
    split; [ exact HT |].
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hglu | exact HMg |].
    exact (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HM) Heq).
Qed.

(** A type of [Γ0] glued under [τ] is glued under an equal [τ'], at a
    gluing of the same value at a large enough index, and its elements
    move between the two. *)
Lemma glu_type_move_sub_eq : forall {i : nat} {a P El Γ0 B Srt Δ τ τ'},
    type_sort Srt ->
    Γ0 ⊢ B : Srt ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ B[τ] ® P ->
    Δ ⊢ˢ τ ≈ τ' : Γ0 ->
    exists (k : nat) Pk Elk, DG a ∈ glu_univ_elem k ↘ Pk ↘ Elk /\ Δ ⊢ B[τ] ® Pk /\ Δ ⊢ B[τ'] ® Pk /\
      (forall N c, Δ ⊢ N : B[τ] ® c ∈ El -> Δ ⊢ N : B[τ'] ® c ∈ Elk) /\
      (forall N c, Δ ⊢ N : B[τ'] ® c ∈ Elk -> Δ ⊢ N : B[τ] ® c ∈ El).
Proof.
  intros * HS HB Hglu HP Heq.
  assert (HSk : exists κ (j : nat), Srt = abs_kind_sort κ Typeω@j)
    by (destruct HS as [j | |]; [ exists ak_relevant, j | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity).
  destruct HSk as (κ & j & ->).
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Heq) as Hτ.
  assert (HBτ : Δ ⊢ B[τ] : abs_kind_sort κ Typeω@j)
    by (replace (abs_kind_sort κ Typeω@j) with ((abs_kind_sort κ Typeω@j)[τ]) by (rewrite abs_kind_sort_sub; reflexivity); mauto 3).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu HP HBτ) as [Hk _].
  assert (HE : Δ ⊢ B[τ] ≈ B[τ'] : abs_kind_sort κ Typeω@(max i j)).
  { apply wf_exp_eq_kind_sort_max_right.
    pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HB) Heq) as H.
    rewrite abs_kind_sort_sub in H; exact H. }
  destruct (glu_univ_elem_cumu_max_left (j := j) Hglu) as (Pk & Elk & Hgk).
  assert (HE' : Δ ⊢ B[τ] ≈ B[τ'] : abs_kind_sort (domain_kind a) Typeω@(large_level (max i j)))
    by (cbn [large_level]; rewrite Hk; exact HE).
  assert (HPk : Δ ⊢ B[τ] ® Pk) by exact (glu_univ_elem_typ_cumu_max_left Hglu Hgk HP).
  exists (max i j), Pk, Elk; split; [ exact Hgk | split; [ exact HPk | split ] ].
  - eapply glu_univ_elem_typ_resp_exp_eq; [ exact Hgk | exact HPk | exact HE' ].
  - split; intros N c HN.
    + eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hgk | exact (glu_univ_elem_exp_cumu_max_left Hglu Hgk HN) | exact HE' ].
    + eapply glu_univ_elem_exp_lower_max_left; [ exact Hglu | exact Hgk | exact HP |].
      eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hgk | exact HN | apply wf_exp_eq_sym; exact HE' ].
Qed.

(** Equal substitutions stay equal along a Kripke weakening. *)
Lemma wf_sub_eq_sb_wk : forall {Δ Γ0 σ σ' Δ' φ},
    Δ ⊢ˢ σ ≈ σ' : Γ0 -> Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ˢ sb_wk σ φ ≈ sb_wk σ' φ : Γ0.
Proof.
  intros * Heq Hφ.
  eapply wf_sub_eq_respects_sb_eq; [| symmetry; apply sb_wk_compose ].
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [| symmetry; apply sb_wk_compose ]; apply wf_sub_eq_sym.
  eapply wf_sub_eq_compose_left; [ exact Heq | eapply kripke_escape; exact Hφ ].
Qed.

(** A factorization of [σ0'] weakened is one of an equal [σ0]'s. *)
Lemma glu_sub_through_resp_sub_eq : forall {Δ σ0 σ0' Γ0 Δ' φ Γ1 ζ σ1},
    Δ ⊢ˢ σ0 ≈ σ0' : Γ0 -> glu_sub_through Δ σ0' Γ0 Δ' φ Γ1 ζ σ1 -> glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1.
Proof.
  intros * Heq [Hφ Hζ Hσ1 E]; constructor; [ exact Hφ | exact Hζ | exact Hσ1 |].
  eapply wf_sub_eq_trans; [ eapply wf_sub_eq_sb_wk; [ exact Heq | exact Hφ ] | exact E ].
Qed.

(** A factorization of [σ0] weakened by [φ], then by [ψ], is one of
    [σ0] weakened by the composite. *)
Lemma glu_sub_through_wk : forall {Δ σ0 Γ0 Δ' φ Δ'' ψ Γ1 ζ σ1},
    Δ' ⊢ᵏ φ : Δ -> glu_sub_through Δ' (sb_wk σ0 φ) Γ0 Δ'' ψ Γ1 ζ σ1 -> glu_sub_through Δ σ0 Γ0 Δ'' (φ ⊙ ψ) Γ1 ζ σ1.
Proof.
  intros * Hφ [Hψ Hζ Hσ1 E]; constructor; [ exact (kripke_compose _ _ _ _ _ Hψ Hφ) | exact Hζ | exact Hσ1 |].
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [ apply wf_sub_eq_sym; exact E | apply sb_wk_wk ].
Qed.

(** A glued module value moves along [σ0 ≈ σ0']: its members' types and
    terms are those of [Γ0] at [σ0], moved by the substitution lemmas;
    an argument glued at [σ0'] is glued at [σ0] at the same value. *)
Lemma glu_dmod_resp_sub_eq :
  (forall Δ σ0 Γ0 H0 h, glu_dmod Δ σ0 Γ0 H0 h -> forall σ0', Δ ⊢ˢ σ0 ≈ σ0' : Γ0 -> glu_dmod Δ σ0' Γ0 H0 h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A global module: [H0[σ0']] is [H0[σ0]] *)
    intros * Hσ HH0 Hl Hlen Hdesc Hargs _ σ0' Heq.
    econstructor; [ exact (wf_sub_eq_right _ _ _ _ _ _ Heq) | exact HH0 | exact Hl | exact Hlen | |].
    + intros * Hst; exact (Hdesc _ _ _ _ _ _ (glu_sub_through_resp_sub_eq Heq Hst)).
    + intros * Hst; exact (Hargs _ _ _ _ _ _ _ (glu_sub_through_resp_sub_eq Heq Hst)).
  - (** A body: a factorization of [σ0'] weakened is one of [σ0]'s *)
    intros * Hσ HH0 Hmem Hsub IHsub σ0' Heq.
    apply glu_dmod_body; [ exact (wf_sub_eq_right _ _ _ _ _ _ Heq) | exact HH0 | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst; exact (Hg _ _ _ _ _ _ _ _ (glu_sub_through_resp_sub_eq Heq Hst)).
    + intros * Hp Hu Hb Hc; exact (IHsub _ _ _ _ _ _ _ Hp Hu Hb Hc _ Heq).
  - (** A value lacking a parameter: likewise *)
    intros * Hσ HH0 Hn Hpar Happ _ σ0' Heq.
    eapply glu_dmod_fun; [ exact (wf_sub_eq_right _ _ _ _ _ _ Heq) | exact HH0 | exact Hn | | ].
    + intros * Hst; exact (Hpar _ _ _ _ _ _ (glu_sub_through_resp_sub_eq Heq Hst)).
    + intros * Hst; exact (Happ _ _ _ _ _ _ _ _ _ _ (glu_sub_through_resp_sub_eq Heq Hst)).
Qed.

(** A substitution weakened along a Kripke weakening is typed. *)
Lemma wf_sub_sb_wk : forall {Δ Γ σ Δ' φ}, Δ ⊢ˢ σ : Γ -> Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ˢ sb_wk σ φ : Γ.
Proof.
  intros * Hσ Hφ.
  eapply wf_sub_sb_eq; [ exact (wf_sub_compose _ _ _ _ _ _ _ Hσ (kripke_escape _ _ _ Hφ)) | symmetry; apply sb_wk_compose ].
Qed.

(** A glued module value's substitution is typed. *)
Lemma glu_dmod_sub_typed : forall {Δ σ0 Γ0 H0 h}, glu_dmod Δ σ0 Γ0 H0 h -> Δ ⊢ˢ σ0 : Γ0.
Proof. intros * H; destruct H; assumption. Qed.

(** [sb_of_list] respects [sb_eq] of its base. *)
Lemma sb_of_list_sb_eq : forall Ms σ τ, sb_eq σ τ -> sb_eq (sb_of_list σ Ms) (sb_of_list τ Ms).
Proof.
  induction Ms as [| M Ms IH]; intros σ τ E; cbn [sb_of_list]; [ exact E |].
  apply IH; intros [| x]; cbn; [ reflexivity | apply E ].
Qed.

(** An instance of a closed telescope, weakened, is the instance at the
    weakened arguments: the closed base is unchanged by weakening. *)
Lemma sb_wk_of_list_closed : forall Ms φ,
    sb_eq (sb_wk (sb_of_list sb_closed_base Ms) φ) (sb_of_list sb_closed_base (List.map (fun M => M[φ]ʷ) Ms)).
Proof.
  intros Ms φ.
  assert (Hgen : forall σ, sb_eq (sb_wk (sb_of_list σ Ms) φ) (sb_of_list (sb_wk σ φ) (List.map (fun M => M[φ]ʷ) Ms))).
  { induction Ms as [| M Ms IH]; intros σ; cbn [sb_of_list List.map]; [ reflexivity |].
    etransitivity; [ apply IH | apply sb_of_list_sb_eq; apply sb_wk_extend ]. }
  etransitivity; [ apply Hgen | apply sb_of_list_sb_eq; intros x; reflexivity ].
Qed.

(** A glued module value is glued at every Kripke weakening: the values
    do not move, the members' and arguments' gluings move along the
    weakening, and an argument at a further weakening is one at the
    composite. *)
Lemma glu_dmod_monotone :
  (forall Δ σ0 Γ0 H0 h, glu_dmod Δ σ0 Γ0 H0 h -> forall Δ' φ, Δ' ⊢ᵏ φ : Δ -> glu_dmod Δ' (sb_wk σ0 φ) Γ0 H0 h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> forall Δ' φ, Δ' ⊢ᵏ φ : Δ ->
     glu_tele_args Δ' ts ρ (List.map (fun M => M[φ]ʷ) Ms) (List.map (fun M => M[φ]ʷ) Ns) args).
Proof.
  apply glu_dmod_mut_ind_all.
  - (** A global module *)
    intros * Hσ HH0 Hl Hlen Hdesc Hargs _ Δ' φ Hφ.
    econstructor; [ exact (wf_sub_sb_wk Hσ Hφ) | exact HH0 | exact Hl | exact Hlen | |].
    + intros * Hst; exact (Hdesc _ _ _ _ _ _ (glu_sub_through_wk Hφ Hst)).
    + intros * Hst; exact (Hargs _ _ _ _ _ _ _ (glu_sub_through_wk Hφ Hst)).
  - (** A body: a factorization of [σ0] weakened twice is one of [σ0]
        weakened by the composite *)
    intros * Hσ HH0 Hmem Hsub IHsub Δ' φ Hφ.
    apply glu_dmod_body; [ exact (wf_sub_sb_wk Hσ Hφ) | exact HH0 | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst; exact (Hg _ _ _ _ _ _ _ _ (glu_sub_through_wk Hφ Hst)).
    + intros * Hp Hu Hb Hc; exact (IHsub _ _ _ _ _ _ _ Hp Hu Hb Hc _ _ Hφ).
  - (** A value lacking a parameter: likewise *)
    intros * Hσ HH0 Hn Hpar Happ _ Δ' φ Hφ.
    eapply glu_dmod_fun; [ exact (wf_sub_sb_wk Hσ Hφ) | exact HH0 | exact Hn | | ].
    + intros * Hst; exact (Hpar _ _ _ _ _ _ (glu_sub_through_wk Hφ Hst)).
    + intros * Hst; exact (Happ _ _ _ _ _ _ _ _ _ _ (glu_sub_through_wk Hφ Hst)).
  - (** No more arguments *)
    intros; constructor.
  - (** An argument, then the rest *)
    intros * Ha Hu HP HN Hargs IHargs Δ' φ Hφ.
    assert (E : forall X, X[sb_of_list sb_closed_base Ms][φ]ʷ = X[sb_of_list sb_closed_base (List.map (fun M => M[φ]ʷ) Ms)])
      by (intros X; rewrite exp_wk_sub; apply exp_sub_sb_eq; apply sb_wk_of_list_closed).
    cbn [List.map]; econstructor; [ exact Ha | exact Hu | rewrite <- E; eapply glu_univ_elem_typ_monotone; eassumption
                                  | rewrite <- E; eapply glu_univ_elem_exp_monotone; eassumption |].
    pose proof (IHargs _ _ Hφ) as H; rewrite List.map_app in H; exact H.
Qed.

(** The head glued at its stored type moves along [σ ≈ σ'], as at the
    declared type, at the larger of the two indices.  Leaves the typing
    of the head's type at that index, and of the head. *)
#[local]
Ltac stored_resp_sub_eq Hsubeq i :=
  match goal with
  | H : exists t, _ /\ glu_stored_type _ _ _ _ t |- exists t, _ /\ glu_stored_type _ _ _ _ t =>
      let t := fresh "t" in let Het := fresh "Het" in let j := fresh "j" in let b := fresh "b" in let Pb := fresh "Pb" in
      let Elb := fresh "Elb" in let Hb := fresh "Hb" in let Hgb := fresh "Hgb" in let HEb := fresh "HEb" in
      let Pm := fresh "Pm" in let Elm := fresh "Elm" in let Hgm := fresh "Hgm" in
      destruct H as (t & Het & [j b Pb Elb Hb Hgb HEb]); exists t; split; [ exact Het |];
      destruct (glu_univ_elem_cumu_max_left (j := i) Hgb) as (Pm & Elm & Hgm);
      refine (mk_glu_stored_type _ _ _ _ _ (max j i) b Pm Elm Hb Hgm _);
      eapply glu_univ_elem_trm_resp_sub_eq;
        [ | | exact Hsubeq | exact Hgm | eapply glu_univ_elem_exp_cumu_max_left; [ exact Hgb | exact Hgm | exact HEb ] ];
        [ apply wf_exp_kind_sort_max_right |]
  end.

Lemma glu_ctx_env_sub_resp_sub_eq : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall {Δ σ σ' ρ},
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      Δ ⊢ˢ σ ≈ σ' : Γ ->
      Δ ⊢ˢ σ' ® ρ ∈ Sb.
Proof.
  (** [gen_presup] misses [wf_sub_eq] (its pattern is one argument short), so
      the two projections are taken by hand, here and below. *)
  induction 1; intros * HSb Hsubeq;
    apply_predicate_equivalence;
    simpl in *;
    (pose proof (wf_sub_eq_left _ _ _ _ _ _ Hsubeq) as Hσ; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hsubeq) as Hσ');
    try eassumption.
  (** The head moves along [σ ≈ σ'] ([glu_univ_elem_trm_resp_sub_eq]); the
      tail, [Wk] postcomposed with either side, by the induction hypothesis. *)
  - destruct_by_head cons_glu_sub_pred.
    assert (⊢ Γ ▹{κ} A) by (econstructor; [ mauto 3 | apply sort_kind_abs_kind_sort ]).
    econstructor; [ exact Hσ' | eassumption | eassumption | | | eassumption |].
    + eapply glu_univ_elem_trm_resp_sub_eq; [ | | exact Hsubeq | eassumption | eassumption ]; mauto 3.
    + stored_resp_sub_eq Hsubeq i; mauto 3.
    + eapply IHglu_ctx_env;
        [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
  - (** A definition entry: as an assumption entry, and the tie does not
        mention [σ]. *)
    destruct_by_head cons_def_glu_sub_pred.
    assert (⊢ Γ ▸ A ≔ M) by mauto 3.
    econstructor; [ exact Hσ' | eassumption | eassumption | | eassumption | | eassumption |].
    + eapply glu_univ_elem_trm_resp_sub_eq; [ | | exact Hsubeq | eassumption | eassumption ]; mauto 3.
    + stored_resp_sub_eq Hsubeq i; mauto 3.
    + eapply IHglu_ctx_env;
        [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
  - (** A module slot: the tie does not mention [σ]; the module value
        moves along the tail of [σ ≈ σ'] ([glu_dmod_resp_sub_eq]). *)
    destruct_by_head cons_mod_glu_sub_pred.
    assert (HWk : Δ ⊢ˢ Wk ⨟ σ ≈ Wk ⨟ σ' : Γ)
      by (eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3).
    econstructor; [ exact Hσ' | eassumption | exact (proj1 glu_dmod_resp_sub_eq _ _ _ _ _ ltac:(eassumption) _ HWk)
                  | eassumption | eassumption |].
    eapply IHglu_ctx_env; [ eassumption | exact HWk ].
  - (** A definition with a module part: as a definition entry, and the
        module tie does not mention [σ] either. *)
    destruct_by_head cons_dm_glu_sub_pred.
    assert (⊢ Γ ▸ₘ A ≔ M ‖ U) by (clear Hsubeq Hσ'; gen_presups; assumption).
    assert (HWk : Δ ⊢ˢ Wk ⨟ σ ≈ Wk ⨟ σ' : Γ)
      by (eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3).
    econstructor; [ exact Hσ' | eassumption | eassumption | | eassumption | eassumption
                  | exact (proj1 glu_dmod_resp_sub_eq _ _ _ _ _ ltac:(eassumption) _ HWk) | | eassumption |].
    + eapply (glu_univ_elem_trm_resp_sub_eq (κ := ak_relevant)); [ | | exact Hsubeq | eassumption | eassumption ]; mauto 3.
    + match goal with H : exists t, _ /\ glu_stored_type _ _ _ _ t |- _ =>
        destruct H as (t & Het & [j b Pb Elb Hb Hgb HEb]) end.
      destruct (glu_univ_elem_cumu_max_left (j := i) Hgb) as (Pm & Elm & Hgm).
      exists t; split; [ exact Het |]; refine (mk_glu_stored_type _ _ _ _ _ (max j i) b Pm Elm Hb Hgm _).
      eapply (glu_univ_elem_trm_resp_sub_eq (κ := ak_relevant));
        [ | | exact Hsubeq | exact Hgm | eapply glu_univ_elem_exp_cumu_max_left; [ exact Hgb | exact Hgm | exact HEb ] ];
        [ apply (wf_exp_kind_sort_max_right _ ak_relevant) | ]; mauto 3.
    + eapply IHglu_ctx_env;
        [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
Qed.

Add Parametric Morphism Sb Γ (H : glu_ctx_env Sb Γ) Δ : (Sb Δ)
    with signature wf_sub_eq gc_deps gc_stack Δ Γ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; intros; eapply glu_ctx_env_sub_resp_sub_eq; mauto 2 using wf_sub_eq_sym.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq : forall {i : nat} {Γ κ A Sb Δ σ σ' ρ},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    Δ ⊢ˢ σ ≈ σ' : Γ ▹{κ} A ->
    Δ ⊢ˢ σ ® ρ ∈ cons_glu_sub_pred i Γ κ A Sb ->
    Δ ⊢ˢ σ' ® ρ ∈ cons_glu_sub_pred i Γ κ A Sb.
Proof.
  intros * Hglu HA Heq Hσ.
  dependent destruction Hσ.
  (pose proof (wf_sub_eq_left _ _ _ _ _ _ Heq) as Hσ; pose proof (wf_sub_eq_right _ _ _ _ _ _ Heq) as Hσ').
  assert (⊢ Γ ▹{κ} A) by (econstructor; [ mauto 3 | apply sort_kind_abs_kind_sort ]).
  econstructor; [ exact Hσ' | eassumption | eassumption | | | eassumption |].
  - eapply glu_univ_elem_trm_resp_sub_eq; [ | | exact Heq | eassumption | eassumption ]; mauto 3.
  - stored_resp_sub_eq Heq i; mauto 3.
  - eapply glu_ctx_env_sub_resp_sub_eq;
      [ eassumption | eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
Qed.

Add Parametric Morphism i Γ κ A Sb Δ (Hglu : EG Γ ∈ glu_ctx_env ↘ Sb) (HA : Γ ⊢ A : abs_kind_sort κ Typeω@i)
  : (cons_glu_sub_pred i Γ κ A Sb Δ)
    with signature wf_sub_eq gc_deps gc_stack Δ (Γ ▹{κ} A) ==> eq ==> iff as cons_glu_sub_pred_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq, wf_sub_eq_sym.
Qed.

(** An element glued at a type's value is related to itself at the value's
    PER at any index: both move to the larger index. *)
Lemma glu_univ_elem_per_elem_any : forall {i j : nat} {a P El Δ B N m R},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ N : B ® m ∈ El ->
    DF a ≈ a ∈ per_univ_elem j ↘ R ->
    Dom m ≈ m ∈ R.
Proof.
  intros * Hglu HN HR.
  assert (exists P' El', DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El') as (P' & El' & Hglu')
    by mauto 3 using glu_univ_elem_cumu_max_left.
  eapply glu_univ_elem_per_elem; [ exact Hglu' | | eapply per_univ_elem_cumu_max_right; exact HR ].
  eapply glu_univ_elem_exp_cumu_max_left; [ exact Hglu | exact Hglu' | exact HN ].
Qed.

Lemma glu_ctx_env_per_env : forall {Γ Sb env_rel Δ σ ρ},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Dom ρ ≈ ρ ∈ env_rel.
Proof.
  intros * Hglu Hper.
  gen ρ σ Δ env_rel.
  induction Hglu; intros.
  (** The gluing of each entry gives the clauses of the context PER of its
      kind: the head by [glu_univ_elem_per_elem_any], a definition's tie
      by [per_head_iff], the module ties and readability as they are. *)
  all: invert_per_ctx_env Hper; apply_predicate_equivalence.
  (** The head's entry, as the context PER asks for it *)
  all: repeat match goal with
         | H : _ ⊢ˢ _ ® _ ∈ cons_glu_sub_pred _ _ _ _ _ |- _ => destruct H
         | H : _ ⊢ˢ _ ® _ ∈ cons_def_glu_sub_pred _ _ _ _ _ |- _ => destruct H
         | H : _ ⊢ˢ _ ® _ ∈ cons_dm_glu_sub_pred _ _ _ _ _ _ |- _ => destruct H
         end.
  all: try match goal with H : exists t, _ /\ glu_stored_type _ _ _ _ t |- _ => destruct H as (?t & ?Het & _) end.
  1: { match goal with E : env_rel <~> _ |- _ => apply E end; exact I. }
  1: { match goal with E : env_rel <~> _ |- _ => apply E end.
       assert (Ht : tail_rel ρ↯ ρ↯) by (eapply IHHglu; eassumption).
       unshelve econstructor; [ exact Ht | | first [ assumption | intros _; eexists; eassumption ] .. ].
       match goal with H : forall ρ0 ρ' (e : tail_rel ρ0 ρ'), rel_typ _ A _ A _ _ |- _ =>
         destruct (H _ _ Ht) as [a1 a2 Ea1 Ea2 HR] end.
       functional_eval_rewrite_clear.
       eapply glu_univ_elem_per_elem_any; eassumption. }
  1: { match goal with E : env_rel <~> _ |- _ => apply E end.
       assert (Ht : tail_rel ρ↯ ρ↯) by (eapply IHHglu; eassumption).
       match goal with H : forall ρ0 ρ' (e : tail_rel ρ0 ρ'), rel_typ _ A _ A _ _ |- _ =>
         destruct (H _ _ Ht) as [a1 a2 Ea1 Ea2 HR] end.
       functional_eval_rewrite_clear.
       unshelve econstructor;
         [ exact Ht | | | first [ assumption | intros _; eexists; eassumption ] .. ].
       - eapply glu_univ_elem_per_elem_any; eassumption.
       - (** At a proposition nothing is asked; at an evaluated kind the tie *)
         match goal with H : forall ρ0 ρ', tail_rel ρ0 ρ' -> rel_typ_kind A ρ0 _ |- _ =>
           destruct (H _ _ Ht) as (a0 & Ea0 & Hk) end.
         functional_eval_rewrite_clear.
         match goal with Hd : evaluated_kind (domain_kind a) -> def_tie A M ρ |- _ => rename Hd into Htie end.
         remember (domain_kind a) as r eqn:Hk.
         destruct r; cbn [def_heads_at]; [ | exact I | ].
         all: destruct Htie as (m & Em & Hm); [ constructor | ].
         all: match goal with Ea : eval_exp _ _ _ _ ?x, HR0 : per_univ_elem _ _ ?x ?x |- _ =>
                apply (per_head_iff Ea Ea HR0) in Hm end.
         all: econstructor; eexists; split; eassumption. }
  1: { destruct_by_head cons_mod_glu_sub_pred.
       match goal with E : env_rel <~> _ |- _ => apply E end.
       econstructor; try eassumption; try (eexists; eassumption); eapply IHHglu; eassumption. }
  1: { match goal with E : env_rel <~> _ |- _ => apply E end.
       assert (Ht : tail_rel ρ↯ ρ↯) by (eapply IHHglu; eassumption).
       match goal with H : forall ρ0 ρ' (e : tail_rel ρ0 ρ'), rel_typ _ A _ A _ _ |- _ =>
         destruct (H _ _ Ht) as [a1 a2 Ea1 Ea2 HR] end.
       functional_eval_rewrite_clear.
       subst.
       unshelve econstructor; [ exact Ht | | | first [ assumption | eexists; eexists; eassumption ] .. ].
       - eapply glu_univ_elem_per_elem_any; eassumption.
       - cbn [def_heads_at].
         match goal with Hd : def_tie A M ρ |- _ => destruct Hd as (m & Em & Hm) end.
         match goal with Ea : eval_exp _ _ _ _ ?x, HR0 : per_univ_elem _ _ ?x ?x |- _ =>
           apply (per_head_iff Ea Ea HR0) in Hm end.
         econstructor; eexists; split; eassumption. }
Qed.

Lemma glu_ctx_env_wf_ctx : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    ⊢ Γ.
Proof.
  induction 1; intros;
    first
      [ eassumption
      | econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]
      | econstructor; [ eassumption | apply type_sort_abs_kind; constructor | eassumption ]
      | mauto 3 ].
Qed.

Lemma glu_ctx_env_sub_escape : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      Δ ⊢ˢ σ : Γ.
Proof.
  induction 1; intros;
    handle_functional_glu_univ_elem;
    try destruct_by_head cons_glu_sub_pred;
    try destruct_by_head cons_def_glu_sub_pred;
    try destruct_by_head cons_mod_glu_sub_pred;
    try destruct_by_head cons_dm_glu_sub_pred;
    eassumption.
Qed.

Hint Resolve glu_ctx_env_wf_ctx glu_ctx_env_sub_escape : mctt.

Lemma glu_ctx_env_per_ctx_env : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    exists env_rel, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel.
Proof.
  intros.
  eapply rel_ctx_wf_per_ctx_env, completeness_fundamental_ctx; mauto 2.
Qed.

Hint Resolve glu_ctx_env_per_ctx_env : mctt.

(** The head of a glued substitution, glued at its type's value at one
    index, is glued at it at another index, at a type glued there. *)
Lemma glu_univ_elem_exp_change_index : forall {i j : nat} {a P El P' El' Δ B N m},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Δ ⊢ B ® P' ->
    Δ ⊢ N : B ® m ∈ El ->
    Δ ⊢ N : B ® m ∈ El'.
Proof.
  intros * Hi Hj HB HN.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hi) as [R HR].
  eapply (glu_univ_elem_exp_conv (k := i)); [ eexists; exact HR | exact Hi | exact Hj | exact HN | exact HB ].
Qed.

(** Stated at a single context, since syntactic context equality is not a
    judgment; this is all [functional_glu_ctx_env] needs. The two derivations
    may still assign different universe levels to the same type, which the
    final cumulativity step handles. *)
Lemma glu_ctx_env_resp_per_ctx_helper : forall {Γ Sb Sb'},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EG Γ ∈ glu_ctx_env ↘ Sb' ->
    (Sb -∙> Sb').
Proof.
  intros * Hglu Hglu'.
  gen Sb'.
  induction Hglu; intros;
    dependent destruction Hglu';
    apply_predicate_equivalence;
    try firstorder.

  (** A module slot: the tie does not depend on the tail's derivation. *)
  3: { assert (HT : TSb -∙> TSb0) by intuition.
       intros Δ' σ' ρ' Hc; destruct Hc.
       econstructor; try eassumption; apply HT; eassumption. }
  (** An entry with a term part: its head moves to the other derivation's
      index ([glu_univ_elem_exp_change_index]), at its type glued there by
      the tail; the ties do not depend on the index. *)
  all: assert (HT : TSb -∙> TSb0) by intuition.
  all: intros Δ' σ' ρ' Hc; destruct Hc.
  all: match goal with HT : ?S -∙> ?S0, Htl : ?S _ (Wk⨟_) _ |- _ => pose proof (HT _ _ _ Htl) as Ht' end.
  all: match goal with Ht' : ?S0 _ _ _, H5 : forall Δ0 σ0 ρ0, ?S0 Δ0 σ0 ρ0 -> glu_rel_typ_with_sub _ _ _ _ _ |- _ =>
         destruct (H5 _ _ _ Ht') as [a' P' El' Ea' Hg' HA'] end.
  all: functional_eval_rewrite_clear.
  all: econstructor; try eassumption.
  all: rewrite exp_sub_shift in *.
  all: match goal with Hg : glu_univ_elem _ ?P0 ?El0 ?x, HN : ?El0 _ _ _ _ |- _ =>
         exact (glu_univ_elem_exp_change_index Hg Hg' HA' HN) end.
Qed.

Corollary functional_glu_ctx_env : forall {Γ Sb Sb'},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EG Γ ∈ glu_ctx_env ↘ Sb' ->
    (Sb <∙> Sb').
Proof.
  intros; split; eapply glu_ctx_env_resp_per_ctx_helper; eassumption.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq : mctt.
#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq_ge : mctt.
#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq' : mctt.
#[export]
Hint Resolve glu_univ_elem_per_univ_elem_typ_escape : mctt.
#[export]
Hint Resolve glu_univ_elem_per_univ_typ_escape : mctt.
#[export]
Hint Resolve glu_univ_elem_cumu_ge : mctt.
#[export]
Hint Resolve glu_univ_elem_per_subtyp_typ_escape : mctt.
#[export]
Hint Resolve mk_glu_rel_typ_with_sub' : mctt.
#[export]
Hint Resolve mk_glu_rel_typ_with_sub'' : mctt.
#[export]
Hint Resolve mk_glu_rel_exp_with_sub' : mctt.
#[export]
Hint Resolve mk_glu_rel_exp_with_sub'' : mctt.
#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mctt.
#[export]
Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mctt.
#[export] Existing Instance glu_ctx_env_sub_morphism_iff2_Proper.
#[export] Existing Instance cons_glu_sub_pred_morphism_iff_Proper.
#[export]
Hint Resolve glu_ctx_env_wf_ctx glu_ctx_env_sub_escape : mctt.
#[export]
Hint Resolve glu_ctx_env_per_ctx_env : mctt.
Ltac apply_functional_glu_ctx_env1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_ctx_env biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (EG ?Γ ∈ glu_ctx_env ↘ ?Sb1),
      H2 : EG ?Γ ∈ glu_ctx_env ↘ ?Sb2 |- _ =>
      assert_fails (unify Sb1 Sb2);
      match goal with
      | H : Sb1 <∙> Sb2 |- _ => fail 1
      | _ => assert (Sb1 <∙> Sb2) by (eapply functional_glu_ctx_env; [apply H1 | apply H2]) || tactic_error Sb1 Sb2
      end
  end.

Ltac apply_functional_glu_ctx_env :=
  repeat apply_functional_glu_ctx_env1.

Ltac handle_functional_glu_ctx_env :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_ctx_env;
  apply_predicate_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_ctx_env_cons_clean_inversion : forall {Γ TSb κ A Sb},
  EG Γ ∈ glu_ctx_env ↘ TSb ->
  EG Γ ▹{κ} A ∈ glu_ctx_env ↘ Sb ->
  exists i,
    Γ ⊢ A : abs_kind_sort κ Typeω@i /\
      (forall Δ σ ρ,
          Δ ⊢ˢ σ ® ρ ∈ TSb ->
          glu_rel_typ_with_sub i Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred i Γ κ A TSb).
Proof.
  intros.
  simpl in *.
  match_by_head glu_ctx_env progressive_invert.
  apply_functional_glu_ctx_env.
  (** [i] has to be given: the cumulativity hints let [intuition] pick any
      larger level for the type, which then no longer matches [TSb]'s. *)
  exists i; intuition.
  assert (Sb <∙> cons_glu_sub_pred i Γ κ A TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Lemma glu_ctx_env_cons_def_clean_inversion : forall {Γ TSb A M Sb},
  EG Γ ∈ glu_ctx_env ↘ TSb ->
  EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ Sb ->
  exists i κ,
    Γ ⊢ A : abs_kind_sort κ Typeω@i /\
      Γ ⊢ M : A /\
      (forall Δ σ ρ,
          Δ ⊢ˢ σ ® ρ ∈ TSb ->
          glu_rel_typ_with_sub i Δ A σ ρ) /\
      (forall Δ σ ρ,
          Δ ⊢ˢ σ ® ρ ∈ TSb ->
          glu_rel_exp_with_sub i Δ M A σ ρ) /\
      (Sb <∙> cons_def_glu_sub_pred i Γ A M TSb).
Proof.
  intros.
  simpl in *.
  match_by_head glu_ctx_env progressive_invert.
  apply_functional_glu_ctx_env.
  exists i, κ; intuition.
  assert (Sb <∙> cons_def_glu_sub_pred i Γ A M TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

(** The inversion of a context ending in a definition with a module part,
    at a given gluing of its tail. *)
Lemma glu_ctx_env_cons_dm_clean_inversion : forall {Γ TSb A M U Sb},
  EG Γ ∈ glu_ctx_env ↘ TSb ->
  EG Γ ▸ₘ A ≔ M ‖ U ∈ glu_ctx_env ↘ Sb ->
  exists i,
    Γ ⊢ A : Typeω@i /\
      Γ ⊢ M : A /\
      ⊢ Γ ▸ₘ A ≔ M ‖ U /\
      (forall Δ σ ρ,
          Δ ⊢ˢ σ ® ρ ∈ TSb ->
          glu_rel_typ_with_sub i Δ A σ ρ) /\
      (forall Δ σ ρ,
          Δ ⊢ˢ σ ® ρ ∈ TSb ->
          glu_rel_exp_with_sub i Δ M A σ ρ) /\
      (Sb <∙> cons_dm_glu_sub_pred i Γ A M U TSb).
Proof.
  intros.
  simpl in *.
  match_by_head glu_ctx_env progressive_invert.
  apply_functional_glu_ctx_env.
  exists i; intuition.
  assert (Sb <∙> cons_dm_glu_sub_pred i Γ A M U TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

End Fixed_GCtx.

Ltac invert_glu_ctx_env H :=
  (unshelve eapply (glu_ctx_env_cons_clean_inversion _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? []]])
  + (unshelve eapply (glu_ctx_env_cons_def_clean_inversion _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_ctx_env_cons_dm_clean_inversion _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? [? [? [? [? []]]]]])
  + dependent destruction H.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** Postcomposition by a Kripke weakening, [sb_wk], the operation Lemma 6.39
    uses on the semantic side. The head clause follows from
    [glu_univ_elem_exp_monotone] by a [rewrite], since [M[σ][φ]ʷ] and
    [M[(sb_wk σ φ)]] are the same expression ([exp_wk_sub]). Only the tail
    needs a judgmental step: the rearrangement it needs is an [sb_eq], which no
    gluing predicate respects. *)
Lemma glu_ctx_env_sub_monotone : forall Γ Sb,
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ' φ Δ τ ρ,
      Δ ⊢ˢ τ ® ρ ∈ Sb ->
      Δ' ⊢ᵏ φ : Δ ->
      Δ' ⊢ˢ (sb_wk τ φ) ® ρ ∈ Sb.
Proof.
  induction 1; intros * HSb Hφ;
    apply_predicate_equivalence;
    simpl in *;
    saturate_kripke_escape.
  1: (rewrite sb_wk_compose; mauto 3).
  (** [ρ] does not move, so the ties are unchanged; the head moves along the
      weakening ([glu_univ_elem_exp_monotone]); the tail is the weakened
      tail, up to an [sb_eq]. *)
  all: try destruct_by_head cons_glu_sub_pred.
  all: try destruct_by_head cons_def_glu_sub_pred.
  all: try destruct_by_head cons_mod_glu_sub_pred.
  all: try destruct_by_head cons_dm_glu_sub_pred.
  all: econstructor;
    [ rewrite sb_wk_compose; mauto 3
    | first [ eassumption | rewrite <- !exp_wk_sub; eapply glu_univ_elem_exp_monotone; eassumption
            | match goal with H : exists t, _ /\ glu_stored_type _ _ _ _ t |- exists t, _ /\ glu_stored_type _ _ _ _ t =>
                destruct H as (?t & ?Het & [?j ?b ?Pb ?Elb ?Hb ?Hgb ?HEb]); eexists; split; [ eassumption |];
                econstructor; [ eassumption | eassumption |];
                rewrite <- !exp_wk_sub; eapply glu_univ_elem_exp_monotone; eassumption end
            | (** the module value: along the weakening, then to the
                  weakened substitution's tail *)
              match goal with H : glu_dmod _ (Wk ⨟ ?s) _ _ _ |- glu_dmod _ _ _ _ _ =>
                pose proof (proj1 glu_dmod_monotone _ _ _ _ _ H _ _ Hφ) as Hm;
                eapply (proj1 glu_dmod_resp_sub_eq); [ exact Hm |];
                apply wf_sub_eq_of_sb_eq; [ exact (glu_dmod_sub_typed Hm) | apply sb_wk_shift_pre ] end ].. |].
  all: assert (Δ' ⊢ˢ (sb_wk (Wk ⨟ σ) φ) ® ρ↯ ∈ TSb) by mauto 3.
  all: assert (Δ' ⊢ˢ (sb_wk (Wk ⨟ σ) φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
  all: eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | eassumption | ].
  all: eapply wf_sub_eq_of_sb_eq; [ eassumption | apply sb_wk_shift_pre ].
Qed.

(** Extension by any entry whose term projection glues as the head. *)
(** The head is a term entry at the value of the type: it reads back, as an
    element of the type's PER ([entry_readable_of_elem]). *)
Lemma cons_glu_sub_pred_helper_gen : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El en c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ sentry_exp en : A[σ] ® c ∈ El ->
    Δ ⊢ˢ sb_extend σ en ® ρ ↦ c ⦂ entry_type_value a ∈ cons_glu_sub_pred i Γ κ A Sb.
Proof.
  intros * HSb Hσg HA Ha Hglu Hc.
  assert (Δ ⊢ˢ σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  assert (Δ ⊢ sentry_exp en : A[σ]) by (eapply glu_univ_elem_trm_escape; eassumption).
  assert (⊢ Γ ▹{κ} A) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
  assert (Δ ⊢ˢ sb_extend σ en : Γ ▹{κ} A).
  { apply wf_sub_extend_gen; [ assumption | assumption | | |].
    - intros B Hlk; inversion Hlk; subst; rewrite exp_sub_shift_extend; assumption.
    - intros B L Hlk; inversion Hlk.
    - intros U Hlk; inversion Hlk. }
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ Hc HR) as Hcc.
  (** [#0[sb_extend σ en]] is [sentry_exp en] and [Wk ⨟ sb_extend σ en] is
      [σ], both by computation; only [A[↑]ʷ[sb_extend σ en]] needs a rewrite. *)
  econstructor; [ eassumption | exact Ha | exact Hglu | | | | ].
  - rewrite exp_sub_shift_extend; exact Hc.
  - (** The stored type is the type's value *)
    eexists; split; [ reflexivity |].
    refine (mk_glu_stored_type _ _ _ _ _ i a P El ltac:(constructor) Hglu _).
    rewrite exp_sub_shift_extend; exact Hc.
  - split; [ exact (proj1 (entry_readable_of_elem HR Hcc)) | cbn; lia ].
  - first [ exact Hσg | cbn; exact Hσg | eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | exact Hσg | mauto 3 ] ].
Qed.

Lemma cons_glu_sub_pred_helper : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El M c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M : A[σ] ® c ∈ El ->
    Δ ⊢ˢ σ,,M ® ρ ↦ c ⦂ entry_type_value a ∈ cons_glu_sub_pred i Γ κ A Sb.
Proof.
  intros; eapply (cons_glu_sub_pred_helper_gen (en := se_exp M)); eassumption.
Qed.

Hint Resolve cons_glu_sub_pred_helper : mctt.

(** The head of the initial environment of a slot or a definition with a
    module part: the closure of the unit's literal, glued as the literal
    at the tail of [Id], by the context gluing's premise. *)
Lemma glu_slot_value_head : forall Δ Γ U TSb ρ h,
    (forall Δ σ ρ h, Δ ⊢ˢ σ ® ρ ∈ TSb -> ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h -> glu_dmod Δ σ Γ (me_lit U) h) ->
    Δ ⊢ˢ Wk ® ρ ∈ TSb -> ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
    glu_dmod Δ (Wk ⨟ Id) Γ (me_lit U) h.
Proof.
  intros * Hs HWk Hh.
  pose proof (Hs _ _ _ _ HWk Hh) as Hg.
  eapply (proj1 glu_dmod_resp_sub_eq); [ exact Hg |].
  apply wf_sub_eq_of_sb_eq; [ exact (glu_dmod_sub_typed Hg) | symmetry; apply sb_compose_id_right ].
Qed.

Lemma initial_env_glu_rel_exp : forall {Γ ρ Sb},
    initial_env_f Γ ρ ->
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊢ˢ Id ® ρ ∈ Sb.
Proof.
  intros * Hinit HΓ.
  gen ρ.
  induction HΓ; intros * Hinit;
    dependent destruction Hinit;
    apply_predicate_equivalence.
  1: { cbn; mauto 3. }
  1: { (** An assumption: the head is the fresh variable *)
    assert (HΓA : ⊢ Γ ▹{κ} A) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
    assert (HId : Γ ⊢ˢ Id ® ρ ∈ TSb) by (apply IHHΓ; assumption).
    match goal with H : forall Δ σ ρ, TSb Δ σ ρ -> glu_rel_typ_with_sub _ _ _ _ _ |- _ =>
      destruct (H _ _ _ HId) as [a' P El Ea' Hglu HAg] end.
    functional_eval_rewrite_clear.
    rewrite exp_sub_id in HAg.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu HAg ltac:(eassumption)) as [Hk Hnl].
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    econstructor; [ mauto 3 | eassumption | exact Hglu | | | | ].
    - (** The head is [var0_glu_elem] once the identity substitutions are gone. *)
      subst κ; rewrite !exp_sub_id; exact (var0_glu_elem Hglu Hnl HAg).
    - (** The stored type is the type's value *)
      eexists; split; [ reflexivity |]; econstructor; [ constructor | exact Hglu |].
      subst κ; rewrite !exp_sub_id; exact (var0_glu_elem Hglu Hnl HAg).
    - split; [ exact (proj1 (entry_readable_of_elem HR (var_per_elem _ HR Hnl))) | cbn; lia ].
    - (** The tail is the induction hypothesis pushed along [↑]: [Wk ⨟ Id] and
          [sb_wk Id ↑] both send [x] to [#(S x)], so [eapply] converts them. *)
      match goal with HG : EG Γ ∈ glu_ctx_env ↘ TSb |- _ =>
        eapply (glu_ctx_env_sub_monotone _ _ HG (Γ ▹{κ} A) wk_shift Γ Id ρ); [ exact HId | apply kripke_shift; exact HΓA ] end. }
  1: { (** A definition of an evaluated kind: the head is [⟦M⟧ρ], glued with
        [M[↑]ʷ] by the gluing of [M] along [↑], hence with [#0] by δ. *)
    assert (HΓAM : ⊢ Γ ▸ A ≔ M) by (econstructor; [ eassumption | apply type_sort_abs_kind; constructor | eassumption ]).
    assert (HId : Γ ⊢ˢ Id ® ρ ∈ TSb) by (apply IHHΓ; assumption).
    assert (HWk : Γ ▸ A ≔ M ⊢ˢ Wk ® ρ ∈ TSb).
    { match goal with HG : EG Γ ∈ glu_ctx_env ↘ TSb |- _ =>
        eapply (glu_ctx_env_sub_monotone _ _ HG (Γ ▸ A ≔ M) wk_shift Γ Id ρ); [ exact HId | apply kripke_shift_def; exact HΓAM ] end. }
    match goal with H : forall Δ σ ρ, TSb Δ σ ρ -> glu_rel_exp_with_sub _ _ M _ _ _ |- _ =>
      destruct (H _ _ _ HWk) as [a' m' P El Ea' Hm' Hglu HMg] end.
    functional_eval_rewrite_clear.
    assert (m' = m) as ->.
    { match goal with Hev : evaluated_kind (domain_kind a) |- _ =>
        destruct (domain_kind a); cbn in Hm'; [ | inversion Hev | ]; eapply functional_eval_exp; eassumption end. }
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMg HR) as Hmm.
    econstructor; [ mauto 3 | eassumption | exact Hglu | | | | | exact HWk ].
    - rewrite !exp_sub_id.
      rewrite !exp_sub_of_shift in HMg.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    - intros _; exists m; split; [ eassumption |].
      eapply per_head_of; [ eassumption | eassumption | exact HR | exact Hmm ].
    - eexists; split; [ reflexivity |]; econstructor; [ constructor | exact Hglu |].
      rewrite !exp_sub_id.
      rewrite !exp_sub_of_shift in HMg.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    - split; [ exact (proj1 (entry_readable_of_elem HR Hmm)) | cbn; lia ]. }
  1: { (** A definition of a proposition: the head is the body kept,
        [⋆ᵈ⟨M, ρ⟩], glued as [M[↑]ʷ] is; no tie is asked. *)
    assert (HΓAM : ⊢ Γ ▸ A ≔ M) by (econstructor; [ eassumption | apply type_sort_abs_kind; constructor | eassumption ]).
    assert (HId : Γ ⊢ˢ Id ® ρ ∈ TSb) by (apply IHHΓ; assumption).
    assert (HWk : Γ ▸ A ≔ M ⊢ˢ Wk ® ρ ∈ TSb).
    { match goal with HG : EG Γ ∈ glu_ctx_env ↘ TSb |- _ =>
        eapply (glu_ctx_env_sub_monotone _ _ HG (Γ ▸ A ≔ M) wk_shift Γ Id ρ); [ exact HId | apply kripke_shift_def; exact HΓAM ] end. }
    match goal with H : forall Δ σ ρ, TSb Δ σ ρ -> glu_rel_exp_with_sub _ _ M _ _ _ |- _ =>
      destruct (H _ _ _ HWk) as [a' m' P El Ea' Hm' Hglu HMg] end.
    functional_eval_rewrite_clear.
    match goal with Hk : domain_kind a = ak_propositional |- _ => rewrite Hk in Hm'; cbn in Hm'; subst m' end.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMg HR) as Hmm.
    econstructor; [ mauto 3 | eassumption | exact Hglu | | | | | exact HWk ].
    - rewrite !exp_sub_id.
      rewrite !exp_sub_of_shift in HMg.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    - match goal with Hk : domain_kind a = ak_propositional |- _ => rewrite Hk; intros Hev; inversion Hev end.
    - eexists; split; [ reflexivity |]; econstructor; [ constructor | exact Hglu |].
      rewrite !exp_sub_id.
      rewrite !exp_sub_of_shift in HMg.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    - split; [ exact (proj1 (entry_readable_of_elem HR Hmm)) | cbn; lia ]. }
  1: { (** A module slot: the initial environment is related to itself at
        the canonical context PER, whose clauses are the slot's. *)
    assert (HΓU : ⊢ Γ ▹ₘ U) by (econstructor; eassumption).
    assert (HId : Γ ⊢ˢ Id ® ρ ∈ TSb) by (apply IHHΓ; assumption).
    assert (HWk : Γ ▹ₘ U ⊢ˢ Wk ® ρ ∈ TSb).
    { match goal with HG : EG Γ ∈ glu_ctx_env ↘ TSb |- _ =>
        eapply (glu_ctx_env_sub_monotone _ _ HG (Γ ▹ₘ U) wk_shift Γ Id ρ); [ exact HId | apply kripke_shift_mod; exact HΓU ] end. }
    destruct (rel_ctx_wf_per_ctx_env (completeness_fundamental_ctx _ HΓU)) as [R HR].
    pose proof (proj1 (proj1 wf_scoped _ _ _ HΓU)) as Hs.
    destruct (per_ctx_then_per_env_initial_env HR Hs Hs) as (ρ1 & ρ2 & Hi1 & _ & Hρ).
    assert (ρ1 = ρ ↦ᵐ h ⦂ U) as -> by (eapply (functional_initial_env _ _ Hi1); econstructor; eassumption).
    invert_per_ctx_env HR.
    match goal with E : R <~> _ |- _ => apply E in Hρ end.
    destruct Hρ.
    econstructor; [ mauto 3 | eassumption | | reflexivity | eassumption | exact HWk ].
    eapply glu_slot_value_head; [ eassumption | exact HWk | eassumption ]. }
  1: { (** A definition with a module part: the head as a definition's, the
        module clauses from the canonical context PER as a slot's. *)
    assert (HΓU : ⊢ Γ ▸ₘ A ≔ M ‖ U) by eassumption.
    assert (HId : Γ ⊢ˢ Id ® ρ ∈ TSb) by (apply IHHΓ; assumption).
    assert (HWk : Γ ▸ₘ A ≔ M ‖ U ⊢ˢ Wk ® ρ ∈ TSb).
    { match goal with HG : EG Γ ∈ glu_ctx_env ↘ TSb |- _ =>
        eapply (glu_ctx_env_sub_monotone _ _ HG (Γ ▸ₘ A ≔ M ‖ U) wk_shift Γ Id ρ); [ exact HId | apply kripke_shift_dm; exact HΓU ] end. }
    match goal with H : forall Δ σ ρ, TSb Δ σ ρ -> glu_rel_exp_with_sub _ _ M _ _ _ |- _ =>
      destruct (H _ _ _ HWk) as [a' m' P El Ea' Hm' Hglu HMg] end.
    functional_eval_rewrite_clear.
    destruct (rel_ctx_wf_per_ctx_env (completeness_fundamental_ctx _ HΓU)) as [R0 HR0].
    pose proof (proj1 (proj1 wf_scoped _ _ _ HΓU)) as Hs.
    destruct (per_ctx_then_per_env_initial_env HR0 Hs Hs) as (ρ1 & ρ2 & Hi1 & _ & Hρ).
    assert (ρ1 = ρ ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ U) as -> by (eapply (functional_initial_env _ _ Hi1); econstructor; eassumption).
    invert_per_ctx_env HR0.
    match goal with E : R0 <~> _ |- _ => apply E in Hρ end.
    destruct Hρ.
    (** The type is of a universe, so the term's value is evaluated *)
    assert (HAk : domain_kind a = ak_relevant).
    { assert (HAt : (Γ ▸ₘ A ≔ M ‖ U) ⊢ A[Wk] ® P) by (eapply glu_univ_elem_trm_typ; eassumption).
      assert (HAs : (Γ ▸ₘ A ≔ M ‖ U) ⊢ A[Wk] : abs_kind_sort ak_relevant Typeω@i) by (cbn; mauto 3).
      exact (proj1 (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu HAt HAs)). }
    rewrite HAk in Hm'; cbn in Hm'.
    assert (m' = m) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMg HR) as Hmm.
    assert (HEl0 : Γ ▸ₘ A ≔ M ‖ U ⊢ #0[Id] : A[↑]ʷ[Id] ® m ∈ El).
    { rewrite !exp_sub_id.
      rewrite !exp_sub_of_shift in HMg.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ]. }
    econstructor; [ mauto 3 | eassumption | exact Hglu | exact HEl0 | | eassumption | | | eassumption | exact HWk ].
    - exists m; split; [ eassumption |].
      eapply per_head_of; [ eassumption | eassumption | exact HR | exact Hmm ].
    - eapply glu_slot_value_head; [ eassumption | exact HWk | eassumption ].
    - eexists; split; [ reflexivity |]; econstructor; [ constructor | exact Hglu | exact HEl0 ]. }
Qed.

(** *** Tactics for [glu_rel_*] *)

End Fixed_GCtx.

#[export]
Hint Resolve cons_glu_sub_pred_helper : mctt.
Ltac destruct_glu_rel_by_assumption sub_glu_rel H :=
  repeat
    match goal with
    | H' : ?Δ ⊢ˢ ?σ ® ?ρ ∈ ?sub_glu_rel0 |- _ =>
        unify sub_glu_rel0 sub_glu_rel;
        destruct (H _ _ _ H') as [];
        destruct_conjs;
        mark_with H' 1
    end;
  unmark_all_with 1.
Ltac destruct_glu_rel_exp_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ ?sub_glu_rel -> glu_rel_exp_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_glu_rel_typ_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ ?sub_glu_rel -> glu_rel_typ_with_sub _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** *** Lemmas about [glu_rel_exp] *)

Lemma glu_rel_exp_clean_inversion1 : forall {Γ Sb M A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : A ->
    exists i,
    forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? [].
  destruct_conjs.
  eexists; intros.
  handle_functional_glu_ctx_env.
  mauto.
Qed.

Definition glu_rel_exp_clean_inversion2_result i Sb M A :=
  forall Δ σ ρ,
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    glu_rel_exp_with_sub i Δ M A σ ρ.

Lemma glu_rel_exp_clean_inversion2 : forall {i : nat} {Γ Sb M A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : Typeω@i ->
    Γ ⊩ M : A ->
    glu_rel_exp_clean_inversion2_result i Sb M A.
Proof.
  unfold glu_rel_exp_clean_inversion2_result.
  intros * ? HA HM.
  eapply glu_rel_exp_clean_inversion1 in HA; [| eassumption].
  eapply glu_rel_exp_clean_inversion1 in HM; [| eassumption].
  destruct HA as [iA HA], HM as [iM HM].
  intros Δ σ ρ HSb.
  destruct (HA _ _ _ HSb) as [u a0 Pu Elu Eu Ha0 Hgu HAu].
  destruct (HM _ _ _ HSb) as [a m P El Ea Hm Hg HMg].
  simplify_evals; cbn [domain_kind glu_term_value] in Ha0.
  functional_eval_rewrite_clear.
  (** The type's value is glued at [i], as an element of [Typeω@i]; the
      term moves there ([glu_univ_elem_exp_conv]). *)
  basic_invert_glu_univ_elem Hgu; apply_predicate_equivalence.
  destruct HAu as [_ _ [Pt Elt Hgt Hpt]].
  destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [R HR].
  econstructor; [ eassumption | exact Hm | exact Hgt |].
  eapply (glu_univ_elem_exp_conv (k := iM)); [ eexists; exact HR | exact Hg | exact Hgt | exact HMg | exact Hpt ].
Qed.

End Fixed_GCtx.

Ltac invert_glu_rel_exp H :=
  (unshelve eapply (glu_rel_exp_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_rel_exp_to_wf_exp : forall {Γ A M},
    Γ ⊩ M : A ->
    Γ ⊢ M : A.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel) as [env_rel] by mauto 3.
  assert (HΓ : ⊢ Γ) by (eapply glu_ctx_env_wf_ctx; eassumption).
  pose proof (proj1 (proj1 wf_scoped _ _ _ HΓ)) as Hs.
  match goal with HR : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel |- _ =>
    destruct (per_ctx_then_per_env_initial_env HR Hs Hs) as (ρ & ρ' & ? & ? & ?) end.
  functional_initial_env_rewrite_clear.
  assert (Γ ⊢ˢ Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  assert (Γ ⊢ M[Id] : A[Id]) as HId by mauto 3 using glu_univ_elem_trm_escape.
  rewrite !exp_sub_id in HId; eassumption.
Qed.

Hint Resolve glu_rel_exp_to_wf_exp : mctt.

(** *** The Readback of a Glued Environment

    A kept proof reads back as its term under definitions binding the
    readbacks of the entries of its environment ([read_proof_kept]).  For
    an environment glued to a substitution, those definitions form a
    well-formed context into which the variables of the proof's context
    map as themselves, and they ζ-reduce to the substitution
    ([glu_env_lets]); the proof's readback is then typed and equal to the
    proof at the substitution ([lets_exp_of_sub]). *)

(** The definitions of the first [S k] positions: those of the positions
    [k], …, [1], then the head, innermost. *)
Lemma read_lets_snoc : forall k ρ s bs, Rlets ρ at S k in gc_deps ⍮ gc_stack ⍮ s ↘ bs ->
  exists bs0 b0, bs = bs0 ++ b0 :: nil /\ Rlets ρ↯ at k in gc_deps ⍮ gc_stack ⍮ s ↘ bs0 /\
    Rent (env_entry ρ 0) in gc_deps ⍮ gc_stack ⍮ (s + k) ↘ b0.
Proof.
  induction k as [| k IH]; intros * H; inversion H; subst.
  - match goal with H0 : read_lets _ _ _ ρ 0 _ |- _ => inversion H0; subst end.
    eexists nil, _; split; [ reflexivity | split; [ constructor | rewrite PeanoNat.Nat.add_0_r; eassumption ] ].
  - match goal with H1 : read_lets _ _ (S s) ρ (S k) _ |- _ => destruct (IH _ _ _ H1) as (bs0' & b0 & -> & H2 & H3) end.
    match goal with H1 : read_entry _ _ s (env_entry ρ (S k)) ?b |- _ => exists (b :: bs0'), b0; split; [ reflexivity | split ];
      [ constructor; [ rewrite env_entry_drop; exact H1 | exact H2 ] | replace (s + S k) with (S s + k) by lia; exact H3 ] end.
Qed.

Lemma ctx_lets_snoc : forall bs b Γ, ctx_lets Γ (bs ++ b :: nil) = ctx_lets (ctx_lets Γ bs) (b :: nil).
Proof. induction bs as [| c bs IH]; intros; cbn [List.app]; [ reflexivity |]; destruct c; cbn [ctx_lets]; apply IH. Qed.

Lemma lets_sub_snoc : forall bs b, sb_eq (lets_sub (bs ++ b :: nil)) (binding_zeta_sub b ⨟ lets_sub bs).
Proof.
  induction bs as [| c bs IH]; intros; cbn [List.app lets_sub].
  - rewrite sb_compose_id_left, sb_compose_id_right; reflexivity.
  - rewrite IH, sb_compose_assoc; reflexivity.
Qed.

Lemma length_ctx_lets : forall bs Γ, List.length (ctx_lets Γ bs) = List.length bs + List.length Γ.
Proof. induction bs as [| c bs IH]; intros; [ reflexivity |]; destruct c; cbn [ctx_lets]; rewrite IH; cbn; lia. Qed.

(** A chain's context weakens to its base. *)
Lemma ctx_lets_kripke : forall bs Γ, ⊢ ctx_lets Γ bs -> ctx_lets Γ bs ⊢ᵏ wk_shiftn (List.length bs) : Γ.
Proof.
  induction bs as [| b bs IH]; intros * H; cbn [List.length ctx_lets] in *.
  - rewrite wk_shiftn_zero; apply kripke_id; exact H.
  - destruct b as [A M | U | A M U]; cbn [ctx_lets] in *.
    all: pose proof (wf_wk_cod _ _ _ _ _ (ctx_lets_wk_shiftn bs H)) as Hb.
    all: (eapply wk_kripke_Proper;
          [| eapply kripke_compose; [ exact (IH _ H) | first [ apply kripke_shift_def | apply kripke_shift_mod | apply kripke_shift_dm ]; exact Hb ] ]).
    all: intros x; cbn; lia.
Qed.

(** Past the chain, its ζ-substitution is the identity. *)
Lemma lets_sub_shiftn : forall bs x, lets_sub bs (x + List.length bs) = se_var x.
Proof.
  induction bs as [| b bs IH]; intros; cbn [lets_sub List.length]; [ rewrite PeanoNat.Nat.add_0_r; reflexivity |].
  unfold sb_compose; replace (x + S (List.length bs)) with (S x + List.length bs) by lia; rewrite IH.
  destruct b; reflexivity.
Qed.

(** A term glued at a type's value reads back, with the type, as plain
    normal forms equal to them at every weakening: realizability gives
    the annotated readbacks ([realize_glu_typ_top], [realize_glu_elem_top]),
    which are the plain ones ([nf_ne_annotate_proofs_plain]). *)
Lemma glu_stored_readback : forall Δ T N v κ (i j : nat) b P El,
    Δ ⊢ T : abs_kind_sort κ Typeω@i ->
    DG b ∈ glu_univ_elem j ↘ P ↘ El -> Δ ⊢ N : T ® v ∈ El ->
    forall Δ0 φ0 A' W, Δ0 ⊢ᵏ φ0 : Δ -> Rtyp b in gc_deps ⍮ gc_stack ⍮ List.length Δ0 ↘ A' ->
      Rnf ⇓ b v in gc_deps ⍮ gc_stack ⍮ List.length Δ0 ↘ W ->
      exists n, Δ0 ⊢ T[φ0]ʷ ≈ A' : abs_kind_sort κ Typeω@n /\ Δ0 ⊢ N[φ0]ʷ ≈ W : T[φ0]ʷ.
Proof.
  intros * HT Hg HN * Hφ HA' HW.
  destruct (glu_univ_elem_cumu_max_left (j := i) Hg) as (Pm & Elm & Hgm).
  pose proof (glu_univ_elem_exp_cumu_max_left Hg Hgm HN) as HNm.
  pose proof (glu_univ_elem_trm_typ _ _ _ _ Hgm _ _ _ _ HNm) as HTm.
  assert (HTs : Δ ⊢ T : abs_kind_sort κ Typeω@(max j i)) by (apply wf_exp_kind_sort_max_right; exact HT).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hgm HTm HTs) as [Hk Hn].
  pose proof (realize_glu_typ_top _ _ _ _ Hgm Hn _ _ HTm) as [_ _ Hrt].
  pose proof (realize_glu_elem_top _ _ _ _ Hgm _ _ _ _ HNm) as [_ _ _ _ _ _ Hre].
  pose proof (Hrt _ _ _ Hφ HA') as E1; pose proof (Hre _ _ _ Hφ HW) as E2; unfold glu_nf_eq in E1, E2.
  rewrite Hk in E1; cbn [large_level] in E1.
  pose proof (proj1 nf_ne_annotate_proofs_plain _ _ _ _ _ (presup_exp_eq_right E1)) as E3.
  pose proof (proj1 nf_ne_annotate_proofs_plain _ _ _ _ _ (presup_exp_eq_right E2)) as E4.
  exists (max j i); split; etransitivity; eassumption.
Qed.

(** A scoped term is scoped by its free bound: the readback of a kept
    proof binds only the positions below it, and the term is copied
    under them. *)
Lemma syn_scoped_shrink :
  (forall M m n, exp_scoped m M -> exp_free_bound M <= n -> exp_scoped n M) /\
  (forall H m n, modexp_scoped m H -> modexp_free_bound H <= n -> modexp_scoped n H) /\
  (forall b m n, binding_scoped m b -> binding_free_bound b <= n -> binding_scoped n b) /\
  (forall U m n, gunit_scoped m U -> gunit_free_bound U <= n -> gunit_scoped n U) /\
  (forall D m n, moddef_scoped m D -> moddef_free_bound D <= n -> moddef_scoped n D) /\
  (forall Φ m n, gmod_scoped m Φ -> gmod_free_bound Φ <= n -> gmod_scoped n Φ) /\
  (forall E m n, gentry_scoped m E -> gentry_free_bound E <= n -> gentry_scoped n E) /\
  (forall e m n, centry_scoped m e -> centry_free_bound e <= n -> centry_scoped n e).
Proof.
  syn_mut_ind; scoped_case;
    repeat match goal with
           | B : option exp |- _ => destruct B
           end; cbn in *; destruct_all;
    repeat split; try lia; try assumption.
  all: try (match goal with IH : forall m n, _ -> _ <= n -> ?P n ?X, Hs : ?P _ ?X |- ?P _ ?X => eapply IH; [ exact Hs | lia ] end).
  - (** The uniform parameters of an eliminator *)
    assert (HUs : list_max (map exp_free_bound Us) <= n) by lia. clear - H H2 HUs.
    apply List.list_max_le, List.Forall_map in HUs.
    induction H; cbn in *; [ exact I |]; inversion HUs; subst; destruct H2 as [Hx Hl].
    split; [ eapply H; [ exact Hx | assumption ] | apply IHForall; assumption ].
  - (** Its blocks *)
    match goal with HB : _ <= n |- _ => assert (HBk : list_max (map (fun b : eblock =>
              match b with
              | eb_mk nm Z A Bs =>
                  Init.Nat.max (exp_free_bound Z - (nm - 1))
                    (Init.Nat.max (exp_free_bound A - nm)
                       (list_max (map (fun br : (String.string * nat * typ)%type => exp_free_bound (snd br) - snd (fst br)) Bs)))
              end) Bks) <= n) by lia end.
    clear - H0 H4 HBk.
    apply List.list_max_le, List.Forall_map in HBk.
    induction H0 as [| [nm Z A Bs] Bks [HZ [HA HB]] _ IH]; cbn in *; [ exact I |].
    inversion HBk as [| ? ? Hb0 HBk']; subst.
    destruct H4 as ((HZs & HAs & HBs) & Hl); split; [| apply IH; assumption ].
    split; [ eapply HZ; [ exact HZs | lia ] | split; [ eapply HA; [ exact HAs | lia ] |] ].
    assert (HBm : list_max (map (fun br : (String.string * nat * typ)%type => exp_free_bound (snd br) - snd (fst br)) Bs) <= n)
      by lia.
    apply List.list_max_le, List.Forall_map in HBm.
    clear - HB HBs HBm; induction HB as [| [[c k] B] Bs HB0 _ IH]; cbn in *; [ exact I |].
    inversion HBm; subst; destruct HBs as [Hs Hl]; split; [ eapply HB0; [ exact Hs | cbn in *; lia ] | apply IH; assumption ].
  - (** The fields of a tuple *)
    assert (Hfs : list_max (map (fun f : (String.string * typ)%type => exp_free_bound (snd f)) fs) <= n) by lia.
    clear - H0 H3 Hfs.
    apply List.list_max_le, List.Forall_map in Hfs.
    induction H0; cbn in *; [ exact I |]; inversion Hfs; subst; destruct H3 as [Hx Hl].
    split; [ eapply H; [ exact Hx | assumption ] | apply IHForall; assumption ].
  - (** The parameters of a unit *)
    match goal with H2 : Init.Nat.max ?t _ <= n |- _ => assert (Ht : t <= n) by lia end.
    clear - H H1 Ht.
    induction H as [| e Δ He _ IH]; cbn in *; [ exact I |].
    destruct H1 as [Hs Hl]; split; [ eapply He; [ exact Hs | lia ] | apply IH; [ exact Hl | lia ] ].
  - eapply H0; [ reflexivity | exact H3 | lia ].
Qed.

Lemma exp_scoped_shrink : forall M m n, exp_scoped m M -> exp_free_bound M <= n -> exp_scoped n M.
Proof. exact (proj1 syn_scoped_shrink). Qed.

Lemma gunit_scoped_shrink : forall U m n, gunit_scoped m U -> gunit_free_bound U <= n -> gunit_scoped n U.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_scoped_shrink)))). Qed.

(** Past a chain, weakening then ζ-reducing is the identity. *)
Lemma exp_wk_lets_sub : forall bs X, X[wk_shiftn (List.length bs)]ʷ[lets_sub bs] = X.
Proof.
  intros; rewrite exp_sub_wk; etransitivity; [| apply exp_sub_id ]; apply exp_sub_sb_eq; intros x; cbn; apply lets_sub_shiftn.
Qed.

(** One more definition of the chain, binding an assumption of [Γ]: its
    type and body equal to the substitution's at the assumption, the
    variables of [Γ] map into the longer chain by [q τ0], which ζ-reduces
    to the substitution.  The premises at [τ0] are the statement of
    [glu_env_lets] for the shorter chain; the two equations are what the
    gluing gives ([glu_stored_readback]). *)
Lemma env_lets_step_ass : forall Γ κ A (i : nat) Δ' bs0 τ0 σ' A' W (n : nat),
  Γ ⊢ A : abs_kind_sort κ Typeω@i ->
  ⊢ ctx_lets Δ' bs0 -> ctx_lets Δ' bs0 ⊢ˢ τ0 : Γ ->
  Δ' ⊢ˢ τ0 ⨟ lets_sub bs0 ≈ Wk ⨟ σ' : Γ ->
  Δ' ⊢ˢ σ' : Γ ▹{κ} A ->
  ctx_lets Δ' bs0 ⊢ A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ ≈ A' : abs_kind_sort κ Typeω@n ->
  ctx_lets Δ' bs0 ⊢ #0[σ'][wk_shiftn (List.length bs0)]ʷ ≈ W : A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ ->
  ⊢ ctx_lets Δ' (bs0 ++ b_def A' W :: nil) /\
  ctx_lets Δ' (bs0 ++ b_def A' W :: nil) ⊢ˢ q τ0 : Γ ▹{κ} A /\
  Δ' ⊢ˢ q τ0 ⨟ lets_sub (bs0 ++ b_def A' W :: nil) ≈ σ' : Γ ▹{κ} A.
Proof.
  intros * HA HΔ0 Hτ0 Heq0 Hσ' EA' EW.
  rewrite ctx_lets_snoc; cbn [ctx_lets].
  set (Δ0 := ctx_lets Δ' bs0) in *.
  pose proof (ctx_lets_wk_shiftn bs0 HΔ0) as Hwn.
  pose proof (lets_sub_wf bs0 HΔ0) as HL0.
  assert (HAτ : Δ0 ⊢ A[τ0] : abs_kind_sort κ Typeω@i)
    by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hτ0) as H; rewrite abs_kind_sort_sub in H; exact H).
  (** [A[τ0]] is the substitution's type at the head, through the chain *)
  pose proof (ctx_lets_unfold_definitions bs0 HAτ) as E1.
  assert (E2 : Δ' ⊢ A[τ0][lets_sub bs0] ≈ A[↑]ʷ[σ'] : abs_kind_sort κ Typeω@i).
  { rewrite exp_sub_sub, exp_sub_shift.
    pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HA) Heq0) as H; rewrite abs_kind_sort_sub in H; exact H. }
  pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ E2 _ _ Hwn) as E3; rewrite abs_kind_sort_wk in E3; cbn in E3.
  assert (EA : Δ0 ⊢ A[τ0] ≈ A' : abs_kind_sort κ Typeω@(max i n)).
  { etransitivity; [ apply wf_exp_eq_kind_sort_max_left; etransitivity; [ exact E1 | exact E3 ] | apply wf_exp_eq_kind_sort_max_right; exact EA' ]. }
  pose proof (presup_exp_eq_right EA') as HA'.
  assert (HW : Δ0 ⊢ W : A').
  { eapply wf_conv_sort; [ exact (presup_exp_eq_right EW) | exact HA' | apply type_sort_abs_kind; constructor | exact EA' ]. }
  assert (HΓ1 : ⊢ Δ0 ▸ A' ≔ W) by (eapply wf_ctx_extend_def; [ exact HA' | apply type_sort_abs_kind; constructor | exact HW ]).
  split; [ exact HΓ1 |].
  assert (Hsh : Δ0 ▸ A' ≔ W ⊢ʷ ↑ : Δ0) by (apply wf_wk_shift; exact HΓ1).
  assert (Hq : Δ0 ▸ A' ≔ W ⊢ˢ q τ0 : Γ ▹{κ} A).
  { unfold sb_q; apply wf_sub_extend_gen.
    - eapply wf_sub_sb_eq; [| symmetry; apply sb_wk_compose ].
      eapply wf_sub_compose; [ exact Hτ0 | eapply wf_sub_sb_eq; [ exact (wf_sub_shift _ _ _ _ HΓ1) | symmetry; apply sb_of_wk_shift ] ].
    - econstructor; [ exact HA | apply sort_kind_abs_kind_sort ].
    - intros A0 Hl; inversion Hl; subst; cbn [sentry_exp].
      rewrite exp_sub_shift_extend, <- exp_wk_sub.
      eapply wf_conv_sort; [ apply wf_vlookup; [ exact HΓ1 | constructor ] | | apply type_sort_abs_kind; constructor |].
      + pose proof (proj1 wk_preserves_wf _ _ _ _ _ HAτ _ _ Hsh) as H; rewrite abs_kind_sort_wk in H; cbn in H.
        apply wf_exp_kind_sort_max_right with (n := n) in H; rewrite PeanoNat.Nat.max_comm in H; exact H.
      + pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ _ _ EA) _ _ Hsh) as H;
          rewrite abs_kind_sort_wk in H; cbn in H; exact H.
    - intros A0 M0 Hl; inversion Hl.
    - intros U0 Hl; inversion Hl. }
  split; [ exact Hq |].
  (** The ζ-substitution of the longer chain, after [q τ0], is that of the
      shorter one extended by [W] *)
  assert (Hsb : sb_eq (q τ0 ⨟ lets_sub (bs0 ++ b_def A' W :: nil)) ((τ0 ⨟ lets_sub bs0),,W[lets_sub bs0]))
    by (rewrite lets_sub_snoc; cbn [binding_zeta_sub]; rewrite <- sb_compose_assoc, sb_q_extend, sb_extend_compose; reflexivity).
  assert (EW0 : Δ' ⊢ W[lets_sub bs0] ≈ #0[σ'] : A[τ0][lets_sub bs0]).
  { pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ _ _ EW) (wf_sub_eq_refl _ _ _ _ _ HL0)) as H.
    rewrite !exp_wk_lets_sub in H.
    eapply wf_exp_eq_conv_sort; [ exact H | exact (presup_exp_eq_left E2) | apply type_sort_abs_kind; constructor | symmetry; exact E2 ]. }
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [| symmetry; exact Hsb ]; apply wf_sub_eq_sym.
  constructor.
  - eapply wf_sub_extend; [ exact (wf_sub_eq_left _ _ _ _ _ _ Heq0) | exact HA | apply sort_kind_abs_kind_sort |].
    rewrite <- exp_sub_sub; exact (presup_exp_eq_left EW0).
  - exact Hσ'.
  - intros x T Hl; inversion Hl; subst.
    + rewrite exp_sub_shift_extend, <- exp_sub_sub; exact EW0.
    + rewrite exp_sub_shift_extend; match goal with H : Γ ∋ # _ : _ |- _ => exact (wf_sub_eq_apply _ _ _ _ _ _ Heq0 _ _ H) end.
  - intros x U Hl; inversion Hl; subst.
    match goal with H : Γ ∋ # _ ≔ₘ _ |- _ => exact (wf_sub_eq_apply_mod _ _ _ _ _ _ Heq0 _ _ H) end.
Qed.

(** The same for a definition of [Γ]: the chain's definition is also its
    body at [τ0], since the substitution's head is the body at it
    ([wf_sub_apply_def]). *)
Lemma env_lets_step_def : forall Γ κ A M (i : nat) Δ' bs0 τ0 σ' A' W (n : nat),
  Γ ⊢ A : abs_kind_sort κ Typeω@i -> Γ ⊢ M : A ->
  ⊢ ctx_lets Δ' bs0 -> ctx_lets Δ' bs0 ⊢ˢ τ0 : Γ ->
  Δ' ⊢ˢ τ0 ⨟ lets_sub bs0 ≈ Wk ⨟ σ' : Γ ->
  Δ' ⊢ˢ σ' : Γ ▸ A ≔ M ->
  ctx_lets Δ' bs0 ⊢ A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ ≈ A' : abs_kind_sort κ Typeω@n ->
  ctx_lets Δ' bs0 ⊢ #0[σ'][wk_shiftn (List.length bs0)]ʷ ≈ W : A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ ->
  ⊢ ctx_lets Δ' (bs0 ++ b_def A' W :: nil) /\
  ctx_lets Δ' (bs0 ++ b_def A' W :: nil) ⊢ˢ q τ0 : Γ ▸ A ≔ M /\
  Δ' ⊢ˢ q τ0 ⨟ lets_sub (bs0 ++ b_def A' W :: nil) ≈ σ' : Γ ▸ A ≔ M.
Proof.
  intros * HA HM HΔ0 Hτ0 Heq0 Hσ' EA' EW.
  rewrite ctx_lets_snoc; cbn [ctx_lets].
  set (Δ0 := ctx_lets Δ' bs0) in *.
  pose proof (ctx_lets_wk_shiftn bs0 HΔ0) as Hwn.
  pose proof (lets_sub_wf bs0 HΔ0) as HL0.
  assert (HSi : type_sort (abs_kind_sort κ Typeω@i)) by (apply type_sort_abs_kind; constructor).
  assert (HAτ : Δ0 ⊢ A[τ0] : abs_kind_sort κ Typeω@i)
    by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hτ0) as H; rewrite abs_kind_sort_sub in H; exact H).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM Hτ0) as HMτ.
  pose proof (ctx_lets_unfold_definitions bs0 HAτ) as E1.
  assert (E2 : Δ' ⊢ A[τ0][lets_sub bs0] ≈ A[↑]ʷ[σ'] : abs_kind_sort κ Typeω@i).
  { rewrite exp_sub_sub, exp_sub_shift.
    pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HA) Heq0) as H; rewrite abs_kind_sort_sub in H; exact H. }
  pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ E2 _ _ Hwn) as E3; rewrite abs_kind_sort_wk in E3; cbn in E3.
  assert (E13 : Δ0 ⊢ A[τ0] ≈ A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ : abs_kind_sort κ Typeω@i)
    by (etransitivity; [ exact E1 | exact E3 ]).
  assert (EA : Δ0 ⊢ A[τ0] ≈ A' : abs_kind_sort κ Typeω@(max i n)).
  { etransitivity; [ apply wf_exp_eq_kind_sort_max_left; exact E13 | apply wf_exp_eq_kind_sort_max_right; exact EA' ]. }
  pose proof (presup_exp_eq_right EA') as HA'.
  assert (HW : Δ0 ⊢ W : A').
  { eapply wf_conv_sort; [ exact (presup_exp_eq_right EW) | exact HA' | apply type_sort_abs_kind; constructor | exact EA' ]. }
  (** The chain's definition is the body at [τ0] *)
  assert (WM : Δ0 ⊢ W ≈ M[τ0] : A[τ0]).
  { pose proof (ctx_lets_unfold_definitions bs0 HMτ) as E1M.
    assert (E2M : Δ' ⊢ M[τ0][lets_sub bs0] ≈ M[↑]ʷ[σ'] : A[τ0][lets_sub bs0])
      by (rewrite (exp_sub_sub M), (exp_sub_shift M), (exp_sub_sub A);
          exact (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HM) Heq0)).
    pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ E2M _ _ Hwn) as E3M.
    assert (ED : Δ' ⊢ #0[σ'] ≈ M[↑]ʷ[σ'] : A[↑]ʷ[σ'])
      by (exact (wf_sub_apply_def _ _ _ _ _ Hσ' 0 _ _ ltac:(constructor))).
    pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ ED _ _ Hwn) as ED'.
    pose proof (presup_exp_eq_left E13) as HT0.
    eapply wf_exp_eq_conv_sort; [| exact HT0 | exact HSi | symmetry; exact E13 ].
    etransitivity; [ symmetry; exact EW |].
    etransitivity; [ exact ED' |].
    etransitivity; [ symmetry; eapply wf_exp_eq_conv_sort; [ exact E3M | exact (presup_exp_eq_right E13) | exact HSi | exact E3 ] |].
    symmetry; eapply wf_exp_eq_conv_sort; [ exact E1M | exact (presup_exp_eq_right E13) | exact HSi | exact E13 ]. }
  assert (HΓ1 : ⊢ Δ0 ▸ A' ≔ W) by (eapply wf_ctx_extend_def; [ exact HA' | apply type_sort_abs_kind; constructor | exact HW ]).
  split; [ exact HΓ1 |].
  assert (Hsh : Δ0 ▸ A' ≔ W ⊢ʷ ↑ : Δ0) by (apply wf_wk_shift; exact HΓ1).
  assert (HAτw : Δ0 ▸ A' ≔ W ⊢ A[τ0][↑]ʷ : abs_kind_sort κ Typeω@(max i n)).
  { pose proof (proj1 wk_preserves_wf _ _ _ _ _ HAτ _ _ Hsh) as H; rewrite abs_kind_sort_wk in H; cbn in H.
    apply wf_exp_kind_sort_max_right with (n := n) in H; rewrite PeanoNat.Nat.max_comm in H; exact H. }
  assert (EAw : Δ0 ▸ A' ≔ W ⊢ A'[↑]ʷ ≈ A[τ0][↑]ʷ : abs_kind_sort κ Typeω@(max i n)).
  { pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ _ _ EA) _ _ Hsh) as H;
      rewrite abs_kind_sort_wk in H; cbn in H; exact H. }
  assert (Hq : Δ0 ▸ A' ≔ W ⊢ˢ q τ0 : Γ ▸ A ≔ M).
  { unfold sb_q; apply wf_sub_extend_gen.
    - eapply wf_sub_sb_eq; [| symmetry; apply sb_wk_compose ].
      eapply wf_sub_compose; [ exact Hτ0 | eapply wf_sub_sb_eq; [ exact (wf_sub_shift _ _ _ _ HΓ1) | symmetry; apply sb_of_wk_shift ] ].
    - eapply wf_ctx_extend_def; [ exact HA | exact HSi | exact HM ].
    - intros A0 Hl; inversion Hl; subst; cbn [sentry_exp].
      rewrite exp_sub_shift_extend, <- exp_wk_sub.
      eapply wf_conv_sort; [ apply wf_vlookup; [ exact HΓ1 | constructor ] | exact HAτw | apply type_sort_abs_kind; constructor | exact EAw ].
    - intros A0 M0 Hl; inversion Hl; subst; cbn [sentry_exp].
      rewrite !exp_sub_shift_extend, <- !exp_wk_sub.
      etransitivity.
      + eapply wf_exp_eq_conv_sort; [ apply wf_exp_eq_var_delta; [ exact HΓ1 | constructor ] | exact HAτw
                                     | apply type_sort_abs_kind; constructor | exact EAw ].
      + pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ WM _ _ Hsh) as H; exact H.
    - intros U0 Hl; inversion Hl. }
  split; [ exact Hq |].
  assert (Hsb : sb_eq (q τ0 ⨟ lets_sub (bs0 ++ b_def A' W :: nil)) ((τ0 ⨟ lets_sub bs0),,W[lets_sub bs0]))
    by (rewrite lets_sub_snoc; cbn [binding_zeta_sub]; rewrite <- sb_compose_assoc, sb_q_extend, sb_extend_compose; reflexivity).
  assert (EW0 : Δ' ⊢ W[lets_sub bs0] ≈ #0[σ'] : A[τ0][lets_sub bs0]).
  { pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ _ _ EW) (wf_sub_eq_refl _ _ _ _ _ HL0)) as H.
    rewrite !exp_wk_lets_sub in H.
    eapply wf_exp_eq_conv_sort; [ exact H | exact (presup_exp_eq_left E2) | apply type_sort_abs_kind; constructor | symmetry; exact E2 ]. }
  assert (WM0 : Δ' ⊢ W[lets_sub bs0] ≈ M[τ0 ⨟ lets_sub bs0] : A[τ0 ⨟ lets_sub bs0]).
  { rewrite <- !exp_sub_sub; exact (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ WM (wf_sub_eq_refl _ _ _ _ _ HL0)). }
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [| symmetry; exact Hsb ]; apply wf_sub_eq_sym.
  constructor.
  - eapply wf_sub_extend_def; [ exact (wf_sub_eq_left _ _ _ _ _ _ Heq0) | exact HA | exact HSi | exact HM | | exact WM0 ].
    exact (presup_exp_eq_left WM0).
  - exact Hσ'.
  - intros x T Hl; inversion Hl; subst.
    + rewrite exp_sub_shift_extend, <- exp_sub_sub; exact EW0.
    + rewrite exp_sub_shift_extend; match goal with H : Γ ∋ # _ : _ |- _ => exact (wf_sub_eq_apply _ _ _ _ _ _ Heq0 _ _ H) end.
  - intros x U Hl; inversion Hl; subst.
    match goal with H : Γ ∋ # _ ≔ₘ _ |- _ => exact (wf_sub_eq_apply_mod _ _ _ _ _ _ Heq0 _ _ H) end.
Qed.

(** The same for a module slot of [Γ], bound by its declared unit [U]:
    [U] reads only positions the chain binds, so [τ0] leaves it as it is;
    its literal is, by δ, what the substitution sends the slot to. *)
Lemma env_lets_step_mod : forall Γ U Δ' bs0 τ0 σ' k,
  gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> gunit_scoped k U -> (forall x, x < k -> τ0 x = se_var x) ->
  ⊢ ctx_lets Δ' bs0 -> ctx_lets Δ' bs0 ⊢ˢ τ0 : Γ ->
  Δ' ⊢ˢ τ0 ⨟ lets_sub bs0 ≈ Wk ⨟ σ' : Γ ->
  Δ' ⊢ˢ σ' : Γ ▹ₘ U ->
  ⊢ ctx_lets Δ' (bs0 ++ b_mod U :: nil) /\
  ctx_lets Δ' (bs0 ++ b_mod U :: nil) ⊢ˢ q τ0 : Γ ▹ₘ U /\
  Δ' ⊢ˢ q τ0 ⨟ lets_sub (bs0 ++ b_mod U :: nil) ≈ σ' : Γ ▹ₘ U.
Proof.
  intros * HU Hsc Hvar HΔ0 Hτ0 Heq0 Hσ'.
  rewrite ctx_lets_snoc; cbn [ctx_lets].
  set (Δ0 := ctx_lets Δ' bs0) in *.
  pose proof (lets_sub_wf bs0 HΔ0) as HL0.
  assert (EUτ : U[τ0]ᵘ = U) by exact (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id))) _ _ _ Hsc Hvar).
  assert (HUτ : gc_deps ⍮ gc_stack ⍮ Δ0 ⊢ᵘ U ≈ U) by (rewrite <- EUτ at 1 2; exact (sub_preserves_unit _ _ _ _ _ _ _ HU Hτ0)).
  assert (HΓ1 : ⊢ Δ0 ▹ₘ U) by (econstructor; exact HUτ).
  split; [ exact HΓ1 |].
  assert (Hq : Δ0 ▹ₘ U ⊢ˢ q τ0 : Γ ▹ₘ U).
  { pose proof (wf_sub_q_mod _ _ _ _ _ _ Hτ0 HU ltac:(rewrite EUτ; exact HUτ)) as H; rewrite EUτ in H; exact H. }
  split; [ exact Hq |].
  assert (EUL : U[lets_sub bs0]ᵘ = U[τ0 ⨟ lets_sub bs0]ᵘ) by (rewrite <- gunit_sub_sub, EUτ; reflexivity).
  assert (Hsb : sb_eq (q τ0 ⨟ lets_sub (bs0 ++ b_mod U :: nil)) ((τ0 ⨟ lets_sub bs0) ,,ₘ me_lit U[τ0 ⨟ lets_sub bs0]ᵘ)).
  { rewrite lets_sub_snoc; cbn [binding_zeta_sub].
    rewrite <- sb_compose_assoc, sb_q_compose_extend_gen, sb_compose_id_right, sb_extend_compose_gen.
    cbn [sentry_sub modexp_sub]; rewrite EUL; reflexivity. }
  assert (HUe : gc_deps ⍮ gc_stack ⍮ Δ' ⊢ᵘ U[τ0 ⨟ lets_sub bs0]ᵘ ≈ U[Wk ⨟ σ']ᵘ) by exact (sub_eq_preserves_unit _ _ _ _ _ HU _ _ _ Heq0).
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [| symmetry; exact Hsb ]; apply wf_sub_eq_sym.
  constructor.
  - apply wf_sub_extend_mod; [ exact (wf_sub_eq_left _ _ _ _ _ _ Heq0) | exact HU |].
    exact (sub_preserves_unit _ _ _ _ _ _ _ HU (wf_sub_eq_left _ _ _ _ _ _ Heq0)).
  - exact Hσ'.
  - intros x T Hl; inversion Hl; subst.
    rewrite exp_sub_shift_extend; match goal with H : Γ ∋ # _ : _ |- _ => exact (wf_sub_eq_apply _ _ _ _ _ _ Heq0 _ _ H) end.
  - intros x U0 Hl; inversion Hl; subst.
    + (** The slot: its literal, against what [σ'] sends it to *)
      cbn [sb_extend sentry_modexp].
      pose proof (wf_sub_apply_mod _ _ _ _ _ Hσ' 0 _ ltac:(constructor)) as Hm.
      rewrite gunit_sub_wk in Hm; rewrite (gunit_sub_sb_eq U (ι wk_shift ⨟ σ') (Wk ⨟ σ')) in Hm
        by (rewrite sb_of_wk_shift; reflexivity).
      destruct Hm as [[-> HUu] | (y & -> & Hy)].
      * apply wf_me_lit; exact HUe.
      * cbn [sentry_modexp]; eapply wf_me_trans; [ apply wf_me_lit; exact HUe |].
        apply wf_me_sym; apply wf_me_delta_slot; [ exact (wf_sub_dom _ _ _ _ _ Hσ') | exact Hy ].
    + match goal with H : Γ ∋ # _ ≔ₘ _ |- _ => exact (wf_sub_eq_apply_mod _ _ _ _ _ _ Heq0 _ _ H) end.
Qed.

(** The same for a definition with a module part: its term part as a
    definition's, its module part as a slot's. *)
Lemma env_lets_step_dm : forall Γ A M E (i : nat) Δ' bs0 τ0 σ' A' W (n : nat) k,
  Γ ⊢ A : Typeω@i -> Γ ⊢ M : A ->
  gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
  gunit_scoped k (gu_mk nil (md_alias E)) -> (forall x, x < k -> τ0 x = se_var x) ->
  ⊢ ctx_lets Δ' bs0 -> ctx_lets Δ' bs0 ⊢ˢ τ0 : Γ ->
  Δ' ⊢ˢ τ0 ⨟ lets_sub bs0 ≈ Wk ⨟ σ' : Γ ->
  Δ' ⊢ˢ σ' : Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ->
  ctx_lets Δ' bs0 ⊢ A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ ≈ A' : Typeω@n ->
  ctx_lets Δ' bs0 ⊢ #0[σ'][wk_shiftn (List.length bs0)]ʷ ≈ W : A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ ->
  ⊢ ctx_lets Δ' (bs0 ++ b_def_mod A' W (gu_mk nil (md_alias E)) :: nil) /\
  ctx_lets Δ' (bs0 ++ b_def_mod A' W (gu_mk nil (md_alias E)) :: nil) ⊢ˢ q τ0 : Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) /\
  Δ' ⊢ˢ q τ0 ⨟ lets_sub (bs0 ++ b_def_mod A' W (gu_mk nil (md_alias E)) :: nil) ≈ σ' : Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E).
Proof.
  intros * HA HM HU Hsc Hvar HΔ0 Hτ0 Heq0 Hσ' EA' EW.
  set (U := gu_mk nil (md_alias E)) in *.
  rewrite ctx_lets_snoc; cbn [ctx_lets].
  set (Δ0 := ctx_lets Δ' bs0) in *.
  pose proof (ctx_lets_wk_shiftn bs0 HΔ0) as Hwn.
  pose proof (lets_sub_wf bs0 HΔ0) as HL0.
  assert (HSi : type_sort Typeω@i) by constructor.
  assert (EUτ : U[τ0]ᵘ = U) by exact (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id))) _ _ _ Hsc Hvar).
  assert (HUτ : gc_deps ⍮ gc_stack ⍮ Δ0 ⊢ᵘ U ≈ U) by (rewrite <- EUτ at 1 2; exact (sub_preserves_unit _ _ _ _ _ _ _ HU Hτ0)).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hτ0) as HAτ; cbn in HAτ.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM Hτ0) as HMτ.
  pose proof (ctx_lets_unfold_definitions bs0 HAτ) as E1.
  assert (E2 : Δ' ⊢ A[τ0][lets_sub bs0] ≈ A[↑]ʷ[σ'] : Typeω@i).
  { rewrite exp_sub_sub, exp_sub_shift; exact (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HA) Heq0). }
  pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ E2 _ _ Hwn) as E3; cbn in E3.
  assert (E13 : Δ0 ⊢ A[τ0] ≈ A[↑]ʷ[σ'][wk_shiftn (List.length bs0)]ʷ : Typeω@i) by (etransitivity; [ exact E1 | exact E3 ]).
  assert (EA : Δ0 ⊢ A[τ0] ≈ A' : Typeω@(max i n)).
  { etransitivity; [ apply (wf_exp_eq_kind_sort_max_left _ ak_relevant); exact E13
                   | apply (wf_exp_eq_kind_sort_max_right _ ak_relevant); exact EA' ]. }
  pose proof (presup_exp_eq_right EA') as HA'.
  assert (HW : Δ0 ⊢ W : A') by (eapply wf_conv_sort; [ exact (presup_exp_eq_right EW) | exact HA' | constructor | exact EA' ]).
  assert (WM : Δ0 ⊢ W ≈ M[τ0] : A[τ0]).
  { pose proof (ctx_lets_unfold_definitions bs0 HMτ) as E1M.
    assert (E2M : Δ' ⊢ M[τ0][lets_sub bs0] ≈ M[↑]ʷ[σ'] : A[τ0][lets_sub bs0])
      by (rewrite (exp_sub_sub M), (exp_sub_shift M), (exp_sub_sub A);
          exact (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HM) Heq0)).
    pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ E2M _ _ Hwn) as E3M.
    assert (ED : Δ' ⊢ #0[σ'] ≈ M[↑]ʷ[σ'] : A[↑]ʷ[σ'])
      by (exact (wf_sub_apply_def _ _ _ _ _ Hσ' 0 _ _ ltac:(constructor))).
    pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ ED _ _ Hwn) as ED'.
    pose proof (presup_exp_eq_left E13) as HT0.
    eapply wf_exp_eq_conv_sort; [| exact HT0 | exact HSi | symmetry; exact E13 ].
    etransitivity; [ symmetry; exact EW |].
    etransitivity; [ exact ED' |].
    etransitivity; [ symmetry; eapply wf_exp_eq_conv_sort; [ exact E3M | exact (presup_exp_eq_right E13) | exact HSi | exact E3 ] |].
    symmetry; eapply wf_exp_eq_conv_sort; [ exact E1M | exact (presup_exp_eq_right E13) | exact HSi | exact E13 ]. }
  assert (HΓ1 : ⊢ Δ0 ▸ₘ A' ≔ W ‖ U) by (eapply wf_ctx_extend_dm; [ exact HA' | exact HW | exact HUτ ]).
  split; [ exact HΓ1 |].
  assert (Hsh : Δ0 ▸ₘ A' ≔ W ‖ U ⊢ʷ ↑ : Δ0) by (apply wf_wk_shift; exact HΓ1).
  assert (HAτw : Δ0 ▸ₘ A' ≔ W ‖ U ⊢ A[τ0][↑]ʷ : Typeω@(max i n)).
  { pose proof (proj1 wk_preserves_wf _ _ _ _ _ HAτ _ _ Hsh) as H; cbn in H.
    apply (wf_exp_kind_sort_max_right _ ak_relevant) with (n := n) in H; rewrite PeanoNat.Nat.max_comm in H; exact H. }
  assert (EAw : Δ0 ▸ₘ A' ≔ W ‖ U ⊢ A'[↑]ʷ ≈ A[τ0][↑]ʷ : Typeω@(max i n)).
  { pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ _ _ EA) _ _ Hsh) as H; cbn in H; exact H. }
  assert (Hq : Δ0 ▸ₘ A' ≔ W ‖ U ⊢ˢ q τ0 : Γ ▸ₘ A ≔ M ‖ U).
  { unfold sb_q; apply wf_sub_extend_gen.
    - eapply wf_sub_sb_eq; [| symmetry; apply sb_wk_compose ].
      eapply wf_sub_compose; [ exact Hτ0 | eapply wf_sub_sb_eq; [ exact (wf_sub_shift _ _ _ _ HΓ1) | symmetry; apply sb_of_wk_shift ] ].
    - eapply wf_ctx_extend_dm; [ exact HA | exact HM | exact HU ].
    - intros A0 Hl; inversion Hl; subst; cbn [sentry_exp].
      rewrite exp_sub_shift_extend, <- exp_wk_sub.
      eapply wf_conv_sort; [ apply wf_vlookup; [ exact HΓ1 | constructor ] | exact HAτw | constructor | exact EAw ].
    - intros A0 M0 Hl; inversion Hl; subst; cbn [sentry_exp].
      rewrite !exp_sub_shift_extend, <- !exp_wk_sub.
      etransitivity.
      + eapply wf_exp_eq_conv_sort; [ apply wf_exp_eq_var_delta; [ exact HΓ1 | constructor ] | exact HAτw | constructor | exact EAw ].
      + exact (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ WM _ _ Hsh).
    - intros U0 Hl; inversion Hl; subst; right; exists 0; split; [ reflexivity |].
      rewrite gunit_sub_shift_extend, <- gunit_wk_sub, EUτ; constructor. }
  split; [ exact Hq |].
  assert (EUL : U[lets_sub bs0]ᵘ = U[τ0 ⨟ lets_sub bs0]ᵘ) by (rewrite <- gunit_sub_sub, EUτ; reflexivity).
  assert (Hsb : sb_eq (q τ0 ⨟ lets_sub (bs0 ++ b_def_mod A' W U :: nil))
                  ((τ0 ⨟ lets_sub bs0) ,,ᵈ W[lets_sub bs0] ‖ me_lit U[τ0 ⨟ lets_sub bs0]ᵘ)).
  { rewrite lets_sub_snoc; cbn [binding_zeta_sub].
    rewrite <- sb_compose_assoc, sb_q_compose_extend_gen, sb_compose_id_right, sb_extend_compose_gen.
    cbn [sentry_sub modexp_sub]; rewrite EUL; reflexivity. }
  assert (EW0 : Δ' ⊢ W[lets_sub bs0] ≈ #0[σ'] : A[τ0][lets_sub bs0]).
  { pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ _ _ EW) (wf_sub_eq_refl _ _ _ _ _ HL0)) as H.
    rewrite !exp_wk_lets_sub in H.
    eapply wf_exp_eq_conv_sort; [ exact H | exact (presup_exp_eq_left E2) | constructor | symmetry; exact E2 ]. }
  assert (WM0 : Δ' ⊢ W[lets_sub bs0] ≈ M[τ0 ⨟ lets_sub bs0] : A[τ0 ⨟ lets_sub bs0]).
  { rewrite <- !exp_sub_sub; exact (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ WM (wf_sub_eq_refl _ _ _ _ _ HL0)). }
  assert (HUe : gc_deps ⍮ gc_stack ⍮ Δ' ⊢ᵘ U[τ0 ⨟ lets_sub bs0]ᵘ ≈ U[Wk ⨟ σ']ᵘ) by exact (sub_eq_preserves_unit _ _ _ _ _ HU _ _ _ Heq0).
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [| symmetry; exact Hsb ]; apply wf_sub_eq_sym.
  constructor.
  - eapply wf_sub_extend_dm; [ exact (wf_sub_eq_left _ _ _ _ _ _ Heq0) | exact HA | exact HM | exact HU
                             | exact (presup_exp_eq_left WM0) | exact WM0 |].
    exact (sub_preserves_unit _ _ _ _ _ _ _ HU (wf_sub_eq_left _ _ _ _ _ _ Heq0)).
  - exact Hσ'.
  - intros x T Hl; inversion Hl; subst.
    + rewrite exp_sub_shift_extend, <- exp_sub_sub; exact EW0.
    + rewrite exp_sub_shift_extend; match goal with H : Γ ∋ # _ : _ |- _ => exact (wf_sub_eq_apply _ _ _ _ _ _ Heq0 _ _ H) end.
  - intros x U0 Hl; inversion Hl; subst.
    + cbn [sb_extend sentry_modexp].
      pose proof (wf_sub_apply_mod _ _ _ _ _ Hσ' 0 _ ltac:(constructor)) as Hm.
      rewrite gunit_sub_wk in Hm; rewrite (gunit_sub_sb_eq U (ι wk_shift ⨟ σ') (Wk ⨟ σ')) in Hm
        by (rewrite sb_of_wk_shift; reflexivity).
      destruct Hm as [[Hm HUu] | (y & Hy0 & Hy)].
      * rewrite Hm; apply wf_me_lit; exact HUe.
      * rewrite Hy0; cbn [sentry_modexp]; eapply wf_me_trans; [ apply wf_me_lit; exact HUe |].
        apply wf_me_sym; apply wf_me_delta_slot; [ exact (wf_sub_dom _ _ _ _ _ Hσ') | exact Hy ].
    + match goal with H : Γ ∋ # _ ≔ₘ _ |- _ => exact (wf_sub_eq_apply_mod _ _ _ _ _ _ Heq0 _ _ H) end.
Qed.

(** No definition: the substitution itself, weakened. *)
Lemma env_lets_base : forall Γ Δ σ Δ' φ, Δ ⊢ˢ σ : Γ -> Δ' ⊢ᵏ φ : Δ ->
    exists τ, ⊢ ctx_lets Δ' nil /\ ctx_lets Δ' nil ⊢ˢ τ : Γ /\ (forall x, x < 0 -> τ x = se_var x) /\
      Δ' ⊢ˢ τ ⨟ lets_sub nil ≈ sb_wk σ φ : Γ.
Proof.
  intros * Hσ Hφ; cbn [ctx_lets lets_sub].
  assert (Ht : Δ' ⊢ˢ sb_wk σ φ : Γ)
    by (eapply wf_sub_sb_eq; [ exact (wf_sub_compose _ _ _ _ _ _ _ Hσ (kripke_escape _ _ _ Hφ)) | symmetry; apply sb_wk_compose ]).
  exists (sb_wk σ φ); split; [ eapply kripke_dom; eassumption | split; [ exact Ht | split; [ intros; lia |] ] ].
  apply wf_sub_eq_of_sb_eq; [ eapply wf_sub_sb_eq; [ exact Ht | symmetry; apply sb_compose_id_right ] | apply sb_compose_id_right ].
Qed.

(** The definitions the readback of the first [k] positions of an
    environment glued to [σ] produces, at a Kripke weakening [φ], form a
    well-formed chain into which the variables of [Γ] map as themselves
    below [k], and they ζ-reduce to [σ] weakened by [φ].  The positions
    below [k] are closed under the stored units ([proof_scope]). *)
Lemma glu_env_lets : forall Γ Sb, EG Γ ∈ glu_ctx_env ↘ Sb ->
  forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb ->
  forall k Δ' φ bs, k <= List.length Γ ->
    (forall j, j < k -> S j + entry_unit_bound (env_entry ρ j) <= k) ->
    Δ' ⊢ᵏ φ : Δ ->
    Rlets ρ at k in gc_deps ⍮ gc_stack ⍮ List.length Δ' ↘ bs ->
    exists τ, ⊢ ctx_lets Δ' bs /\ ctx_lets Δ' bs ⊢ˢ τ : Γ /\
      (forall x, x < k -> τ x = se_var x) /\ Δ' ⊢ˢ τ ⨟ lets_sub bs ≈ sb_wk σ φ : Γ.
Proof.
  intros Γ Sb HΓ; induction HΓ; intros Δ σ ρ Hσ k Δ' φ bs Hk Hcl Hφ Hbs;
    apply_predicate_equivalence; cbn in Hσ.
  (** The empty context: no position *)
  1: { destruct k; [| cbn in Hk; lia ]; inversion Hbs; subst; eapply env_lets_base; eassumption. }
  all: destruct Hσ.
  all: destruct k as [| k]; [ inversion Hbs; subst; eapply env_lets_base; eassumption |].
  all: destruct (read_lets_snoc _ _ _ _ Hbs) as (bs0 & b0 & -> & Hbs0 & Hb0).
  all: assert (Hcl' : forall j, j < k -> S j + entry_unit_bound (env_entry ρ↯ j) <= k)
         by (intros j Hj; rewrite env_entry_drop; specialize (Hcl (S j) ltac:(lia)); lia).
  all: destruct (IHHΓ _ _ _ ltac:(eassumption) k Δ' φ bs0 ltac:(cbn in Hk; lia) Hcl' Hφ Hbs0) as (τ0 & HΔ0 & Hτ0 & Hvar0 & Heq0).
  all: eapply wf_sub_eq_respects_sb_eq in Heq0; [| apply sb_wk_shift_pre ].
  all: pose proof (read_lets_length _ _ _ _ Hbs0) as Hlb.
  all: assert (Hlen : List.length Δ' + k = List.length (ctx_lets Δ' bs0)) by (rewrite length_ctx_lets; lia).
  all: rewrite Hlen in Hb0.
  all: pose proof (kripke_compose _ _ _ _ _ (ctx_lets_kripke _ _ HΔ0) Hφ) as Hφ0.
  all: match goal with |- context [sb_wk ?s ?f] =>
         match goal with Hσt : _ ⊢ˢ s : _ |- _ =>
           pose proof Hσt as Hσs;
           assert (Hσ' : _ ⊢ˢ sb_wk s f : _ ) by
             (eapply wf_sub_sb_eq; [ exact (wf_sub_compose _ _ _ _ _ _ _ Hσt (kripke_escape _ _ _ Hφ)) | symmetry; apply sb_wk_compose ])
         end;
         assert (Hwkn : forall X n0, X[s][f ⊙ wk_shiftn n0]ʷ = X[sb_wk s f][wk_shiftn n0]ʷ)
           by (intros X n0; rewrite <- exp_wk_wk, exp_wk_sub; reflexivity)
       end.
  - (** An assumption *)
    match goal with H : Γ ⊢ A : _ |- _ => rename H into HA end.
    match goal with Hs : exists t, _ /\ glu_stored_type _ _ _ _ t |- _ => destruct Hs as (t & Het & [j b Pb Elb Hb Hgb HEb]) end.
    rewrite Het in Hb0; inversion Hb0; subst.
    match goal with Ht : eval_entry_type _ _ t ?b1 |- _ => pose proof (functional_eval_entry_type _ _ _ Ht Hb) as -> end.
    assert (HT : Δ ⊢ A[↑]ʷ[σ] : abs_kind_sort κ Typeω@i)
      by (rewrite exp_sub_shift; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA (wf_sub_compose _ _ _ _ _ _ _ (wf_sub_shift _ _ _ _ (wf_sub_cod _ _ _ _ _ Hσs)) Hσs)) as HT0;
          rewrite abs_kind_sort_sub in HT0; exact HT0).
    match goal with Hr : read_typ _ _ _ b ?A1, Hw : read_nf _ _ _ (⇓ b _) ?W1 |- _ =>
      destruct (glu_stored_readback _ _ _ _ _ _ _ _ _ _ HT Hgb HEb _ _ A1 W1 Hφ0 Hr Hw) as (n & EA' & EW') end.
    repeat rewrite Hwkn in EA'; repeat rewrite Hwkn in EW'.
    destruct (env_lets_step_ass _ _ _ _ _ _ _ _ _ _ _ HA HΔ0 Hτ0 Heq0 Hσ' EA' EW') as (HΔ1 & Hq & Heq).
    exists (q τ0); split; [ exact HΔ1 | split; [ exact Hq | split; [ apply sb_q_fix; exact Hvar0 | exact Heq ] ] ].
  - (** A definition *)
    match goal with H : Γ ⊢ A : _ |- _ => rename H into HA end.
    match goal with Hs : exists t, _ /\ glu_stored_type _ _ _ _ t |- _ => destruct Hs as (t & Het & [j b Pb Elb Hb Hgb HEb]) end.
    rewrite Het in Hb0; inversion Hb0; subst.
    match goal with Ht : eval_entry_type _ _ t ?b1 |- _ => pose proof (functional_eval_entry_type _ _ _ Ht Hb) as -> end.
    assert (HT : Δ ⊢ A[↑]ʷ[σ] : abs_kind_sort κ Typeω@i)
      by (rewrite exp_sub_shift; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA (wf_sub_compose _ _ _ _ _ _ _ (wf_sub_shift _ _ _ _ (wf_sub_cod _ _ _ _ _ Hσs)) Hσs)) as HT0;
          rewrite abs_kind_sort_sub in HT0; exact HT0).
    match goal with Hr : read_typ _ _ _ b ?A1, Hw : read_nf _ _ _ (⇓ b _) ?W1 |- _ =>
      destruct (glu_stored_readback _ _ _ _ _ _ _ _ _ _ HT Hgb HEb _ _ A1 W1 Hφ0 Hr Hw) as (n & EA' & EW') end.
    repeat rewrite Hwkn in EA'; repeat rewrite Hwkn in EW'.
    destruct (env_lets_step_def _ _ _ _ _ _ _ _ _ _ _ _ HA ltac:(eassumption) HΔ0 Hτ0 Heq0 Hσ' EA' EW') as (HΔ1 & Hq & Heq).
    exists (q τ0); split; [ exact HΔ1 | split; [ exact Hq | split; [ apply sb_q_fix; exact Hvar0 | exact Heq ] ] ].
  - (** A module slot, bound by its unit *)
    specialize (Hcl 0 ltac:(lia)).
    match goal with He : env_entry ρ 0 = de_mod _ U |- _ => rewrite He in Hb0, Hcl end.
    inversion Hb0; subst.
    cbn [entry_unit_bound] in Hcl.
    match goal with HU : _ ⍮ _ ⍮ Γ ⊢ᵘ U ≈ U |- _ => rename HU into HUw end.
    assert (Hsc : gunit_scoped (List.length bs0) U).
    { destruct wf_scoped as (_ & _ & _ & _ & _ & _ & HUs & _).
      eapply gunit_scoped_shrink; [ exact (proj1 (proj2 (HUs _ _ _ _ _ HUw))) | lia ]. }
    destruct (env_lets_step_mod _ _ _ _ _ _ _ HUw Hsc Hvar0 HΔ0 Hτ0 Heq0 Hσ') as (HΔ1 & Hq & Heq).
    exists (q τ0); split; [ exact HΔ1 | split; [ exact Hq | split; [ apply sb_q_fix; exact Hvar0 | exact Heq ] ] ].
  - (** A definition with a module part *)
    match goal with H : Γ ⊢ A : Typeω@i |- _ => rename H into HA end.
    match goal with H : Γ ⊢ M : A |- _ => rename H into HM end.
    match goal with Hs : exists t, _ /\ glu_stored_type _ _ _ _ t |- _ => destruct Hs as (t & Het & [j b Pb Elb Hb Hgb HEb]) end.
    specialize (Hcl 0 ltac:(lia)).
    rewrite Het in Hb0, Hcl; inversion Hb0; subst.
    match goal with Ht : eval_entry_type _ _ t ?b1 |- _ => pose proof (functional_eval_entry_type _ _ _ Ht Hb) as -> end.
    cbn [entry_unit_bound] in Hcl.
    match goal with Hwf : ⊢ Γ ▸ₘ A ≔ M ‖ U |- _ => inversion Hwf; subst end.
    match goal with HUw : _ ⍮ _ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias ?E0) ≈ _ |- _ =>
      assert (Hsc : gunit_scoped (List.length bs0) (gu_mk nil (md_alias E0)))
        by (destruct wf_scoped as (_ & _ & _ & _ & _ & _ & HUs & _);
            eapply gunit_scoped_shrink; [ exact (proj1 (proj2 (HUs _ _ _ _ _ HUw))) | lia ]) end.
    assert (HT : Δ ⊢ A[↑]ʷ[σ] : abs_kind_sort ak_relevant Typeω@i)
      by (rewrite exp_sub_shift; exact (sub_preserves_exp _ _ _ _ _ _ _ HA (wf_sub_compose _ _ _ _ _ _ _ (wf_sub_shift _ _ _ _ (wf_sub_cod _ _ _ _ _ Hσs)) Hσs))).
    match goal with Hr : read_typ _ _ _ b ?A1, Hw : read_nf _ _ _ (⇓ b _) ?W1 |- _ =>
      destruct (glu_stored_readback _ _ _ _ _ _ _ _ _ _ HT Hgb HEb _ _ A1 W1 Hφ0 Hr Hw) as (n & EA' & EW') end.
    repeat rewrite Hwkn in EA'; repeat rewrite Hwkn in EW'.
    destruct (env_lets_step_dm _ _ _ _ _ _ _ _ _ _ _ _ _ HA HM ltac:(eassumption) Hsc Hvar0 HΔ0 Hτ0 Heq0 Hσ' EA' EW')
      as (HΔ1 & Hq & Heq).
    exists (q τ0); split; [ exact HΔ1 | split; [ exact Hq | split; [ apply sb_q_fix; exact Hvar0 | exact Heq ] ] ].
Qed.

(** *** The Value of a Term at the Kind of Its Type

    A glued term's value is the proof kept, [⋆ᵈ⟨M, ρ⟩], at a proposition
    ([glu_term_value]).  An element glued at an evaluated value gives one
    glued at the term's value: at a proposition any proof that reads back is
    an element, and a proof kept over an environment of the context reads
    back ([per_ctx_env_kept_proof_readable]). *)

(** A type value of the propositional kind is a proposition. *)
Lemma per_univ_elem_per_prop_of_kind : forall {i R a a'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    domain_kind a = ak_propositional ->
    Dom a ≈ a' ∈ per_prop.
Proof.
  intros * H Hk.
  basic_invert_per_univ_elem H; try assumption.
  all: cbn in Hk; try discriminate Hk.
  all: match goal with H : evaluated_kind _ |- _ => inversion H; subst; discriminate end.
Qed.

(** The scope of a kept proof is closed under the stored units of the
    entries inside it: [proof_scope_from] walks the positions in order,
    widening the scope by each unit it meets. *)
Lemma proof_scope_from_closed : forall ρ0 ρ j n, ρ = List.skipn j ρ0 ->
    (forall x, x < j -> x < n /\ S x + entry_unit_bound (env_entry ρ0 x) <= n) ->
    n <= proof_scope_from ρ j n /\
    forall x, x < proof_scope_from ρ j n -> S x + entry_unit_bound (env_entry ρ0 x) <= proof_scope_from ρ j n.
Proof.
  intros ρ0 ρ; revert ρ0; induction ρ as [| e ρ IH]; intros ρ0 j n Hρ Hv; cbn [proof_scope_from].
  - split; [ lia |]; intros x Hx.
    destruct (PeanoNat.Nat.lt_ge_cases x j) as [Hxj | Hxj]; [ exact (proj2 (Hv _ Hxj)) |].
    pose proof (f_equal (@List.length _) Hρ) as HL; rewrite List.length_skipn in HL; cbn in HL.
    rewrite env_entry_ge by lia; cbn; lia.
  - destruct (PeanoNat.Nat.ltb_spec j n) as [Hjn | Hjn].
    + assert (He : env_entry ρ0 j = e)
        by (rewrite env_entry_nth, <- (PeanoNat.Nat.add_0_r j), <- List.nth_skipn, <- Hρ; reflexivity).
      destruct (IH ρ0 (S j) (Nat.max n (S j + entry_unit_bound e))) as [Hge Hcl].
      * change (S j) with (1 + j); rewrite <- List.skipn_skipn, <- Hρ; reflexivity.
      * intros x Hx; destruct (PeanoNat.Nat.eq_dec x j) as [-> | Hne]; [ rewrite He; lia |].
        destruct (Hv x ltac:(lia)); lia.
      * split; [ lia | exact Hcl ].
    + split; [ lia |]; intros x Hx; destruct (Hv x ltac:(lia)); lia.
Qed.

(** A kept proof over an environment glued to [σ] reads back as the proof
    at [σ], at every Kripke weakening: the definitions of its scope form a
    chain into which the variables of the proof's context map as
    themselves ([glu_env_lets]), and the chain over the proof is the proof
    at the substitution the chain ζ-reduces to ([lets_exp_of_sub]). *)
Lemma glu_kept_proof_read : forall Γ Sb, EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb ->
    forall M P, Γ ⊢ M : P -> Γ ⊢ P : Propₘ ->
    forall Δ' φ R, Δ' ⊢ᵏ φ : Δ -> Rprf ⋆ᵈ⟨M, ρ⟩ in gc_deps ⍮ gc_stack ⍮ List.length Δ' ↘ R ->
      Δ' ⊢ R ≈ M[σ][φ]ʷ : P[σ][φ]ʷ.
Proof.
  intros * HΓ * Hσ * HM HP * Hφ HR.
  inversion HR; subst.
  match goal with Hb : read_lets _ _ _ ρ _ ?bs |- _ => rename Hb into Hbs end.
  destruct (glu_ctx_env_per_ctx_env HΓ) as [RΓ HRΓ].
  pose proof (glu_ctx_env_per_env HΓ HRΓ Hσ) as Hρ.
  pose proof (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HM))) as HsM.
  pose proof (exp_scoped_free_bound _ _ HsM) as HfM.
  destruct (per_ctx_env_proof_scope_from _ _ _ HRΓ _ _ Hρ 0 (exp_free_bound M) ltac:(cbn; lia)) as [Hle _].
  destruct (proof_scope_from_closed ρ ρ 0 (exp_free_bound M) eq_refl ltac:(intros; lia)) as [Hge Hcl].
  unfold proof_scope in Hbs.
  destruct (glu_env_lets _ _ HΓ _ _ _ Hσ (proof_scope_from ρ 0 (exp_free_bound M)) _ _ _ ltac:(cbn in Hle; lia) Hcl Hφ Hbs)
    as (τ & HΔ1 & Hτ & Hvar & Heq).
  pose proof (read_lets_length _ _ _ _ Hbs) as Hlb.
  assert (HsM' : exp_scoped (List.length bs) M) by (eapply exp_scoped_shrink; [ exact HsM | lia ]).
  destruct (lets_exp_of_sub _ HM HP HsM' Hτ ltac:(rewrite Hlb; exact Hvar) Heq) as [_ E].
  rewrite !exp_wk_sub; exact E.
Qed.

(** A type of a proof of [Γ] whose instance is a proposition is one: its
    sort is of the kind of its instance's ([exp_eq_same_kind]). *)
Lemma typ_prop_of_sub : forall Γ M B Δ σ, Γ ⊢ M : B -> Δ ⊢ˢ σ : Γ -> Δ ⊢ B[σ] : Propₘ -> Γ ⊢ B : Propₘ.
Proof.
  intros * HM Hσ HB.
  pose proof (presup_exp_typ_cases HM) as Hc; inversion Hc as [? S HS HBS | Hx1 Hx2]; subst.
  - pose proof (sub_preserves_exp _ _ _ _ _ _ _ HBS Hσ) as H.
    inversion HS; subst; [ | exact HBS | ]; exfalso; cbn in H.
    + pose proof (exp_eq_same_kind _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl H) (sort_kind_universe _) HB sort_kind_prop) as E; discriminate E.
    + pose proof (exp_eq_same_kind _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl H) sort_kind_level HB sort_kind_prop) as E; discriminate E.
  - exfalso; cbn in HB; exact (level_sort_untyped HB).
Qed.

(** An element glued at the value of a term at a glued environment is
    glued at the term's value at the kind of its type: at a proposition,
    the proof kept, which reads back as the proof at the substitution
    ([glu_kept_proof_read]). *)
Lemma glu_term_value_intro : forall {i a P El Γ Sb M B Δ σ ρ m},
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ M : B ->
    (evaluated_kind (domain_kind a) -> ⟦ M ⟧ ρ ↘ m) ->
    Δ ⊢ M[σ] : B[σ] ® m ∈ El ->
    exists m', glu_term_value M ρ (domain_kind a) m' /\ Δ ⊢ M[σ] : B[σ] ® m' ∈ El.
Proof.
  intros * Hglu HΓ Hσ HM Hm HN.
  destruct (domain_kind a) eqn:Hk.
  - exists m; split; [ apply Hm; constructor | exact HN ].
  - (** At a proposition: the proof kept *)
    exists ⋆ᵈ⟨M, ρ⟩; split; [ reflexivity |].
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R' HR'].
    pose proof (per_univ_elem_per_prop_of_kind HR' Hk) as Hp.
    destruct (glu_univ_elem_prop_inv _ _ _ _ Hp Hglu) as [_ HEl].
    apply HEl in HN; apply HEl.
    destruct HN as [HAt HNt _ _].
    pose proof (glu_ctx_env_sub_escape HΓ _ _ _ Hσ) as Hσt.
    pose proof (typ_prop_of_sub _ _ _ _ _ HM Hσt (proj1 HAt)) as HBp.
    destruct (glu_ctx_env_per_ctx_env HΓ) as [RΓ HRΓ].
    pose proof (glu_ctx_env_per_env HΓ HRΓ Hσ) as Hρ.
    pose proof (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HM))) as HsM.
    destruct (per_ctx_env_kept_proof_readable _ _ _ M HRΓ (exp_scoped_free_bound _ _ HsM) _ _ Hρ) as [Hr _].
    econstructor; [ exact HAt | exact HNt | apply per_proof_refl; exact Hr |].
    intros Δ' φ R Hφ HR; symmetry; exact (glu_kept_proof_read _ _ HΓ _ _ _ Hσ _ _ HM HBp _ _ _ Hφ HR).
  - exists m; split; [ apply Hm; constructor | exact HN ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_to_wf_exp : mctt.
