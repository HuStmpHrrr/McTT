From Stdlib Require Import Lia List PeanoNat Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import ContextCases FundamentalTheorem UniverseCases UnitCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Soundness.LogicalRelation Require Export Realizability.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Add Parametric Morphism i a Γ A M : (glu_elem_bot i a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Add Parametric Morphism i a Γ A M R (H : per_univ_elem i R a a) : (glu_elem_top i a Γ A M)
    with signature R ==> iff as glu_elem_top_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    pose proof (per_elem_then_per_top H Hmm') as Hmm'';
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm'' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Lemma glu_univ_elem_typ_unique_upto_exp_eq : forall {i j : uidx} {a P P' El El' Γ A A'},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Typeω@(max (ulvl i) (ulvl j)).
Proof.
  intros.
  assert (Γ ⊢ A ® glu_typ_top i a) as [] by mauto 3.
  assert (Γ ⊢ A' ® glu_typ_top j a) as [] by mauto 3.
  match_by_head per_top_typ ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  (** Both are types of the large universe of their index's tier, and both
      are equal to the common readback there. *)
  assert (Γ ⊢ A : Typeω@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_max_left.
  assert (Γ ⊢ A' : Typeω@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_max_right.
  assert (Γ ⊢ A ≈ V : Typeω@(ulvl i)) as HAV by (rewrite <- (exp_wk_id A); mauto 4).
  assert (Γ ⊢ A' ≈ V : Typeω@(ulvl j)) as HA'V by (rewrite <- (exp_wk_id A'); mauto 4).
  assert (Γ ⊢ A ≈ V : Typeω@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_eq_max_left.
  assert (Γ ⊢ A' ≈ V : Typeω@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_eq_max_right; mautosolve 4.
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq : mctt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq_ge : forall {i j : uidx} {a P P' El El' Γ A A'},
    uidx_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Typeω@(ulvl j).
Proof.
  intros.
  replace (ulvl j) with (max (ulvl i) (ulvl j)) by (pose proof (uidx_le_ulvl_le _ _ ltac:(eassumption)); lia); mautosolve 4.
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq_ge : mctt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq' : forall {i : uidx} {a P El Γ A A'},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P ->
    Γ ⊢ A ≈ A' : Typeω@(ulvl i).
Proof.
  intros * Hglu HA HA'.
  assert (Γ ⊢ A ® glu_typ_top i a) as [] by mauto 3.
  assert (Γ ⊢ A' ® glu_typ_top i a) as [] by mauto 3.
  match_by_head per_top_typ ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  assert (Γ ⊢ A ≈ V : Typeω@(ulvl i)) by (rewrite <- (exp_wk_id A); mauto 4).
  assert (Γ ⊢ A' ≈ V : Typeω@(ulvl i)) by (rewrite <- (exp_wk_id A'); mauto 4).
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq' : mctt.

Lemma glu_univ_elem_per_univ_elem_typ_escape : forall {i : uidx} {a a' elem_rel P P' El El' Γ A A'},
    DF a ≈ a' ∈ per_univ_elem i ↘ elem_rel ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Typeω@(ulvl i).
Proof.
  simpl in *.
  intros * Hper Hglu Hglu' HA HA'.
  assert (DG a ∈ glu_univ_elem i ↘ P' ↘ El') by (setoid_rewrite Hper; eassumption).
  handle_functional_glu_univ_elem; mautosolve 4.
Qed.

Hint Resolve glu_univ_elem_per_univ_elem_typ_escape : mctt.

Lemma glu_univ_elem_per_univ_typ_escape : forall {i : uidx} {a a' P P' El El' Γ A A'},
    Dom a ≈ a' ∈ per_univ i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Typeω@(ulvl i).
Proof.
  intros * [] **.
  mauto 4.
Qed.

Hint Resolve glu_univ_elem_per_univ_typ_escape : mctt.

Lemma glu_univ_elem_per_univ_typ_iff : forall {i : uidx} {a a' P P' El El'},
    Dom a ≈ a' ∈ per_univ i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  intros * Hper **.
  eapply functional_glu_univ_elem;
    [eassumption | rewrite Hper];
    eassumption.
Qed.

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
Corollary glu_univ_elem_cumu_ge_uidx : forall {i j : uidx} {a P El},
    uidx_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem j ↘ P' ↘ El'.
Proof.
  intros.
  assert (Dom a ≈ a ∈ per_univ i) as [R] by mauto 2.
  assert (DF a ≈ a ∈ per_univ_elem j ↘ R) by (eapply per_univ_elem_cumu_uidx; eassumption).
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

Lemma ind_comps_lower_n : forall p D ups NP NEl AP AEl DP DEl (NEl' : nat -> list domain -> glu_exp_pred) Γ Us,
    ind_glu_comps p D ups NP NEl AP AEl DP DEl Γ Us ->
    (forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
       forall Γ A M m, NP k vs Γ A -> NEl' k vs Γ A M m -> NEl k vs Γ A M m) ->
    forall n Ns ns, n <= ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) n ns ns ->
      (forall j N T' v, j < n -> List.nth_error Ns j = Some N ->
         List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) j = Some T' ->
         List.nth_error ns j = Some v -> Γ ⊢ N : T' ® v ∈ NEl' j (List.firstn j ns)) ->
      (forall j N T' v, j < n -> List.nth_error Ns j = Some N ->
         List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) j = Some T' ->
         List.nth_error ns j = Some v -> Γ ⊢ N : T' ® v ∈ NEl j (List.firstn j ns)).
Proof.
  intros * [HCN _ _] HNl n Ns ns Hn Hp H'.
  assert (Hl : List.length ns = n) by (destruct Hp; assumption).
  enough (forall m, m <= n -> forall j N T' v, j < m -> List.nth_error Ns j = Some N ->
            List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) j = Some T' ->
            List.nth_error ns j = Some v -> Γ ⊢ N : T' ® v ∈ NEl j (List.firstn j ns)) as Hm
    by (intros; eapply (Hm n); eauto).
  induction m as [| m IH]; intros Hm j N T' v Hj HN HT Hv; [ lia |].
  destruct (Nat.eq_dec j m) as [-> | Hne]; [| eapply IH; eauto; lia ].
  assert (Hpm : tele_prefix_rel (canon_nparams_rel D ups) m (List.firstn m ns) (List.firstn m ns)) by (eapply tele_prefix_rel_of_pre; [ exact Hp | lia ]).
  eapply HNl; [ lia | exact Hpm | | eapply H'; eauto; lia ].
  eapply (HCN m Ns (List.firstn m ns) T'); [ rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
  intros j' N' T'' v' Hj' HN' HT' Hv'.
  rewrite List.firstn_firstn, Nat.min_l by lia.
  rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec j' m); [| discriminate ].
  eapply IH; eauto; lia.
Qed.

Lemma ind_comps_lower_a : forall p D ups NP NEl AP AEl DP DEl
    (AEl' : list domain -> String.string -> nat -> list domain -> glu_exp_pred) Γ Us Ns ns c gs gs1 gs2 As vs,
    ind_glu_comps p D ups NP NEl AP AEl DP DEl Γ Us ->
    (forall ms c gs k vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       k < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups ms c) k vs vs ->
       forall Γ A M m, AP ms c k vs Γ A -> AEl' ms c k vs Γ A M m -> AEl ms c k vs Γ A M m) ->
    glu_nparams D NEl Γ Us Ns ns -> tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ns ns ->
    ind_con D c = Some gs -> gs = gs1 ++ gs2 -> List.length vs = List.length gs1 ->
    tele_prefix_rel (canon_args_rel D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs) (nonrec_arg_vals gs1 vs) ->
    (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
       List.nth_error vs (List.length hs1) = Some v ->
       Γ ⊢ N : T' ® v ∈ AEl' ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
    (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
       List.nth_error vs (List.length hs1) = Some v ->
       Γ ⊢ N : T' ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
Proof.
  intros * [_ HCA _] HAl Hnp Hns Hc Heq Hvl Hp H'.
  enough (forall m, forall hs1 B hs2 N T' v, List.length hs1 < m -> gs1 = hs1 ++ ca_arg B :: hs2 ->
            List.nth_error As (List.length hs1) = Some N ->
            List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
            List.nth_error vs (List.length hs1) = Some v ->
            Γ ⊢ N : T' ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) as Hm
    by (intros; eapply (Hm (S (List.length hs1))); eauto).
  induction m as [| m IH]; intros hs1 B hs2 N T' v Hlt Heq1 HN HT Hv; [ lia |].
  destruct (Nat.eq_dec (List.length hs1) m) as [Hlm | Hne]; [| eapply IH; eauto; lia ].
  assert (Hl1 : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
  assert (HK : List.length (cargs_nonrec hs1) < List.length (cargs_nonrec gs))
    by (rewrite Heq, Heq1, !cargs_nonrec_app, !List.length_app; cbn; lia).
  assert (Hpre : tele_prefix_rel (canon_args_rel D ups ns c) (List.length (cargs_nonrec hs1))
                   (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
  { pose proof (tele_prefix_rel_of_pre _ _ _ _ (List.length (cargs_nonrec hs1)) Hp
                  ltac:(rewrite Heq1, cargs_nonrec_app, List.length_app; cbn; lia)) as Hq.
    rewrite (nonrec_firstn _ _ _ _ _ Heq1 Hvl) in Hq; exact Hq. }
  eapply HAl; [ exact Hns | exact Hc | exact HK | exact Hpre | | eapply H'; eauto ].
  eapply (HCA c gs hs1 B (hs2 ++ gs2) Ns ns As (List.firstn (List.length hs1) vs) T');
    [ exact Hc | rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact Hnp | exact Hns
    | rewrite List.length_firstn; lia | exact HT | | exact Hpre ].
  intros hs1' B' hs2' N' T'' v' Heq2 HN' HT' Hv'.
  assert (Hlt' : List.length hs1' < List.length hs1) by (rewrite Heq2, List.length_app; cbn; lia).
  rewrite List.firstn_firstn, Nat.min_l by lia.
  rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1') (List.length hs1)); [| discriminate ].
  eapply (IH hs1' B' (hs2' ++ ca_arg B :: hs2)); [ lia | rewrite Heq1, Heq2, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ].
Qed.

Lemma glu_nparams_lower : forall p D ups NP NEl AP AEl DP DEl (NEl' : nat -> list domain -> glu_exp_pred) Γ Us Ns ns,
    ind_glu_comps p D ups NP NEl AP AEl DP DEl Γ Us ->
    (forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
       forall Γ A M m, NP k vs Γ A -> NEl' k vs Γ A M m -> NEl k vs Γ A M m) ->
    tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ns ns ->
    glu_nparams D NEl' Γ Us Ns ns -> glu_nparams D NEl Γ Us Ns ns.
Proof.
  intros * Hc HNl Hns [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
  intros k N A n HN HA Hn.
  assert (Hk : k < ind_nn D) by (rewrite <- L2; apply List.nth_error_Some; congruence).
  eapply (ind_comps_lower_n _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl (ind_nn D) Ns ns); [ lia | | | exact Hk | exact HN | exact HA | exact Hn ].
  - destruct Hns as [_ Hns]; split; [ exact L2 | exact Hns ].
  - intros; eapply H; eassumption.
Qed.

Lemma ind_glu_comps_cumu : forall p D ups NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' Γ Us,
    tele_ass (ind_params D) -> ind_canon_props D ups ->
    (forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
       (forall Γ T, NP k vs Γ T -> NP' k vs Γ T) /\ (forall Γ T N n, NP k vs Γ T -> NEl' k vs Γ T N n -> NEl k vs Γ T N n)) ->
    (forall ms c gs k vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       k < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups ms c) k vs vs ->
       (forall Γ T, AP ms c k vs Γ T -> AP' ms c k vs Γ T) /\ (forall Γ T N n, AP ms c k vs Γ T -> AEl' ms c k vs Γ T N n -> AEl ms c k vs Γ T N n)) ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t)) k ys ys ->
       (forall Γ A, DP (ms ++ ws ++ ys) B Γ A -> DP' (ms ++ ws ++ ys) B Γ A) /\
       (forall Γ A M m, DP (ms ++ ws ++ ys) B Γ A -> DEl' (ms ++ ws ++ ys) B Γ A M m -> DEl (ms ++ ws ++ ys) B Γ A M m)) ->
    ind_glu_comps p D ups NP NEl AP AEl DP DEl Γ Us -> ind_glu_comps p D ups NP' NEl' AP' AEl' DP' DEl' Γ Us.
Proof.
  intros * Hass Hcp HN HA HD Hc.
  assert (HNl : forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
             forall Γ A M m, NP k vs Γ A -> NEl' k vs Γ A M m -> NEl k vs Γ A M m)
    by (intros; eapply (proj2 (HN _ _ ltac:(eassumption) ltac:(eassumption))); eassumption).
  assert (HAl : forall ms c gs k vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
             k < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups ms c) k vs vs ->
             forall Γ A M m, AP ms c k vs Γ A -> AEl' ms c k vs Γ A M m -> AEl ms c k vs Γ A M m)
    by (intros; eapply (proj2 (HA _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))); eassumption).
  pose proof Hc as [HCN HCA HCR]; constructor.
  - intros k Ns ns T Hl Hk HT Hpre Hp.
    apply (proj1 (HN k ns Hk Hp)).
    apply (HCN k Ns ns T Hl Hk HT); [| exact Hp ].
    intros j N T' n Hj HN0 HT' Hn.
    eapply (ind_comps_lower_n _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl k Ns ns); [ lia | exact Hp | | exact Hj | exact HN0 | exact HT' | exact Hn ].
    exact Hpre.
  - intros c gs gs1 A0 gs2 Ns ns As vs T Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    assert (HK : List.length (cargs_nonrec gs1) < List.length (cargs_nonrec gs))
      by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
    apply (proj1 (HA _ _ _ _ _ Hns Hcon HK Hp)).
    pose proof (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl Hns Hnp) as Hnp'.
    eapply HCA; [ exact Hcon | exact Heq | exact Hnp' | exact Hns | exact Hvl | exact HT | | exact Hp ].
    intros hs1 B hs2 N T' v Heq1 HN0 HT' Hv.
    eapply (ind_comps_lower_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gs1 (ca_arg A0 :: gs2) As vs Hc HAl Hnp' Hns Hcon Heq Hvl Hp Hpre);
      eassumption.
  - intros c gs gs1 t gs2 Ns ns As vs T Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc HNl Hns Hnp) as Hnp'.
    pose proof (HCR c gs gs1 t gs2 Ns ns As vs T Hcon Heq Hnp' Hns Hvl HT
                  (ind_comps_lower_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gs1 (ca_rec t :: gs2) As vs Hc HAl Hnp' Hns Hcon Heq Hvl Hp Hpre)
                  Hp) as H.
    subst gs.
    exact (glu_shape_typ_change p D ups ups DP DP' DEl DEl' Hass Hcp ltac:(intros; reflexivity) HD
             t Γ _ T H ns c gs1 t gs2 (nonrec_arg_vals gs1 vs) 0 nil ltac:(rewrite List.app_nil_r; reflexivity)
             Hns Hcon Hp eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
Qed.

(** Equal lists of terms at a closed telescope are equal at every
    weakening. *)
Lemma exps_eq_at_wk : forall Δ Δ' φ T Xs Ys, tele_ass T -> ctx_scoped 0 T -> Δ' ⊢ᵏ φ : Δ ->
    exps_eq_at Δ T Xs Ys -> exps_eq_at Δ' T (List.map (fun X => X[φ]ʷ) Xs) (List.map (fun Y => Y[φ]ʷ) Ys).
Proof.
  intros * Hass Hs Hφ [Hl H]; split; [ rewrite !List.length_map; exact Hl |].
  intros k X Y A HX HY HA.
  rewrite List.nth_error_map in HX, HY.
  destruct (List.nth_error Xs k) as [X0 |] eqn:HX0; [| discriminate ]; injection HX as <-.
  destruct (List.nth_error Ys k) as [Y0 |] eqn:HY0; [| discriminate ]; injection HY as <-.
  rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HA.
  destruct (List.nth_error (tele_insts T Id Xs) k) as [A0 |] eqn:HA0; [| discriminate ]; injection HA as <-.
  pose proof (H _ _ _ _ HX0 HY0 HA0); mauto 3.
Qed.

(** The parameters of a type predicate at a weakening, at a list equal to
    them there, are equal to the ones of another predicate glued to the same
    values. *)
Lemma exps_eq_at_params_wk : forall p D Δ Δ' φ Xs Ys, ind_lookup gc_deps gc_stack p = Some D -> Δ' ⊢ᵏ φ : Δ ->
    exps_eq_at Δ (ind_params D) Xs Ys ->
    exps_eq_at Δ' (ind_params D) (List.map (fun X => X[φ]ʷ) Xs) (List.map (fun Y => Y[φ]ʷ) Ys).
Proof.
  intros * Hl Hφ H.
  assert (HΔ : ⊢ Δ) by (eapply kripke_cod; eassumption).
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ [Hass _ Hs _ _ _ _]].
  eapply exps_eq_at_wk; eassumption.
Qed.

(** Equal parameters are equal at their uniform part. *)
Lemma exps_eq_at_uparams_of_params : forall D Δ Xs Ys, decl_closed D ->
    List.length Xs = ind_np D -> exps_eq_at Δ (ind_params D) Xs Ys ->
    exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) Xs) (List.firstn (ind_nu D) Ys).
Proof.
  intros * Hc HXl [Hl H]; split; [ rewrite !List.length_firstn; lia |].
  pose proof (decl_uparams_ass D Hc) as HassU.
  pose proof (decl_closed_nu D Hc) as Hle.
  intros k X Y A HX HY HA.
  rewrite List.nth_error_firstn in HX, HY.
  destruct (Nat.ltb_spec k (ind_nu D)); [| discriminate ].
  apply (H k X Y A HX HY).
  rewrite <- (List.firstn_skipn (ind_nu D) Xs), params_split, tele_insts_app
    by (try exact HassU; rewrite List.length_firstn, length_ind_uparams by exact Hle; lia).
  rewrite List.nth_error_app1; [ exact HA |].
  rewrite length_tele_insts by exact HassU; rewrite List.length_firstn, length_ind_uparams by exact Hle; lia.
Qed.

(** Parameters with an equal uniform part, the rest unchanged. *)
Lemma exps_eq_at_params_of_uparams : forall D Δ Xs Us', decl_closed D ->
    List.length Xs = ind_np D ->
    (forall k X A, List.nth_error Xs k = Some X -> List.nth_error (tele_insts (ind_params D) Id Xs) k = Some A -> Δ ⊢ X : A) ->
    exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) Xs) Us' ->
    exps_eq_at Δ (ind_params D) Xs (Us' ++ List.skipn (ind_nu D) Xs).
Proof.
  intros * Hc HXl HXt [Hl H].
  pose proof (decl_uparams_ass D Hc) as HassU.
  pose proof (decl_closed_nu D Hc) as Hle.
  assert (LU : List.length (List.firstn (ind_nu D) Xs) = ind_nu D) by (rewrite List.length_firstn; lia).
  pose proof Hl as Hl0; rewrite LU in Hl0.
  split; [ rewrite List.length_app, List.length_skipn; lia |].
  intros k X Y A HX HY HA.
  destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HY by lia.
    apply (H k X Y A); [ rewrite List.nth_error_firstn; destruct (Nat.ltb_spec k (ind_nu D)); [ exact HX | lia ] | exact HY |].
    rewrite <- (List.firstn_skipn (ind_nu D) Xs), params_split, tele_insts_app in HA
      by (try exact HassU; rewrite LU, length_ind_uparams by exact Hle; lia).
    rewrite List.nth_error_app1 in HA; [ exact HA |].
    rewrite length_tele_insts, length_ind_uparams by (exact HassU || exact Hle); lia.
  - rewrite List.nth_error_app2 in HY by lia.
    rewrite List.nth_error_skipn in HY.
    replace (ind_nu D + (k - List.length Us')) with k in HY by lia.
    rewrite HX in HY; injection HY as <-.
    apply wf_exp_eq_refl; eapply HXt; eassumption.
Qed.

(** The right side of equal parameters is typed at its own telescope. *)
Lemma exps_eq_at_typed_r : forall p D Δ Xs Ys, ind_lookup gc_deps gc_stack p = Some D -> ⊢ Δ ->
    List.length Xs = ind_np D -> exps_eq_at Δ (ind_params D) Xs Ys ->
    forall k Y A, List.nth_error Ys k = Some Y -> List.nth_error (tele_insts (ind_params D) Id Ys) k = Some A -> Δ ⊢ Y : A.
Proof.
  intros * Hl HΔ HXl [HlXY HXY] k Y A HY HA.
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
  destruct (nth_error_lt_some Xs k ltac:(rewrite HlXY; apply List.nth_error_Some; congruence)) as [X HX].
  destruct (nth_error_lt_some (tele_insts (ind_params D) Id Xs) k) as [T0 HT0].
  { rewrite length_tele_insts_params by (try apply decl_closed_params, Hc; exact HXl).
    rewrite HXl; unfold ind_np; assert (k < List.length Xs) by (apply List.nth_error_Some; congruence); unfold ind_np in *; lia. }
  pose proof (HXY _ _ _ _ HX HY HT0) as HXY0.
  destruct (params_types_cong _ _ _ _ _ Hl HΔ HXl ltac:(rewrite <- HlXY; exact HXl) HXY _ _ _ HT0 HA) as [i HTT].
  eapply wf_conv'; [ gen_presups; eassumption | exact HTT ].
Qed.

Lemma exps_eq_at_uparams_trans : forall p D Δ Xs Ys Zs, ind_lookup gc_deps gc_stack p = Some D -> ⊢ Δ ->
    List.length Xs = ind_nu D -> exps_eq_at Δ (ind_uparams D) Xs Ys -> exps_eq_at Δ (ind_uparams D) Ys Zs ->
    exps_eq_at Δ (ind_uparams D) Xs Zs.
Proof.
  intros * Hl HΔ HXl [Hl1 H1] [Hl2 H2].
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
  pose proof (length_ind_uparams D (decl_closed_nu D Hc)) as LU.
  split; [ congruence |].
  eapply (tele_eq_trans Δ (ind_uparams D) Xs Ys Zs (decl_uparams_ass D Hc) (uparams_ctx_wf _ _ _ Hl HΔ)); [ lia | lia | lia | exact H1 | exact H2 ].
Qed.

Lemma map_wk_id : forall Ps, List.map (fun P => P[wk_id]ʷ) Ps = Ps.
Proof. intros; rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; reflexivity. Qed.

(** The components of an inductive type at uniform parameters [Us], at
    every weakening and at every instance equal to them there. *)
Definition ind_comps_kripke (p : qname) (D : ind_decl) (ups : list domain)
    (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
    (Γ : ctx) (Us : list exp) : Prop :=
  forall Δ φ, Δ ⊢ᵏ φ : Γ ->
    ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ (List.map (fun U => U[φ]ʷ) Us) /\
    forall Us', exps_eq_at Δ (ind_uparams D) (List.map (fun U => U[φ]ʷ) Us) Us' ->
      ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us'.

Lemma ind_comps_kripke_wk : forall p D ups NP NEl AP AEl DP DEl Γ Us Δ φ,
    ind_comps_kripke p D ups NP NEl AP AEl DP DEl Γ Us -> Δ ⊢ᵏ φ : Γ ->
    ind_comps_kripke p D ups NP NEl AP AEl DP DEl Δ (List.map (fun U => U[φ]ʷ) Us).
Proof.
  intros * Hk Hφ Δ' φ' Hφ'; rewrite map_wk_wk; apply Hk; eapply kripke_compose; eassumption.
Qed.

(** An element of an inductive type glued at gluings of its telescopes
    that contain the given ones, under types glued at the given ones: an
    element of a larger universe moved down.  The components are needed
    at every instance of the uniform parameters equal to the given ones,
    since a recursive argument is an element at every instance of the
    parameters equal to the ones of its type.  A recursive argument of a
    function shape is moved down at the domains' gluings of the
    components, its argument moved up. *)
Lemma ind_glu_elem_lower : forall p D ups NP NEl AP AEl DP DEl (NEl' : nat -> list domain -> glu_exp_pred)
    (AEl' : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP' : list domain -> exp -> glu_typ_pred) (DEl' : list domain -> exp -> glu_exp_pred),
    ind_lookup gc_deps gc_stack p = Some D -> tele_ass (ind_params D) -> ind_canon_props D ups ->
    (forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
       forall Γ A M m, NP k vs Γ A -> NEl' k vs Γ A M m -> NEl k vs Γ A M m) ->
    (forall ms c gs k vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       k < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups ms c) k vs vs ->
       forall Γ A M m, AP ms c k vs Γ A -> AEl' ms c k vs Γ A M m -> AEl ms c k vs Γ A M m) ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t)) k ys ys ->
       forall Γ A M m, DEl (ms ++ ws ++ ys) B Γ A M m -> DEl' (ms ++ ws ++ ys) B Γ A M m) ->
    forall Γ Ps M m, ind_glu_elem p D ups NEl' AEl' DP' DEl' Γ Ps M m ->
      (forall Δ φ, Δ ⊢ᵏ φ : Γ ->
         ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ (List.firstn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ps)) /\
         forall Us', exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ps)) Us' ->
           ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us') ->
      ind_glu_elem p D ups NEl AEl DP DEl Γ Ps M m.
Proof.
  intros p D ups NP NEl AP AEl DP DEl NEl' AEl' DP' DEl' Hl Hass Hcp HNl HAl HDl.
  pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
  apply (ind_glu_elem_mut_ind p D ups NEl' AEl' DP' DEl'
           (fun Γ Ps M m _ =>
              (forall Δ φ, Δ ⊢ᵏ φ : Γ ->
                 ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ (List.firstn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ps)) /\
                 forall Us', exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ps)) Us' ->
                   ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us') ->
              ind_glu_elem p D ups NEl AEl DP DEl Γ Ps M m)
           (fun Γ pre t A N v _ => forall ms c0 gs1 t0 gs2 ws k ys, pre = ms ++ ws ++ ys ->
              tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms ->
              ind_con D c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
              tele_prefix_rel (canon_args_rel D ups ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
              ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
              tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t0)) k ys ys ->
              glu_shape_typ ups DP DEl Γ pre t A -> ⊢ Γ ->
              forall Us σ, List.length Us = ind_nu D -> A = ptyp_ty_at p Us σ t ->
              ind_comps_kripke p D ups NP NEl AP AEl DP DEl Γ Us ->
              glu_rec p D ups NEl AEl DP DEl Γ pre t A N v)).
  - intros * Hcon HPl Hbl Hvl HAl' HM Hb Hv Hnp HAs Harg Hrec IH Hk.
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
    pose proof (dc_nu _ Hc) as Hle.
    assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
    pose proof (proj1 (Hk _ _ Hid)) as Hc0.
    rewrite map_wk_id in Hc0.
    pose proof (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc0 HNl Hb Hnp) as Hnp'.
    assert (HargL : forall gs1 A0 gs2 N A v, gs = gs1 ++ ca_arg A0 :: gs2 ->
              List.nth_error As (List.length gs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
              List.nth_error vs (List.length gs1) = Some v ->
              Γ ⊢ N : A ® v ∈ AEl (List.skipn (ind_nu D) bs) c (List.length (cargs_nonrec gs1))
                                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))).
    { pose proof (ind_comps_lower_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gs nil As vs Hc0 HAl Hnp' Hb Hcon
                    ltac:(rewrite List.app_nil_r; reflexivity) Hvl Hv) as L.
      rewrite List.firstn_skipn in L.
      exact (L Harg). }
    eapply ind_glu_elem_con; try eassumption.
    intros gs1 t gs2 N A v Heq HN0 HA0 Hv0.
    assert (Hlt : List.length gs1 < List.length vs) by (rewrite Hvl, Heq, List.length_app; cbn; lia).
    assert (Hpw : tele_prefix_rel (canon_args_rel D ups (List.skipn (ind_nu D) bs) c) (List.length (cargs_nonrec gs1))
                    (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)))
      by (eapply nonrec_prefix_pre; eassumption).
    assert (HA0' : List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (List.firstn (ind_nu D) Ps ++ List.skipn (ind_nu D) Ps)) As)
                     (List.length gs1) = Some A) by (rewrite List.firstn_skipn; exact HA0).
    assert (Hsh : glu_shape_typ ups DP DEl Γ (List.skipn (ind_nu D) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A).
    { destruct Hc0 as [_ _ HCR].
      refine (HCR c gs gs1 t gs2 _ _ As (List.firstn (List.length gs1) vs) A Hcon Heq Hnp' Hb
                ltac:(rewrite List.length_firstn; lia) HA0' _ Hpw).
      intros hs1 B hs2 N' T' v' Heq1 HN' HT' Hv'.
      assert (Hh : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.firstn_skipn in HT'.
      eapply (HargL hs1 B (hs2 ++ ca_rec t :: gs2)); [ rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ]. }
    pose proof (cargs_rec_type_at _ _ _ _ _ _ _ _ _ Heq Hle HPl HA0) as HAσ.
    apply (IH _ _ _ _ _ _ Heq HN0 HA0 Hv0 (List.skipn (ind_nu D) bs) c gs1 t gs2
             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil
             ltac:(rewrite List.app_nil_r; reflexivity) Hb ltac:(rewrite <- Heq; exact Hcon) Hpw eq_refl ltac:(lia)
             (tele_prefix_rel_nil _) Hsh HΓ (List.firstn (ind_nu D) Ps) _ ltac:(rewrite List.length_firstn; pose proof (decl_closed_nu D Hc); lia) HAσ).
    intros Δ φ Hφ; rewrite <- List.firstn_map; exact (Hk Δ φ Hφ).
  - intros * Hm Hr _; eapply ind_glu_elem_neut; eassumption.
  - intros * Hs1 Hs2 IH ms c0 gs1 t0 gs2 ws k1 ys Hpre Hm Hc Hw Hsk Hk1 Hy _ HΓ Us σ HUl HA Hk.
    cbn [ptyp_ty_at] in HA.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hcl].
    assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
    pose proof (proj1 (Hk _ _ Hid)) as Hc0; rewrite map_wk_id in Hc0.
    (** The uniform parameters of the leaf's type are [Us]. *)
    assert (HU : forall Q, A = apps (a_ind p) Q -> List.firstn (ind_nu D) Q = Us).
    { intros Q HQ; rewrite HA in HQ; apply apps_ind_inj in HQ; subst Q.
      rewrite List.firstn_app, <- HUl, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r. }
    apply glu_rec_self.
    + intros bsr Q Hbs HQ.
      destruct (Hs1 _ _ Hbs HQ) as (HQl & Hbt & Hgn).
      split; [ exact HQl | split; [ exact Hbt |] ].
      intros bsr' Hb'; destruct (Hgn _ Hb') as [Hn' Hpt]; split; [| exact Hpt ].
      rewrite (HU _ HQ) in Hn' |- *.
      exact (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc0 HNl (canon_nparams_rel_refl_r' p D ups Hass Hcp _ _ Hb') Hn').
    + intros bsr Q Hbs HQ Δ φ Q' Hφ HQ'.
      destruct (Hs1 _ _ Hbs HQ) as (HQl & _ & _).
      apply (IH _ _ Hbs HQ Δ φ Q' Hφ HQ').
      intros Δ' φ' Hφ'.
      pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hc2.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      (** The uniform part of [Q'] at [φ'] is [Us] at [φ ⊙ φ']. *)
      assert (HQU : exps_eq_at Δ' (ind_uparams D) (List.map (fun U => U[φ ⊙ φ']ʷ) Us)
                      (List.firstn (ind_nu D) (List.map (fun P => P[φ']ʷ) Q'))).
      { pose proof (exps_eq_at_params_wk _ _ _ _ _ _ _ Hl Hφ' HQ') as H.
        rewrite map_wk_wk in H.
        pose proof (exps_eq_at_uparams_of_params _ _ _ _ Hcl ltac:(rewrite List.length_map; exact HQl) H) as H'.
        rewrite List.firstn_map, (HU _ HQ) in H'; exact H'. }
      destruct (Hk _ _ Hc2) as [_ Hk2].
      split.
      * apply Hk2; exact HQU.
      * intros Us' HUs'.
        apply Hk2; eapply exps_eq_at_uparams_trans; [ exact Hl | exact HΔ' | | exact HQU | exact HUs' ].
        rewrite List.length_map; exact HUl.
  - intros * Hd He Hg IH ms c0 gs1 t0 gs2 ws k1 ys Hpre Hm Hc Hw Hsk Hk1 Hy Hsh HΓ Us σ HUl HA Hk.
    destruct (shape_pi_step p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) Hass HnP HnI HaP HaI HdP HdI
                ms c0 gs1 t0 gs2 ws ws k1 ys ys B t Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
    subst pre.
    pose proof (HDl _ _ _ _ _ _ _ _ _ _ Hm Hc eq_refl Hw HB Hy) as HDu.
    cbn [ptyp_ty_at] in HA.
    apply glu_rec_pi.
    + intros IT OT HA0 Δ φ Hφ; exact (proj1 (Hsh IT OT HA0) Δ φ Hφ).
    + intros IT OT HA0 Δ φ b c Hφ Hc' Hb; exact (He IT OT HA0 Δ φ b c Hφ Hc' (HDu _ _ _ _ Hb)).
    + intros IT OT HA0 Δ φ b c fc Hφ Hc' Hb Hfc.
      assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
      pose proof HA as HA1; rewrite HA0 in HA1; injection HA1 as _ HOT.
      apply (IH _ _ HA0 Δ φ b c fc Hφ Hc' (HDu _ _ _ _ Hb) Hfc ms c0 gs1 t0 gs2 ws (S k1) (ys ++ c :: nil)
               ltac:(rewrite <- !List.app_assoc; reflexivity) Hm Hc Hw Hs' Hk' (Hstep _ _ Hc')
               (proj2 (Hsh _ _ HA0) Δ φ b c Hφ Hc' Hb) HΔ (List.map (fun U => U[φ]ʷ) Us)
               (sb_compose (sb_q σ) ((ι φ),,b)) ltac:(rewrite List.length_map; exact HUl)).
      * rewrite HOT, ptyp_ty_at_sub, List.map_map; f_equal.
        apply List.map_ext; intros; apply exp_shift_extend_wk.
      * exact (ind_comps_kripke_wk _ _ _ _ _ _ _ _ _ _ _ _ _ Hk Hφ).
Qed.


Lemma ind_rps_of_per : forall i R p D as1 as2, DF d_ind p as1 ≈ d_ind p as2 ∈ per_univ_elem i ↘ R ->
    ind_lookup gc_deps gc_stack p = Some D ->
    forall n, exists Ms, Rps as1 at List.rev (ind_params D) in gc_deps ⍮ gc_stack ⍮ nil ⍮ n ↘ Ms.
Proof.
  intros * H Hl n.
  destruct (per_univ_then_per_top_typ H n) as (W & Hr & _).
  inversion Hr; subst.
  match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
  eauto.
Qed.

(** Two lists of parameters glued to the same values are equal. *)
Lemma glu_params_top_eq : forall p D Δ Ps Qs as',
    ind_lookup gc_deps gc_stack p = Some D -> ⊢ Δ ->
    (exists Ms, Rps as' at List.rev (ind_params D) in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms) ->
    glu_params_top D Δ Ps as' -> glu_params_top D Δ Qs as' -> exps_eq_at Δ (ind_params D) Ps Qs.
Proof.
  intros * Hl HΔ (Ms & HMs) [HPl _ HPr] [HQl _ HQr].
  assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
  pose proof (HPr _ _ _ Hid HMs) as [HPM HPMs]; pose proof (HQr _ _ _ Hid HMs) as [HQM HQMs].
  rewrite (map_wk_id Ps) in HPM, HPMs; rewrite (map_wk_id Qs) in HQM, HQMs.
  split; [ congruence |].
  assert (HMl : List.length (nfs_to_exps Ms) = ind_np D) by congruence.
  eapply (params_eq_trans _ p D Ps (nfs_to_exps Ms) Qs Hl HΔ HPl HMl HQl HPMs).
  eapply (params_eq_sym _ p D Qs (nfs_to_exps Ms) Hl HΔ HQl HMl HQMs).
Qed.

Lemma ind_typ_at_cumu : forall p D ups ns NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' a b Γ A Ps,
    tele_ass (ind_params D) -> ind_canon_props D ups ->
    a <= b ->
    (forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
       (forall Γ T, NP k vs Γ T -> NP' k vs Γ T) /\ (forall Γ T N n, NP k vs Γ T -> NEl' k vs Γ T N n -> NEl k vs Γ T N n)) ->
    (forall ms c gs k vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       k < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups ms c) k vs vs ->
       (forall Γ T, AP ms c k vs Γ T -> AP' ms c k vs Γ T) /\ (forall Γ T N n, AP ms c k vs Γ T -> AEl' ms c k vs Γ T N n -> AEl ms c k vs Γ T N n)) ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t)) k ys ys ->
       (forall Γ A, DP (ms ++ ws ++ ys) B Γ A -> DP' (ms ++ ws ++ ys) B Γ A) /\
       (forall Γ A M m, DP (ms ++ ws ++ ys) B Γ A -> DEl' (ms ++ ws ++ ys) B Γ A M m -> DEl (ms ++ ws ++ ys) B Γ A M m)) ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl Typeω@a Γ A Ps -> ind_typ_at p D ups ns NP' NEl' AP' AEl' DP' DEl' Typeω@b Γ A Ps.
Proof.
  intros * Hass Hcp Hab HN HA HD (HA0 & Hk); split; [ eapply lift_exp_eq_ge; eassumption |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & Hs & Hc).
  split; [ exact Hpt | split ].
  - destruct (Nat.eq_dec a b) as [<- | Hne]; [ exact Hs |].
    eapply wf_subtyp_trans; [ exact Hs | apply wf_subtyp_univ; [ eapply kripke_dom; eassumption | lia ] ].
  - intros Ps' HPs'; eapply ind_glu_comps_cumu; [ exact Hass | exact Hcp | exact HN | exact HA | exact HD | exact (Hc _ HPs') ].
Qed.

(** A type of an inductive type at parameters [Ps] is one at parameters
    [Qs] glued to the same values. *)
Lemma ind_typ_at_params_change : forall p D ups ns NP NEl AP AEl DP DEl a Γ A Ps Qs,
    ind_lookup gc_deps gc_stack p = Some D ->
    (forall n, exists Ms, Rps ups ++ ns at List.rev (ind_params D) in gc_deps ⍮ gc_stack ⍮ nil ⍮ n ↘ Ms) ->
    (forall Δ φ, Δ ⊢ᵏ φ : Γ -> glu_params_top D Δ (List.map (fun P => P[φ]ʷ) Qs) (ups ++ ns)) ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl Typeω@a Γ A Ps -> ind_typ_at p D ups ns NP NEl AP AEl DP DEl Typeω@a Γ A Qs.
Proof.
  intros * Hl Hrb HQ (HA0 & Hk).
  assert (Heq : forall Δ φ, Δ ⊢ᵏ φ : Γ -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Ps) (List.map (fun P => P[φ]ʷ) Qs)).
  { intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & _ & _).
    eapply glu_params_top_eq; [ exact Hl | eapply kripke_dom; eassumption | apply Hrb | exact Hpt | exact (HQ _ _ Hφ) ]. }
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  split.
  - destruct (Hk _ _ Hid) as ([HPl _ _] & Hs & _).
    destruct (Heq _ _ Hid) as [_ HPQ]; destruct (HQ _ _ Hid) as [HQl _ _].
    rewrite (map_wk_id Ps) in HPl, Hs, HPQ; rewrite (map_wk_id Qs) in HPQ, HQl.
    etransitivity; [ exact HA0 |].
    eapply wf_exp_eq_subtyp'; [| exact Hs ].
    eapply wf_exp_eq_ind_apps; [ exact Hl | exact HΓ | exact HPl | exact HQl | exact HPQ ].
  - intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as ([HPl HPt HPr] & Hs & Hc).
    pose proof (Heq _ _ Hφ) as [HlPQ HPQ]; pose proof (HQ _ _ Hφ) as HQt.
    pose proof HQt as [HQl _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    split; [ exact HQt | split ].
    + destruct (ind_sort_inst_cong _ _ _ _ _ Hl HΔ HPl HQl HPQ) as [k Hk'].
      eapply wf_subtyp_trans; [ eapply wf_subtyp_refl'; symmetry; exact Hk' | exact Hs ].
    + intros Ps' [HlQP' HQP']; apply Hc; split; [ congruence |].
      eapply (params_eq_trans _ p D _ _ _ Hl HΔ HPl HQl); [ congruence | exact HPQ | exact HQP' ].
Qed.


(** The case of an inductive type in the cumulativity of the gluing, from
    the one of its telescopes' types. *)
Lemma glu_univ_elem_cumu_ind : forall (i j : uidx) p D ups ns NP NEl AP AEl DP DEl elem_rel NP' NEl' AP' AEl' DP' DEl' elem_rel',
    uidx_le i j -> ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> tele_ass (ind_params D) ->
    DF d_ind p (ups ++ ns) ≈ d_ind p (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
    DF d_ind p (ups ++ ns) ≈ d_ind p (ups ++ ns) ∈ per_univ_elem j ↘ elem_rel' ->
    (forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_prefix_rel (canon_nparams_rel D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
    (forall ms c gs k A vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_prefix_rel (canon_args_rel D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
    (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_prefix_rel (canon_nparams_rel D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
       (forall Γ T, NP k vs Γ T -> NP' k vs Γ T) /\ (forall Γ T N n, NEl k vs Γ T N n -> NEl' k vs Γ T N n) /\
       (forall Γ T N n, NP k vs Γ T -> NEl' k vs Γ T N n -> NEl k vs Γ T N n)) ->
    (forall ms c gs k A vs b, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_prefix_rel (canon_args_rel D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       (forall Γ T, AP ms c k vs Γ T -> AP' ms c k vs Γ T) /\ (forall Γ T N n, AEl ms c k vs Γ T N n -> AEl' ms c k vs Γ T N n) /\
       (forall Γ T N n, AP ms c k vs Γ T -> AEl' ms c k vs Γ T N n -> AEl ms c k vs Γ T N n)) ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t)) k ys ys ->
       exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b) ->
    (forall ms c gs gs1 t gs2 ws k B ys b, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t)) k ys ys ->
       ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
       (forall Γ T, DP (ms ++ ws ++ ys) B Γ T -> DP' (ms ++ ws ++ ys) B Γ T) /\
       (forall Γ T N n, DEl (ms ++ ws ++ ys) B Γ T N n -> DEl' (ms ++ ws ++ ys) B Γ T N n) /\
       (forall Γ T N n, DP (ms ++ ws ++ ys) B Γ T -> DEl' (ms ++ ws ++ ys) B Γ T N n -> DEl (ms ++ ws ++ ys) B Γ T N n)) ->
    (forall Γ A, ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl Typeω@(ulvl i) Γ A ->
       ind_glu_typ_pred p D ups ns NP' NEl' AP' AEl' DP' DEl' Typeω@(ulvl j) Γ A) /\
    (forall Γ A M m, ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl elem_rel Typeω@(ulvl i) Γ A M m ->
       ind_glu_exp_pred p D ups ns NP' NEl' AP' AEl' DP' DEl' elem_rel' Typeω@(ulvl j) Γ A M m) /\
    (forall Γ A M m, ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl Typeω@(ulvl i) Γ A ->
       ind_glu_exp_pred p D ups ns NP' NEl' AP' AEl' DP' DEl' elem_rel' Typeω@(ulvl j) Γ A M m ->
       ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl elem_rel Typeω@(ulvl i) Γ A M m).
Proof.
  intros * Hge Hl Hu Hass Hper Hper' HeN HeA HN3 HA3 HeD HD3.
  assert (HN : forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
             (forall Γ T, NP k vs Γ T -> NP' k vs Γ T) /\ (forall Γ T N n, NEl k vs Γ T N n -> NEl' k vs Γ T N n) /\
             (forall Γ T N n, NP k vs Γ T -> NEl' k vs Γ T N n -> NEl k vs Γ T N n)).
  { intros k vs Hk Hp.
    destruct (nparams_lt_ass D k Hass ltac:(rewrite List.length_rev, length_nparams; lia)) as [A HA].
    destruct (HeN _ _ _ HA Hp) as [b Hb]; exact (HN3 _ _ _ _ HA Hp Hb). }
  assert (HA : forall ms c gs k vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
             k < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups ms c) k vs vs ->
             (forall Γ T, AP ms c k vs Γ T -> AP' ms c k vs Γ T) /\ (forall Γ T N n, AEl ms c k vs Γ T N n -> AEl' ms c k vs Γ T N n) /\
             (forall Γ T N n, AP ms c k vs Γ T -> AEl' ms c k vs Γ T N n -> AEl ms c k vs Γ T N n)).
  { intros ms c gs k vs Hm Hc Hk Hp.
    destruct (nth_error_lt_some' _ _ Hk) as [A HA].
    destruct (HeA _ _ _ _ _ _ Hm Hc HA Hp) as [b Hb]; exact (HA3 _ _ _ _ _ _ _ Hm Hc HA Hp Hb). }
  assert (HN2 : forall k vs, k < ind_nn D -> tele_prefix_rel (canon_nparams_rel D ups) k vs vs ->
             (forall Γ T, NP k vs Γ T -> NP' k vs Γ T) /\ (forall Γ T N n, NP k vs Γ T -> NEl' k vs Γ T N n -> NEl k vs Γ T N n))
    by (intros k vs Hk Hp; destruct (HN k vs Hk Hp) as (E1 & _ & E3); split; assumption).
  assert (HA2 : forall ms c gs k vs, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
             k < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups ms c) k vs vs ->
             (forall Γ T, AP ms c k vs Γ T -> AP' ms c k vs Γ T) /\ (forall Γ T N n, AP ms c k vs Γ T -> AEl' ms c k vs Γ T N n -> AEl ms c k vs Γ T N n))
    by (intros ms c gs k vs Hm Hc Hk Hp; destruct (HA ms c gs k vs Hm Hc Hk Hp) as (E1 & _ & E3); split; assumption).
  assert (HD : forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t)) k ys ys ->
             (forall Γ T, DP (ms ++ ws ++ ys) B Γ T -> DP' (ms ++ ws ++ ys) B Γ T) /\
             (forall Γ T N n, DEl (ms ++ ws ++ ys) B Γ T N n -> DEl' (ms ++ ws ++ ys) B Γ T N n) /\
             (forall Γ T N n, DP (ms ++ ws ++ ys) B Γ T -> DEl' (ms ++ ws ++ ys) B Γ T N n -> DEl (ms ++ ws ++ ys) B Γ T N n)).
  { intros * Hm Hc Heq Hw HB Hy.
    destruct (HeD _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [b Hb]; exact (HD3 _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy Hb). }
  assert (HD2 : forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups) ms ws (ptyp_doms t)) k ys ys ->
             (forall Γ T, DP (ms ++ ws ++ ys) B Γ T -> DP' (ms ++ ws ++ ys) B Γ T) /\
             (forall Γ T N n, DP (ms ++ ws ++ ys) B Γ T -> DEl' (ms ++ ws ++ ys) B Γ T N n -> DEl (ms ++ ws ++ ys) B Γ T N n))
    by (intros * Hm Hc Heq Hw HB Hy; destruct (HD _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as (E1 & _ & E3); split; assumption).
  pose proof (ind_canon_of_per _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as Hcp.
  pose proof (ind_rps_of_per _ _ _ _ _ _ Hper Hl) as Hrb.
  pose proof (uidx_le_ulvl_le _ _ Hge) as Hij.
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hper Hper') as Hrel.
  split; [| split ].
  - intros Γ A (Ps & HPs); exists Ps; eapply ind_typ_at_cumu; [ exact Hass | exact Hcp | exact Hij | exact HN2 | exact HA2 | exact HD2 | exact HPs ].
  - intros Γ A M m [HM Hm Ps HPs Hk].
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Ps _ _); [ apply Hrel; exact Hm | eapply ind_typ_at_cumu; [ exact Hass | exact Hcp | exact Hij | exact HN2 | exact HA2 | exact HD2 | exact HPs ] |].
    intros Δ φ Ps' Hφ HPs'; eapply (ind_glu_elem_mono p D ups NEl AEl DP DEl Hass Hcp); [| | | exact (Hk _ _ _ Hφ HPs') ].
    + intros k vs Hk' Hp; apply (proj1 (proj2 (HN k vs Hk' Hp))).
    + intros ms c gs k vs Hm' Hc Hk' Hp; apply (proj1 (proj2 (HA ms c gs k vs Hm' Hc Hk' Hp))).
    + exact HD2.
  - intros Γ A M m (Ps & HPs) [HM Hm Qs HQs Hk].
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Qs _ _); [ apply Hrel; exact Hm | |].
    + eapply ind_typ_at_params_change; [ exact Hl | exact Hrb | | exact HPs ].
      intros Δ φ Hφ; exact (proj1 (proj2 HQs Δ φ Hφ)).
    + intros Δ φ Ps' Hφ HPs'.
      eapply ind_glu_elem_lower; [ exact Hl | exact Hass | exact Hcp | | | | exact (Hk _ _ _ Hφ HPs') | ].
      * intros k vs Hk' Hp; apply (proj2 (proj2 (HN k vs Hk' Hp))).
      * intros ms c gs k vs Hm' Hc Hk' Hp; apply (proj2 (proj2 (HA ms c gs k vs Hm' Hc Hk' Hp))).
      * intros * Hm' Hc Heq Hw HB Hy; exact (proj1 (proj2 (HD _ _ _ _ _ _ _ _ _ _ Hm' Hc Heq Hw HB Hy))).
      * intros Δ' φ' Hφ'.
        pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hc.
        assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
        destruct (proj2 HPs _ _ Hc) as (HPt & _ & HPc).
        pose proof (proj1 (proj2 HQs _ _ Hc)) as HQt.
        pose proof (glu_params_top_eq _ _ _ _ _ _ Hl HΔ' (Hrb _) HPt HQt) as [HlPQ HPQ].
        pose proof (exps_eq_at_params_wk _ _ _ _ _ _ _ Hl Hφ' HPs') as [HlQ' HQ'].
        rewrite map_wk_wk in HlQ', HQ'.
        destruct HPt as [HPl _ _]; destruct HQt as [HQl _ _].
        assert (HlP' : List.length (List.map (fun P => P[φ']ʷ) Ps') = ind_np D) by (clear - HlQ' HPl HQl; rewrite !List.length_map in *; lia).
        assert (E1 : exps_eq_at Δ' (ind_params D) (List.map (fun P => P[φ ⊙ φ']ʷ) Ps) (List.map (fun P => P[φ']ʷ) Ps')).
        { split; [ clear - HlQ' HPl HQl; rewrite !List.length_map in *; lia |].
          eapply (params_eq_trans _ p D _ _ _ Hl HΔ' HPl HQl); [ exact HlP' | exact HPQ | exact HQ' ]. }
        split; [ apply HPc; exact E1 |].
        intros Us' HUs'.
        destruct (decl_of_lookup _ _ _ _ _ HΔ' Hl) as [_ Hc0].
        pose proof (exps_eq_at_params_of_uparams D Δ' _ _ Hc0 HlP' (exps_eq_at_typed_r _ _ _ _ _ Hl HΔ' HPl E1) HUs') as E2.
        destruct HUs' as [HlU _].
        pose proof (decl_closed_nu D Hc0) as Hle0.
        rewrite List.length_firstn in HlU.
        replace Us' with (List.firstn (ind_nu D) (Us' ++ List.skipn (ind_nu D) (List.map (fun P => P[φ']ʷ) Ps')))
          by (apply firstn_app_exact; lia).
        apply HPc; destruct E1 as [HlE1 HE1]; destruct E2 as [HlE2 HE2]; split; [ congruence |].
        eapply (params_eq_trans _ p D _ _ _ Hl HΔ' HPl HlP'); [ rewrite <- HlE2; exact HlP' | exact HE1 | exact HE2 ].
Qed.

Section glu_univ_elem_cumulativity.
  #[local]
  Lemma glu_univ_elem_cumulativity_ge : forall {i j : uidx} {a P P' El El'},
      uidx_le i j ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El ->
      DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
      (forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® P') /\
        (forall Γ A M m, Γ ⊢ M : A ® m ∈ El -> Γ ⊢ M : A ® m ∈ El') /\
        (forall Γ A M m, Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El' -> Γ ⊢ M : A ® m ∈ El).
  Proof.
    simpl.
    intros * Hge Hglu Hglu'. gen El' P' j.
    glu_univ_elem_induction Hglu; repeat split; intros;
      try assert (DF a ≈ a ∈ per_univ_elem j ↘ in_rel) by (eapply per_univ_elem_cumu_uidx; eassumption);
      invert_glu_univ_elem Hglu';
      handle_functional_glu_univ_elem;
      simpl in *; destruct_glu_records;
      (** Every equation of a glued type is in the ambient universe of its
          index, the large universe [Typeω@(ulvl u)], so each is lifted along
          the order on large levels ([uidx_le_ulvl_le]). *)
      try match goal with Hge : uidx_le ?u ?v |- _ =>
        let Hl := fresh "Hl" in
        pose proof (uidx_le_ulvl_le _ _ Hge) as Hl;
        repeat match goal with H : _ ⍮ _ ⍮ _ ⊢ ?A ≈ ?B : Typeω@(ulvl u) |- _ =>
          let T := constr:(_ ⊢ A ≈ B : Typeω@(ulvl v)) in
          assert_fails (assert T by assumption);
          pose proof (lift_exp_eq_ge _ _ _ _ _ _ _ Hl H) end;
        repeat match goal with H : _ ⍮ _ ⍮ _ ⊢ ?A : Typeω@(ulvl u) |- _ =>
          let T := constr:(_ ⊢ A : Typeω@(ulvl v)) in
          assert_fails (assert T by assumption);
          pose proof (lift_exp_ge _ _ _ _ _ _ Hl H) end end;
      try solve [repeat split; intros; destruct_conjs; mauto 2 | intuition mauto 3].
    (** A small universe: only the ambient universe of its type-level gluing
        changes between the two indices; the level term, the element's gluing
        at the realiser of the level and its readback clause carry over. *)
    all: try solve
      [ econstructor;
        [ eassumption | econstructor; [ eassumption | eapply lift_exp_eq_ge; eassumption ]
        | econstructor; eassumption | eassumption ] ].

    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_typ_pred.
      econstructor; intros; mauto 4.
      + assert (Δ ⊢ IT[φ]ʷ ® IP) by mauto.
        enough (forall Γ A, Γ ⊢ A ® IP -> Γ ⊢ A ® IP') by mauto 4.
        eapply proj1; mautosolve 4.
      + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        apply_relation_equivalence.
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        assert (forall Γ A, Γ ⊢ A ® OP m equiv_m -> Γ ⊢ A ® OP' m equiv_m) by (eapply proj1; mauto).
        enough (Δ ⊢ OT[(ι φ),,M] ® OP m equiv_m) by mauto.
        enough (Δ ⊢ M : IT[φ]ʷ ® m ∈ IEl) by mauto.
        eapply IHHglu; mautosolve 4.
    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_exp_pred.
      handle_per_univ_elem_irrel.
      econstructor; intros; mauto 4.
      + enough (forall Γ A, Γ ⊢ A ® IP -> Γ ⊢ A ® IP') by mauto 4.
        eapply proj1; mautosolve 4.
      + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        handle_per_univ_elem_irrel.
        destruct_rel_mod_eval.
        destruct_rel_mod_app.
        handle_per_univ_elem_irrel.
        eexists; split; mauto 4.
        assert (forall Γ A M m, Γ ⊢ M : A ® m ∈ OEl n equiv_n -> Γ ⊢ M : A ® m ∈ OEl' n equiv_n) by (eapply proj1, proj2; mauto 4).
        enough (Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® fa ∈ OEl n equiv_n) by mauto 4.
        assert (Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl) by (eapply IHHglu; mauto 3).
        assert (exists mn, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv_n) by mauto 4.
        destruct_conjs.
        functional_eval_rewrite_clear; mautosolve 4.
    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_typ_pred.
      destruct_by_head pi_glu_exp_pred.
      handle_per_univ_elem_irrel.
      econstructor; intros; mauto.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      handle_per_univ_elem_irrel.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      handle_per_univ_elem_irrel.
      match goal with
      | _: ⟦ B ⟧ ρ ↦ n ↘ ?a |- _ =>
          rename a into b
      end.
      eexists; split; mauto 4.
      assert (forall Γ A M m, Γ ⊢ A ® OP n equiv_n -> Γ ⊢ M : A ® m ∈ OEl' n equiv_n -> Γ ⊢ M : A ® m ∈ OEl n equiv_n) by (eapply proj2, proj2; eauto 3).
      assert (Δ ⊢ OT[(ι φ),,N] ® OP n equiv_n) by mauto 4.
      enough (Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® fa ∈ OEl' n equiv_n) by mauto 4.
      assert (Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl') by (eapply IHHglu; mauto 3).
      assert (Δ ⊢ IT[φ]ʷ ® IP') by (eapply glu_univ_elem_trm_typ; mauto 2).
      assert (Δ ⊢ IT0[φ]ʷ ® IP') by mauto 2.
      assert (Δ ⊢ IT[φ]ʷ ≈ IT0[φ]ʷ : Typeω@(ulvl j)) as HITeq by mauto 2.
      assert (Δ ⊢ N : IT0[φ]ʷ ® n ∈ IEl') by (rewrite <- HITeq; mauto 3).
      assert (exists mn, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT0[(ι φ),,N] ® mn ∈ OEl' n equiv_n) by mauto 3.
      destruct_conjs.
      functional_eval_rewrite_clear.
      assert (DG b ∈ glu_univ_elem j ↘ OP' n equiv_n ↘ OEl' n equiv_n) as Hbj by mauto 3.
      assert (Δ ⊢ OT0[(ι φ),,N] ® OP' n equiv_n) by (eapply glu_univ_elem_trm_typ; mauto 3).
      (** Both codomains are glued at [j], so they are equal in [Typeω@(ulvl j)];
          the one at [i] is moved up by the induction hypothesis. *)
      match goal with HOT : _ ⊢ OT[(ι φ),,N] ® OP ?n0 ?eq0, Hev : ⟦ B ⟧ _ ↦ _ ↘ b |- _ =>
        assert (Δ ⊢ OT[(ι φ),,N] ® OP' n0 eq0)
          by (eapply (proj1 (H2 n0 eq0 b Hev j Hge (OP' n0 eq0) (OEl' n0 eq0) Hbj)); exact HOT) end.
      assert (Δ ⊢ OT[(ι φ),,N] ≈ OT0[(ι φ),,N] : Typeω@(ulvl j)) as Heq
        by (eapply (glu_univ_elem_typ_unique_upto_exp_eq' (i := j)); [ exact Hbj | eassumption | eassumption ]).
      rewrite Heq; eassumption.
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mauto.
      destruct_by_head neut_glu_typ_pred.
      econstructor; mautosolve 4.
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mautosolve 4.
    - assert (D0 = D) by congruence; subst D0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      edestruct (glu_univ_elem_cumu_ind i j p D ups ns NP NEl AP AEl DP DEl elem_rel NP0 NEl0 AP0 AEl0 DP0 DEl0 elem_rel0) as (L1 & L2 & L3);
        [ exact Hge | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | | | eassumption | | ].
      + intros k A0 vs b HA0 Hp Hb.
        match goal with IH : forall (k : nat) (A : typ) (vs : list domain) (b : domain), _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact HA0 | exact Hp | exact Hb | exact Hge |] end.
        match goal with Hg : forall (k : nat) (A : typ) (vs : list domain) (b : domain), _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + intros ms c gs k A0 vs b Hm Hc HA0 Hp Hb.
        match goal with IH : forall (ms : list domain) (c : String.string) (gs : list carg) (k : nat) (A : typ) (vs : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact Hm | exact Hc | exact HA0 | exact Hp | exact Hb | exact Hge |] end.
        match goal with Hg : forall (ms : list domain) (c : String.string) (gs : list carg) (k : nat) (A : typ) (vs : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + intros ms c gs gs1 t gs2 ws k B ys b Hm Hc Heq Hw HB Hy Hb.
        match goal with IH : forall (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg)
                                (ws : list domain) (k : nat) (B : typ) (ys : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact Hm | exact Hc | exact Heq | exact Hw | exact HB | exact Hy | exact Hb | exact Hge |] end.
        match goal with Hg : forall (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg)
                                (ws : list domain) (k : nat) (B : typ) (ys : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + eapply L1; eassumption.
    - assert (D0 = D) by congruence; subst D0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      edestruct (glu_univ_elem_cumu_ind i j p D ups ns NP NEl AP AEl DP DEl elem_rel NP0 NEl0 AP0 AEl0 DP0 DEl0 elem_rel0) as (L1 & L2 & L3);
        [ exact Hge | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | | | eassumption | | ].
      + intros k A0 vs b HA0 Hp Hb.
        match goal with IH : forall (k : nat) (A : typ) (vs : list domain) (b : domain), _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact HA0 | exact Hp | exact Hb | exact Hge |] end.
        match goal with Hg : forall (k : nat) (A : typ) (vs : list domain) (b : domain), _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + intros ms c gs k A0 vs b Hm Hc HA0 Hp Hb.
        match goal with IH : forall (ms : list domain) (c : String.string) (gs : list carg) (k : nat) (A : typ) (vs : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact Hm | exact Hc | exact HA0 | exact Hp | exact Hb | exact Hge |] end.
        match goal with Hg : forall (ms : list domain) (c : String.string) (gs : list carg) (k : nat) (A : typ) (vs : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + intros ms c gs gs1 t gs2 ws k B ys b Hm Hc Heq Hw HB Hy Hb.
        match goal with IH : forall (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg)
                                (ws : list domain) (k : nat) (B : typ) (ys : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact Hm | exact Hc | exact Heq | exact Hw | exact HB | exact Hy | exact Hb | exact Hge |] end.
        match goal with Hg : forall (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg)
                                (ws : list domain) (k : nat) (B : typ) (ys : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + eapply L2; eassumption.
    - assert (D0 = D) by congruence; subst D0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      edestruct (glu_univ_elem_cumu_ind i j p D ups ns NP NEl AP AEl DP DEl elem_rel NP0 NEl0 AP0 AEl0 DP0 DEl0 elem_rel0) as (L1 & L2 & L3);
        [ exact Hge | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | | | eassumption | | ].
      + intros k A0 vs b HA0 Hp Hb.
        match goal with IH : forall (k : nat) (A : typ) (vs : list domain) (b : domain), _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact HA0 | exact Hp | exact Hb | exact Hge |] end.
        match goal with Hg : forall (k : nat) (A : typ) (vs : list domain) (b : domain), _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + intros ms c gs k A0 vs b Hm Hc HA0 Hp Hb.
        match goal with IH : forall (ms : list domain) (c : String.string) (gs : list carg) (k : nat) (A : typ) (vs : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact Hm | exact Hc | exact HA0 | exact Hp | exact Hb | exact Hge |] end.
        match goal with Hg : forall (ms : list domain) (c : String.string) (gs : list carg) (k : nat) (A : typ) (vs : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + intros ms c gs gs1 t gs2 ws k B ys b Hm Hc Heq Hw HB Hy Hb.
        match goal with IH : forall (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg)
                                (ws : list domain) (k : nat) (B : typ) (ys : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> _ -> _ -> forall j0 : uidx, _ |- _ =>
          eapply IH; [ exact Hm | exact Hc | exact Heq | exact Hw | exact HB | exact Hy | exact Hb | exact Hge |] end.
        match goal with Hg : forall (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg)
                                (ws : list domain) (k : nat) (B : typ) (ys : list domain) (b : domain),
                          _ -> _ -> _ -> _ -> _ -> _ -> _ -> glu_univ_elem j _ _ b |- _ =>
          eapply Hg; eassumption end.
      + eapply L3; eassumption.
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
Corollary glu_univ_elem_exp_lower_uidx : forall {i j : uidx} {a P P' El El' Γ A M m},
    uidx_le i j ->
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
Corollary glu_univ_elem_typ_cumu_ge_uidx : forall {i j : uidx} {a P P' El El' Γ A},
    uidx_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros * Hle Hi Hj HA.
  destruct (glu_univ_elem_cumulativity_ge Hle Hi Hj) as (Htyp & _); exact (Htyp _ _ HA).
Qed.

Corollary glu_univ_elem_exp_cumu_ge_uidx : forall {i j : uidx} {a P P' El El' Γ A M m},
    uidx_le i j ->
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

Lemma glu_univ_elem_exp_conv : forall {i : nat} {j : nat} {k : nat} {a a' P P' El El' Γ A M m},
    Dom a ≈ a' ∈ per_univ k ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ A ® P' ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros * [] ? ? ? ?.
  assert (Dom a ≈ a' ∈ per_univ (max i k)) as Haa' by (eexists; mauto using per_univ_elem_cumu_max_right).
  assert (exists P El, DG a ∈ glu_univ_elem (max i k) ↘ P ↘ El) as [Pik [Elik]] by mauto using glu_univ_elem_cumu_max_left.
  assert (DG a' ∈ glu_univ_elem (max i k) ↘ Pik ↘ Elik) by (setoid_rewrite <- Haa'; eassumption).
  assert (Γ ⊢ M : A ® m ∈ Elik) by (eapply glu_univ_elem_exp_cumu_max_left; [| | eassumption]; eassumption).
  assert (exists P El, DG a' ∈ glu_univ_elem (max j (max i k)) ↘ P ↘ El) as [Ptop [Eltop]] by mauto using glu_univ_elem_cumu_max_right.
  assert (Γ ⊢ M : A ® m ∈ Eltop) by (eapply glu_univ_elem_exp_cumu_max_right; [| | eassumption]; eassumption).
  eapply glu_univ_elem_exp_lower_max_left; mauto.
Qed.

(** The same along indices: an element moves to the gluing of a related
    type at any index, given the type's gluing there. *)
Lemma uidx_le_ul_max : forall (u : uidx) n, ulvl u <= n -> uidx_le u (ul n).
Proof. intros u0 n0 H; destruct u0; cbn in *; [ exact I | lia ]. Qed.

Lemma glu_univ_elem_exp_conv_uidx : forall {i j k : uidx} {a a' P P' El El' Γ A M m},
    Dom a ≈ a' ∈ per_univ k ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ A ® P' ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros * [R HR] Hi Hj HM HA.
  set (n := Nat.max (ulvl i) (Nat.max (ulvl j) (ulvl k))).
  assert (Hin : uidx_le i (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  assert (Hjn : uidx_le j (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  assert (Hkn : uidx_le k (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_uidx Hin Hi) as (Pn & Eln & Hn).
  assert (HMn : Γ ⊢ M : A ® m ∈ Eln) by (eapply glu_univ_elem_exp_cumu_ge_uidx; [ exact Hin | exact Hi | exact Hn | exact HM ]).
  assert (Hn' : DG a' ∈ glu_univ_elem (ul n) ↘ Pn ↘ Eln)
    by (eapply glu_univ_elem_resp_per_univ; [ eexists; eapply per_univ_elem_cumu_uidx; eassumption | exact Hn ]).
  eapply glu_univ_elem_exp_lower_uidx; [ exact Hjn | exact Hj | exact Hn' | exact HA | exact HMn ].
Qed.

(** ** The Order on Levels, Syntactically

    Two level terms glued to levels in the canonical order ([per_sublvl]) are
    in the syntactic order [maxl t t' ≈ t'].  Each is equal to its readback,
    and the readbacks are canonical levels in [lvl_le], which the level
    equations turn into the equation ([lvl_exp_of_le]).  This is the
    syntactic content of a semantic subtyping between small universes. *)
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
  destruct (Hle (length Γ)) as [[c xs] [d ys] HL HL' HLL'].
  assert (Γ ⊢ t ≈ nf_lvl_of (c, xs) : Level@n) as Htc
    by (rewrite <- (exp_wk_id t); eapply glu_lvl_readback; mauto 3).
  assert (Γ ⊢ t' ≈ nf_lvl_of (d, ys) : Level@n) as Htd
    by (rewrite <- (exp_wk_id t'); eapply glu_lvl_readback; mauto 3).
  (** The readbacks are canonical levels of sort [n], their atoms typed at
      their own sorts, which the absorption step of [lvl_exp_of_le] needs. *)
  assert (nf_lvl_ws n Γ (nf_lvl_of (c, xs))) as [Hc Hxs]
    by (eapply glu_lvl_ws_readback; [ exact Ht | mauto 3 | exact HL ]).
  assert (nf_lvl_ws n Γ (nf_lvl_of (d, ys))) as [Hd Hys]
    by (eapply glu_lvl_ws_readback; [ exact Ht' | mauto 3 | exact HL' ]).
  unfold nf_lvl_of in *; cbn [nf_to_exp fst snd] in *.
  transitivity (maxl (lvl_exp_of c (la_to_list xs)) (lvl_exp_of d (la_to_list ys)));
    [ apply wf_exp_eq_maxl_cong; assumption |].
  transitivity (lvl_exp_of d (la_to_list ys));
    [ apply lvl_exp_of_le; assumption | symmetry; assumption ].
Qed.

Lemma glu_univ_elem_per_subtyp_typ_escape : forall {i : uidx} {a a' P P' El El' Γ A A'},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ⊆ A'.
Proof.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  gen A' A Γ. gen El' El P' P.
  induction Hsubtyp; intros; subst;
    (** Two related inductive types are equal. *)
    try (match goal with H : DF d_ind _ _ ≈ d_ind _ _ ∈ per_univ_elem _ ↘ _ |- _ =>
           eapply wf_subtyp_refl'; eapply glu_univ_elem_per_univ_typ_escape;
             [ eexists; exact H | exact Hglu | exact Hglu' | exact HA | exact HA' ] end; fail);
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    handle_per_univ_elem_irrel;
    destruct_by_head pi_glu_typ_pred;
    saturate_glu_by_per;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    try solve [simpl in *; mauto 3].
  - match_by_head (per_bot b b') ltac:(fun H => specialize (H (length Γ)) as [V []]).
    simpl in *.
    destruct_conjs.
    assert (Γ ⊢ A ≈ V : Typeω@(ulvl i)) as HAV by (rewrite <- (exp_wk_id A); mauto 4).
    assert (Γ ⊢ A' ≈ V : Typeω@(ulvl i)) as HA'V by (rewrite <- (exp_wk_id A'); mauto 4).
    rewrite HAV, HA'V.
    (** Both read back to the same neutral, so the goal is reflexivity at the
        large universe of the index. *)
    gen_presups.
    eapply wf_subtyp_refl_typ; eassumption.
  (** [Level], [⊤] and [⊥]: both sides are equal to the same closed type
      in the ambient universe, so the goal is reflexivity, at the large level
      the index lives at. *)
  - simpl in *; gen_presups; bulky_rewrite; eapply (wf_subtyp_refl_typ _ _ _ _ 0); mauto 3.
  - simpl in *; gen_presups; bulky_rewrite; eapply (wf_subtyp_refl_typ _ _ _ _ 0); mauto 3.
  - simpl in *; gen_presups; bulky_rewrite; eapply (wf_subtyp_refl_typ _ _ _ _ 0); mauto 3.
  (** A universe below a larger one, in either tier, and a small one below a
      large one.  Two small universes are below each other by the syntactic
      order on their glued level terms ([glu_lvl_sublvl_eq]); a small one is
      below a large one because its level term is a level. *)
  - simpl in *; bulky_rewrite; mauto 3.
  - simpl in *; destruct_conjs; destruct_glu_records; gen_presups.
    match goal with
    | Hle : per_sublvl ?l ?l', Hl : per_lvl ?l ?l, Hl' : per_lvl ?l' ?l',
        Ht : glu_lvl ?nt _ ?t ?l, Ht' : glu_lvl ?nt' _ ?t' ?l',
        Heq : _ ⊢ A ≈ Type⟨?t⟩ : _, Heq' : _ ⊢ A' ≈ Type⟨?t'⟩ : _ |- _ =>
        (** The two level terms are glued at their own sorts; both move to
            the larger of the two, where the order on levels is stated. *)
        let HΓ := fresh "HΓ" in
        assert (HΓ : ⊢ Γ) by (gen_presups; assumption);
        assert (Γ ⊢ t : Level@(Nat.max nt nt'))
          by (eapply glu_lvl_escape; [ exact Hl | eapply glu_lvl_sort_le; [ | exact Ht ] | exact HΓ ]; lia);
        assert (Γ ⊢ t' : Level@(Nat.max nt nt'))
          by (eapply glu_lvl_escape; [ exact Hl' | eapply glu_lvl_sort_le; [ | exact Ht' ] | exact HΓ ]; lia);
        rewrite Heq, Heq';
        eapply wf_subtyp_suniv; [ assumption | eassumption | eassumption |];
        eapply glu_lvl_sublvl_eq;
          [ exact HΓ | exact Hl | exact Hl' | exact Hle
          | eapply glu_lvl_sort_le; [ | exact Ht ]
          | eapply glu_lvl_sort_le; [ | exact Ht' ] ]; lia
    end.
  - simpl in *; destruct_conjs; destruct_glu_records; gen_presups.
    match goal with
    | Ht : glu_lvl ?nt _ ?t ?l, Heq : _ ⊢ A ≈ Type⟨?t⟩ : _ |- _ =>
        assert (exists k, Γ ⊢ t : Level@k) as [? ?] by (eapply wf_univ_lvl_inversion; eassumption);
        rewrite Heq
    end.
    bulky_rewrite; mauto 3.
  - destruct_by_head pi_glu_typ_pred.
    rename x into IP. rename x0 into IEl. rename x1 into OP. rename x2 into OEl.
    rename A0 into A'. rename IT0 into IT'. rename OT0 into OT'.
    rename x3 into OP'. rename x4 into OEl'.
    assert (Γ ⊢ IT ® IP) by (rewrite <- (exp_wk_id IT); mauto 4).
    assert (Γ ⊢ IT' ® IP) by (rewrite <- (exp_wk_id IT'); mauto 4).
    do 2 bulky_rewrite1.
    assert (Γ ⊢ IT ≈ IT' : Typeω@(ulvl i)) as HITeq by mauto 4.
    enough (Γ ▹ IT' ⊢ OT ⊆ OT') by mauto 3.
    assert (Dom ⇑! a (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel) as equiv_len_len' by (eapply per_bot_then_per_elem; mauto 4).
    assert (Dom ⇑! a (length Γ) ≈ ⇑! a (length Γ) ∈ in_rel) as equiv_len_len by (eapply per_bot_then_per_elem; mauto 4).
    assert (Dom ⇑! a' (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel) as equiv_len'_len' by (eapply per_bot_then_per_elem; mauto 4).
    handle_per_univ_elem_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    apply_relation_equivalence.
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    match goal with
    | _: (⟦ B ⟧ ρ ↦ ⇑! a (length Γ) ↘ ?a0),
        _: ⟦ B' ⟧ ρ' ↦ ⇑! a' (length Γ) ↘ ?a0' |- _ =>
        rename a0 into b;
        rename a0' into b'
    end.
    assert (DG b ∈ glu_univ_elem i ↘ OP ⇑! a (length Γ) equiv_len_len ↘ OEl ⇑! a (length Γ) equiv_len_len) by mauto 4.
    assert (DG b' ∈ glu_univ_elem i ↘ OP' ⇑! a' (length Γ) equiv_len'_len' ↘ OEl' ⇑! a' (length Γ) equiv_len'_len') by mauto 4.
    assert (Γ ▹ IT' ⊢ OT ® OP ⇑! a (length Γ) equiv_len_len).
    {
      assert (Γ ▹ IT ⊢ #0 : IT[↑]ʷ ® ⇑! a (length Γ) ∈ IEl) by (eapply var0_glu_elem; mauto 3).
      assert (⊢ Γ ▹ IT) by mauto 3.
      assert (Γ ▹ IT ⊢ OT[ι ↑,,#0] ® OP ⇑! a (length Γ) equiv_len_len) by mauto 4.
      assert (Γ ▹ IT ⊢ OT ® OP ⇑! a (length Γ) equiv_len_len)
        by (eapply glu_univ_elem_typ_resp_exp_eq; [ eassumption | eassumption
                                                  | eapply (shift_var_eq _ _ (Typeω@(ulvl i)) _ (ul (ulvl i))); eassumption ]).
      eapply glu_univ_elem_typ_resp_ctxsub; [ eassumption | eassumption | mauto 4 ].
    }
    assert (Γ ▹ IT' ⊢ OT' ® OP' ⇑! a' (length Γ) equiv_len'_len').
    {
      assert (Γ ▹ IT' ⊢ #0 : IT'[↑]ʷ ® ⇑! a' (length Γ) ∈ IEl) by (eapply var0_glu_elem; mauto 3).
      assert (⊢ Γ ▹ IT') by mauto 3.
      assert (Γ ▹ IT' ⊢ OT'[ι ↑,,#0] ® OP' ⇑! a' (length Γ) equiv_len'_len') by mauto 4.
      eapply glu_univ_elem_typ_resp_exp_eq; [ eassumption | eassumption
                                            | eapply (shift_var_eq _ _ (Typeω@(ulvl i)) _ (ul (ulvl i))); eassumption ].
    }
    mauto 3.
Qed.

Hint Resolve glu_univ_elem_per_subtyp_typ_escape : mctt.

Lemma glu_univ_elem_per_subtyp_trm_if : forall {i : uidx} {a a' P P' El El' Γ A A' M m},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  assert (Γ ⊢ A ⊆ A') by (eapply glu_univ_elem_per_subtyp_typ_escape; only 4: eapply glu_univ_elem_trm_typ; mauto).
  gen m M A' A. gen Γ. gen El' El P' P.
  induction Hsubtyp; intros; subst;
    (** Two related inductive types have the same gluing. *)
    try (match goal with H : DF d_ind _ _ ≈ d_ind _ _ ∈ per_univ_elem _ ↘ _ |- _ =>
           let Hu := fresh "Hu" in
           assert (Hu : Dom _ ≈ _ ∈ per_univ _) by (eexists; exact H);
           destruct (glu_univ_elem_per_univ_typ_iff Hu Hglu Hglu') as [_ HEE];
           apply HEE; eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hglu | exact HA' |];
           eapply glu_univ_elem_per_univ_typ_escape;
             [ eexists; exact H | exact Hglu | exact Hglu' | eapply glu_univ_elem_trm_typ; [ exact Hglu | exact HA' ] | exact HA ] end; fail);
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    handle_per_univ_elem_irrel;
    repeat invert_glu_rel1;
    saturate_glu_by_per;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    repeat invert_glu_rel1;
    try solve [simpl in *; intuition mauto 3].
  (** A type of levels below one of a larger sort: the element is a level of
      the larger sort, and its readback equation moves there
      ([glu_lvl_sort_le]). *)
  all: try solve [ simpl in *; destruct_conjs; econstructor;
                   [ mauto 3 | eapply per_lvl_at_mono; eassumption | eapply glu_lvl_sort_le; eassumption ] ].
  - match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Γ)) as [V []]).
    econstructor; mauto 3.
    + econstructor; mauto 3.
    + intros.
      match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Δ)) as [? []]).
      functional_read_rewrite_clear.
      assert (Δ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ) by mauto 3.
      assert (Δ ⊢ M[φ]ʷ ≈ M' : A[φ]ʷ) by mauto 3.
      mauto 3.
  - simpl in *.
    destruct_conjs.
    econstructor; [ mauto 3 | mauto 3 |].
    assert (exists P El, DG m ∈ glu_univ_elem j ↘ P ↘ El) as [? [?]] by mauto 3.
    glu_witness2; mauto 3.
    eapply glu_univ_elem_typ_cumu_ge; revgoals; mautosolve 3.
  (** Small universe below small universe: the element is glued at the larger
      realiser by cumulativity (the order on levels bounds the realisers), and
      its readback moves by subsumption along [A ⊆ A']. *)
  - simpl in *; destruct_conjs.
    match goal with
    | Hg : glu_univ_elem (us (dlvl_real ?l)) ?P0 _ m, Hp : ?P0 Γ M, Hle : per_sublvl ?l ?l' |- _ =>
        assert (exists P El, DG m ∈ glu_univ_elem (us (dlvl_real l')) ↘ P ↘ El) as [Pj [Elj Hj]]
          by (eapply (glu_univ_elem_cumu_ge_uidx (i := us (dlvl_real l)));
              [ cbn; apply per_sublvl_real; exact Hle | exact Hg ]);
        econstructor;
        [ mauto 3
        | glu_witness2; eassumption
        | glu_witness2;
          [ exact Hj
          | eapply (glu_univ_elem_typ_cumu_ge_uidx (i := us (dlvl_real l)) (j := us (dlvl_real l')));
            [ cbn; apply per_sublvl_real; exact Hle | exact Hg | exact Hj | exact Hp ] ]
        | intros Δ φ W Hφ Hr; eapply wf_exp_eq_subtyp'; [ eauto | mauto 3 ] ]
    end.
  (** Small universe below a large one: the element is glued at the large
      index, by cumulativity across the tiers. *)
  - simpl in *; destruct_conjs.
    match goal with Hg : glu_univ_elem (us ?n) ?P0 _ m, Hp : ?P0 Γ M |- _ =>
      assert (exists P El, DG m ∈ glu_univ_elem (ul j) ↘ P ↘ El) as [Pj [Elj Hj]]
        by (eapply (glu_univ_elem_cumu_ge_uidx (i := us n)); [ exact I | exact Hg ]);
      econstructor; [ mauto 3 | assumption |];
      glu_witness2; [ exact Hj |];
      eapply (glu_univ_elem_typ_cumu_ge_uidx (i := us n) (j := ul j));
        [ exact I | exact Hg | exact Hj | exact Hp ]
    end.
  - rename A0 into A'.
    rename IT0 into IT'. rename OT0 into OT'.
    rename x into IP. rename x0 into IEl.
    rename x1 into OP. rename x2 into OEl.
    rename x3 into OP'. rename x4 into OEl'.
    handle_per_univ_elem_irrel.
    econstructor; mauto 3.
    + enough (Sub Πᵈ a ρ B <: Πᵈ a' ρ' B' at i) by (eapply per_elem_subtyping; try eassumption).
      econstructor; mauto 3.
    + intros.
      assert (Γ ⊢ IT ® IP) by (rewrite <- (exp_wk_id IT); mauto 4).
      assert (Γ ⊢ IT' ® IP) by (rewrite <- (exp_wk_id IT'); mauto 4).
      assert (Δ ⊢ IT'[φ]ʷ ≈ IT[φ]ʷ : Typeω@(ulvl i)) by (symmetry; mauto 4 using glu_univ_elem_per_univ_typ_escape).
      assert (Δ ⊢ N : IT'[φ]ʷ ® n ∈ IEl) by (simpl; bulky_rewrite1; eassumption).
      assert (exists mn : domain, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT'[(ι φ),,N] ® mn ∈ OEl n equiv_n) by mauto 3.
      destruct_conjs.
      eexists; split; mauto 3.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      match goal with
      | _: (⟦ B ⟧ ρ ↦ n ↘ ?a),
          _: ⟦ B' ⟧ ρ' ↦ n ↘ ?a' |- _ =>
          rename a into b;
          rename a' into b'
      end.
      assert (DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n) by mauto 3.
      assert (DG b' ∈ glu_univ_elem i ↘ OP' n equiv_n ↘ OEl' n equiv_n) by mauto 3.
      assert (Δ ⊢ OT'[(ι φ),,N] ® OP n equiv_n) by (eapply glu_univ_elem_trm_typ; mauto 3).
      assert (Sub b <: b' at i) by mauto 3.
      assert (Δ ⊢ OT'[(ι φ),,N] ⊆ OT[(ι φ),,N]) by mauto 3.
      intuition.
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

Lemma mk_glu_rel_exp_with_sub' : forall {i : nat} {Δ A M σ ρ a m},
    ⟦ A ⟧ ρ ↘ a ->
    ⟦ M ⟧ ρ ↘ m ->
    (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ] : A[σ] ® m ∈ El) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

Hint Resolve mk_glu_rel_exp_with_sub' : mctt.

Lemma mk_glu_rel_exp_with_sub'' : forall {i : nat} {Δ A M σ ρ a m},
    ⟦ A ⟧ ρ ↘ a ->
    ⟦ M ⟧ ρ ↘ m ->
    Dom a ≈ a ∈ per_univ i ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ] : A[σ] ® m ∈ El) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? ? [] ?.
  assert (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) as [? []] by mauto.
  eapply mk_glu_rel_exp_with_sub'; mauto.
Qed.

Hint Resolve mk_glu_rel_exp_with_sub'' : mctt.

Lemma glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : forall {i : nat} {Δ A M σ Γ ρ},
  Δ ⊢ˢ σ : Γ ->
  glu_rel_exp_with_sub i Δ M A σ ρ ->
  glu_rel_exp_with_sub (S i) Δ A Typeω@i σ ρ.
Proof.
  intros * ? [].
  econstructor; mauto.
  assert (Δ ⊢ A[σ] : Typeω@i) by (eapply (glu_univ_elem_trm_univ_lvl (ul i)); [ reflexivity | eassumption.. ]).
  repeat split; try glu_witness2; mauto 3.
  eapply (glu_univ_elem_trm_typ (ul i)); eassumption.
Qed.

Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : mctt.

Lemma glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : forall {i : nat} {Δ A} {j : nat} {σ ρ},
  glu_rel_exp_with_sub i Δ A Typeω@j σ ρ ->
  glu_rel_typ_with_sub j Δ A σ ρ.
Proof.
  intros * [].
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  destruct_glu_records.
  econstructor; mauto 3.
Qed.

Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mctt.

Lemma glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : forall {Δ A} {j : nat} {σ Γ ρ},
  Δ ⊢ˢ σ : Γ ->
  glu_rel_typ_with_sub j Δ A σ ρ ->
  glu_rel_exp_with_sub (S j) Δ A Typeω@j σ ρ.
Proof.
  intros * ? [].
  simplify_evals.
  econstructor; mauto.
  assert (Δ ⊢ A[σ] : Typeω@j) by (eapply (glu_univ_elem_univ_lvl (ul j)); [ reflexivity | eassumption.. ]).
  repeat split; try glu_witness2; mauto 3.
Qed.

Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mctt.

(** *** Lemmas for [glu_ctx_env] *)

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
  - destruct_by_head cons_glu_sub_pred.
    econstructor; mauto 4.
    (** The tail: [Wk] postcomposed with either side, by the induction hypothesis. *)
    2: eapply IHglu_ctx_env;
         [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ▹ A ⊢ A[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; mauto 3).
    assert (Δ ⊢ A[↑]ʷ[σ] ≈ A[↑]ʷ[σ'] : Typeω@i) as <- by mauto 3.
    assert (Δ ⊢ #0[σ] ≈ #0[σ'] : A[↑]ʷ[σ]) as <- by mauto 3.
    eassumption.
  - (** A definition entry: as an assumption entry, and the tie does not
        mention [σ]. *)
    destruct_by_head cons_def_glu_sub_pred.
    econstructor; mauto 4.
    2: eapply IHglu_ctx_env;
         [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
    assert (⊢ Γ ▸ A ≔ M) by mauto 3.
    assert (Γ ▸ A ≔ M ⊢ A[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; mauto 3).
    assert (Δ ⊢ A[↑]ʷ[σ] ≈ A[↑]ʷ[σ'] : Typeω@i) as <- by mauto 3.
    assert (Δ ⊢ #0[σ] ≈ #0[σ'] : A[↑]ʷ[σ]) as <- by mauto 3.
    eassumption.
  - (** A module slot: the tie does not mention [σ]. *)
    destruct_by_head cons_mod_glu_sub_pred.
    econstructor; [ exact Hσ' | eassumption |].
    eapply IHglu_ctx_env;
      [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
Qed.

Add Parametric Morphism Sb Γ (H : glu_ctx_env Sb Γ) Δ : (Sb Δ)
    with signature wf_sub_eq gc_deps gc_stack Δ Γ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; intros; eapply glu_ctx_env_sub_resp_sub_eq; mauto 2 using wf_sub_eq_sym.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq : forall {i : nat} {Γ A Sb Δ σ σ' ρ},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊢ A : Typeω@i ->
    Δ ⊢ˢ σ ≈ σ' : Γ ▹ A ->
    Δ ⊢ˢ σ ® ρ ∈ cons_glu_sub_pred i Γ A Sb ->
    Δ ⊢ˢ σ' ® ρ ∈ cons_glu_sub_pred i Γ A Sb.
Proof.
  intros * Hglu HA Heq Hσ.
  dependent destruction Hσ.
  (pose proof (wf_sub_eq_left _ _ _ _ _ _ Heq) as Hσ; pose proof (wf_sub_eq_right _ _ _ _ _ _ Heq) as Hσ').
  assert (⊢ Γ ▹ A) by mauto 3.
  assert (Γ ▹ A ⊢ˢ Wk : Γ) by mauto 3.
  assert (Γ ▹ A ⊢ A[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; mauto 3).
  assert (Δ ⊢ˢ Wk ⨟ σ : Γ) by mauto 3.
  assert (Δ ⊢ˢ Wk ⨟ σ' : Γ) by mauto 3.
  assert (Δ ⊢ˢ Wk ⨟ σ ≈ Wk ⨟ σ' : Γ) by mauto 3.
  econstructor; mauto 3.
  - assert (Δ ⊢ A[↑]ʷ[σ] ≈ A[↑]ʷ[σ'] : Typeω@i) as <- by mauto 4.
    assert (Δ ⊢ #0[σ] ≈ #0[σ'] : A[↑]ʷ[σ]) as <-; mauto 3.
  - assert (Δ ⊢ˢ Wk ⨟ σ ≈ Wk ⨟ σ' : Γ) as <-; eassumption.
Qed.

Add Parametric Morphism i Γ A Sb Δ (Hglu : EG Γ ∈ glu_ctx_env ↘ Sb) (HA : Γ ⊢ A : Typeω@i) : (cons_glu_sub_pred i Γ A Sb Δ)
    with signature wf_sub_eq gc_deps gc_stack Δ (Γ ▹ A) ==> eq ==> iff as cons_glu_sub_pred_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq, wf_sub_eq_sym.
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
  4:{ (** A module slot: the tie is part of the gluing. *)
    apply_predicate_equivalence.
    destruct_by_head cons_mod_glu_sub_pred.
    invert_per_ctx_env Hper.
    apply_predicate_equivalence.
    match goal with E : env_rel <~> _ |- _ => apply E end.
    repeat split; try eassumption; eapply IHHglu; eassumption. }
  3:{ (** A definition entry, read against its canonical context PER: the
        tie is part of the gluing. *)
    apply_predicate_equivalence.
    destruct_by_head cons_def_glu_sub_pred.
    assert (HAs : Γ ⊨ A : Typeω@i) by (apply completeness_fundamental_exp; eassumption).
    assert (HMs : Γ ⊨ M : A) by (apply completeness_fundamental_exp; eassumption).
    assert (⊢ Γ) by mauto 3.
    destruct (rel_ctx_wf_per_ctx_env (completeness_fundamental_ctx _ ltac:(eassumption))) as [tail_rel Htail].
    pose proof (per_ctx_env_of_def Htail HAs HMs) as Hd.
    assert (E : env_rel <~> per_env_extend_def A M tail_rel) by (eapply per_ctx_env_right_irrel; eassumption).
    apply E.
    assert (Hρ : Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (eapply IHHglu; eassumption).
    destruct (rel_exp_of_typ_inversion_simple_at Htail HAs _ _ Hρ) as [a1 [a2 [Ha1 [Ha2 [R HR]]]]].
    functional_eval_rewrite_clear.
    constructor; [ split; [ assumption |] | assumption | assumption ].
    eapply per_head_of; [ eassumption | eassumption | exact HR |].
    eapply glu_univ_elem_per_elem; eassumption. }
  all: invert_per_ctx_env Hper;
    apply_predicate_equivalence;
    handle_per_ctx_env_irrel;
    mauto 3.

  rename i0 into j.
  inversion_clear_by_head cons_glu_sub_pred.
  assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by intuition.
  destruct_rel_typ.
  handle_per_univ_elem_irrel.
  assert (exists P' El', DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El') as [? []] by mauto 3 using glu_univ_elem_cumu_max_left.
  eexists; eapply glu_univ_elem_per_elem; mauto using per_univ_elem_cumu_max_right.
  eapply glu_univ_elem_exp_cumu_max_left; [| | eassumption]; eassumption.
Qed.

Lemma glu_ctx_env_wf_ctx : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    ⊢ Γ.
Proof.
  induction 1; intros; mauto 3.
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

  (** An assumption entry and a definition entry alike: the tie does not
      depend on the level. *)
  (** A module slot: the tie does not depend on the tail's derivation. *)
  3:{ assert (HT : TSb -∙> TSb0) by intuition.
      intros Δ' σ' ρ' []; econstructor; [ eassumption | eassumption | apply HT; eassumption ]. }
  all: rename i0 into j.
  all: rename TSb0 into TSb'.
  all: assert (TSb -∙> TSb') by intuition.
  all: intros Δ' σ' ρ' [].
  all: assert (Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb') by intuition.
  all: assert (glu_rel_typ_with_sub j Δ A (Wk ⨟ σ) ρ↯) as [] by mauto 3.
  all: destruct_rel_typ.
  all: handle_functional_glu_univ_elem.
  all: econstructor; mauto 4.
  all: eapply (@glu_univ_elem_exp_conv i j i a a P P0 El El0); [ mauto 3 | eassumption | eassumption | eassumption | ].
  all: rewrite exp_sub_shift.
  all: eassumption.
Qed.

Corollary functional_glu_ctx_env : forall {Γ Sb Sb'},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EG Γ ∈ glu_ctx_env ↘ Sb' ->
    (Sb <∙> Sb').
Proof.
  intros; split; eapply glu_ctx_env_resp_per_ctx_helper; eassumption.
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_elem_bot_morphism_iff4_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff4_Proper.
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
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : mctt.
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


Lemma glu_ctx_env_cons_clean_inversion : forall {Γ TSb A Sb},
  EG Γ ∈ glu_ctx_env ↘ TSb ->
  EG Γ ▹ A ∈ glu_ctx_env ↘ Sb ->
  exists i,
    Γ ⊢ A : Typeω@i /\
      (forall Δ σ ρ,
          Δ ⊢ˢ σ ® ρ ∈ TSb ->
          glu_rel_typ_with_sub i Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred i Γ A TSb).
Proof.
  intros.
  simpl in *.
  match_by_head glu_ctx_env progressive_invert.
  apply_functional_glu_ctx_env.
  (** [i] has to be given: the cumulativity hints let [intuition] pick any
      larger level for the type, which then no longer matches [TSb]'s. *)
  exists i; intuition.
  assert (Sb <∙> cons_glu_sub_pred i Γ A TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Lemma glu_ctx_env_cons_def_clean_inversion : forall {Γ TSb A M Sb},
  EG Γ ∈ glu_ctx_env ↘ TSb ->
  EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ Sb ->
  exists i,
    Γ ⊢ A : Typeω@i /\
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
  exists i; intuition.
  assert (Sb <∙> cons_def_glu_sub_pred i Γ A M TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

End Fixed_GCtx.

Ltac invert_glu_ctx_env H :=
  (unshelve eapply (glu_ctx_env_cons_clean_inversion _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? []]])
  + (unshelve eapply (glu_ctx_env_cons_def_clean_inversion _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? [? [? [? []]]]])
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
  (** A module slot: [ρ] does not move, so the tie is unchanged. *)
  3:{ destruct_by_head cons_mod_glu_sub_pred.
      econstructor; [ rewrite sb_wk_compose; mauto 3 | eassumption |].
      assert (Δ' ⊢ˢ (sb_wk (Wk ⨟ σ) φ) ® ρ↯ ∈ TSb) by mauto 3.
      assert (Δ' ⊢ˢ (sb_wk (Wk ⨟ σ) φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
      eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | eassumption | ].
      eapply wf_sub_eq_of_sb_eq; [ eassumption | apply sb_wk_shift_pre ]. }

  (** An assumption entry and a definition entry alike: [ρ] does not move, so
      the tie is unchanged.  Each leaves the substitution, the head and the
      tail. *)
  all: try destruct_by_head cons_glu_sub_pred.
  all: try destruct_by_head cons_def_glu_sub_pred.
  all: econstructor; mauto 3.
  1,4: (rewrite sb_wk_compose; mauto 3).
  1,3: (rewrite <- !exp_wk_sub; eapply glu_univ_elem_exp_monotone; eassumption).
  all: assert (Δ' ⊢ˢ (sb_wk (Wk ⨟ σ) φ) ® ρ↯ ∈ TSb) by mauto 3.
  all: assert (Δ' ⊢ˢ (sb_wk (Wk ⨟ σ) φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
  all: eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | eassumption | ].
  all: eapply wf_sub_eq_of_sb_eq; [ eassumption | apply sb_wk_shift_pre ].
Qed.

(** Extension by any entry whose term projection glues as the head. *)
Lemma cons_glu_sub_pred_helper_gen : forall {Γ Sb Δ σ ρ A a} {i : nat} {P El en c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ sentry_exp en : A[σ] ® c ∈ El ->
    Δ ⊢ˢ sb_extend σ en ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb.
Proof.
  intros.
  assert (Δ ⊢ˢ σ : Γ) by mauto 2.
  assert (Δ ⊢ sentry_exp en : A[σ]) by mauto 2 using glu_univ_elem_trm_escape.
  assert (⊢ Γ ▹ A) by mauto 3.
  assert (Δ ⊢ˢ sb_extend σ en : Γ ▹ A).
  { apply wf_sub_extend_gen; [ assumption | assumption | | |].
    - intros B Hlk; inversion Hlk; subst; rewrite exp_sub_shift_extend; assumption.
    - intros B L Hlk; inversion Hlk.
    - intros U Hlk; inversion Hlk. }
  econstructor; mauto 3.
  rewrite exp_sub_shift_extend; eassumption.
Qed.

Lemma cons_glu_sub_pred_helper : forall {Γ Sb Δ σ ρ A a} {i : nat} {P El M c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M : A[σ] ® c ∈ El ->
    Δ ⊢ˢ σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb.
Proof.
  intros.
  assert (Δ ⊢ˢ σ : Γ) by mauto 2.
  assert (Δ ⊢ M : A[σ]) by mauto 2 using glu_univ_elem_trm_escape.
  assert (Δ ⊢ˢ σ,,M : Γ ▹ A) by mauto 2.
  (** [#0[σ,,M]] is [M] and [Wk ⨟ (σ,,M)] is [σ], both by computation; only
      [A[↑]ʷ[σ,,M]] needs a rewrite. *)
  econstructor; mauto 3.
  rewrite exp_sub_shift_extend; eassumption.
Qed.

Hint Resolve cons_glu_sub_pred_helper : mctt.

Lemma initial_env_glu_rel_exp : forall {Γ ρ Sb},
    initial_env_f Γ ρ ->
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊢ˢ Id ® ρ ∈ Sb.
Proof.
  intros * Hinit HΓ.
  gen ρ.
  induction HΓ; intros * Hinit;
    dependent destruction Hinit;
    apply_predicate_equivalence;
    try solve [econstructor; mauto | cbn; mauto 3].

  - assert (glu_rel_typ_with_sub i Γ A Id ρ) as Hgr by mauto; destruct_anon Hgr.
    functional_eval_rewrite_clear.
    econstructor; mauto.
    (** The head is [var0_glu_elem] once the identity substitutions are gone. *)
    1: (rewrite !exp_sub_id in H5 |- *; eapply var0_glu_elem; eassumption).
    (** The tail is the induction hypothesis pushed along [↑]: [Wk ⨟ Id] and
        [sb_wk Id ↑] both send [x] to [#(S x)], so [eapply] converts them. *)
    assert (⊢ Γ ▹ A) by mauto 3.
    eapply (glu_ctx_env_sub_monotone _ _ H (Γ ▹ A) wk_shift Γ Id ρ); mauto 3.
  - (** A definition: the head is [⟦M⟧ρ], glued with [M[↑]ʷ] by the gluing
        of [M] along [↑], hence with [#0] by δ. *)
    assert (⊢ Γ ▸ A ≔ M) by mauto 3.
    assert (HWk : Γ ▸ A ≔ M ⊢ˢ Wk ® ρ ∈ TSb)
      by (eapply (glu_ctx_env_sub_monotone _ _ H (Γ ▸ A ≔ M) wk_shift Γ Id ρ);
          [ apply IHHΓ; assumption | apply kripke_shift_def; assumption ]).
    assert (glu_rel_exp_with_sub i (Γ ▸ A ≔ M) M A Wk ρ) as [] by mauto.
    functional_eval_rewrite_clear.
    econstructor; [ mauto 3 | eassumption | eassumption | | | exact HWk ].
    + rewrite !exp_sub_id.
      match goal with Hg : El _ _ M[Wk] _ |- _ => rewrite !exp_sub_of_shift in Hg end.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    + exists m; split; [ eassumption |].
      match goal with Hg : El _ _ M[Wk] _, Hglu : glu_univ_elem _ _ _ _ |- _ =>
        destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR];
        pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ Hg HR) end.
      eapply per_head_of; [ eassumption | eassumption | exact HR | eassumption ].
  - (** A module slot: its closure is related to itself, by the unit's
        validity at the initial environment. *)
    assert (⊢ Γ ▹ₘ U) by mauto 3.
    assert (HId : Γ ⊢ˢ Id ® ρ ∈ TSb) by (apply IHHΓ; assumption).
    assert (HWk : Γ ▹ₘ U ⊢ˢ Wk ® ρ ∈ TSb)
      by (eapply (glu_ctx_env_sub_monotone _ _ H (Γ ▹ₘ U) wk_shift Γ Id ρ);
          [ exact HId | apply kripke_shift_mod; assumption ]).
    econstructor; [ mauto 3 | | exact HWk ].
    destruct (glu_ctx_env_per_ctx_env H) as [R HR].
    pose proof (glu_ctx_env_per_env H HR HId) as Hρ.
    match goal with Hu : wf_unit_eq _ _ _ _ _ |- _ =>
      destruct (proj1 (proj2 completeness_fundamental_modules) _ _ _ Hu) as [HU _ _] end.
    destruct (rel_modexp_at _ _ _ _ _ HU HR _ _ Hρ) as (h1 & h2 & Hh1 & Hh2 & Hr).
    match goal with Hh : ⟦ me_lit U ⟧ᵐ _ ⍮ _ ⍮ ρ ↘ h |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ Hh1 Hh) as ->; pose proof (functional_eval_modexp _ _ _ _ Hh2 Hh) as -> end.
    cbn; exists h; split; assumption.
  (** The level of an assumption's type, left free by the assumption case. *)
  Unshelve. all: exact 0.
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
  destruct_conjs.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  destruct_glu_records.
  destruct_conjs.
  econstructor; mauto 3.
  eapply glu_univ_elem_exp_conv; revgoals; mauto 3.
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
  assert (exists ρ ρ', initial_env_f Γ ρ /\ initial_env_f Γ ρ' /\ Dom ρ ≈ ρ' ∈ env_rel) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert (Γ ⊢ˢ Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  assert (Γ ⊢ M[Id] : A[Id]) as HId by mauto 3 using glu_univ_elem_trm_escape.
  rewrite !exp_sub_id in HId; eassumption.
Qed.

Hint Resolve glu_rel_exp_to_wf_exp : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_to_wf_exp : mctt.
