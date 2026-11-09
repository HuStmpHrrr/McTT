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
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Add Parametric Morphism i a Γ A M : (glu_elem_bot i a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_morphism_iff4.
Proof.
  (** A neutral related to one: it reads back as it does, up to proofs, so
      at a type of levels free of proofs too ([nf_ne_proof_free_eq]). *)
  assert (Hdir : forall m m', Dom m ≈ m' ∈ per_bot -> Γ ⊢ M : A ® m ∈ glu_elem_bot i a -> Γ ⊢ M : A ® m' ∈ glu_elem_bot i a).
  { intros m m' Hmm' [P El HM Hglu HA (Hna & Hb & Hpf) Hrb].
    econstructor; [ exact HM | exact Hglu | exact HA | split; [ exact Hna | split ] |].
    - etransitivity; [ symmetry; exact Hmm' | etransitivity; [ exact Hb | exact Hmm' ] ].
    - intros Hk; destruct (Hpf Hk) as [Hl _].
      assert (Hr : neutral_proof_free m').
      { intros s M' HM'; destruct (Hmm' s) as [W1 W2 H1 H2 E].
        pose proof (functional_read_ne _ _ _ _ HM' H2) as ->.
        pose proof (proj2 nf_ne_proof_free_eq _ (Hl _ _ H1) _ E) as <-; exact (Hl _ _ H1). }
      split; exact Hr.
    - intros Δ φ M' Hφ HM'; destruct (Hmm' (length Δ)) as [W1 W2 H1 H2 E].
      pose proof (functional_read_ne _ _ _ _ HM' H2) as ->.
      exact (glu_ne_eq_upto _ _ _ _ _ E (Hrb _ _ _ Hφ H1)). }
  intros m m' Hmm'; split; apply Hdir; [ exact Hmm' | symmetry; exact Hmm' ].
Qed.

Add Parametric Morphism i a Γ A M R (H : per_univ_elem i R a a) : (glu_elem_top i a Γ A M)
    with signature R ==> iff as glu_elem_top_morphism_iff4.
Proof.
  (** A related element reads back as it does, up to proofs. *)
  assert (Hdir : forall m m', R m m' -> Γ ⊢ M : A ® m ∈ glu_elem_top i a -> Γ ⊢ M : A ® m' ∈ glu_elem_top i a).
  { intros m m' Hmm' [P El HM Hglu HA Hp Hrd].
    pose proof (per_elem_then_per_top H Hmm') as Ht.
    econstructor; [ exact HM | exact Hglu | exact HA | etransitivity; [ symmetry; exact Ht | etransitivity; [ exact Hp | exact Ht ] ] |].
    intros Δ φ w Hφ Hw; destruct (Ht (length Δ)) as [W1 W2 H1 H2 E].
    pose proof (functional_read_nf _ _ _ _ Hw H2) as ->.
    exact (glu_nf_eq_upto _ _ _ _ _ E (Hrd _ _ _ Hφ H1)). }
  intros m m' Hmm'; split; apply Hdir; [ exact Hmm' | symmetry; exact Hmm' ].
Qed.

(** An equation at the sort of a kind next to a large universe holds next
    to a larger one. *)
Lemma wf_exp_eq_kind_sort_max_left : forall Γ κ X Y n m,
    Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@n -> Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@(max n m).
Proof. intros * H; destruct κ; cbn in *; [ mauto 3 using lift_exp_eq_max_left | exact H | exact H ]. Qed.

Lemma wf_exp_eq_kind_sort_max_right : forall Γ κ X Y n m,
    Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@m -> Γ ⊢ X ≈ Y : abs_kind_sort κ Typeω@(max n m).
Proof. intros * H; destruct κ; cbn in *; [ mauto 3 using lift_exp_eq_max_right | exact H | exact H ]. Qed.

(** Two types glued at the same value are equal: both are equal to its
    readback up to proofs, and annotated readbacks related up to proofs are
    equal ([nf_annotate_proofs_upto]). *)
Lemma glu_typ_top_unique : forall i j a Γ A A',
    Γ ⊢ A ® glu_typ_top i a -> Γ ⊢ A' ® glu_typ_top j a ->
    Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(max (large_level i) (large_level j)).
Proof.
  intros * [HA Hp Hr] [_ _ Hr'].
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  destruct (Hp (length Γ)) as [V V0 HV _ _].
  destruct (Hr _ _ _ Hid HV) as (W1 & E1 & H1); destruct (Hr' _ _ _ Hid HV) as (W2 & E2 & H2).
  rewrite exp_wk_id in H1, H2.
  assert (E : nf_eq_upto_proofs W1 W2) by (etransitivity; [ symmetry; exact E1 | exact E2 ]).
  apply wf_exp_eq_kind_sort_max_left with (m := large_level j) in H1.
  apply wf_exp_eq_kind_sort_max_right with (n := large_level i) in H2.
  etransitivity; [ exact H1 |]; etransitivity; [| symmetry; exact H2 ].
  eapply nf_annotate_proofs_upto; [ exact (presup_exp_eq_right H1) | eexists; exact (presup_exp_eq_right H2) | exact E ].
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
  simpl in *.
  intros * Hper Hglu Hglu' Hn HA HA'.
  assert (DG a ∈ glu_univ_elem i ↘ P' ↘ El') by (setoid_rewrite Hper; eassumption).
  eapply glu_univ_elem_typ_unique_upto_exp_eq'; [ exact Hglu | exact Hn | exact HA |].
  destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu H) as [HPP _]; apply HPP; exact HA'.
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

Lemma glu_univ_elem_per_univ_typ_iff : forall {i : universe_index} {a a' P P' El El'},
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
  intros * Hass Hcp HN HA HD Hc.
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
    exact (glu_shape_typ_change p D ups ups m Mm (DP m) (DP' m) (DEl m) (DEl' m) Hass Hcp HM ltac:(intros; reflexivity)
             (fun ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 Hm0 Hc0 Heq0 Hw0 HB0 Hy0 =>
                HD m Mm ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 HM Hm0 Hc0 Heq0 Hw0 HB0 Hy0)
             t Γ _ _ T H ns c gs1 t gs2 (nonrec_arg_vals gs1 vs) 0 nil ltac:(rewrite List.app_nil_r; reflexivity)
             ltac:(cbn [List.firstn]; rewrite List.app_nil_r; reflexivity)
             Hns Hcon Hp eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
Qed.

(** Equal lists of terms at a closed telescope are equal at every
    weakening. *)
Lemma exps_eq_at_wk : forall Δ Δ' φ T Xs Ys, all_assumptions T -> ctx_scoped 0 T -> Δ' ⊢ᵏ φ : Δ ->
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
Lemma exps_eq_at_params_wk : forall p D k Mk Δ Δ' φ Xs Ys, ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D k = Some Mk -> Δ' ⊢ᵏ φ : Δ ->
    exps_eq_at Δ (im_params D Mk) Xs Ys ->
    exps_eq_at Δ' (im_params D Mk) (List.map (fun X => X[φ]ʷ) Xs) (List.map (fun Y => Y[φ]ʷ) Ys).
Proof.
  intros * Hl HMk Hφ H.
  assert (HΔ : ⊢ Δ) by (eapply kripke_cod; eassumption).
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
  eapply exps_eq_at_wk; [ eapply decl_closed_params_ass; eassumption | eapply decl_closed_params; eassumption
                       | exact Hφ | exact H ].
Qed.

(** Equal parameters are equal at their uniform part. *)
Lemma exps_eq_at_uparams_of_params : forall D Mk Δ Xs Ys, decl_closed D ->
    List.length Xs = im_np D Mk -> exps_eq_at Δ (im_params D Mk) Xs Ys ->
    exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) Xs) (List.firstn (ind_nu D) Ys).
Proof.
  intros * Hc HXl [Hl H]; split; [ rewrite !List.length_firstn; lia |].
  pose proof (decl_uparams_ass D Hc) as HassU.
  intros k X Y A HX HY HA.
  rewrite List.nth_error_firstn in HX, HY.
  destruct (Nat.ltb_spec k (ind_nu D)); [| discriminate ].
  apply (H k X Y A HX HY).
  unfold im_params; rewrite <- (List.firstn_skipn (ind_nu D) Xs), tele_insts_app
    by (try exact HassU; rewrite List.length_firstn; unfold im_np, ind_nu in *; lia).
  rewrite List.nth_error_app1; [ exact HA |].
  rewrite length_tele_insts by exact HassU; rewrite List.length_firstn; unfold im_np, ind_nu in *; lia.
Qed.

(** Parameters with an equal uniform part, the rest unchanged. *)
Lemma exps_eq_at_params_of_uparams : forall D Mk Δ Xs Us', decl_closed D ->
    List.length Xs = im_np D Mk ->
    (forall k X A, List.nth_error Xs k = Some X -> List.nth_error (tele_insts (im_params D Mk) Id Xs) k = Some A -> Δ ⊢ X : A) ->
    exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) Xs) Us' ->
    exps_eq_at Δ (im_params D Mk) Xs (Us' ++ List.skipn (ind_nu D) Xs).
Proof.
  intros * Hc HXl HXt [Hl H].
  pose proof (decl_uparams_ass D Hc) as HassU.
  assert (LU : List.length (List.firstn (ind_nu D) Xs) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HXl; lia).
  pose proof Hl as Hl0; rewrite LU in Hl0.
  split; [ rewrite List.length_app, List.length_skipn; unfold im_np, im_nn in HXl; lia |].
  intros k X Y A HX HY HA.
  destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HY by lia.
    apply (H k X Y A); [ rewrite List.nth_error_firstn; destruct (Nat.ltb_spec k (ind_nu D)); [ exact HX | lia ] | exact HY |].
    unfold im_params in HA; rewrite <- (List.firstn_skipn (ind_nu D) Xs), tele_insts_app in HA
      by (try exact HassU; rewrite LU; unfold ind_nu; lia).
    rewrite List.nth_error_app1 in HA; [ exact HA |].
    rewrite length_tele_insts by exact HassU; rewrite LU; unfold ind_nu in *; lia.
  - rewrite List.nth_error_app2 in HY by lia.
    rewrite List.nth_error_skipn in HY.
    replace (ind_nu D + (k - List.length Us')) with k in HY by lia.
    rewrite HX in HY; injection HY as <-.
    apply wf_exp_eq_refl; eapply HXt; eassumption.
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

Lemma exps_eq_at_uparams_trans : forall p D Δ Xs Ys Zs, ind_lookup gc_deps gc_stack p = Some D -> ⊢ Δ ->
    List.length Xs = ind_nu D -> exps_eq_at Δ (ind_uparams D) Xs Ys -> exps_eq_at Δ (ind_uparams D) Ys Zs ->
    exps_eq_at Δ (ind_uparams D) Xs Zs.
Proof.
  intros * Hl HΔ HXl [Hl1 H1] [Hl2 H2].
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
  split; [ congruence |].
  unfold ind_nu in HXl.
  eapply (tele_eq_trans Δ (ind_uparams D) Xs Ys Zs (decl_uparams_ass D Hc) (uparams_ctx_wf _ _ _ Hl HΔ)); [ lia | lia | lia | exact H1 | exact H2 ].
Qed.

Lemma map_wk_id : forall Ps, List.map (fun P => P[wk_id]ʷ) Ps = Ps.
Proof. intros; rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; reflexivity. Qed.

(** The components of an inductive type at uniform parameters [Us], at
    every weakening and at every instance equal to them there. *)
Definition ind_components_kripke (p : qname) (D : ind_decl) (ups : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (Γ : ctx) (Us : list exp) : Prop :=
  forall Δ φ, Δ ⊢ᵏ φ : Γ ->
    ind_glu_components p D ups NP NEl AP AEl DP DEl Δ (List.map (fun U => U[φ]ʷ) Us) /\
    forall Us', exps_eq_at Δ (ind_uparams D) (List.map (fun U => U[φ]ʷ) Us) Us' ->
      ind_glu_components p D ups NP NEl AP AEl DP DEl Δ Us'.

Lemma ind_components_kripke_wk : forall p D ups NP NEl AP AEl DP DEl Γ Us Δ φ,
    ind_components_kripke p D ups NP NEl AP AEl DP DEl Γ Us -> Δ ⊢ᵏ φ : Γ ->
    ind_components_kripke p D ups NP NEl AP AEl DP DEl Δ (List.map (fun U => U[φ]ʷ) Us).
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
Lemma ind_glu_elem_lower : forall p D ups NP NEl AP AEl DP DEl (NEl' : nat -> nat -> list domain -> glu_exp_pred)
    (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP' : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl' : nat -> list domain -> list centry -> exp -> glu_exp_pred),
    ind_lookup gc_deps gc_stack p = Some D -> group_structure D -> ind_canon_props D ups ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ A M n, NP m j vs Γ A -> NEl' m j vs Γ A M n -> NEl m j vs Γ A M n) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       forall Γ A M n, AP m ms c j vs Γ A -> AEl' m ms c j vs Γ A M n -> AEl m ms c j vs Γ A M n) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       forall Γ A M n, DEl m (ms ++ ws ++ ys) Ts B Γ A M n -> DEl' m (ms ++ ws ++ ys) Ts B Γ A M n) ->
    forall k Γ Us Ns M m, ind_glu_elem p D ups NEl' AEl' DP' DEl' k Γ Us Ns M m ->
      ind_components_kripke p D ups NP NEl AP AEl DP DEl Γ Us ->
      ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m.
Proof.
  intros p D ups NP NEl AP AEl DP DEl NEl' AEl' DP' DEl' Hl Hass Hcp HNl HAl HDl.
  pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
  apply (ind_glu_elem_mut_ind p D ups NEl' AEl' DP' DEl'
           (fun k Γ Us Ns M m _ => ind_components_kripke p D ups NP NEl AP AEl DP DEl Γ Us ->
              ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m)
           (fun k Γ Us pre Ts t A N v _ => forall Mk ms c0 gs1 t0 gs2 ws kk ys, ind_member D k = Some Mk -> pre = ms ++ ws ++ ys ->
              Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t0) ->
              tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms ->
              ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
              tele_prefix_rel (canon_args_rel D ups k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
              ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
              tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t0)
                kk ys ys ->
              glu_shape_typ (canon_doms_rel D ups k) (DP k) (DEl k) Γ pre Ts t A -> ⊢ Γ ->
              forall σ, List.length Us = ind_nu D -> A = ptyp_ty_at p D Us σ t ->
              ind_components_kripke p D ups NP NEl AP AEl DP DEl Γ Us ->
              glu_rec p D ups NEl AEl DP DEl k Γ Us pre Ts t A N v)).
  - intros k Mk hd k' c gs Us Ns bs vs As Γ M HMk Hrv Href Hcon HUl HNl' Hbl Hvl HAl' HM Hb Hv Hnp HAs Harg Hrec IH Hk.
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
    assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
    pose proof (proj1 (Hk _ _ Hid)) as Hc0.
    rewrite map_wk_id in Hc0.
    pose proof (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc0 HNl HMk Hb Hnp) as Hnp'.
    assert (HargL : forall gs1 r0 A0 gs2 N A v, gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
              List.nth_error As (List.length gs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
              List.nth_error vs (List.length gs1) = Some v ->
              Γ ⊢ N : A ® v ∈ AEl k (List.skipn (im_unu D Mk) bs) c (List.length (cargs_nonrec gs1))
                                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))).
    { pose proof (ind_components_lower_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gs nil As vs Hc0 HAl HMk Hnp' Hb Hcon
                    ltac:(rewrite List.app_nil_r; reflexivity) Hvl Hv) as L.
      exact (L Harg). }
    eapply ind_glu_elem_con; [ exact HMk | exact Hrv | exact Href | exact Hcon | exact HUl | exact HNl' | exact Hbl | exact Hvl | exact HAl'
                             | exact HM | exact Hb | exact Hv | exact Hnp' | exact HAs | exact HargL |].
    intros gs1 t gs2 N A v Heq HN0 HA0 Hv0.
    assert (Hlt : List.length gs1 < List.length vs) by (rewrite Hvl, Heq, List.length_app; cbn; lia).
    assert (Hpw : tele_prefix_rel (canon_args_rel D ups k (List.skipn (im_unu D Mk) bs) c) (List.length (cargs_nonrec gs1))
                    (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)))
      by (eapply nonrec_prefix_pre; eassumption).
    assert (Hsh : glu_shape_typ (canon_doms_rel D ups k) (DP k) (DEl k) Γ
                    (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                    (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t A).
    { destruct Hc0 as [_ _ HCR].
      refine (HCR k Mk c gs gs1 t gs2 _ _ As (List.firstn (List.length gs1) vs) A HMk Hcon Heq Hnp' Hb
                ltac:(rewrite List.length_firstn; lia) HA0 _ Hpw).
      intros hs1 rB B hs2 N' T' v' Heq1 HN' HT' Hv'.
      assert (Hh : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
      rewrite List.firstn_firstn, Nat.min_l by lia.
      eapply (HargL hs1 rB B (hs2 ++ ca_rec t :: gs2));
        [ rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ]. }
    pose proof (cargs_rec_type_at p D Mk _ _ _ _ (Us ++ Ns) _ _ Heq Hc ltac:(rewrite List.length_app; unfold im_np; lia) HA0) as HAσ.
    rewrite firstn_app_exact in HAσ by exact HUl.
    apply (IH _ _ _ _ _ _ Heq HN0 HA0 Hv0 Mk (List.skipn (im_unu D Mk) bs) c gs1 t gs2
             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil HMk
             ltac:(rewrite List.app_nil_r; reflexivity) ltac:(cbn [List.firstn]; rewrite List.app_nil_r; reflexivity)
             Hb ltac:(rewrite <- Heq; exact Hcon) Hpw eq_refl ltac:(lia)
             (tele_prefix_rel_nil _) Hsh HΓ _ HUl HAσ Hk).
  - intros k Mk hd k' m Γ Us Ns M as' HMk Hrv Href Hm Hr _; eapply ind_glu_elem_neut; eassumption.
  - (** A record view: its fields, as a constructor's arguments after no
        non-uniform parameter. *)
    intros k Mk qr Is fl c gs Us Ns As m vs Γ M HMk Hh Hcs HUl HNl' HAl' Hps HM Hv HAs Harg Hrec IH Hk.
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
    assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
    pose proof (proj1 (Hk _ _ Hid)) as Hc0.
    rewrite map_wk_id in Hc0.
    pose proof (rview_struct_nparams _ _ _ (group_structure_record_struct _ Hass) _ _ _ _ _ HMk Hh) as Hnp0.
    destruct (rview_struct_con _ _ _ (group_structure_record_struct _ Hass) _ _ _ _ _ HMk Hh) as (gs0 & Hcs0 & Hlg).
    rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
    pose proof (ind_con_single _ _ _ Hcs) as Hcon.
    assert (Hvl : List.length vs = List.length gs) by (rewrite (eval_projs_length _ _ _ Hps); congruence).
    assert (Hb : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) nil nil)
      by (rewrite Hnp0; split; reflexivity + exact I).
    assert (Hnp' : glu_nparams k Mk NEl Γ Us Ns nil).
    { constructor; [ exact HNl' | unfold im_nn; rewrite Hnp0; reflexivity |].
      intros j N A n _ _ Hn; destruct j; discriminate Hn. }
    assert (HargL : forall gs1 r0 A0 gs2 N A v, gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
              List.nth_error As (List.length gs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
              List.nth_error vs (List.length gs1) = Some v ->
              Γ ⊢ N : A ® v ∈ AEl k nil c (List.length (cargs_nonrec gs1))
                                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))).
    { pose proof (ind_components_lower_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gs nil As vs Hc0 HAl HMk Hnp' Hb Hcon
                    ltac:(rewrite List.app_nil_r; reflexivity) Hvl Hv) as L.
      exact (L Harg). }
    eapply ind_glu_elem_record; [ exact HMk | exact Hh | exact Hcs | exact HUl | exact HNl' | exact HAl' | exact Hps
                                | exact HM | exact Hv | exact HAs | exact HargL |].
    intros gs1 t gs2 N A v Heq HN0 HA0 Hv0.
    assert (Hlt : List.length gs1 < List.length vs) by (rewrite Hvl, Heq, List.length_app; cbn; lia).
    assert (Hpw : tele_prefix_rel (canon_args_rel D ups k nil c) (List.length (cargs_nonrec gs1))
                    (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)))
      by (eapply nonrec_prefix_pre; eassumption).
    assert (Hsh : glu_shape_typ (canon_doms_rel D ups k) (DP k) (DEl k) Γ
                    (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) (cargs_nonrec_tele gs1) t A).
    { destruct Hc0 as [_ _ HCR].
      (** The view has no non-uniform parameter *)
      enough (HS : glu_shape_typ (canon_doms_rel D ups k) (DP k) (DEl k) Γ
                     (nil ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                     (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t A) by (rewrite Hnp0 in HS; exact HS).
      refine (HCR k Mk c gs gs1 t gs2 _ _ As (List.firstn (List.length gs1) vs) A HMk Hcon Heq Hnp' Hb
                ltac:(rewrite List.length_firstn; lia) HA0 _ Hpw).
      intros hs1 rB B hs2 N' T' v' Heq1 HN' HT' Hv'.
      assert (Hh1 : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
      rewrite List.firstn_firstn, Nat.min_l by lia.
      eapply (HargL hs1 rB B (hs2 ++ ca_rec t :: gs2));
        [ rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ]. }
    pose proof (cargs_rec_type_at p D Mk _ _ _ _ (Us ++ Ns) _ _ Heq Hc ltac:(rewrite List.length_app; unfold im_np; lia) HA0) as HAσ.
    rewrite firstn_app_exact in HAσ by exact HUl.
    apply (IH _ _ _ _ _ _ Heq HN0 HA0 Hv0 Mk nil c gs1 t gs2
             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil HMk
             ltac:(rewrite List.app_nil_r; reflexivity)
             ltac:(rewrite Hnp0; cbn [List.firstn List.rev List.app]; rewrite List.app_nil_r; reflexivity)
             Hb ltac:(rewrite <- Heq; exact Hcon) Hpw eq_refl ltac:(lia)
             (tele_prefix_rel_nil _) Hsh HΓ _ HUl HAσ Hk).
  - intros j Mj Ps Ts pre A Us Γ N x k HMj Hc1 Hc2 IH2 Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre HTs Hm Hc Hw Hsk Hk1 Hy _ HΓ σ HUl HA Hk.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hcl].
    assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
    pose proof (proj1 (Hk _ _ Hid)) as Hc0; rewrite map_wk_id in Hc0.
    apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
    + intros bsr Q Hbs HQ.
      destruct (Hc1 _ _ Hbs HQ) as (HQl & Hbt & Hgn).
      split; [ exact HQl | split; [ exact Hbt |] ].
      intros bsr' Hb'; destruct (Hgn _ Hb') as [Hn' Hpt]; split; [| exact Hpt ].
      exact (glu_nparams_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc0 HNl HMj
               (canon_nparams_rel_refl_r' p D ups Hass Hcp _ _ _ _ HMj Hb') Hn').
    + intros bsr Q Hbs HQ Δ φ Us' Q' Hφ HUl' HQ'.
      destruct (Hc1 _ _ Hbs HQ) as (HQl & _ & _).
      apply (IH2 _ _ Hbs HQ Δ φ Us' Q' Hφ HUl' HQ').
      intros Δ' φ' Hφ'.
      pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hφφ.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      (** The uniform part of [Us'] at [φ'] is [Us] at [φ ⊙ φ']. *)
      assert (HQU : exps_eq_at Δ' (ind_uparams D) (List.map (fun U => U[φ ⊙ φ']ʷ) Us) (List.map (fun U => U[φ']ʷ) Us')).
      { pose proof (exps_eq_at_params_wk _ _ _ _ _ _ _ _ _ Hl HMj Hφ' HQ') as H.
        rewrite map_wk_wk in H.
        pose proof H as H'; eapply exps_eq_at_uparams_of_params in H';
          [| exact Hcl | rewrite List.length_map, List.length_app; unfold im_np; lia ].
        rewrite !List.map_app, !firstn_app_exact in H' by (rewrite List.length_map; assumption); exact H'. }
      destruct (Hk _ _ Hφφ) as [_ Hk2].
      split.
      * apply Hk2; exact HQU.
      * intros Us'' HUs''.
        apply Hk2; eapply exps_eq_at_uparams_trans; [ exact Hl | exact HΔ' | | exact HQU | exact HUs'' ].
        rewrite List.length_map; exact HUl.
  - intros A Γ k pre Ts B x Us t N Hd He Hg IH Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre HTs Hm Hc Hw Hsk Hk1 Hy Hsh HΓ σ HUl HA Hk.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hcl].
    destruct (shape_pi_step p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) Hass HnP HnI HaP HaI HdP HdI
                k Mk ms c0 gs1 t0 gs2 ws ws k1 ys ys B t HMk Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
    subst pre Ts.
    pose proof (HDl _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as HDu.
    cbn [ptyp_ty_at] in HA.
    apply glu_rec_pi.
    + intros IT OT HA0 Δ φ Hφ; exact (proj1 (Hsh IT OT HA0) Δ φ Hφ).
    + intros IT OT HA0 Δ φ b c Hφ Hc' Hb; exact (He IT OT HA0 Δ φ b c Hφ Hc' (HDu _ _ _ _ Hb)).
    + intros IT OT HA0 Δ φ b c fc Hφ Hc' Hb Hfc.
      assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
      pose proof HA as HA1; rewrite HA0 in HA1; injection HA1 as _ HOT.
      apply (IH _ _ HA0 Δ φ b c fc Hφ Hc' (HDu _ _ _ _ Hb) Hfc Mk ms c0 gs1 t0 gs2 ws (S k1) (ys ++ c :: nil) HMk
               ltac:(rewrite <- !List.app_assoc; reflexivity) ltac:(apply prefix_tele_snoc_dom; exact HB)
               Hm Hc Hw Hs' Hk' (Hstep _ _ Hc')
               (proj2 (Hsh _ _ HA0) Δ φ b c Hφ Hc' Hb) HΔ
               (sb_compose (sb_q σ) ((ι φ),,b)) ltac:(rewrite List.length_map; exact HUl)).
      * rewrite HOT, ptyp_ty_at_sub by (try exact Hcl; rewrite List.length_map; exact HUl); rewrite List.map_map; f_equal.
        apply List.map_ext; intros; apply exp_shift_extend_wk.
      * exact (ind_components_kripke_wk _ _ _ _ _ _ _ _ _ _ _ _ _ Hk Hφ).
Qed.


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

(** Parameters equal to the annotations of readbacks related up to proofs
    are equal: the annotations are ([nf_annotate_proofs_upto]). *)
Lemma params_eq_annotate_upto : forall p D k Mk Δ Ps Qs W1 W2,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ Δ ->
    List.length Ps = im_np D Mk -> List.length Qs = im_np D Mk ->
    exps_eq_at Δ (im_params D Mk) Ps (List.map nf_to_exp (List.map nf_annotate_proofs W1)) ->
    exps_eq_at Δ (im_params D Mk) Qs (List.map nf_to_exp (List.map nf_annotate_proofs W2)) ->
    nfs_eq_upto_proofs W1 W2 -> exps_eq_at Δ (im_params D Mk) Ps Qs.
Proof.
  intros * Hl HMk HΔ HPl HQl HP HQ E.
  set (A1 := List.map nf_to_exp (List.map nf_annotate_proofs W1)) in *.
  set (A2 := List.map nf_to_exp (List.map nf_annotate_proofs W2)) in *.
  destruct HP as [HlP HP], HQ as [HlQ HQ].
  assert (HA1 : List.length A1 = im_np D Mk) by congruence.
  assert (HA2 : List.length A2 = im_np D Mk) by congruence.
  assert (H12 : forall j X Y T, List.nth_error A1 j = Some X -> List.nth_error A2 j = Some Y ->
                  List.nth_error (tele_insts (im_params D Mk) Id A1) j = Some T -> Δ ⊢ X ≈ Y : T).
  { intros j X Y T HX HY HT.
    unfold A1, A2 in HX, HY; rewrite !List.nth_error_map in HX, HY.
    destruct (List.nth_error W1 j) as [w1 |] eqn:Hw1; [| discriminate ];
      destruct (List.nth_error W2 j) as [w2 |] eqn:Hw2; [| discriminate ]; cbn in HX, HY; injection HX as <-; injection HY as <-.
    destruct (nfs_eq_upto_proofs_nth _ _ _ _ E Hw1) as (w2' & Hw2' & Ew); rewrite Hw2 in Hw2'; injection Hw2' as <-.
    destruct (nth_error_lt_some (tele_insts (im_params D Mk) Id A2) j) as [T2 HT2].
    { destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
      rewrite length_tele_insts_params by (try (eapply decl_closed_params_ass; eassumption); exact HA2).
      try rewrite <- HA2; apply List.nth_error_Some; unfold A2; rewrite !List.nth_error_map, Hw2; discriminate. }
    eapply nf_annotate_proofs_upto; [ | eexists | exact Ew ].
    - eapply (exps_eq_at_typed_r p D k Mk Δ Ps A1 Hl HMk HΔ HPl (conj HlP HP)); [| exact HT ].
      unfold A1; rewrite !List.nth_error_map, Hw1; reflexivity.
    - eapply (exps_eq_at_typed_r p D k Mk Δ Qs A2 Hl HMk HΔ HQl (conj HlQ HQ)); [| exact HT2 ].
      unfold A2; rewrite !List.nth_error_map, Hw2; reflexivity. }
  split; [ congruence |].
  eapply (params_eq_trans _ p D k Mk Ps A1 Qs Hl HMk HΔ HPl HA1 HQl HP).
  eapply (params_eq_trans _ p D k Mk A1 A2 Qs Hl HMk HΔ HA1 HA2 HQl H12).
  eapply (params_eq_sym _ p D k Mk Qs A2 Hl HMk HΔ HQl HA2 HQ).
Qed.

(** Two lists of parameters glued to the same values are equal. *)
Lemma glu_params_top_eq : forall p D k Mk Δ Ps Qs as',
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ Δ ->
    (exists Ms, Rps as' at List.rev (im_params D Mk) in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms) ->
    glu_params_top D Mk Δ Ps as' -> glu_params_top D Mk Δ Qs as' -> exps_eq_at Δ (im_params D Mk) Ps Qs.
Proof.
  intros * Hl HMk HΔ (Ms & HMs) [HPl _ HPr] [HQl _ HQr].
  assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
  destruct (HPr _ _ _ Hid HMs) as (W1 & E1 & HPMs); destruct (HQr _ _ _ Hid HMs) as (W2 & E2 & HQMs).
  rewrite (map_wk_id Ps) in HPMs; rewrite (map_wk_id Qs) in HQMs.
  eapply params_eq_annotate_upto; [ exact Hl | exact HMk | exact HΔ | exact HPl | exact HQl | exact HPMs | exact HQMs |].
  etransitivity; [ symmetry; exact E1 | exact E2 ].
Qed.

Lemma ind_typ_at_cumu : forall p D ups ns NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' k Mk a b Γ A Ps,
    group_structure D -> ind_canon_props D ups ->
    a <= b ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\
       (forall Γ T N n, NP m j vs Γ T -> NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
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
  intros * Hass Hcp Hab HN HA HD (HA0 & Hk); split; [ eapply lift_exp_eq_ge; eassumption |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & Hs & Hc).
  split; [ exact Hpt | split ].
  - destruct (Nat.eq_dec a b) as [<- | Hne]; [ exact Hs |].
    eapply wf_subtyp_trans; [ exact Hs | apply wf_subtyp_univ; [ eapply kripke_dom; eassumption | lia ] ].
  - intros Ps' HPs'; eapply ind_glu_components_cumu; [ exact Hass | exact Hcp | exact HN | exact HA | exact HD | exact (Hc _ HPs') ].
Qed.

(** A type of a declared member at parameters [Ps] is one at parameters
    [Qs] glued to the same values. *)
Lemma ind_typ_at_params_change : forall p D ups ns NP NEl AP AEl DP DEl k Mk pm a Γ A Ps Qs,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    (forall n, exists Ms, Rps ups ++ ns at List.rev (im_params D Mk) in gc_deps ⍮ gc_stack ⍮ nil ⍮ n ↘ Ms) ->
    (forall Δ φ, Δ ⊢ᵏ φ : Γ -> glu_params_top D Mk Δ (List.map (fun P => P[φ]ʷ) Qs) (ups ++ ns)) ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@a Γ A Ps ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@a Γ A Qs.
Proof.
  intros * Hl HMk Hh Hrb HQ (HA0 & Hk).
  assert (Heq : forall Δ φ, Δ ⊢ᵏ φ : Γ ->
                  exps_eq_at Δ (im_params D Mk) (List.map (fun P => P[φ]ʷ) Ps) (List.map (fun P => P[φ]ʷ) Qs)).
  { intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & _ & _).
    eapply glu_params_top_eq; [ exact Hl | exact HMk | eapply kripke_dom; eassumption | apply Hrb | exact Hpt
                              | exact (HQ _ _ Hφ) ]. }
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  split.
  - destruct (Hk _ _ Hid) as ([HPl _ _] & Hs & _).
    destruct (Heq _ _ Hid) as [_ HPQ]; destruct (HQ _ _ Hid) as [HQl _ _].
    rewrite (map_wk_id Ps) in HPl, Hs, HPQ; rewrite (map_wk_id Qs) in HPQ, HQl.
    etransitivity; [ exact HA0 |].
    eapply wf_exp_eq_subtyp'; [| exact Hs ].
    eapply wf_exp_eq_ind_apps; [ exact Hl | exact HMk | exact (decl_member_lt _ _ _ _ _ _ HΓ Hl HMk Hh) | exact HΓ
                               | exact HPl | exact HQl | exact HPQ ].
  - intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as ([HPl HPt HPr] & Hs & Hc).
    pose proof (Heq _ _ Hφ) as [HlPQ HPQ]; pose proof (HQ _ _ Hφ) as HQt.
    pose proof HQt as [HQl _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    split; [ exact HQt | split ].
    + destruct (ind_sort_inst_cong _ _ _ _ _ _ _ Hl HMk HΔ HPl HQl HPQ) as [n Hk'].
      eapply wf_subtyp_trans; [ eapply wf_subtyp_refl'; symmetry; exact Hk' | exact Hs ].
    + intros Ps' [HlQP' HQP']; apply Hc; split; [ congruence |].
      eapply (params_eq_trans _ p D k Mk _ _ _ Hl HMk HΔ HPl HQl); [ congruence | exact HPQ | exact HQP' ].
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
  split; [| split ].
  - intros Γ A (Ps & HPs); exists Ps; eapply ind_typ_at_cumu;
      [ exact Hass | exact Hcp | exact Hij | exact HN2 | exact HA2 | exact HD2 | exact HPs ].
  - intros Γ A M m [HM Hm Ps HPs Hk].
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Ps _ _);
      [ apply Hrel; exact Hm
      | eapply ind_typ_at_cumu; [ exact Hass | exact Hcp | exact Hij | exact HN2 | exact HA2 | exact HD2 | exact HPs ] |].
    intros Δ φ Ps' Hφ HPs'; eapply (ind_glu_elem_mono p D ups NEl AEl DP DEl Hass Hcp); [| | | exact (Hk _ _ _ Hφ HPs') ].
    + intros m0 Mm j0 vs HM0 Hj Hp; apply (proj1 (proj2 (HN m0 Mm j0 vs HM0 Hj Hp))).
    + intros m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp; apply (proj1 (proj2 (HA m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp))).
    + exact HD2.
  - intros Γ A M m (Ps & HPs) [HM Hm Qs HQs Hk].
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Qs _ _); [ apply Hrel; exact Hm | |].
    + eapply ind_typ_at_params_change; [ exact Hl | exact HMk | exact Hh | exact Hrb | | exact HPs ].
      intros Δ φ Hφ; exact (proj1 (proj2 HQs Δ φ Hφ)).
    + intros Δ φ Ps' Hφ HPs'.
      eapply ind_glu_elem_lower; [ exact Hl | exact Hass | exact Hcp | | | | exact (Hk _ _ _ Hφ HPs') | ].
      * intros m0 Mm j0 vs HM0 Hj Hp; apply (proj2 (proj2 (HN m0 Mm j0 vs HM0 Hj Hp))).
      * intros m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp; apply (proj2 (proj2 (HA m0 Mm ms c gs j0 vs HM0 Hm' Hc Hj Hp))).
      * intros * HM0 Hm' Hc Heq Hw HB Hy; exact (proj1 (proj2 (HD _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hc Heq Hw HB Hy))).
      * intros Δ' φ' Hφ'.
        pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hc.
        assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
        destruct (proj2 HPs _ _ Hc) as (HPt & _ & HPc).
        pose proof (proj1 (proj2 HQs _ _ Hc)) as HQt.
        pose proof (glu_params_top_eq _ _ _ _ _ _ _ _ Hl HMk HΔ' (Hrb _) HPt HQt) as [HlPQ HPQ].
        pose proof (exps_eq_at_params_wk _ _ _ _ _ _ _ _ _ Hl HMk Hφ' HPs') as [HlQ' HQ'].
        rewrite map_wk_wk in HlQ', HQ'.
        destruct HPt as [HPl _ _]; destruct HQt as [HQl _ _].
        assert (HlP' : List.length (List.map (fun P => P[φ']ʷ) Ps') = im_np D Mk)
          by (clear - HlQ' HPl HQl; rewrite !List.length_map in *; lia).
        assert (E1 : exps_eq_at Δ' (im_params D Mk) (List.map (fun P => P[φ ⊙ φ']ʷ) Ps) (List.map (fun P => P[φ']ʷ) Ps')).
        { split; [ clear - HlQ' HPl HQl; rewrite !List.length_map in *; lia |].
          eapply (params_eq_trans _ p D k Mk _ _ _ Hl HMk HΔ' HPl HQl); [ exact HlP' | exact HPQ | exact HQ' ]. }
        destruct (decl_of_lookup _ _ _ _ _ HΔ' Hl) as [_ Hc0].
        rewrite <- List.firstn_map.
        split; [ apply HPc; exact E1 |].
        intros Us' HUs'.
        pose proof (exps_eq_at_params_of_uparams D Mk Δ' _ _ Hc0 HlP' (exps_eq_at_typed_r _ _ _ _ _ _ _ Hl HMk HΔ' HPl E1) HUs')
          as E2.
        destruct HUs' as [HlU _].
        rewrite List.length_firstn in HlU.
        replace Us' with (List.firstn (ind_nu D) (Us' ++ List.skipn (ind_nu D) (List.map (fun P => P[φ']ʷ) Ps')))
          by (apply firstn_app_exact; unfold im_np in HlP'; lia).
        apply HPc; destruct E1 as [HlE1 HE1]; destruct E2 as [HlE2 HE2]; split; [ congruence |].
        eapply (params_eq_trans _ p D k Mk _ _ _ Hl HMk HΔ' HPl HlP'); [ rewrite <- HlE2; exact HlP' | exact HE1 | exact HE2 ].
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

(** The right side of equal lists at a closed telescope is typed at its
    own instance of the telescope. *)
Lemma tele_eq_typed_r : forall Δ C Xs Ys, all_assumptions C -> ⊢ C ++ Δ ->
    List.length Xs = List.length C -> List.length Ys = List.length C ->
    (forall k X Y T, List.nth_error Xs k = Some X -> List.nth_error Ys k = Some Y ->
       List.nth_error (tele_insts C Id Xs) k = Some T -> Δ ⊢ X ≈ Y : T) ->
    forall j Y T, List.nth_error Ys j = Some Y -> List.nth_error (tele_insts C Id Ys) j = Some T -> Δ ⊢ Y : T.
Proof.
  intros * Hass HC HXl HYl HXY j Y T HY HT.
  assert (HΔ : ⊢ Δ) by (eapply ctx_app_wf_tail; exact HC).
  destruct (nth_error_lt_some Xs j ltac:(rewrite HXl, <- HYl; apply List.nth_error_Some; congruence)) as [X HX].
  destruct (nth_error_lt_some (tele_insts C Id Xs) j) as [T0 HT0].
  { rewrite length_tele_insts by exact Hass.
    assert (j < List.length Ys) by (apply List.nth_error_Some; congruence); lia. }
  destruct (tele_insts_cong C Δ Δ Id Id Xs Ys Hass HC ltac:(apply wf_sub_eq_refl; mauto 3) HXl HYl HXY _ _ _ HT0 HT)
    as (S & HS & HTT).
  eapply wf_conv_sort; [ exact (presup_exp_eq_right (HXY _ _ _ _ HX HY HT0)) | exact (presup_exp_eq_right HTT) | exact HS | exact HTT ].
Qed.

(** Lists equal to the annotations of readbacks related up to proofs, at
    a closed telescope, are equal ([nf_annotate_proofs_upto]). *)
Lemma tele_eq_annotate_upto : forall Δ C Ps Qs W1 W2, all_assumptions C -> ⊢ C ++ Δ ->
    List.length Ps = List.length C -> List.length Qs = List.length C ->
    exps_eq_at Δ C Ps (List.map nf_to_exp (List.map nf_annotate_proofs W1)) ->
    exps_eq_at Δ C Qs (List.map nf_to_exp (List.map nf_annotate_proofs W2)) ->
    nfs_eq_upto_proofs W1 W2 -> exps_eq_at Δ C Ps Qs.
Proof.
  intros * Hass HC HPl HQl HP HQ E.
  set (A1 := List.map nf_to_exp (List.map nf_annotate_proofs W1)) in *.
  set (A2 := List.map nf_to_exp (List.map nf_annotate_proofs W2)) in *.
  destruct HP as [HlP HP], HQ as [HlQ HQ].
  assert (HA1 : List.length A1 = List.length C) by congruence.
  assert (HA2 : List.length A2 = List.length C) by congruence.
  assert (H12 : forall j X Y T, List.nth_error A1 j = Some X -> List.nth_error A2 j = Some Y ->
                  List.nth_error (tele_insts C Id A1) j = Some T -> Δ ⊢ X ≈ Y : T).
  { intros j X Y T HX HY HT.
    unfold A1, A2 in HX, HY; rewrite !List.nth_error_map in HX, HY.
    destruct (List.nth_error W1 j) as [w1 |] eqn:Hw1; [| discriminate ];
      destruct (List.nth_error W2 j) as [w2 |] eqn:Hw2; [| discriminate ]; cbn in HX, HY; injection HX as <-; injection HY as <-.
    destruct (nfs_eq_upto_proofs_nth _ _ _ _ E Hw1) as (w2' & Hw2' & Ew); rewrite Hw2 in Hw2'; injection Hw2' as <-.
    destruct (nth_error_lt_some (tele_insts C Id A2) j) as [T2 HT2].
    { rewrite length_tele_insts by exact Hass; rewrite <- HA2, ?PeanoNat.Nat.min_id; apply List.nth_error_Some.
      unfold A2; rewrite !List.nth_error_map, Hw2; discriminate. }
    eapply nf_annotate_proofs_upto; [ | eexists | exact Ew ].
    - eapply (tele_eq_typed_r Δ C Ps A1 Hass HC HPl HA1 HP); [| exact HT ].
      unfold A1; rewrite !List.nth_error_map, Hw1; reflexivity.
    - eapply (tele_eq_typed_r Δ C Qs A2 Hass HC HQl HA2 HQ); [| exact HT2 ].
      unfold A2; rewrite !List.nth_error_map, Hw2; reflexivity. }
  split; [ congruence |].
  eapply (tele_eq_trans _ C Ps A1 Qs Hass HC HPl HA1 HQl HP).
  eapply (tele_eq_trans _ C A1 A2 Qs Hass HC HA1 HA2 HQl H12).
  eapply (tele_eq_sym _ C Qs A2 Hass HC HQl HA2 HQ).
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
  destruct (HPr _ _ _ Hid HMs) as (W1 & E1 & HPMs); destruct (HQr _ _ _ Hid HMs) as (W2 & E2 & HQMs).
  rewrite (map_wk_id Ps) in HPMs; rewrite (map_wk_id Qs) in HQMs.
  eapply tele_eq_annotate_upto; [ exact Hass | exact HC | exact HPl | exact HQl | exact HPMs | exact HQMs |].
  etransitivity; [ symmetry; exact E1 | exact E2 ].
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
  intros * Hφ Hr; destruct (HR _ _ _ Hφ Hr) as (W' & Hu & Heq).
  exists W'; split; [ exact Hu | eapply lift_exp_eq_ge; eassumption ].
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
  assert (HMn : Γ ⊢ M : A ® m ∈ Eln) by (eapply glu_univ_elem_exp_cumu_ge_universe_index; [ exact Hin | exact Hi | exact Hn | exact HM ]).
  assert (Hn' : DG a' ∈ glu_univ_elem (ul n) ↘ Pn ↘ Eln)
    by (eapply glu_univ_elem_resp_per_univ; [ eexists; eapply per_univ_elem_cumu_universe_index; eassumption | exact Hn ]).
  eapply glu_univ_elem_exp_lower_universe_index; [ exact Hjn | exact Hj | exact Hn' | exact HA | exact HMn ].
Qed.

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
    the gluings are the same ([glu_univ_elem_per_univ_typ_iff]). *)
Lemma glu_univ_elem_per_univ_elem_trm : forall {i a a' R P P' El El' Γ A A' M m},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * HR Hglu Hglu' HA HM.
  assert (Hu : Dom a ≈ a' ∈ per_univ i) by (eexists; exact HR).
  destruct (glu_univ_elem_per_univ_typ_iff Hu Hglu Hglu') as [HPP HEE].
  apply HEE; eapply glu_univ_elem_trm_resp_glu_typ;
    [ exact Hglu | eapply glu_univ_elem_trm_typ; eassumption | apply HPP; exact HA | exact HM ].
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
    intros Δ φ W Hφ Hr; destruct (Hrd _ _ _ Hφ Hr) as (W' & HW' & Heq).
    exists W'; split; [ exact HW' | eapply wf_exp_eq_subtyp'; [ exact Heq | mauto 3 ] ]. }
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
  assert (Hu : Dom a ≈ a' ∈ per_univ i) by (eexists; exact H0).
  destruct (glu_univ_elem_per_univ_typ_iff Hu H5 H12) as [HPP HEE].
  econstructor;
    [ mauto 3 | eapply per_elem_subtyping; [ exact Hs | exact H8 | exact H15 | exact Hm ]
    | exact HA | exact HIT' | exact HOT' | exact HIP' |].
  intros Δ φ N n Hφ HN en.
  assert (en0 : in_rel0 n n) by (apply H10; exact en).
  assert (HN1 : Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl)
    by (eapply glu_univ_elem_trm_resp_glu_typ; [ exact H5 | apply HPP; exact (HIP' _ _ Hφ) | exact (HIP _ _ Hφ) | apply HEE; exact HN ]).
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
    econstructor; [ exact Hσ' | eassumption | eassumption | | eassumption | eassumption |].
    + eapply glu_univ_elem_trm_resp_sub_eq; [ | | exact Hsubeq | eassumption | eassumption ]; mauto 3.
    + eapply IHglu_ctx_env;
        [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
  - (** A definition entry: as an assumption entry, and the tie does not
        mention [σ]. *)
    destruct_by_head cons_def_glu_sub_pred.
    assert (⊢ Γ ▸ A ≔ M) by mauto 3.
    econstructor; [ exact Hσ' | eassumption | eassumption | | eassumption | eassumption | eassumption |].
    + eapply glu_univ_elem_trm_resp_sub_eq; [ | | exact Hsubeq | eassumption | eassumption ]; mauto 3.
    + eapply IHglu_ctx_env;
        [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
  - (** A module slot: the tie does not mention [σ]. *)
    destruct_by_head cons_mod_glu_sub_pred.
    econstructor; [ exact Hσ' | eassumption | eassumption | eassumption |].
    eapply IHglu_ctx_env;
      [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
  - (** A definition with a module part: as a definition entry, and the
        module tie does not mention [σ] either. *)
    destruct_by_head cons_dm_glu_sub_pred.
    assert (⊢ Γ ▸ₘ A ≔ M ‖ U) by (clear Hsubeq Hσ'; gen_presups; assumption).
    econstructor; [ exact Hσ' | eassumption | eassumption | | eassumption | eassumption | eassumption | eassumption |].
    + eapply (glu_univ_elem_trm_resp_sub_eq (κ := ak_relevant)); [ | | exact Hsubeq | eassumption | eassumption ]; mauto 3.
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
  econstructor; [ exact Hσ' | eassumption | eassumption | | eassumption | eassumption |].
  - eapply glu_univ_elem_trm_resp_sub_eq; [ | | exact Heq | eassumption | eassumption ]; mauto 3.
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
  1: { match goal with E : env_rel <~> _ |- _ => apply E end; exact I. }
  1: { destruct_by_head cons_glu_sub_pred.
       match goal with E : env_rel <~> _ |- _ => apply E end.
       assert (Ht : tail_rel ρ↯ ρ↯) by (eapply IHHglu; eassumption).
       unshelve econstructor; [ exact Ht | | assumption | assumption | assumption | assumption ].
       match goal with H : forall ρ0 ρ' (e : tail_rel ρ0 ρ'), rel_typ _ A _ A _ _ |- _ =>
         destruct (H _ _ Ht) as [a1 a2 Ea1 Ea2 HR] end.
       functional_eval_rewrite_clear.
       eapply glu_univ_elem_per_elem_any; eassumption. }
  1: { destruct_by_head cons_def_glu_sub_pred.
       match goal with E : env_rel <~> _ |- _ => apply E end.
       assert (Ht : tail_rel ρ↯ ρ↯) by (eapply IHHglu; eassumption).
       match goal with H : forall ρ0 ρ' (e : tail_rel ρ0 ρ'), rel_typ _ A _ A _ _ |- _ =>
         destruct (H _ _ Ht) as [a1 a2 Ea1 Ea2 HR] end.
       functional_eval_rewrite_clear.
       unshelve econstructor; [ exact Ht | | | assumption | assumption | assumption | assumption ].
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
       econstructor; try eassumption; eapply IHHglu; eassumption. }
  1: { destruct_by_head cons_dm_glu_sub_pred.
       match goal with E : env_rel <~> _ |- _ => apply E end.
       assert (Ht : tail_rel ρ↯ ρ↯) by (eapply IHHglu; eassumption).
       match goal with H : forall ρ0 ρ' (e : tail_rel ρ0 ρ'), rel_typ _ A _ A _ _ |- _ =>
         destruct (H _ _ Ht) as [a1 a2 Ea1 Ea2 HR] end.
       functional_eval_rewrite_clear.
       subst.
       unshelve econstructor; [ exact Ht | | | assumption.. ].
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
    | first [ eassumption | rewrite <- !exp_wk_sub; eapply glu_univ_elem_exp_monotone; eassumption ].. |].
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
  - intros _; eexists; reflexivity.
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
    - intros _; eexists; reflexivity.
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
    - intros _; eexists; reflexivity.
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
    - intros _; eexists; reflexivity.
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
    econstructor; [ mauto 3 | eassumption | eassumption | eassumption | exact HWk ]. }
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
    econstructor; [ mauto 3 | eassumption | exact Hglu | | | eassumption | eassumption | eassumption | exact HWk ].
    - rewrite !exp_sub_id.
      rewrite !exp_sub_of_shift in HMg.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    - exists m; split; [ eassumption |].
      eapply per_head_of; [ eassumption | eassumption | exact HR | exact Hmm ]. }
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

(** The same from the term's scope alone: at a proposition the proof kept
    reads back over an environment of the context. *)
Lemma glu_term_value_intro_scoped : forall {i a P El Γ M Δ A N m ρ R},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exp_scoped (List.length Γ) M ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ ∈ R ->
    (evaluated_kind (domain_kind a) -> ⟦ M ⟧ ρ ↘ m) ->
    Δ ⊢ N : A ® m ∈ El ->
    exists m', glu_term_value M ρ (domain_kind a) m' /\ Δ ⊢ N : A ® m' ∈ El.
Proof.
  intros * Hglu HsM HΓ Hρ Hm HN.
  destruct (domain_kind a) eqn:Hk.
  - exists m; split; [ apply Hm; constructor | exact HN ].
  - (** At a proposition: the proof kept *)
    exists ⋆ᵈ⟨M, ρ⟩; split; [ reflexivity |].
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R' HR'].
    pose proof (per_univ_elem_per_prop_of_kind HR' Hk) as Hp.
    destruct (glu_univ_elem_prop_inv _ _ _ _ Hp Hglu) as [_ HEl].
    apply HEl in HN; apply HEl.
    destruct HN as [HAt HNt _].
    destruct (per_ctx_env_kept_proof_readable _ _ _ M HΓ (exp_scoped_free_bound _ _ HsM) _ _ Hρ) as [Hr _].
    econstructor; [ exact HAt | exact HNt | split; exact Hr ].
  - exists m; split; [ apply Hm; constructor | exact HN ].
Qed.

Lemma glu_term_value_intro : forall {i a P El Γ M B Δ A N m ρ R},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ M : B ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ ∈ R ->
    (evaluated_kind (domain_kind a) -> ⟦ M ⟧ ρ ↘ m) ->
    Δ ⊢ N : A ® m ∈ El ->
    exists m', glu_term_value M ρ (domain_kind a) m' /\ Δ ⊢ N : A ® m' ∈ El.
Proof.
  intros * Hglu HM.
  exact (glu_term_value_intro_scoped Hglu (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HM)))).
Qed.

(** ** Glued Weakenings

    A term judgment weakens along a glued weakening.  As in the PER model
    ([rel_exp_under_ctx_wk]) the values of [M[φ]ʷ] at [ρ] and of [M] at
    [⟪φ⟫ ρ] are not equal, only related ([rel_exp_under_ctx_wk_simple]);
    the gluing moves along the relation. *)
Lemma glu_rel_exp_wk : forall {Γ Δ φ A M},
    Γ ⊩ʷ φ : Δ -> Δ ⊩ M : A -> Γ ⊩ M[φ]ʷ : A[φ]ʷ.
Proof.
  intros * [SbΓ HSbΓ SbΔ HSbΔ _ Hφs Hφg] HM.
  pose proof HM as [SbΔ' HSbΔ' i HMb].
  assert (E : SbΔ <∙> SbΔ') by (eapply functional_glu_ctx_env; eassumption).
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  destruct (rel_exp_under_ctx_wk_simple Hφs (completeness_fundamental_exp _ _ _ HMt)) as (RΓ & HRΓ & j & Hs).
  assert (Hsc : exp_scoped (List.length Γ) M[φ]ʷ).
  { eapply exp_scoped_wk; [ exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HMt))) |].
    exact (rel_wk_under_ctx_bound _ _ _ Hφs). }
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := max i j); [ exact HSbΓ |].
  intros Δ' σ ρ Hσ.
  pose proof (glu_ctx_env_per_env HSbΓ HRΓ Hσ) as Hρ.
  pose proof (Hφg _ _ _ Hσ) as Hσ'; apply E in Hσ'.
  destruct (HMb _ _ _ Hσ') as [a m P El Ea Em Hg HE].
  destruct (Hs _ _ Hρ) as (a1 & a2 & R & Ea1 & Ea2 & HR & Hm).
  assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
  rewrite <- !exp_sub_wk in HE.
  (** The gluing at the weakened type's value, at the larger level *)
  destruct (glu_univ_elem_cumu_max_left (j := j) Hg) as (P' & El' & Hg').
  assert (HE' : Δ' ⊢ M[φ]ʷ[σ] : A[φ]ʷ[σ] ® m ∈ El')
    by (eapply glu_univ_elem_exp_cumu_max_left; [ exact Hg | exact Hg' | exact HE ]).
  pose proof (per_univ_elem_cumu_max_right i j _ _ _ HR) as HRk.
  assert (Hg1 : DG a1 ∈ glu_univ_elem (max i j) ↘ P' ↘ El')
    by (eapply glu_univ_elem_resp_per_univ; [| exact Hg' ]; eexists; symmetry; exact HRk).
  pose proof (per_univ_elem_kind _ _ _ _ HR) as Hk.
  (** The term's value: the weakened term's, moved along the relation *)
  assert (Hev : exists m1, (evaluated_kind (domain_kind a1) -> ⟦ M[φ]ʷ ⟧ ρ ↘ m1) /\ Δ' ⊢ M[φ]ʷ[σ] : A[φ]ʷ[σ] ® m1 ∈ El').
  { destruct (domain_kind a1) eqn:Hk1;
      [| exists m; split; [ intros Hek; inversion Hek | exact HE' ] |].
    all: destruct Hm as [Hp | (m1 & m2 & Em1 & Em2 & Hm12)]; [ congruence |].
    all: exists m1; split; [ intros _; exact Em1 |].
    all: rewrite <- Hk in Em; cbn [glu_term_value] in Em.
    all: pose proof (functional_eval_exp _ _ _ _ Em2 Em) as ->.
    all: destruct (glu_univ_elem_per_univ _ _ _ _ Hg') as [R2 HR2].
    all: pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRk HR2) as ER.
    all: assert (HPR : PER R2) by (eapply per_elem_PER; exact HR2).
    all: apply (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hg' _ HR2 _ _ _ _ _ HE'); symmetry; apply ER; exact Hm12. }
  destruct Hev as (m1 & Em1 & HE1).
  destruct (glu_term_value_intro_scoped Hg1 Hsc HRΓ Hρ Em1 HE1) as (m' & Hm' & HN).
  econstructor; [ exact Ea1 | exact Hm' | exact Hg1 | exact HN ].
Qed.

(** ** Glued Substitutions

    A term judgment moves along a glued substitution, as along a glued
    weakening: the values of [M[τ]] at [ρ] and of [M] at the value of [τ]
    at [ρ] are related by the judgment of [M] in the PER model, read along
    [τ]. *)
Lemma glu_rel_exp_sub : forall {Γ Δ τ A M},
    Γ ⊩ˢ τ : Δ -> Δ ⊩ M : A -> Γ ⊩ M[τ] : A[τ].
Proof.
  intros * [SbΓ HSbΓ SbΔ HSbΔ Hτt Hτs Hτg] HM.
  pose proof HM as [SbΔ' HSbΔ' i HMb].
  assert (E : SbΔ <∙> SbΔ') by (eapply functional_glu_ctx_env; eassumption).
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HMt Hτt) as HMτ.
  destruct (completeness_fundamental_exp _ _ _ HMt) as [RΔ HRΔ j HMgen].
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [RΓ HRΓ].
  destruct (rel_sub_under_ctx_simple Hτs) as [RΓ1 [HRΓ1 [RΔ1 [HRΔ1 Hs]]]].
  assert (E1 : RΓ <~> RΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ HMt)) as (RΔ2 & HRΔ2 & j2 & Hsim).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := max i j); [ exact HSbΓ |].
  intros Δ' σ ρ Hσ.
  pose proof (glu_ctx_env_per_env HSbΓ HRΓ Hσ) as Hρ.
  destruct (Hs _ _ (proj1 (E1 _ _) Hρ)) as [ρτ0 [ρτ0' [Hev [_ _]]]].
  destruct (Hτg _ _ _ Hσ) as (ρτ & Hσ' & Hrel); apply E in Hσ'.
  pose proof (Hrel _ _ HRΔ2 Hev) as Hρτ.
  destruct (HMb _ _ _ Hσ') as [a m P El Ea Em Hg HE].
  rewrite <- !exp_sub_sub in HE.
  (** The substituted judgment's values at [ρ] against [M]'s at the value
      of [τ], and those against [M]'s at the glued environment *)
  destruct (HMgen _ _ HRΓ _ _ Hτs _ _ _ _ Hρ Hev Hev) as [R [Htyp Hexp]].
  pose proof Htyp as [a1 a2 a3 a4 Ea1 Ea2 _ _ Hch].
  destruct Hch as (HR & _).
  destruct (Hsim _ _ Hρτ) as (b & b' & R' & Eb & Eb' & HR' & Hm').
  assert (b = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (b' = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (HR22 : DF a2 ≈ a2 ∈ per_univ_elem j ↘ R) by (eapply per_univ_trans; [ apply per_univ_sym; exact HR | exact HR ]).
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR22 HR') as ERR'.
  assert (HRR' : DF a2 ≈ a ∈ per_univ_elem j2 ↘ R) by (eapply per_univ_elem_resp_iff; [ exact HR' | symmetry; exact ERR' ]).
  pose proof (per_univ_trans _ _ _ _ _ _ HR HRR') as HR1.
  assert (HPR0 : PER R) by (eapply per_elem_PER; exact HR).
  (** The gluing at the substituted type's value, at the larger level *)
  destruct (glu_univ_elem_cumu_max_left (j := j) Hg) as (P' & El' & Hg').
  assert (HE' : Δ' ⊢ M[τ][σ] : A[τ][σ] ® m ∈ El')
    by (eapply glu_univ_elem_exp_cumu_max_left; [ exact Hg | exact Hg' | exact HE ]).
  pose proof (per_univ_elem_cumu_max_right i j _ _ _ HR1) as HRk.
  assert (Hg1 : DG a1 ∈ glu_univ_elem (max i j) ↘ P' ↘ El')
    by (eapply glu_univ_elem_resp_per_univ; [| exact Hg' ]; eexists; symmetry; exact HRk).
  pose proof (per_univ_elem_kind _ _ _ _ HR1) as Hk.
  pose proof (per_univ_elem_kind _ _ _ _ HR) as Hk2.
  (** The term's value: the substituted term's, moved along the relation *)
  assert (Hv : exists m1, (evaluated_kind (domain_kind a1) -> ⟦ M[τ] ⟧ ρ ↘ m1) /\ Δ' ⊢ M[τ][σ] : A[τ][σ] ® m1 ∈ El').
  { destruct (domain_kind a1) eqn:Hk1;
      [| exists m; split; [ intros Hek; inversion Hek | exact HE' ] |].
    all: destruct Hexp as [(c & Hc & Hp) | [v1 v2 v3 v4 Hv1 Hv2 _ _ Hvc]];
      [ assert (c = a1) as -> by (eapply functional_eval_exp; eassumption); congruence |].
    all: destruct Hm' as [Hp' | (w2 & w & Ew2 & Ew & Hw)]; [ congruence |].
    all: destruct Hvc as (Hm12 & _).
    all: exists v1; split; [ intros _; exact Hv1 |].
    all: rewrite <- Hk in Em; cbn [glu_term_value] in Em.
    all: pose proof (functional_eval_exp _ _ _ _ Ew Em) as ->.
    all: pose proof (functional_eval_exp _ _ _ _ Ew2 Hv2) as ->.
    all: assert (Hm12' : R v1 m) by (etransitivity; [ exact Hm12 | apply ERR'; exact Hw ]).
    all: clear Hm12; rename Hm12' into Hm12.
    all: destruct (glu_univ_elem_per_univ _ _ _ _ Hg') as [R2 HR2].
    all: pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRk HR2) as ER.
    all: assert (HPR : PER R2) by (eapply per_elem_PER; exact HR2).
    all: apply (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hg' _ HR2 _ _ _ _ _ HE'); symmetry; apply ER; exact Hm12. }
  destruct Hv as (m1 & Em1 & HE1).
  destruct (glu_term_value_intro Hg1 HMτ HRΓ Hρ Em1 HE1) as (m' & Hmv & HN).
  econstructor; [ exact Ea1 | exact Hmv | exact Hg1 | exact HN ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_to_wf_exp : mctt.
