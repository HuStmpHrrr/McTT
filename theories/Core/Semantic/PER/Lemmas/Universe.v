(** * PER Lemmas: the Universe PER

    The second part of [Core.Semantic.PER.Lemmas]: related types are of
    one kind; [per_univ_elem] is right irrelevant, symmetric and
    transitive; chains of related types. *)
From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions PER.Tele.
From Mctt.Core.Semantic.PER.Lemmas Require Export Basic.
Import Domain_Notations Fixed_Notations.
Import ListNotations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Related types are of one sort: both propositions or both relevant. *)
Lemma per_univ_elem_kind : forall i R a a',
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    domain_kind a = domain_kind a'.
Proof.
  intros * H; per_univ_elem_induction H; intros; try reflexivity.
  all: try match goal with Hp : per_prop _ _ |- _ => destruct Hp end; congruence.
Qed.

(** So are two types related modulo evaluation. *)
Lemma rel_mod_eval_kind : forall (Rel : relation domain -> domain -> domain -> Prop) A ρ A' ρ' R r,
    (forall R x y, Rel R x y -> domain_kind x = domain_kind y) ->
    rel_mod_eval Rel A ρ A' ρ' R -> rel_typ_kind A ρ r -> rel_typ_kind A' ρ' r.
Proof.
  intros * Hrel [a a' Ha Ha' HR] (a0 & Ha0 & Hr).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  exists a'; split; [ exact Ha' | rewrite <- (Hrel _ _ _ HR); exact Hr ].
Qed.

Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF a ≈ b' ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen a' b' R'.
  per_univ_elem_induction Horig; intros * Heq Hright;
    subst; basic_invert_per_univ_elem Hright; unfold per_univ;
    intros;
    apply_relation_equivalence;
    try reflexivity.
  (** A record type: the fields' relations agree with those of the other
      derivation along related prefixes, the field types being the same. *)
  3: {
    assert (R0 = R) as -> by congruence.
    assert (Hfr : forall k pa pb1 pb2, k < List.length (record_fields R) -> tele_prefix_rel fr k pa pb1 ->
                    tele_prefix_rel fr0 k pa pb2 -> (fr k pa <~> fr0 k pa)).
    { intros k pa pb1 pb2 Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [[f T] HT].
      match goal with
      | Hf1 : fields_evals _ R _ _ fr, Hf2 : fields_evals _ R _ _ fr0 |- _ =>
          destruct (Hf1 _ _ _ _ _ HT Hp1) as [a1 a1' E1 E1' [Hper Hmot]];
          destruct (Hf2 _ _ _ _ _ HT Hp2) as [a2 a2' E2 E2' Hper2]
      end.
      functional_eval_rewrite_clear; exact (Hmot _ _ _ eq_refl Hper2). }
    intros v v'; split; apply record_rel_change; intros;
      [ eapply Hfr; eassumption | symmetry; eapply Hfr; eassumption ]. }
  (** An inductive type: the telescope relations agree with those of the
      other derivation, and so do the elements. *)
  2: {
    assert (D0 = D) as -> by congruence.
    match goal with H1 : ind_member D k = Some ?M1, H2 : ind_member D k = Some ?M2 |- _ =>
      assert_fails constr_eq M1 M2; rewrite H1 in H2; injection H2 as <- end.
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    rename H into Hl, H0 into Hass, H1 into HM, H2 into Hh, H6 into HnP, H7 into Hn, H8 into HnI, H9 into HaP, H10 into Ha,
      H11 into HaI, H12 into HdP, H13 into Hd, H14 into HdI, H17 into Hns.
    rename H26 into HnP0, H27 into Hn0, H28 into HnI0, H29 into HaP0, H30 into Ha0, H31 into HaI0, H32 into HdP0, H33 into Hd0,
      H34 into HdI0, H37 into Hns0.
    assert (Hnr : forall m Mm kk vs vs1 vs2, ind_member D m = Some Mm -> kk < List.length (List.rev (im_nparams Mm)) ->
                    tele_prefix_rel (nr m) kk vs vs1 -> tele_prefix_rel (nr0 m) kk vs vs2 -> (nr m kk vs <~> nr0 m kk vs)).
    { intros m Mm kk vs vs1 vs2 Hm Hk Hp1 Hp2.
      destruct (nparams_lt_ass D m Mm kk Hass Hm Hk) as (κ & A & HA).
      destruct (Hn _ _ _ _ _ _ _ Hm HA Hp1) as [a1 a1' E1 E1' [Hper Hmot]].
      destruct (Hn0 _ _ _ _ _ _ _ Hm HA Hp2) as [a2 a2' E2 E2' Hper2].
      functional_eval_rewrite_clear; exact (Hmot _ _ _ eq_refl Hper2). }
    assert (Har : forall m Mm ms ms1 ms2 c gs kk vs vs1 vs2, ind_member D m = Some Mm ->
               tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> kk < List.length (cargs_nonrec gs) ->
               tele_prefix_rel (ar m ms c) kk vs vs1 -> tele_prefix_rel (ar0 m ms c) kk vs vs2 ->
               (ar m ms c kk vs <~> ar0 m ms c kk vs)).
    { intros m Mm ms ms1 ms2 c gs kk vs vs1 vs2 Hm Hm1 Hm2 Hc Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm Hm1 Hc HA Hp1) as [a1 a1' E1 E1' [Hper Hmot]].
      destruct (Ha0 _ _ _ _ _ _ _ _ _ _ Hm Hm2 Hc HA Hp2) as [a2 a2' E2 E2' Hper2].
      functional_eval_rewrite_clear; exact (Hmot _ _ _ eq_refl Hper2). }
    assert (Hdr : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 kk ys ys1 ys2, ind_member D m = Some Mm ->
               tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
               tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
               tele_prefix_rel (ar0 m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
               kk < List.length (ptyp_doms t) ->
               tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) kk ys ys1 ->
               tele_prefix_rel (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) kk ys ys2 ->
               (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t kk ys <~> shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t kk ys)).
    { intros m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 kk ys ys1 ys2 Hm Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      unfold shape_doms_rel at 1 2; rewrite (List.nth_error_nth _ _ _ HB).
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hm1 Hc Heq Hw1 HB Hp1) as [a1 a1' E1 E1' [Hper Hmot]].
      destruct (Hd0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hm2 Hc Heq Hw2 HB Hp2) as [a2 a2' E2 E2' Hper2].
      functional_eval_rewrite_clear; exact (Hmot _ _ _ eq_refl Hper2). }
    (** The elements: the relations, the admissible bases and indices
        change ([ind_rel_change]), the right index moves ([ind_rel_idx]),
        and a declared member's elements read no given base. *)
    assert (HnB : forall m Mm kk vs vs1 vs2, ind_member D m = Some Mm -> kk < List.length (List.rev (im_nparams Mm)) ->
                    tele_prefix_rel (nr0 m) kk vs vs1 -> tele_prefix_rel (nr m) kk vs vs2 -> (nr0 m kk vs <~> nr m kk vs))
      by (intros; symmetry; eapply Hnr; eassumption).
    assert (HaB : forall m Mm ms ms1 ms2 c gs kk vs vs1 vs2, ind_member D m = Some Mm ->
               tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> kk < List.length (cargs_nonrec gs) ->
               tele_prefix_rel (ar0 m ms c) kk vs vs1 -> tele_prefix_rel (ar m ms c) kk vs vs2 ->
               (ar0 m ms c kk vs <~> ar m ms c kk vs))
      by (intros; symmetry; eapply Har; eassumption).
    assert (HdB : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 kk ys ys1 ys2, ind_member D m = Some Mm ->
               tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
               tele_prefix_rel (ar0 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
               tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
               kk < List.length (ptyp_doms t) ->
               tele_prefix_rel (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) kk ys ys1 ->
               tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) kk ys ys2 ->
               (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t kk ys <~> shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t kk ys))
      by (intros; symmetry; eapply Hdr; eassumption).
    pose proof (tele_rel_nr_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr _ _ HM _ _ Hns) as Hns'.
    pose proof (tele_rel_nr_change' p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr _ _ HM _ _ Hns0) as Hns0'.
    unfold grp_rel; intros m m'; split; intro Hm.
    - eapply (proj1 (ind_rel_base_r p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 ups'0 H35 ups'
                       (adm_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr ups' H15))); [| reflexivity ].
      eapply (ind_rel_idx p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ _ _ _ ns ns' _ _ _ _ HM);
        [ eapply (proj1 (ind_rel_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr _ _
                           (admissible_index_at_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr)
                           (fun m Mm a b Hm H => nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm a b H)));
          exact Hm
        | exact (nparams_rel_refl_l p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ HM _ _ Hns0)
        | exact (nparams_rel_trans p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ HM _ _ _
                   (nparams_rel_sym p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ HM _ _ Hns') Hns0) ].
    - eapply (proj1 (ind_rel_base_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' H15 ups'0
                       (adm_change p D ups nr0 nr ar0 ar dr0 dr HnB HaB HdB ups'0 H35))); [| reflexivity ].
      eapply (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ ns ns'0 _ _ _ _ HM);
        [ eapply (proj1 (ind_rel_change p D ups nr0 nr ar0 ar dr0 dr HnB HaB HdB _ _
                           (admissible_index_at_change p D ups nr0 nr ar0 ar dr0 dr HnB HaB HdB)
                           (fun m Mm a b Hm H => nparams_rel_refl_r p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 m Mm Hm a b H)));
          exact Hm
        | exact (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns)
        | exact (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ _
                   (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns0') Hns) ]. }
  (** A [Π]: the domains are related, so of one sort. *)
  match goal with H1 : per_univ_elem _ in_rel a a' |- _ => pose proof (per_univ_elem_kind _ _ _ _ H1) as Ea end.
  pose proof (per_univ_elem_kind _ _ _ _ equiv_a_a') as Ea0.
  specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  split; intros [Hl Hr Happ]; constructor; try congruence.
  - intros c c' equiv0_c_c'.
    assert (equiv_c_c' : in_rel c c') by firstorder;
    (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear;
     econstructor; intuition).
  - intros c c' equiv_c_c'.
    assert (equiv0_c_c' : in_rel0 c c') by firstorder;
      (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear;
       econstructor; intuition).
Qed.

End Fixed_GCtx.

#[local]
Ltac per_univ_elem_right_irrel_assert1 :=
  match goal with
  | H1 : (DF ?a ≈ ?b ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF ?a ≈ ?b' ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_univ_elem_right_irrel_assert := repeat per_univ_elem_right_irrel_assert1.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_sym : forall i R a b,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b ≈ a ∈ per_univ_elem i ↘ R /\
      (forall m m',
          Dom m ≈ m' ∈ R ->
          Dom m' ≈ m ∈ R).
Proof.
  simpl.
  per_univ_elem_induction1; subst.
  - split.
    + apply per_univ_elem_core_univ'; firstorder.
    + intros m m' Hm.
      match goal with HE : _ <~> per_universe_elements _ |- _ => apply HE in Hm; apply HE end.
      destruct Hm as [[R' HR] Hl Hr]; constructor; [| exact Hr | exact Hl ].
      eexists.
      eapply proj1; mautosolve.
  - (** The two levels are related, hence have the same realiser, so the
        index of the elements is the same on both sides. *)
    assert (Heq : domain_level_real l = domain_level_real l') by (apply per_lvl_real; assumption).
    split.
    + apply per_univ_elem_core_suniv';
        [ apply per_lvl_sym; assumption | rewrite <- Heq | rewrite <- Heq ]; assumption.
    + intros m m' Hm.
      match goal with HE : _ <~> per_universe_elements _ |- _ => apply HE in Hm; apply HE end.
      destruct Hm as [[R' HR] Hl Hr]; constructor; [| exact Hr | exact Hl ].
      eexists.
      eapply proj1; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - (** [LevelSort]: its elements are symmetric as types of the least
        small index. *)
    split.
    + basic_per_univ_elem_econstructor; eassumption.
    + intros m m' Hm; apply_relation_equivalence; unfold per_level_sort, per_level_sort_at in *.
      destruct Hm as [Hl [Hr HR]]; destruct HR as [R HR].
      match goal with IH : forall A B R, per_univ_elem _ R A B -> _ /\ _ |- _ => destruct (IH _ _ _ HR) as [HR' _] end.
      split; [ exact Hr | split; [ exact Hl | eexists; exact HR' ] ].
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - destruct_conjs.
    match goal with H1 : per_univ_elem _ in_rel a a' |- _ => pose proof (per_univ_elem_kind _ _ _ _ H1) as Ea end.
    split.
    + basic_per_univ_elem_econstructor; eauto.
      2: { intros c c' Hc; assert (Hc' : in_rel c' c) by eauto.
           match goal with
           | HT : forall c c' (e : in_rel c c'), rel_mod_eval _ B _ B' _ _,
             HB : forall c c' (e : in_rel c c'), rel_typ_kind B _ _ |- _ =>
               exact (rel_mod_eval_kind _ _ _ _ _ _ _ (fun _ _ _ H => per_univ_elem_kind _ _ _ _ (proj1 H))
                        (HT _ _ Hc') (HB _ _ Hc'))
           end. }
      2: { etransitivity; [ eassumption | apply pi_elements_kind_irrel; congruence ]. }
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      apply_relation_equivalence.
      eassumption.
    + apply_relation_equivalence.
      intros m m' [Hl Hr Happ]; constructor; [ congruence | congruence |].
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      intuition.
  - split; [econstructor | intros; apply_relation_equivalence]; mautosolve.
  - (** An inductive type: the same relations serve the swapped type, by
        the invariance of [nr] and [ar] along related prefixes and the
        symmetry of their types; the elements are swapped by
        [ind_rel_sym_all], their indices exchanged by [ind_rel_idx], and the
        bases admissible beside [ups] are those admissible beside [ups']
        ([adm_iff]). *)
    rename H into Hl, H0 into Hass, H1 into HM, H2 into Hh, H3 into Hu, H4 into Hu', H5 into Hps, H6 into HnP, H7 into Hn,
      H8 into HnI, H9 into HaP, H10 into Ha, H11 into HaI,
      H12 into HdP, H13 into Hd, H14 into HdI, H15 into Hcl, H16 into Hcd, H17 into Hns,
      H18 into HE.
    pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns) as Hsn.
    pose proof (adm_flip p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl Hcd) as Hfl.
    split.
    + basic_per_univ_elem_econstructor;
        [ exact Hl | exact Hass | exact HM | exact Hh | exact Hu' | exact Hu | exact (per_top_ps_sym _ _ _ Hps) | exact HnP | | exact HnI
        | exact HaP | | exact HaI | exact HdP | | exact HdI | exact Hfl
        | exact (adm_diag_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl) | exact Hsn |].
      * intros m Mm k0 κ A vs vs' Hm Hk Hp.
        assert (Hkl : k0 < List.length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        pose proof (nparams_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm k0 vs vs' ltac:(lia) Hp) as Hp'.
        destruct (Hn _ _ _ _ _ _ _ Hm Hk Hp') as [a a' Ea Ea' (_ & Hsym & _)].
        econstructor; [ exact Ea' | exact Ea |].
        eapply per_univ_elem_resp_iff; [ exact Hsym |]; symmetry; exact (HnI _ _ _ _ _ _ _ Hm Hk Hp).
      * intros m Mm ms ms' c gs k0 A vs vs' Hm0 Hm Hc Hk Hp.
        assert (Hkl : k0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        assert (Hp' : tele_prefix_rel (ar m ms' c) k0 vs' vs)
          by (eapply (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0); [ exact Hm | exact Hc | lia |];
              eapply (args_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0);
                [ exact (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm) | exact Hc | lia | exact Hp ]).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm0 (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm) Hc Hk Hp')
          as [a a' Ea Ea' (_ & Hsym & _)].
        econstructor; [ exact Ea' | exact Ea |].
        eapply per_univ_elem_resp_iff; [ exact Hsym |]; symmetry; exact (HaI _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk Hp).
      * intros m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' Hm0 Hm Hc Heq Hp HB Hy.
        assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        assert (Hkl : k0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm) as Hmm.
        assert (Hp' : tele_prefix_rel (ar m ms' c) (List.length (cargs_nonrec gs1)) ws' ws)
          by (eapply (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0); [ exact Hm | exact Hc | exact Hk1 |];
              eapply (args_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0); [ exact Hmm | exact Hc | exact Hk1 | exact Hp ]).
        pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs Hmm Hc _ ws ws' Hk1 Hp) as Hww.
        assert (Hy' : tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms' ws' t) k0 ys' ys).
        { eapply (doms_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0);
            [ exact Hm | exact Hc | exact Heq | exact Hp | lia |].
          eapply (doms_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs gs1 t gs2 ws Hmm Hc Heq Hww);
            [ lia | exact Hy ]. }
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm)
                    Hc Heq Hp' HB Hy')
          as [a a' Ea Ea' (_ & Hsym & _)].
        econstructor; [ exact Ea' | exact Ea |].
        eapply per_univ_elem_resp_iff; [ exact Hsym |]; symmetry; exact (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Heq Hp HB Hy).
      * (** The elements: at the bases admissible beside [ups'], which are
            those beside [ups] ([ind_rel_admissible_index_base]), at the exchanged
            indices. *)
        unfold grp_rel; intros m m'; split; intro Hm0.
        -- apply HE in Hm0; unfold grp_rel in Hm0.
           eapply (ind_rel_idx p D ups' nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ ns ns' _ _ _ _ HM); [| exact Hns | exact Hsn ].
           apply (proj1 (ind_rel_admissible_index_base p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl)).
           apply (ind_rel_bases p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ ups ups' _ _ _ _ _ _ Hcd Hcl Hcl Hcd).
           exact Hm0.
        -- apply HE; unfold grp_rel.
           eapply (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ ns' ns _ _ _ _ HM); [| exact Hsn | exact Hns ].
           apply (proj1 (ind_rel_admissible_index_base p D ups' nr ar dr Hass HnP HnI HaP HaI HdP HdI ups Hfl)).
           apply (ind_rel_bases p D ups' nr ar dr Hass HnP HnI HaP HaI HdP HdI _ ups' ups _ _ _ _ _ _
                    (adm_diag_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl) Hfl Hfl
                    (adm_diag_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl)).
           exact Hm0.
    + intros m m' Hm0; apply HE in Hm0; apply HE; unfold grp_rel in *.
      pose proof (proj1 (ind_rel_sym_all p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _) _ _ _ _ _ _ _ Hm0) as Hm1.
      apply (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ ns' ns _ _ _ _ HM); [| exact Hsn | exact Hns ].
      exact (ind_rel_bases p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ ups' ups _ _ _ _ _ _ Hcl Hcd Hcd Hcl Hm1).
  - (** A record type: the same field relations serve the swapped type, by
        their invariance along related prefixes and the symmetry of the
        field types; the elements are swapped by [record_rel_sym]. *)
    rename H into Hl, H0 into Hnd, H1 into Hn, H2 into Hn', H3 into Hps, H4 into HfP, H5 into Hf, H6 into HfS, H7 into HfI,
      H8 into HE.
    split.
    + basic_per_univ_elem_econstructor;
        [ exact Hl | exact Hnd | exact Hn' | exact Hn | exact (per_top_ps_sym _ _ _ Hps) | exact HfP | | | exact HfI | exact HE ].
      * intros k f T vs vs' Hk Hp.
        assert (Hkl : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
        pose proof (fields_prefix_sym R fr HfP HfI k vs vs' ltac:(lia) Hp) as Hp'.
        destruct (Hf _ _ _ _ _ Hk Hp') as [a a' Ea Ea' (_ & Hsym & _)].
        econstructor; [ exact Ea' | exact Ea |].
        eapply per_univ_elem_resp_iff; [ exact Hsym |]; symmetry; exact (HfI _ _ _ _ _ Hk Hp).
      * (** The sorts at the right parameters: those at the left ones, along
            the swapped prefixes. *)
        intros k f T vs vs' Hk Hp.
        assert (Hkl : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
        pose proof (fields_prefix_sym R fr HfP HfI k vs vs' ltac:(lia) Hp) as Hp'.
        eapply rel_mod_eval_kind; [ | exact (Hf _ _ _ _ _ Hk Hp') | exact (HfS _ _ _ _ _ Hk Hp') ].
        intros ? ? ? [Hx _]; exact (per_univ_elem_kind _ _ _ _ Hx).
    + intros m m' Hm; apply HE in Hm; apply HE; exact (record_rel_sym R fr HfP HfI _ _ Hm).
Qed.

Corollary per_univ_sym : forall i R a b,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b ≈ a ∈ per_univ_elem i ↘ R.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_sym' : forall i a b,
    Dom a ≈ b ∈ per_univ i ->
    Dom b ≈ a ∈ per_univ i.
Proof.
  intros * [? ?%per_univ_elem_sym].
  firstorder.
Qed.

Corollary per_elem_sym : forall i R a b m m',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Dom m ≈ m' ∈ R ->
    Dom m' ≈ m ∈ R.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_elem_left_irrel : forall i i' R a b R' a',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF a' ≈ b ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  intros * ?%per_univ_sym ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Corollary per_univ_elem_cross_irrel : forall i i' R a b R' b',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b' ≈ a ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  intros * ? ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

End Fixed_GCtx.

Ltac do_per_univ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_univ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (DF ?a ≈ _ ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF ?a ≈ _ ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : (DF _ ≈ ?b ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF _ ≈ ?b ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : (DF ?a ≈ _ ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF _ ≈ ?a ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      (** Order matters less here, as [H1] and [H2] cannot be exchanged. *)
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_univ_elem_irrel_assert :=
  repeat do_per_univ_elem_irrel_assert1.

Ltac handle_per_univ_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_trans : forall i R a1 a2,
    per_univ_elem i R a1 a2 ->
    (forall j a3,
        per_univ_elem j R a2 a3 ->
        per_univ_elem i R a1 a3) /\
      (forall m1 m2 m3,
          R m1 m2 ->
          R m2 m3 ->
          R m1 m3).
Proof.
  per_univ_elem_induction1;
    [> split;
     [ intros * HT2; basic_invert_per_univ_elem HT2
     | intros * HTR1 HTR2; apply_relation_equivalence ] ..]; mauto.
  - (** The univ case. *)
    subst.
    destruct HTR1 as [HTR1 ? ?], HTR2 as [HTR2 ? ?]; constructor; [| assumption .. ].
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    specialize (H2 _ _ _ H0) as [].
    intuition.
  - (** The small univ case.  Unlike the large one there is no equation
        between the two levels to substitute, so the transitivity of the
        elements is taken from the first of the two derivations. *)
    destruct HTR1 as [HTR1 ? ?], HTR2 as [HTR2 ? ?]; constructor; [| assumption .. ].
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    match goal with
    | HA : per_univ_elem _ ?R ?a ?b, HB : per_univ_elem _ ?R ?b ?c |- per_univ_elem _ _ ?a ?c =>
        specialize (H2 _ _ _ HA) as []
    end.
    intuition.
  - (** The [Level] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The [Prop] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The [LevelSort] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The elements of [LevelSort]: transitive as types of the least
        small index, the two relations identified by irrelevance. *)
    unfold per_level_sort, per_level_sort_at in *.
    destruct HTR1 as [Hl1 [_ [R1 Hm12]]], HTR2 as [_ [Hl3 [R2 Hm23]]].
    assert (E : R2 <~> R1)
      by (eapply per_univ_elem_right_irrel; [ exact Hm23 | apply per_univ_sym; exact Hm12 ]).
    assert (Hm23' : DF m2 ≈ m3 ∈ per_univ_elem (us (0, 0)) ↘ R1)
      by (eapply per_univ_elem_resp_iff; [ exact Hm23 | exact E ]).
    match goal with IH : forall A B R, per_univ_elem _ R A B -> (forall j a3, _) /\ _ |- _ =>
      destruct (IH _ _ _ Hm12) as [IH1 _] end.
    split; [ exact Hl1 | split; [ exact Hl3 | eexists; exact (IH1 _ _ Hm23') ] ].
  - (** A proposition. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The pi case. *)
    destruct_conjs.
    basic_per_univ_elem_econstructor; eauto.
    4: { etransitivity; [ eassumption | apply pi_elements_kind_irrel;
                                          [ symmetry; eapply per_univ_elem_kind; eassumption | reflexivity ] ]. }
    3: { intros c c' Hc.
         match goal with HB : forall c c' (e : in_rel c c'), rel_typ_kind B _ _ |- _ => apply (HB c c') end.
         handle_per_univ_elem_irrel; intuition. }
    + handle_per_univ_elem_irrel.
      intuition.
    + intros.
      handle_per_univ_elem_irrel.
      assert (in_rel c c') by firstorder.
      assert (in_rel c c) by intuition.
      assert (in_rel0 c c) by intuition.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      handle_per_univ_elem_irrel; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The function case. *)
    destruct HTR1 as [Hl1 Hr1 HTR1], HTR2 as [Hl2 Hr2 HTR2]; constructor; [ assumption | assumption |].
    intros.
    assert (in_rel c c) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intuition.
  - (** The neut case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** An inductive type.  The relations of the first derivation serve the
        composite: those of the second agree with them along related
        prefixes, as the relations of types with a common side. *)
    assert (D0 = D) as -> by congruence.
    assert (M0 = M) as -> by congruence.
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    rename H into Hl, H0 into Hass, H1 into HM, H2 into Hh, H3 into Hu, H4 into Hu', H5 into Hps, H6 into HnP, H7 into Hn,
      H8 into HnI, H9 into HaP, H10 into Ha, H11 into HaI, H12 into HdP, H13 into Hd, H14 into HdI,
      H15 into Hcl, H16 into Hcd, H17 into Hns, H18 into HE.
    rename H23 into Hu2, H24 into Hu2', H25 into Hps2, H26 into HnP2, H27 into Hn2, H28 into HnI2,
      H29 into HaP2, H30 into Ha2, H31 into HaI2, H32 into HdP2, H33 into Hd2, H34 into HdI2,
      H35 into Hcl2, H37 into Hns2.
    assert (Hcr : forall m Mm k pa pb pc, ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr m) k pa pb -> tele_prefix_rel (nr0 m) k pb pc -> (nr m k pa <~> nr0 m k pb)).
    { intros m Mm k0 pa pb pc Hm Hk Hp1 Hp2.
      destruct (nparams_lt_ass D m Mm k0 Hass Hm Hk) as (κ & A & HA).
      destruct (Hn _ _ _ _ _ _ _ Hm HA Hp1) as [a a' Ea Ea' (Hper & _)].
      destruct (Hn2 _ _ _ _ _ _ _ Hm HA Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact Hper | apply per_univ_sym; exact Hper2 ]. }
    assert (Hacr : forall m Mm ms ms' ms'' c gs k pa pb pc, ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms' ms'' ->
              ind_con Mm c = Some gs -> k < List.length (cargs_nonrec gs) ->
              tele_prefix_rel (ar m ms c) k pa pb -> tele_prefix_rel (ar0 m ms' c) k pb pc -> (ar m ms c k pa <~> ar0 m ms' c k pb)).
    { intros m Mm ms ms' ms'' c gs k0 pa pb pc Hm0 Hm1 Hm2 Hc Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm0 Hm1 Hc HA Hp1) as [a a' Ea Ea' (Hper & _)].
      destruct (Ha2 _ _ _ _ _ _ _ _ _ _ Hm0 Hm2 Hc HA Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact Hper | apply per_univ_sym; exact Hper2 ]. }
    assert (HnP0 : forall m Mm k vs vs', ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr0 m) k vs vs' -> PER (nr0 m k vs))
      by (intros m Mm k0 ? ? Hm Hk ?; destruct (nparams_lt_ass D m Mm k0 Hass Hm Hk) as (κ & A & HA); eapply HnP2; eassumption).
    assert (HnP1 : forall m Mm k vs vs', ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr m) k vs vs' -> PER (nr m k vs))
      by (intros m Mm k0 ? ? Hm Hk ?; destruct (nparams_lt_ass D m Mm k0 Hass Hm Hk) as (κ & A & HA); eapply HnP; eassumption).
    assert (Hrefl0 : forall m Mm ms ms'', ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms'' ->
              tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms'' ms'').
    { intros * Hm0 Hm; eapply (tele_rel_cross_refl _ (nr m) (nr0 m)); [ | exact (fun k0 vs vs' => HnP0 m Mm k0 vs vs' Hm0) | exact Hm ].
      intros k0 pa pb Hk Hp1 Hp2; exact (Hcr _ _ _ _ _ _ Hm0 Hk Hp1 Hp2). }
    assert (Hcomp : forall m Mm a b c, ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) a b -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) b c ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) a c).
    { intros * Hm0 H1 H2; eapply (tele_rel_compose_cross _ (nr m) (nr0 m)); [ | exact (fun k0 vs vs' => HnP1 m Mm k0 vs vs' Hm0) | exact H1 | exact H2 ].
      intros k0 pa pb pc Hk Hp1 Hp2; exact (Hcr _ _ _ _ _ _ Hm0 Hk Hp1 Hp2). }
    assert (Haprefl : forall m Mm ms ms'' c gs k vs vs'', ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms'' ->
              ind_con Mm c = Some gs -> k <= List.length (cargs_nonrec gs) ->
              tele_prefix_rel (ar m ms c) k vs vs'' -> tele_prefix_rel (ar0 m ms'' c) k vs'' vs'').
    { intros * Hm0 Hm Hc Hk Hp.
      eapply (tele_prefix_rel_cross_refl (ar m ms c) (ar0 m ms'' c) (List.length (cargs_nonrec gs))); [ exact Hk | | | exact Hp ].
      - intros j0 pa pb Hj Hp1 Hp2; exact (Hacr _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Hj Hp1 Hp2).
      - intros j0 ? ? Hj ?; destruct (nth_error_lt_some' _ _ Hj) as [A HA].
        eapply HaP2; [ exact Hm0 | exact (Hrefl0 _ _ _ _ Hm0 Hm) | exact Hc | exact HA | eassumption ]. }
    assert (Hdcr : forall m Mm ms ms' ms'' c gs gs1 t gs2 ws ws' ws'' k ys ys' ys'', ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms' ms'' ->
              ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
              tele_prefix_rel (ar0 m ms' c) (List.length (cargs_nonrec gs1)) ws' ws'' ->
              k < List.length (ptyp_doms t) ->
              tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys' ->
              tele_prefix_rel (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms' ws' t) k ys' ys'' ->
              (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t k ys <~> shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms' ws' t k ys')).
    { intros * Hm0 Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      unfold shape_doms_rel at 1 2; rewrite (List.nth_error_nth _ _ _ HB).
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm1 Hc Heq Hw1 HB Hp1) as [a a' Ea Ea' (Hper & _)].
      destruct (Hd2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm2 Hc Heq Hw2 HB Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact Hper | apply per_univ_sym; exact Hper2 ]. }
    assert (Hdprefl : forall m Mm ms ms'' c gs gs1 t gs2 ws ws'' k ys ys'', ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms'' ->
              ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws'' -> k <= List.length (ptyp_doms t) ->
              tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys'' ->
              tele_prefix_rel (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms'' ws'' t) k ys'' ys'').
    { intros * Hm0 Hm Hc Heq Hw Hk Hp.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (Haprefl _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk1 Hw) as Hw2.
      eapply (tele_prefix_rel_cross_refl (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms'' ws'' t)
                (List.length (ptyp_doms t)));
        [ exact Hk | | | exact Hp ].
      - intros j0 pa pb Hj Hp1 Hp2.
        exact (Hdcr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Heq Hw Hw2 Hj Hp1 Hp2).
      - intros j0 ? ? Hj ?; destruct (nth_error_lt_some' _ _ Hj) as [B HB].
        unfold shape_doms_rel at 1; rewrite (List.nth_error_nth _ _ _ HB).
        eapply HdP2; [ exact Hm0 | exact (Hrefl0 _ _ _ _ Hm0 Hm) | exact Hc | exact Heq | exact Hw2 | exact HB | eassumption ]. }
    (** The second's relations are the first's along prefixes related by
        the first. *)
    assert (HnC : forall m Mm k vs vs1 vs2, ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr0 m) k vs vs1 -> tele_prefix_rel (nr m) k vs vs2 -> (nr0 m k vs <~> nr m k vs)).
    { intros m Mm k0 vs vs1 vs2 Hm Hk Hp1 Hp2; symmetry; eapply Hcr; [ exact Hm | exact Hk | | exact Hp1 ].
      eapply (nparams_prefix_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm k0 vs vs2); [ lia | exact Hp2 ]. }
    assert (HaC : forall m Mm ms ms1 ms2 c gs k vs vs1 vs2, ind_member D m = Some Mm ->
              tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
              ind_con Mm c = Some gs -> k < List.length (cargs_nonrec gs) ->
              tele_prefix_rel (ar0 m ms c) k vs vs1 -> tele_prefix_rel (ar m ms c) k vs vs2 ->
              (ar0 m ms c k vs <~> ar m ms c k vs)).
    { intros m Mm ms ms1 ms2 c gs k0 vs vs1 vs2 Hm0 Hm1 Hm2 Hc Hk Hp1 Hp2; symmetry.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 _ _ Hm2) as Hmm.
      eapply (Hacr m Mm ms ms ms1); [ exact Hm0 | exact Hmm | exact Hm1 | exact Hc | exact Hk | | exact Hp1 ].
      eapply (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs Hmm Hc k0 vs vs2);
        [ lia | exact Hp2 ]. }
    assert (HdC : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2, ind_member D m = Some Mm ->
              tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
              ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_prefix_rel (ar0 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
              tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
              k < List.length (ptyp_doms t) ->
              tele_prefix_rel (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys1 ->
              tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys2 ->
              (shape_doms_rel (dr0 m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t k ys <~> shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t k ys)).
    { intros m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k0 ys ys1 ys2 Hm0 Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hp1 Hp2; symmetry.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 _ _ Hm2) as Hmm.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs Hmm Hc _ ws ws2 Hk1 Hw2)
        as Hww.
      eapply (Hdcr m Mm ms ms ms1 c gs gs1 t gs2 ws ws ws1 k0 ys ys ys1);
        [ exact Hm0 | exact Hmm | exact Hm1 | exact Hc | exact Heq | exact Hww | exact Hw1 | exact Hk | | exact Hp1 ].
      eapply (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs gs1 t gs2 ws Hmm Hc Heq Hww);
        [ lia | exact Hp2 ]. }
    pose proof (adm_flip p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl Hcd) as Hfl.
    basic_per_univ_elem_econstructor;
      [ exact Hl | exact Hass | exact HM | exact Hh | exact Hu | exact Hu2' | exact (per_top_ps_trans _ _ _ _ Hps Hps2)
      | exact HnP | | exact HnI | exact HaP | | exact HaI | exact HdP | | exact HdI | | exact Hcd
      | exact (Hcomp _ _ _ _ _ HM Hns Hns2) | ].
    + intros m Mm k0 κ A vs vs'' Hm Hk Hp.
      assert (Hkl : k0 < List.length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
      assert (Hp2 : tele_prefix_rel (nr0 m) k0 vs'' vs'').
      { eapply (tele_prefix_rel_cross_refl (nr m) (nr0 m) (List.length (List.rev (im_nparams Mm))));
          [ lia | | exact (fun j0 vs1 vs2 => HnP0 m Mm j0 vs1 vs2 Hm) | exact Hp ].
        intros j0 pa pb Hj Hp1 Hp2; exact (Hcr _ _ _ _ _ _ Hm Hj Hp1 Hp2). }
      destruct (Hn _ _ _ _ _ _ _ Hm Hk Hp) as [a a' Ea Ea' (_ & Htr & _)].
      destruct (Hn2 _ _ _ _ _ _ _ Hm Hk Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      econstructor; [ exact Ea | exact Eb' |].
      apply (Htr j); eapply per_univ_elem_resp_iff; [ exact Hper2 |]; symmetry; exact (Hcr _ _ _ _ _ _ Hm Hkl Hp Hp2).
    + intros m Mm ms ms'' c gs k0 A vs vs'' Hm0 Hm Hc Hk Hp.
      assert (Hkl : k0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
      pose proof (Haprefl m Mm ms ms'' c gs k0 vs vs'' Hm0 Hm Hc ltac:(lia) Hp) as Hp2.
      destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk Hp) as [a a' Ea Ea' (_ & Htr & _)].
      destruct (Ha2 _ _ _ _ _ _ _ _ _ _ Hm0 (Hrefl0 _ _ _ _ Hm0 Hm) Hc Hk Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      econstructor; [ exact Ea | exact Eb' |].
      apply (Htr j); eapply per_univ_elem_resp_iff; [ exact Hper2 |]; symmetry;
        exact (Hacr _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Hkl Hp Hp2).
    + intros m Mm ms ms'' c gs gs1 t gs2 ws ws'' k0 B ys ys'' Hm0 Hm Hc Heq Hw HB Hy.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hkl : k0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      pose proof (Haprefl _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk1 Hw) as Hw2.
      pose proof (Hdprefl m Mm ms ms'' c gs gs1 t gs2 ws ws'' k0 ys ys'' Hm0 Hm Hc Heq Hw ltac:(lia) Hy) as Hy2.
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htr & _)].
      destruct (Hd2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 (Hrefl0 _ _ _ _ Hm0 Hm) Hc Heq Hw2 HB Hy2) as [b b' Eb Eb' Hper2].
      pose proof (Hdcr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Heq Hw Hw2 Hkl Hy Hy2) as Hdd.
      unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
      functional_eval_rewrite_clear.
      econstructor; [ exact Ea | exact Eb' |].
      apply (Htr j); eapply per_univ_elem_resp_iff; [ exact Hper2 |]; symmetry; exact Hdd.
    + apply (adm_compose p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups'); [ exact Hcl |].
      exact (adm_change p D ups' nr0 nr ar0 ar dr0 dr HnC HaC HdC _ Hcl2).
    + (** The elements: the right base moved to the composite's
          ([ind_rel_base_r]), at the composite's right index
          ([ind_rel_idx]). *)
      pose proof (Hcomp _ _ _ _ _ HM Hns Hns2) as Hns13.
      pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ _
                    (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns) Hns13) as Hns3.
      pose proof (adm_compose p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' _ Hcl
                    (adm_change p D ups' nr0 nr ar0 ar dr0 dr HnC HaC HdC _ Hcl2)) as Hc3.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns) as Hnn.
      unfold grp_rel in *; intros m m'; split; intro Hm; [ apply HE in Hm | apply HE ].
      * eapply (proj1 (ind_rel_base_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups'0 Hc3 ups' Hcl)); [| reflexivity ].
        exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hm Hnn Hns3).
      * eapply (proj1 (ind_rel_base_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl ups'0 Hc3)); [| reflexivity ].
        exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hm Hnn
                 (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns3)).
  - (** Its elements: the second's left base moved to the first's
        right one ([ind_rel_bases]). *)
    unfold grp_rel in *.
    eapply (proj1 (ind_rel_trans_all p D ups nr ar dr H0 H6 H8 H9 H11 H12 H14 _)); [ exact HTR1 |].
    exact (ind_rel_bases p D ups nr ar dr H0 H6 H8 H9 H11 H12 H14 _ ups ups' _ _ _ _ _ _ H16 H15 H15 H15 HTR2).
  - (** A record type.  The field relations of the first derivation serve
        the composite: those of the second agree with them along related
        prefixes, as the relations of types with a common side. *)
    try match goal with Hl1 : record_lookup _ _ p = Some ?R1, Hl2 : record_lookup _ _ p = Some ?R2 |- _ =>
      assert_fails constr_eq R1 R2; assert (R2 = R1) as -> by congruence end.
    match goal with
    | Hf2 : fields_evals (per_univ_elem ?j) ?R ?ns' ?ns'' ?fr0, Hf1 : fields_evals _ ?R ?ns ?ns' ?fr,
      HfP : fields_per ?R ?fr, HfP2 : fields_per ?R ?fr0, HfI : fields_inv ?R ?fr, HfS : fields_kinds ?R ?ns ?fr,
      Hps : per_top_ps _ ?ns ?ns', Hps2 : per_top_ps _ ?ns' ?ns'',
      Hl : record_lookup _ _ _ = Some ?R, Hnd : List.NoDup _,
      Hn : List.length ?ns = _, Hn2 : List.length ?ns'' = _,
      HE : ?elem_rel <~> record_rel ?R ?fr |- per_univ_elem _ ?elem_rel _ _ =>
        assert (Hcr : forall k pa pb pc, k < List.length (record_fields R) -> tele_prefix_rel fr k pa pb ->
                  tele_prefix_rel fr0 k pb pc -> (fr k pa <~> fr0 k pb));
        [ intros k pa pb pc Hk Hp1 Hp2;
          destruct (nth_error_lt_some' _ _ Hk) as [[f T] HT];
          destruct (Hf1 _ _ _ _ _ HT Hp1) as [a a' Ea Ea' (Hper & _)];
          destruct (Hf2 _ _ _ _ _ HT Hp2) as [b b' Eb Eb' Hper2];
          functional_eval_rewrite_clear;
          eapply per_univ_elem_left_irrel; [ exact Hper | apply per_univ_sym; exact Hper2 ] |];
        basic_per_univ_elem_econstructor;
          [ exact Hl | exact Hnd | exact Hn | exact Hn2 | exact (per_top_ps_trans _ _ _ _ Hps Hps2) | exact HfP | | exact HfS
          | exact HfI | exact HE ];
        intros k f T vs vs'' Hk Hp;
        assert (Hkl : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence);
        assert (Hp2 : tele_prefix_rel fr0 k vs'' vs'')
          by (eapply (tele_prefix_rel_cross_refl fr fr0 (List.length (record_fields R)));
              [ lia | intros j0 pa pb Hj Hq1 Hq2; exact (Hcr _ _ _ _ Hj Hq1 Hq2) | exact (fields_per_lt R fr0 HfP2) | exact Hp ]);
        destruct (Hf1 _ _ _ _ _ Hk Hp) as [a a' Ea Ea' (_ & Htr & _)];
        destruct (Hf2 _ _ _ _ _ Hk Hp2) as [b b' Eb Eb' Hper2];
        functional_eval_rewrite_clear;
        econstructor; [ exact Ea | exact Eb' |];
        apply (Htr j); eapply per_univ_elem_resp_iff; [ exact Hper2 |]; symmetry; exact (Hcr _ _ _ _ Hkl Hp Hp2)
    end.
  - (** Its elements: [record_rel_trans]. *)
    match goal with HfP : fields_per ?R ?fr, HfI : fields_inv ?R ?fr |- record_rel ?R ?fr _ _ =>
      eapply (record_rel_trans R fr HfP HfI); eassumption end.
Qed.

Corollary per_univ_trans : forall i j R a1 a2 a3,
    per_univ_elem i R a1 a2 ->
    per_univ_elem j R a2 a3 ->
    per_univ_elem i R a1 a3.
Proof.
  intros * ?%per_univ_elem_trans.
  firstorder.
Qed.

Corollary per_univ_trans' : forall i j a1 a2 a3,
    Dom a1 ≈ a2 ∈ per_univ i ->
    Dom a2 ≈ a3 ∈ per_univ j ->
    Dom a1 ≈ a3 ∈ per_univ i.
Proof.
  intros * [? ?] [? ?].
  handle_per_univ_elem_irrel.
  firstorder mauto using per_univ_trans.
Qed.

Corollary per_elem_trans : forall i R a1 a2 m1 m2 m3,
    per_univ_elem i R a1 a2 ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * ?% per_univ_elem_trans.
  firstorder.
Qed.

#[local] Instance per_univ_PER {i R} : PER (per_univ_elem i R).
Proof.
  split.
  - auto using per_univ_sym.
  - eauto using per_univ_trans.
Qed.

#[local] Instance per_univ_PER' {i} : PER (per_univ i).
Proof.
  split.
  - auto using per_univ_sym'.
  - eauto using per_univ_trans'.
Qed.

#[local] Instance per_elem_PER {i R a b} `(H : per_univ_elem i R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_elem_sym _ _ _ _ m m' H). eauto.
  - pose proof (fun m0 m1 m2 => per_elem_trans _ _ _ _ m0 m1 m2 H); eauto.
Qed.

(** [per_elem_PER] from a chain, so that [solve_chain_PER] need not read a
    pair off it first. *)
#[local] Instance per_elem_chain_PER {i R l} `(H : rel_chain (per_univ_elem i R) l) : PER R.
Proof.
  destruct (rel_chain_shape _ _ H) as [a [b [l' ->]]].
  eapply per_elem_PER; pairwise.
Qed.

(** ** Chains of Types

    A semantic type judgment provides a chain in [per_univ i], each link with
    its own element PER.  What its consumer needs is the whole chain at one
    PER, namely the one the judgment's element chain lives in.
    [per_univ_chain_at_in] refines the chain to the PER of any one of its
    pairs; this is the only use of irrelevance in the completeness proof.

    The proof uses irrelevance twice, through the left value [x] of the given
    pair: first to the pair [(x, u)], which shares [x], then to [(u, v)],
    which shares [u]. *)
Lemma per_univ_chain_at_in : forall {i R l x y},
    rel_chain (per_univ i) l ->
    In x l ->
    In y l ->
    DF x ≈ y ∈ per_univ_elem i ↘ R ->
    rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain Hx Hy HR.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  apply rel_chain_intro; intros u v Hu Hv.
  assert (Hxu : Dom x ≈ u ∈ per_univ i) by pairwise.
  destruct Hxu as [Rxu HRxu].
  assert (HRxu' : DF x ≈ u ∈ per_univ_elem i ↘ R)
    by (eapply per_univ_elem_resp_iff; [ exact HRxu |];
        eapply per_univ_elem_right_irrel; [ exact HRxu | exact HR ]).
  assert (Huv : Dom u ≈ v ∈ per_univ i) by pairwise.
  destruct Huv as [Ruv HRuv].
  eapply per_univ_elem_resp_iff; [ exact HRuv |].
  eapply per_univ_elem_cross_irrel; [ exact HRuv | exact HRxu' ].
Qed.

(** Weak functionality of [per_univ i]: a chain in it is a chain at one
    element PER, with no anchor needed.  This is the paper's [S ⊆_R ↘ R'];
    [per_univ_chain_at_in] is the case where the caller fixes [R'].  All the
    links' PERs are equivalent, so the first is taken. *)
Corollary per_univ_chain_functional : forall {i l},
    rel_chain (per_univ i) l ->
    exists R, rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  assert (Hab : Dom a ≈ b ∈ per_univ i) by pairwise.
  destruct Hab as [R HR].
  exists R.
  eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in.
Qed.

End Fixed_GCtx.

#[export] Existing Instance per_univ_PER.
#[export] Existing Instance per_univ_PER'.
#[export] Existing Instance per_elem_PER.
#[export] Existing Instance per_elem_chain_PER.
(** Names the element PER of a chain in [per_univ i] and refines the chain to
    it, in place.  Nothing is lost: every pair of the chain remains available
    at [R] through [pairwise]. *)
Ltac functionalize_per_univ_chain H R :=
  apply per_univ_chain_functional in H; destruct H as [R H].

