(** * The Clause of a Member of a Group, Canonically

    Two related members of a group give the relations of the group's
    telescopes as arguments of the clause of [per_univ_elem_core].  These
    are the canonical ones of [Core.Semantic.Inductives.IndPER], at the
    uniform parameters of either type. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Inductives Require Export IndPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** The relation of a related pair of types is the head PER at either. *)
  Lemma per_head_left : forall {S S' ρ ρ' i R a a'},
      ⟦ S ⟧ ρ ↘ a -> ⟦ S' ⟧ ρ' ↘ a' -> DF a ≈ a' ∈ per_univ_elem i ↘ R -> (R <~> per_head S S ρ ρ).
  Proof.
    intros * Ha _ HR; eapply per_head_iff; [ exact Ha | exact Ha |].
    eapply per_univ_trans; [ exact HR | apply per_univ_sym; exact HR ].
  Qed.

  Lemma per_head_right : forall {S S' ρ ρ' i R a a'},
      ⟦ S ⟧ ρ ↘ a -> ⟦ S' ⟧ ρ' ↘ a' -> DF a ≈ a' ∈ per_univ_elem i ↘ R -> (R <~> per_head S' S' ρ' ρ').
  Proof.
    intros * _ Ha' HR; eapply per_head_iff; [ exact Ha' | exact Ha' |].
    eapply per_univ_trans; [ apply per_univ_sym; exact HR | exact HR ].
  Qed.

  (** The conditions of the clause on the canonical relations. *)
  #[warnings="-cannot-define-projection"]
  Record ind_canon_props (D : ind_decl) (ups : list domain) : Prop := mk_ind_canon_props
    { icp_np_per : nparams_per D (canon_nparams_rel D ups)
    ; icp_np_iff : nparams_inv D (canon_nparams_rel D ups)
    ; icp_arg_per : args_per D (canon_nparams_rel D ups) (canon_args_rel D ups)
    ; icp_arg_iff : args_inv D (canon_nparams_rel D ups) (canon_args_rel D ups)
    ; icp_dom_per : doms_per D (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
    ; icp_dom_iff : doms_inv D (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) }.

  (** Two families of relations agree where both are defined, as the
      section [FamChange] of [Core.Semantic.PER.Tele] needs. *)
  #[warnings="-cannot-define-projection"]
  Record ind_fam_agree (D : ind_decl) (nr1 nr2 : nat -> nat -> list domain -> relation domain)
      (ar1 ar2 : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
      (dr1 dr2 : nat -> list domain -> exp -> relation domain) : Prop := mk_ind_fam_agree
    { ifa_np : forall m Mm k vs vs1 vs2, ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
        tele_prefix_rel (nr1 m) k vs vs1 -> tele_prefix_rel (nr2 m) k vs vs2 -> (nr1 m k vs <~> nr2 m k vs)
    ; ifa_arg : forall m Mm ms ms1 ms2 c gs k vs vs1 vs2, ind_member D m = Some Mm ->
        tele_rel (nr1 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr2 m) (List.rev (im_nparams Mm)) ms ms2 ->
        ind_con Mm c = Some gs -> k < List.length (cargs_nonrec gs) ->
        tele_prefix_rel (ar1 m ms c) k vs vs1 -> tele_prefix_rel (ar2 m ms c) k vs vs2 ->
        (ar1 m ms c k vs <~> ar2 m ms c k vs)
    ; ifa_dom : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2, ind_member D m = Some Mm ->
        tele_rel (nr1 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr2 m) (List.rev (im_nparams Mm)) ms ms2 ->
        ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_prefix_rel (ar1 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
        tele_prefix_rel (ar2 m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
        k < List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (dr1 m) ms ws (ptyp_doms t)) k ys ys1 ->
        tele_prefix_rel (shape_doms_rel (dr2 m) ms ws (ptyp_doms t)) k ys ys2 ->
        (shape_doms_rel (dr1 m) ms ws (ptyp_doms t) k ys <~> shape_doms_rel (dr2 m) ms ws (ptyp_doms t) k ys) }.

  Lemma ind_fam_agree_sym : forall D nr1 nr2 ar1 ar2 dr1 dr2,
      ind_fam_agree D nr1 nr2 ar1 ar2 dr1 dr2 -> ind_fam_agree D nr2 nr1 ar2 ar1 dr2 dr1.
  Proof.
    intros * [Hn Ha Hd]; constructor; intros; symmetry; [ eapply Hn | eapply Ha | eapply Hd ]; eassumption.
  Qed.

  (** The relations of the clause agree with the canonical ones at the
      left uniform parameters. *)
  Lemma ind_fam_agree_of_evals : forall i D ups ups' nr ar dr,
      grp_tele_ass D ->
      nparams_evals (per_univ_elem i) D ups ups' nr ->
      args_evals (per_univ_elem i) D ups ups' nr ar ->
      doms_evals (per_univ_elem i) D ups ups' nr ar dr ->
      ind_fam_agree D nr (canon_nparams_rel D ups) ar (canon_args_rel D ups) dr (canon_doms_rel ups).
  Proof.
    intros * Hass Hn Ha Hd; constructor.
    - intros m Mm k vs vs1 vs2 HM Hk Hp _.
      destruct (nparams_lt_ass D m Mm k Hass HM Hk) as [A HA].
      destruct (Hn _ _ _ _ _ _ HM HA Hp) as [a a' Ea Ea' HR].
      unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HM HA).
      exact (per_head_left Ea Ea' HR).
    - intros m Mm ms ms1 ms2 c gs k vs vs1 vs2 HM Hm _ Hc Hk Hp _.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm Hc HA Hp) as [a a' Ea Ea' HR].
      unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hc HA).
      exact (per_head_left Ea Ea' HR).
    - intros m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2 HM Hm _ Hc Heq Hw _ Hk Hy _.
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy) as [b b' Eb Eb' HR].
      unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); unfold canon_doms_rel.
      exact (per_head_left Eb Eb' HR).
  Qed.

  (** A related pair of types of a member of a group: its clause at the
      canonical relations at the left uniform parameters. *)
  #[warnings="-cannot-define-projection"]
  Record ind_canon_clause (p : qname) (D : ind_decl) (k : nat) (ups ups' ns ns' : list domain) (R : relation domain) : Prop :=
    mk_ind_canon_clause
    { icc_ass : grp_tele_ass D
    ; icc_ups : per_top_ps (List.rev (ind_uparams D)) ups ups'
    ; icc_props : ind_canon_props D ups
    ; icc_agree : ind_fam_agree D (canon_nparams_rel D ups) (canon_nparams_rel D ups') (canon_args_rel D ups)
        (canon_args_rel D ups') (canon_doms_rel ups) (canon_doms_rel ups')
    ; icc_adm : adm_uparams D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) ups'
    ; icc_adm_diag : adm_uparams D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) ups
    ; icc_views : views_fresh p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) ups'
    ; icc_views_diag : views_fresh p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) ups
    ; icc_ns : tele_rel (canon_nparams_rel D ups k) (List.rev (member_nparams D k)) ns ns'
    ; icc_elems : R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) k ups ups' ns ns' }.

  Lemma per_univ_elem_ind_canon : forall i R p D k ups ups' ns ns',
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      ind_canon_clause p D k ups ups' ns ns' R.
  Proof.
    intros * H Hl Hu Hu'.
    basic_invert_per_univ_elem H.
    assert (D0 = D) by congruence; subst D0.
    destruct (app_split_eq _ _ _ _ x0 ltac:(congruence)) as [-> ->].
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    rename H0 into Hass, H1 into HM, H2 into Hh, H5 into Hps, H6 into HnP, H7 into Hn, H8 into HnI, H9 into HaP, H10 into Ha,
      H11 into HaI, H12 into HdP, H13 into Hd, H14 into HdI, H15 into Hcl, H16 into Hcd, H17 into Hvl, H18 into Hvd,
      H19 into Hns, H20 into HE.
    (** The relations of the clause are the canonical ones at [ups]. *)
    pose proof (ind_fam_agree_of_evals i D ups ups' nr ar dr Hass
                  ltac:(red; intros * HM0 HA Hp; destruct (Hn _ _ _ _ _ _ HM0 HA Hp) as [a a' Ea Ea' HR]; econstructor; eauto)
                  ltac:(red; intros * HM0 Hm Hc HA Hp; destruct (Ha _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc HA Hp) as [a a' Ea Ea' HR];
                        econstructor; eauto)
                  ltac:(red; intros * HM0 Hm Hc Heq Hw HB Hy;
                        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc Heq Hw HB Hy) as [b b' Eb Eb' HR];
                        econstructor; eauto)) as Hag.
    destruct Hag as [Hn0 Ha0 Hd0].
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (mk_ind_fam_agree _ _ _ _ _ _ _ Hn0 Ha0 Hd0)) as [Hn0' Ha0' Hd0'].
    pose proof (fun m Mm HM => tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM) as F1.
    pose proof (fun m Mm HM => tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' m Mm HM) as F2.
    pose proof (fun m Mm HM => tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM) as P2.
    pose proof (fun m Mm HM => tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' m Mm HM) as P1.
    assert (HAr : forall m Mm ms ms' c gs k vs vs', ind_member D m = Some Mm -> tele_rel (canon_nparams_rel D ups m) (rev (im_nparams Mm)) ms ms' ->
              ind_con Mm c = Some gs -> k <= length (cargs_nonrec gs) ->
              tele_prefix_rel (canon_args_rel D ups m ms c) k vs vs' -> tele_prefix_rel (ar m ms c) k vs vs').
    { intros * HM0 Hm Hc Hk Hp.
      eapply (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM0);
        [ exact (F2 _ _ HM0 _ _ Hm) | exact Hm | exact Hc | exact Hk | exact Hp ]. }
    assert (HAr' : forall m Mm ms ms' c gs k vs vs', ind_member D m = Some Mm -> tele_rel (nr m) (rev (im_nparams Mm)) ms ms' ->
              ind_con Mm c = Some gs -> k <= length (cargs_nonrec gs) ->
              tele_prefix_rel (ar m ms c) k vs vs' -> tele_prefix_rel (canon_args_rel D ups m ms c) k vs vs').
    { intros * HM0 Hm Hc Hk Hp.
      eapply (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' m Mm HM0);
        [ exact (F1 _ _ HM0 _ _ Hm) | exact Hm | exact Hc | exact Hk | exact Hp ]. }
    pose proof (nparams_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Snp.
    pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Sn.
    pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as RnL.
    pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as RnR.
    pose proof (nparams_prefix_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as RnpL.
    pose proof (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Ia.
    pose proof (args_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Sa.
    pose proof (args_prefix_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as RaR.
    pose proof (doms_rel_refl_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as RsI.
    pose proof (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as RsL.
    (** The domain relations of the clause and the canonical ones, at a
        point on the diagonal of the clause. *)
    assert (HDr : forall m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys', ind_member D m = Some Mm ->
              tele_rel (nr m) (rev (im_nparams Mm)) ms ms' ->
              ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_prefix_rel (ar m ms c) (length (cargs_nonrec gs1)) ws ws' -> List.nth_error (ptyp_doms t) k = Some B ->
              tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys' ->
              (dr m (ms ++ ws ++ ys) B <~> canon_doms_rel ups m (ms ++ ws ++ ys) B)).
    { intros m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' HM0 Hm Hc Heq Hw HB Hy.
      assert (Hkl : k0 < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
      assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
      pose proof (F1 _ _ HM0 _ _ Hm) as Hm2.
      pose proof (HAr' _ _ _ _ _ _ _ _ _ HM0 Hm Hc HK Hw) as Hw2.
      pose proof (tele_prefix_rel_sh_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM0 ms ms' ms' c gs gs1 t gs2 ws ws' ws' k0 ys ys'
                    Hm Hm2 Hc Heq Hw Hw2 ltac:(lia) Hy) as Hy2.
      pose proof (Hd0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hm2 Hc Heq Hw Hw2 Hkl Hy Hy2) as Hdd.
      unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd; exact Hdd. }
    assert (Hcp : ind_canon_props D ups).
    { constructor.
      - intros m Mm k0 A vs vs' HM0 HA Hp.
        assert (Hk : k0 < length (rev (im_nparams Mm))) by (apply nth_error_Some; congruence).
        pose proof (P2 _ _ HM0 k0 vs vs' (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        rewrite <- (Hn0 _ _ _ _ _ _ HM0 Hk Hp' Hp); eapply HnP; eassumption.
      - intros m Mm k0 A vs vs' HM0 HA Hp.
        assert (Hk : k0 < length (rev (im_nparams Mm))) by (apply nth_error_Some; congruence).
        pose proof (P2 _ _ HM0 k0 vs vs' (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        pose proof (Snp _ _ HM0 k0 vs vs' (Nat.lt_le_incl _ _ Hk) Hp') as Hs.
        rewrite <- (Hn0 _ _ _ _ _ _ HM0 Hk Hp' Hp), <- (Hn0 _ _ _ _ _ _ HM0 Hk Hs (P1 _ _ HM0 k0 vs' vs (Nat.lt_le_incl _ _ Hk) Hs)).
        eapply HnI; eassumption.
      - intros m Mm ms ms' c gs k0 A vs vs' HM0 Hm Hc HA Hp.
        assert (Hk : k0 < length (cargs_nonrec gs)) by (apply nth_error_Some; congruence).
        pose proof (F2 _ _ HM0 _ _ Hm) as Hm'.
        pose proof (HAr m Mm ms ms' c gs k0 vs vs' HM0 Hm Hc (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hm Hc Hk Hp' Hp); eapply HaP; eassumption.
      - intros m Mm ms ms' c gs k0 A vs vs' HM0 Hm Hc HA Hp.
        assert (Hk : k0 < length (cargs_nonrec gs)) by (apply nth_error_Some; congruence).
        pose proof (F2 _ _ HM0 _ _ Hm) as Hm'.
        pose proof (HAr m Mm ms ms' c gs k0 vs vs' HM0 Hm Hc (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        pose proof (Sn _ _ HM0 _ _ Hm') as Hms.
        pose proof (Sa _ _ HM0 ms' c gs k0 vs vs' (RnL _ _ HM0 _ _ Hms) Hc (Nat.lt_le_incl _ _ Hk)
                      (Ia _ _ HM0 ms ms' c gs k0 vs vs' Hm' Hc (Nat.lt_le_incl _ _ Hk) Hp')) as Hs.
        rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hm Hc Hk Hp' Hp).
        rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ _ _ HM0 Hms (F1 _ _ HM0 _ _ Hms) Hc Hk Hs
                      (HAr' m Mm ms' ms c gs k0 vs' vs HM0 Hms Hc (Nat.lt_le_incl _ _ Hk) Hs)).
        eapply HaI; eassumption.
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' HM0 Hm Hc Heq Hw HB Hy.
        assert (Hkl : k0 < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
        pose proof (F2 _ _ HM0 _ _ Hm) as Hm'.
        pose proof (HAr _ _ _ _ _ _ _ _ _ HM0 Hm Hc HK Hw) as Hw'.
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM0 ms ms' ms' c gs gs1 t gs2 ws ws' ws' k0 ys ys'
                      Hm' Hm Hc Heq Hw' Hw ltac:(lia) Hy) as Hy'.
        rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hc Heq Hw' HB Hy'); eapply HdP; eassumption.
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' HM0 Hm Hc Heq Hw HB Hy.
        assert (Hkl : k0 < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
        pose proof (F2 _ _ HM0 _ _ Hm) as Hm'.
        pose proof (HAr _ _ _ _ _ _ _ _ _ HM0 Hm Hc HK Hw) as Hw'.
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM0 ms ms' ms' c gs gs1 t gs2 ws ws' ws' k0 ys ys'
                      Hm' Hm Hc Heq Hw' Hw ltac:(lia) Hy) as Hy'.
        pose proof (RnR _ _ HM0 _ _ Hm') as Hmr.
        pose proof (RaR _ _ HM0 ms ms' c gs _ ws ws' Hm' Hc HK Hw') as Hwr.
        pose proof (RsI _ _ HM0 ms ms' c gs gs1 t gs2 ws ws' k0 ys ys' Hm' Hc Heq Hw' ltac:(lia) Hy') as Hyr.
        rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hc Heq Hw' HB Hy').
        rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hmr Hc Heq Hwr HB Hyr).
        eapply HdI; eassumption. }
    constructor; [ exact Hass | exact Hps | exact Hcp | constructor | | | | | |].
    - (** At [ups'], the relations of the right types. *)
      intros m Mm k0 vs vs1 vs2 HM0 Hk Hp1 Hp2.
      pose proof (P2 _ _ HM0 k0 vs vs1 (Nat.lt_le_incl _ _ Hk) Hp1) as Hp'.
      pose proof (RnpL _ _ HM0 k0 vs vs1 (Nat.lt_le_incl _ _ Hk) Hp') as Hdg.
      destruct (nparams_lt_ass D m Mm k0 Hass HM0 Hk) as [A HA].
      destruct (Hn _ _ _ _ _ _ HM0 HA Hdg) as [a a' Ea Ea' HR].
      rewrite <- (Hn0 _ _ _ _ _ _ HM0 Hk Hp' Hp1).
      unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HM0 HA).
      exact (per_head_right Ea Ea' HR).
    - intros m Mm ms ms1 ms2 c gs k0 vs vs1 vs2 HM0 Hm1 Hm2 Hc Hk Hp1 Hp2.
      pose proof (F2 _ _ HM0 _ _ Hm1) as Hm'.
      pose proof (RnL _ _ HM0 _ _ Hm') as Hmm.
      pose proof (HAr m Mm ms ms1 c gs k0 vs vs1 HM0 Hm1 Hc (Nat.lt_le_incl _ _ Hk) Hp1) as Hp'.
      pose proof (RaR _ _ HM0 ms ms c gs k0 vs1 vs Hmm Hc (Nat.lt_le_incl _ _ Hk)
                    (Sa _ _ HM0 ms c gs k0 vs vs1 Hmm Hc (Nat.lt_le_incl _ _ Hk) Hp')) as Hpp.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (Ha _ _ _ _ _ _ _ _ _ _ HM0 Hmm Hc HA Hpp) as [a a' Ea Ea' HR].
      rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hm1 Hc Hk Hp' Hp1).
      unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM0 Hc HA).
      exact (per_head_right Ea Ea' HR).
    - intros m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k0 ys ys1 ys2 HM0 Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hy1 Hy2.
      assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      pose proof (F2 _ _ HM0 _ _ Hm1) as Hm'.
      pose proof (RnL _ _ HM0 _ _ Hm') as Hmm.
      pose proof (HAr _ _ _ _ _ _ _ _ _ HM0 Hm1 Hc HK Hw1) as Hw'.
      pose proof (RaR _ _ HM0 _ _ _ _ _ _ _ Hmm Hc HK (Sa _ _ HM0 _ _ _ _ _ _ Hmm Hc HK Hw')) as Hww.
      pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM0 ms ms1 ms1 c gs gs1 t gs2 ws ws1 ws1 k0 ys ys1
                    Hm' Hm1 Hc Heq Hw' Hw1 ltac:(lia) Hy1) as Hy'.
      pose proof (RsL _ _ HM0 ms c gs gs1 t gs2 ws Hmm Hc Heq Hww k0 ys ys1 ltac:(lia) Hy') as Hyy.
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hmm Hc Heq Hww HB Hyy) as [b b' Eb Eb' HR].
      unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB).
      rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm' Hc Heq Hw' HB Hy').
      unfold canon_doms_rel; exact (per_head_right Eb Eb' HR).
    - exact (adm_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 _ Hcl).
    - exact (adm_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 _ Hcd).
    - exact (views_fresh_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 Hass _ Hvl).
    - exact (views_fresh_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 Hass _ Hvd).
    - unfold member_nparams; rewrite HM; exact (F1 _ _ HM _ _ Hns).
    - rewrite HE; intros a b; split.
      + apply (proj1 (ind_rel_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 _ _ _ _ (grp_adm_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 Hass)
                        (okr_at_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0) (fun m Mm a b HM0 H => RnR m Mm HM0 a b H))).
      + apply (proj1 (ind_rel_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' _ _ _ _
                        (grp_adm_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' Hass)
                        (okr_at_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0')
                        (fun m Mm a b HM0 H => F1 _ _ HM0 _ _ (RnR _ _ HM0 _ _ (F2 _ _ HM0 _ _ H))))).
  Qed.

  (** The types of the telescopes of a related pair of members are related
      at the canonical relations. *)
  Lemma per_univ_elem_ind_evals : forall i R p D k ups ups' ns ns',
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      nparams_evals (per_univ_elem i) D ups ups' (canon_nparams_rel D ups) /\
      args_evals (per_univ_elem i) D ups ups' (canon_nparams_rel D ups) (canon_args_rel D ups) /\
      doms_evals (per_univ_elem i) D ups ups' (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups).
  Proof.
    intros * H Hl Hu Hu'.
    basic_invert_per_univ_elem H.
    assert (D0 = D) by congruence; subst D0.
    destruct (app_split_eq _ _ _ _ x0 ltac:(congruence)) as [-> ->].
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    rename H0 into Hass, H7 into Hn, H10 into Ha, H13 into Hd.
    pose proof (ind_fam_agree_of_evals i D ups ups' nr ar dr Hass Hn Ha Hd) as Hag.
    destruct Hag as [Hn0 Ha0 Hd0].
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (mk_ind_fam_agree _ _ _ _ _ _ _ Hn0 Ha0 Hd0)) as [Hn0' Ha0' Hd0'].
    split; [| split ].
    - intros m Mm k0 A vs vs' HM HA Hp.
      assert (Hk : k0 < length (rev (im_nparams Mm))) by (apply nth_error_Some; congruence).
      pose proof (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM k0 vs vs' (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
      destruct (Hn _ _ _ _ _ _ HM HA Hp') as [a a' Ea Ea' HR].
      econstructor; [ exact Ea | exact Ea' |].
      eapply per_univ_elem_resp_iff; [ exact HR | exact (Hn0 _ _ _ _ _ _ HM Hk Hp' Hp) ].
    - intros m Mm ms ms' c gs k0 A vs vs' HM Hm Hc HA Hp.
      assert (Hk : k0 < length (cargs_nonrec gs)) by (apply nth_error_Some; congruence).
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' m Mm HM _ _ Hm) as Hm'.
      pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms' ms' c gs k0 vs vs' Hm' Hm Hc
                    (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
      destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm' Hc HA Hp') as [a a' Ea Ea' HR].
      econstructor; [ exact Ea | exact Ea' |].
      eapply per_univ_elem_resp_iff; [ exact HR | exact (Ha0 _ _ _ _ _ _ _ _ _ _ _ HM Hm' Hm Hc Hk Hp' Hp) ].
    - intros m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' HM Hm Hc Heq Hw HB Hy.
      assert (Hkl : k0 < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
      assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' m Mm HM _ _ Hm) as Hm'.
      pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms' ms' c gs _ ws ws' Hm' Hm Hc HK Hw) as Hw'.
      pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms' ms' c gs gs1 t gs2 ws ws' ws' k0 ys ys'
                    Hm' Hm Hc Heq Hw' Hw ltac:(lia) Hy) as Hy'.
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm' Hc Heq Hw' HB Hy') as [b b' Eb Eb' HR].
      econstructor; [ exact Eb | exact Eb' |].
      pose proof (Hd0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm' Hm Hc Heq Hw' Hw Hkl Hy' Hy) as Hdd.
      unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
      eapply per_univ_elem_resp_iff; [ exact HR | exact Hdd ].
  Qed.

  (** A member of a group related to another stays so at related
      non-uniform parameters, and so is every other declared member. *)
  Lemma per_univ_elem_ind_reinst : forall i R p D k ups ups' ns ns',
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      forall j Mj pm bs bs', ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
        tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs' ->
        exists R', DF d_ind p j (ups ++ bs) ≈ d_ind p j (ups' ++ bs') ∈ per_univ_elem i ↘ R'.
  Proof.
    intros * H Hl Hu Hu' j Mj pm bs bs' HMj Hhj Hbs.
    basic_invert_per_univ_elem H.
    assert (D0 = D) by congruence; subst D0.
    destruct (app_split_eq _ _ _ _ x0 ltac:(congruence)) as [-> ->].
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    pose proof (ind_fam_agree_of_evals i D ups ups' nr ar dr H0 H7 H10 H13) as Hag.
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hag) as [Hn0' Ha0' Hd0'].
    pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' j Mj HMj _ _ Hbs) as Hbs'.
    eexists; basic_per_univ_elem_econstructor; try eassumption; reflexivity.
  Qed.

  Corollary ind_canon_of_per : forall i R p D k ups ups' ns ns',
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      ind_canon_props D ups.
  Proof. intros * H Hl Hu Hu'; exact (icc_props _ _ _ _ _ _ _ _ (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ H Hl Hu Hu')). Qed.

  (** Under the conditions of the clause, the canonical relations are PERs
      along their telescopes. *)
  Section CanonPER.
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Hypothesis (Hass : grp_tele_ass D) (Hcp : ind_canon_props D ups).
    Let nr := canon_nparams_rel D ups.
    Let ar := canon_args_rel D ups.
    Let dr := canon_doms_rel ups.

    Lemma canon_nparams_rel_sym : forall m Mm a b, ind_member D m = Some Mm ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) a b -> tele_rel (nr m) (List.rev (im_nparams Mm)) b a.
    Proof. destruct Hcp as [? ? ? ? ? ?]; intros; eapply (nparams_rel_sym p D ups nr ar dr Hass); eassumption. Qed.

    Lemma canon_nparams_rel_trans : forall m Mm a b c, ind_member D m = Some Mm ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) a b -> tele_rel (nr m) (List.rev (im_nparams Mm)) b c ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) a c.
    Proof. destruct Hcp as [? ? ? ? ? ?]; intros; eapply (nparams_rel_trans p D ups nr ar dr Hass); eassumption. Qed.

    Lemma canon_nparams_rel_refl_l' : forall m Mm a b, ind_member D m = Some Mm ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) a b -> tele_rel (nr m) (List.rev (im_nparams Mm)) a a.
    Proof. intros * HM H; exact (canon_nparams_rel_trans _ _ _ _ _ HM H (canon_nparams_rel_sym _ _ _ _ HM H)). Qed.

    Lemma canon_nparams_rel_refl_r' : forall m Mm a b, ind_member D m = Some Mm ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) a b -> tele_rel (nr m) (List.rev (im_nparams Mm)) b b.
    Proof. intros * HM H; exact (canon_nparams_rel_trans _ _ _ _ _ HM (canon_nparams_rel_sym _ _ _ _ HM H) H). Qed.
  End CanonPER.
End Fixed_GCtx.
