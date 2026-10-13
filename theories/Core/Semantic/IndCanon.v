(** * The Clause of an Inductive Type, Canonically

    Two related inductive types give their telescope relations as
    arguments of the clause of [per_univ_elem_core].  These are the
    canonical ones of [Core.Semantic.IndPER], at the uniform parameters of
    either type. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export IndPER.
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
  Definition ind_canon_props (D : ind_decl) (ups : list domain) : Prop :=
    let T := List.rev (ind_nparams D) in
    let nr := ind_nr D ups in
    let ar := ind_ar D ups in
    let dr := ind_dr ups in
    (forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> PER (nr k vs)) /\
    (forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> (nr k vs <~> nr k vs')) /\
    (forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> PER (ar ms c k vs)) /\
    (forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> (ar ms c k vs <~> ar ms' c k vs')) /\
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' -> ind_con D c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
       PER (dr (ms ++ ws ++ ys) B)) /\
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' -> ind_con D c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
       (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B)).

  (** Two families of relations agree where both are defined, as the
      section [FamChange] of [Core.Semantic.PER.Tele] needs. *)
  Definition ind_fam_agree (D : ind_decl) (nr1 nr2 : nat -> list domain -> relation domain)
      (ar1 ar2 : list domain -> String.string -> nat -> list domain -> relation domain)
      (dr1 dr2 : list domain -> exp -> relation domain) : Prop :=
    let T := List.rev (ind_nparams D) in
    (forall k vs vs1 vs2, k < List.length T -> tele_pre nr1 k vs vs1 -> tele_pre nr2 k vs vs2 ->
       (nr1 k vs <~> nr2 k vs)) /\
    (forall ms ms1 ms2 c gs k vs vs1 vs2, tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 ->
       ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) ->
       tele_pre (ar1 ms c) k vs vs1 -> tele_pre (ar2 ms c) k vs vs2 ->
       (ar1 ms c k vs <~> ar2 ms c k vs)) /\
    (forall ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2,
       tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ar1 ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
       tele_pre (ar2 ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
       k < List.length (ptyp_doms t) ->
       tele_pre (shape_tr dr1 ms ws (ptyp_doms t)) k ys ys1 ->
       tele_pre (shape_tr dr2 ms ws (ptyp_doms t)) k ys ys2 ->
       (shape_tr dr1 ms ws (ptyp_doms t) k ys <~> shape_tr dr2 ms ws (ptyp_doms t) k ys)).

  Lemma ind_fam_agree_sym : forall D nr1 nr2 ar1 ar2 dr1 dr2,
      ind_fam_agree D nr1 nr2 ar1 ar2 dr1 dr2 -> ind_fam_agree D nr2 nr1 ar2 ar1 dr2 dr1.
  Proof.
    intros * (Hn & Ha & Hd); split; [| split ]; intros; symmetry; [ eapply Hn | eapply Ha | eapply Hd ]; eassumption.
  Qed.

  (** The relations of the clause agree with the canonical ones at the
      left uniform parameters. *)
  Lemma ind_fam_agree_of_evals : forall i D ups ups' nr ar dr,
      tele_ass (ind_params D) ->
      (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_pre nr k vs vs' ->
         exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ vs') ↘ a' /\
           DF a ≈ a' ∈ per_univ_elem i ↘ nr k vs) ->
      (forall ms ms' c gs k A vs vs', tele_full nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' ->
         exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ ms' ++ vs') ↘ a' /\
           DF a ≈ a' ∈ per_univ_elem i ↘ ar ms c k vs) ->
      (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr (List.rev (ind_nparams D)) ms ms' ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
         exists b b', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b /\ ⟦ B ⟧ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ b' /\
           DF b ≈ b' ∈ per_univ_elem i ↘ dr (ms ++ ws ++ ys) B) ->
      ind_fam_agree D nr (ind_nr D ups) ar (ind_ar D ups) dr (ind_dr ups).
  Proof.
    intros * Hass Hn Ha Hd; split; [| split ].
    - intros * Hk Hp _.
      destruct (nparams_lt_ass D k Hass Hk) as [A HA].
      destruct (Hn _ _ _ _ HA Hp) as (a & a' & Ea & Ea' & HR).
      unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA).
      exact (per_head_left Ea Ea' HR).
    - intros * Hm _ Hc Hk Hp _.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (Ha _ _ _ _ _ _ _ _ Hm Hc HA Hp) as (a & a' & Ea & Ea' & HR).
      unfold ind_ar; rewrite (nth_atyp_eq _ _ _ _ _ Hc HA).
      exact (per_head_left Ea Ea' HR).
    - intros * Hm _ Hc Heq Hw _ Hk Hy _.
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as (b & b' & Eb & Eb' & HR).
      unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); unfold ind_dr.
      exact (per_head_left Eb Eb' HR).
  Qed.

  Lemma per_univ_elem_ind_canon : forall i R p D ups ups' ns ns',
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      tele_ass (ind_params D) /\
      per_top_ps (List.rev (ind_uparams D)) ups ups' /\
      ind_canon_props D ups /\
      ind_fam_agree D (ind_nr D ups) (ind_nr D ups') (ind_ar D ups) (ind_ar D ups') (ind_dr ups) (ind_dr ups') /\
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ups' /\
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ups /\
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns' /\
      (R <~> ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns).
  Proof.
    intros * H Hl Hu Hu'.
    basic_invert_per_univ_elem H.
    assert (D0 = D) by congruence; subst D0.
    destruct (app_split_eq _ _ _ _ x0 ltac:(congruence)) as [-> ->].
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    (** The relations of the clause are the canonical ones at [ups]. *)
    assert (Hag : ind_fam_agree D nr (ind_nr D ups) ar (ind_ar D ups) dr (ind_dr ups)).
    { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact H0 | | | ].
      - intros * HA Hp; destruct (H5 _ _ _ _ HA Hp) as [a a' Ea Ea' HR]; eauto.
      - intros * Hm Hc HA Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc HA Hp) as [a a' Ea Ea' HR]; eauto.
      - intros * Hm Hc Heq Hw HB Hy; destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [b b' Eb Eb' HR]; eauto. }
    destruct Hag as (Hn0 & Ha0 & Hd0).
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (conj Hn0 (conj Ha0 Hd0))) as (Hn0' & Ha0' & Hd0').
    pose proof (tele_full_nr_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0) as F1.
    pose proof (tele_full_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0') as F2.
    pose proof (tele_pre_nr_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0) as P2.
    pose proof (tele_pre_nr_change' p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0') as P1.
    assert (HAr : forall ms ms' c gs k vs vs', tele_full (ind_nr D ups) (rev (ind_nparams D)) ms ms' ->
              ind_con D c = Some gs -> k <= length (cargs_nonrec gs) ->
              tele_pre (ind_ar D ups ms c) k vs vs' -> tele_pre (ar ms c) k vs vs').
    { intros * Hm Hc Hk Hp.
      eapply (tele_pre_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0); [ exact (F2 _ _ Hm) | exact Hm | exact Hc | exact Hk | exact Hp ]. }
    assert (HAr' : forall ms ms' c gs k vs vs', tele_full nr (rev (ind_nparams D)) ms ms' ->
              ind_con D c = Some gs -> k <= length (cargs_nonrec gs) ->
              tele_pre (ar ms c) k vs vs' -> tele_pre (ind_ar D ups ms c) k vs vs').
    { intros * Hm Hc Hk Hp.
      eapply (tele_pre_ar_change' p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0'); [ exact (F1 _ _ Hm) | exact Hm | exact Hc | exact Hk | exact Hp ]. }
    pose proof (tnrp_sym p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as Snp.
    pose proof (tnr_sym p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as Sn.
    pose proof (tnr_refl_l p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as RnL.
    pose proof (tnr_refl_r p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as RnR.
    pose proof (tnrp_refl_l p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as RnpL.
    pose proof (tarp_inst p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as Ia.
    pose proof (tarp_sym p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as Sa.
    pose proof (tarp_refl_r p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as RaR.
    pose proof (tsh_refl_inst p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as RsI.
    pose proof (tsh_refl_l p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12) as RsL.
    (** The domain relations of the clause and the canonical ones, at a
        point on the diagonal of the clause. *)
    assert (HDr : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr (rev (ind_nparams D)) ms ms' ->
              ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_pre (ar ms c) (length (cargs_nonrec gs1)) ws ws' -> List.nth_error (ptyp_doms t) k = Some B ->
              tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
              (dr (ms ++ ws ++ ys) B <~> ind_dr ups (ms ++ ws ++ ys) B)).
    { intros * Hm Hc Heq Hw HB Hy.
      assert (Hkl : k < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
      assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
      pose proof (F1 _ _ Hm) as Hm2.
      pose proof (HAr' _ _ _ _ _ _ _ Hm Hc HK Hw) as Hw2.
      pose proof (tele_pre_sh_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 ms ms' ms' c gs gs1 t gs2 ws ws' ws' k ys ys'
                    Hm Hm2 Hc Heq Hw Hw2 ltac:(lia) Hy) as Hy2.
      pose proof (Hd0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hm2 Hc Heq Hw Hw2 Hkl Hy Hy2) as Hdd.
      unfold shape_tr in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd; exact Hdd. }
    assert (Hcp : ind_canon_props D ups).
    { split; [| split; [| split; [| split; [| split ] ] ] ].
      - intros * HA Hp.
        assert (Hk : k < length (rev (ind_nparams D))) by (apply nth_error_Some; congruence).
        pose proof (P2 k vs vs' (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        rewrite <- (Hn0 _ _ _ _ Hk Hp' Hp); eapply H4; eassumption.
      - intros * HA Hp.
        assert (Hk : k < length (rev (ind_nparams D))) by (apply nth_error_Some; congruence).
        pose proof (P2 k vs vs' (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        pose proof (Snp k vs vs' (Nat.lt_le_incl _ _ Hk) Hp') as Hs.
        rewrite <- (Hn0 _ _ _ _ Hk Hp' Hp), <- (Hn0 _ _ _ _ Hk Hs (P1 k vs' vs (Nat.lt_le_incl _ _ Hk) Hs)).
        eapply H6; eassumption.
      - intros * Hm Hc HA Hp.
        assert (Hk : k < length (cargs_nonrec gs)) by (apply nth_error_Some; congruence).
        pose proof (F2 _ _ Hm) as Hm'.
        pose proof (HAr ms ms' c gs k vs vs' Hm Hc (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ Hm' Hm Hc Hk Hp' Hp); eapply H7; eassumption.
      - intros * Hm Hc HA Hp.
        assert (Hk : k < length (cargs_nonrec gs)) by (apply nth_error_Some; congruence).
        pose proof (F2 _ _ Hm) as Hm'.
        pose proof (HAr ms ms' c gs k vs vs' Hm Hc (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
        pose proof (Sn _ _ Hm') as Hms.
        pose proof (Sa ms' c gs k vs vs' (RnL _ _ Hms) Hc (Nat.lt_le_incl _ _ Hk)
                      (Ia ms ms' c gs k vs vs' Hm' Hc (Nat.lt_le_incl _ _ Hk) Hp')) as Hs.
        rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ Hm' Hm Hc Hk Hp' Hp).
        rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ Hms (F1 _ _ Hms) Hc Hk Hs
                      (HAr' ms' ms c gs k vs' vs Hms Hc (Nat.lt_le_incl _ _ Hk) Hs)).
        eapply H9; eassumption.
      - intros * Hm Hc Heq Hw HB Hy.
        assert (Hkl : k < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
        pose proof (F2 _ _ Hm) as Hm'.
        pose proof (HAr _ _ _ _ _ _ _ Hm Hc HK Hw) as Hw'.
        pose proof (tele_pre_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 ms ms' ms' c gs gs1 t gs2 ws ws' ws' k ys ys'
                      Hm' Hm Hc Heq Hw' Hw ltac:(lia) Hy) as Hy'.
        rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' Hc Heq Hw' HB Hy'); eapply H10; eassumption.
      - intros * Hm Hc Heq Hw HB Hy.
        assert (Hkl : k < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
        pose proof (F2 _ _ Hm) as Hm'.
        pose proof (HAr _ _ _ _ _ _ _ Hm Hc HK Hw) as Hw'.
        pose proof (tele_pre_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 ms ms' ms' c gs gs1 t gs2 ws ws' ws' k ys ys'
                      Hm' Hm Hc Heq Hw' Hw ltac:(lia) Hy) as Hy'.
        pose proof (RnR _ _ Hm') as Hmr.
        pose proof (RaR ms ms' c gs _ ws ws' Hm' Hc HK Hw') as Hwr.
        pose proof (RsI ms ms' c gs gs1 t gs2 ws ws' k ys ys' Hm' Hc Heq Hw' ltac:(lia) Hy') as Hyr.
        rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' Hc Heq Hw' HB Hy').
        rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ Hmr Hc Heq Hwr HB Hyr).
        eapply H12; eassumption. }
    split; [ exact H0 | split; [ exact H3 | split; [ exact Hcp | split; [ split; [| split ] | split; [| split; [| split ] ] ] ] ] ].
    - (** At [ups'], the relations of the right types. *)
      intros * Hk Hp1 Hp2.
      pose proof (P2 k vs vs1 (Nat.lt_le_incl _ _ Hk) Hp1) as Hp'.
      pose proof (RnpL k vs vs1 (Nat.lt_le_incl _ _ Hk) Hp') as Hd.
      destruct (nparams_lt_ass D k H0 Hk) as [A HA].
      destruct (H5 _ _ _ _ HA Hd) as [a a' Ea Ea' HR].
      rewrite <- (Hn0 _ _ _ _ Hk Hp' Hp1).
      unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA).
      exact (per_head_right Ea Ea' HR).
    - intros * Hm1 Hm2 Hc Hk Hp1 Hp2.
      pose proof (F2 _ _ Hm1) as Hm'.
      pose proof (RnL _ _ Hm') as Hmm.
      pose proof (HAr ms ms1 c gs k vs vs1 Hm1 Hc (Nat.lt_le_incl _ _ Hk) Hp1) as Hp'.
      pose proof (RaR ms ms c gs k vs1 vs Hmm Hc (Nat.lt_le_incl _ _ Hk)
                    (Sa ms c gs k vs vs1 Hmm Hc (Nat.lt_le_incl _ _ Hk) Hp')) as Hpp.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (H8 _ _ _ _ _ _ _ _ Hmm Hc HA Hpp) as [a a' Ea Ea' HR].
      rewrite <- (Ha0 _ _ _ _ _ _ _ _ _ Hm' Hm1 Hc Hk Hp' Hp1).
      unfold ind_ar; rewrite (nth_atyp_eq _ _ _ _ _ Hc HA).
      exact (per_head_right Ea Ea' HR).
    - intros * Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hy1 Hy2.
      assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      pose proof (F2 _ _ Hm1) as Hm'.
      pose proof (RnL _ _ Hm') as Hmm.
      pose proof (HAr _ _ _ _ _ _ _ Hm1 Hc HK Hw1) as Hw'.
      pose proof (RaR _ _ _ _ _ _ _ Hmm Hc HK (Sa _ _ _ _ _ _ Hmm Hc HK Hw')) as Hww.
      pose proof (tele_pre_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 ms ms1 ms1 c gs gs1 t gs2 ws ws1 ws1 k ys ys1
                    Hm' Hm1 Hc Heq Hw' Hw1 ltac:(lia) Hy1) as Hy'.
      pose proof (RsL ms c gs gs1 t gs2 ws Hmm Hc Heq Hww k ys ys1 ltac:(lia) Hy') as Hyy.
      destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hmm Hc Heq Hww HB Hyy) as [b b' Eb Eb' HR].
      unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB).
      rewrite <- (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' Hc Heq Hw' HB Hy').
      unfold ind_dr; exact (per_head_right Eb Eb' HR).
    - exact (adm_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 _ H13).
    - exact (adm_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 _ H14).
    - exact (F1 _ _ H15).
    - rewrite H16; intros a b; split.
      + apply (proj1 (ind_rel_change p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0)).
      + apply (proj1 (ind_rel_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0')).
  Qed.

  (** The types of the telescopes of related inductive types are related at
      the canonical relations. *)
  Lemma per_univ_elem_ind_evals : forall i R p D ups ups' ns ns',
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
         tele_pre (ind_nr D ups) k vs vs' ->
         exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ vs') ↘ a' /\
           DF a ≈ a' ∈ per_univ_elem i ↘ ind_nr D ups k vs) /\
      (forall ms ms' c gs k A vs vs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ind_ar D ups ms c) k vs vs' ->
         exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ ms' ++ vs') ↘ a' /\
           DF a ≈ a' ∈ per_univ_elem i ↘ ind_ar D ups ms c k vs) /\
      (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys' ->
         exists b b', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b /\ ⟦ B ⟧ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ b' /\
           DF b ≈ b' ∈ per_univ_elem i ↘ ind_dr ups (ms ++ ws ++ ys) B).
  Proof.
    intros * H Hl Hu Hu'.
    basic_invert_per_univ_elem H.
    assert (D0 = D) by congruence; subst D0.
    destruct (app_split_eq _ _ _ _ x0 ltac:(congruence)) as [-> ->].
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    assert (Hag : ind_fam_agree D nr (ind_nr D ups) ar (ind_ar D ups) dr (ind_dr ups)).
    { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact H0 | | | ].
      - intros * HA Hp; destruct (H5 _ _ _ _ HA Hp) as [a a' Ea Ea' HR]; eauto.
      - intros * Hm Hc HA Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc HA Hp) as [a a' Ea Ea' HR]; eauto.
      - intros * Hm Hc Heq Hw HB Hy; destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [b b' Eb Eb' HR]; eauto. }
    destruct Hag as (Hn0 & Ha0 & Hd0).
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (conj Hn0 (conj Ha0 Hd0))) as (Hn0' & Ha0' & Hd0').
    pose proof (tele_full_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0') as F2.
    pose proof (tele_pre_nr_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0) as P2.
    split; [| split ].
    - intros * HA Hp.
      assert (Hk : k < length (rev (ind_nparams D))) by (apply nth_error_Some; congruence).
      pose proof (P2 k vs vs' (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
      destruct (H5 _ _ _ _ HA Hp') as [a a' Ea Ea' HR].
      exists a, a'; split; [ exact Ea | split; [ exact Ea' |] ].
      eapply per_univ_elem_resp_iff; [ exact HR | exact (Hn0 _ _ _ _ Hk Hp' Hp) ].
    - intros * Hm Hc HA Hp.
      assert (Hk : k < length (cargs_nonrec gs)) by (apply nth_error_Some; congruence).
      pose proof (F2 _ _ Hm) as Hm'.
      pose proof (tele_pre_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 ms ms' ms' c gs k vs vs' Hm' Hm Hc (Nat.lt_le_incl _ _ Hk) Hp) as Hp'.
      destruct (H8 _ _ _ _ _ _ _ _ Hm' Hc HA Hp') as [a a' Ea Ea' HR].
      exists a, a'; split; [ exact Ea | split; [ exact Ea' |] ].
      eapply per_univ_elem_resp_iff; [ exact HR | exact (Ha0 _ _ _ _ _ _ _ _ _ Hm' Hm Hc Hk Hp' Hp) ].
    - intros * Hm Hc Heq Hw HB Hy.
      assert (Hkl : k < length (ptyp_doms t)) by (apply nth_error_Some; congruence).
      assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, length_app; lia).
      pose proof (F2 _ _ Hm) as Hm'.
      pose proof (tele_pre_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 ms ms' ms' c gs _ ws ws' Hm' Hm Hc HK Hw) as Hw'.
      pose proof (tele_pre_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 ms ms' ms' c gs gs1 t gs2 ws ws' ws' k ys ys'
                    Hm' Hm Hc Heq Hw' Hw ltac:(lia) Hy) as Hy'.
      destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' Hc Heq Hw' HB Hy') as [b b' Eb Eb' HR].
      exists b, b'; split; [ exact Eb | split; [ exact Eb' |] ].
      pose proof (Hd0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' Hm Hc Heq Hw' Hw Hkl Hy' Hy) as Hdd.
      unfold shape_tr in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
      eapply per_univ_elem_resp_iff; [ exact HR | exact Hdd ].
  Qed.

  (** An inductive type related to another stays so at related non-uniform
      parameters. *)
  Lemma per_univ_elem_ind_reinst : forall i R p D ups ups' ns ns',
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      forall bs bs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs' ->
        exists R', DF d_ind p (ups ++ bs) ≈ d_ind p (ups' ++ bs') ∈ per_univ_elem i ↘ R'.
  Proof.
    intros * H Hl Hu Hu' bs bs' Hbs.
    basic_invert_per_univ_elem H.
    assert (D0 = D) by congruence; subst D0.
    destruct (app_split_eq _ _ _ _ x0 ltac:(congruence)) as [-> ->].
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    assert (Hag : ind_fam_agree D nr (ind_nr D ups) ar (ind_ar D ups) dr (ind_dr ups)).
    { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact H0 | | | ].
      - intros * HA Hp; destruct (H5 _ _ _ _ HA Hp) as [a a' Ea Ea' HR]; eauto.
      - intros * Hm Hc HA Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc HA Hp) as [a a' Ea Ea' HR]; eauto.
      - intros * Hm Hc Heq Hw HB Hy; destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [b b' Eb Eb' HR]; eauto. }
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hag) as (Hn0' & Ha0' & Hd0').
    pose proof (tele_full_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0' _ _ Hbs) as Hbs'.
    eexists; basic_per_univ_elem_econstructor; try eassumption; reflexivity.
  Qed.

  Corollary ind_canon_of_per : forall i R p D ups ups' ns ns',
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      ind_canon_props D ups.
  Proof. intros * H Hl Hu Hu'; exact (proj1 (proj2 (proj2 (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ H Hl Hu Hu')))). Qed.

  (** Under the conditions of the clause, the canonical relations are PERs
      along their telescopes. *)
  Section CanonPER.
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Hypothesis (Hass : tele_ass (ind_params D)) (Hcp : ind_canon_props D ups).
    Let T := List.rev (ind_nparams D).
    Let nr := ind_nr D ups.
    Let ar := ind_ar D ups.
    Let dr := ind_dr ups.

    Lemma canon_tnr_sym : forall a b, tele_full nr T a b -> tele_full nr T b a.
    Proof. destruct Hcp as (? & ? & ? & ? & ? & ?); eapply (tnr_sym p D ups nr ar dr Hass); eassumption. Qed.

    Lemma canon_tnr_trans : forall a b c, tele_full nr T a b -> tele_full nr T b c -> tele_full nr T a c.
    Proof. destruct Hcp as (? & ? & ? & ? & ? & ?); eapply (tnr_trans p D ups nr ar dr Hass); eassumption. Qed.

    Lemma canon_tnr_refl_l' : forall a b, tele_full nr T a b -> tele_full nr T a a.
    Proof. intros * H; exact (canon_tnr_trans _ _ _ H (canon_tnr_sym _ _ H)). Qed.

    Lemma canon_tnr_refl_r' : forall a b, tele_full nr T a b -> tele_full nr T b b.
    Proof. intros * H; exact (canon_tnr_trans _ _ _ (canon_tnr_sym _ _ H) H). Qed.

  End CanonPER.
End Fixed_GCtx.
