From Stdlib Require Import Nat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution IndCong.
From Mctt.Core.Semantic Require Import IndCanon.
From Mctt.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations Wk_Notations Fixed_Notations.

Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A Kripke weakening is [⇑^n] on the nose ([kripke_shiftn]), so it acts on
    a variable by index arithmetic alone. *)
Lemma wk_var_kripke : forall Γ Δ φ x,
    Δ ⊢k φ : Γ ->
    φ x = x + (length Δ - length Γ).
Proof.
  intros * H%kripke_shiftn; destruct H as [_ Hφ].
  now rewrite (Hφ x).
Qed.

(** The instance the gluing model needs: the canonical variable of an extended
    context reads back as the de Bruijn index counting down from the length of
    the context the weakening lands in. *)
Corollary wk_var0_kripke : forall Γ A Δ φ,
    Δ ⊢k φ : Γ ▹ A ->
    φ 0 = length Δ - length Γ - 1.
Proof. intros * H; pose proof (wk_var_kripke _ _ _ 0 H); simpl in *; lia. Qed.

Lemma var_glu_elem_bot : forall a i P El Γ A,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A[↑]ʷ ® #ᵈ (length Γ) ∈ glu_elem_bot i a.
Proof.
  intros. saturate_glu_info.
  (** The ambient universe of the index is the large universe [Typeω@(ulvl i)],
      at which the syntactic rules apply directly. *)
  econstructor; mauto 4.
  - eapply glu_univ_elem_typ_monotone; eauto.
    mauto 4.
  - intros. progressive_inversion.
    assert (φ 0 = length Δ - length Γ - 1) as <- by (eapply wk_var0_kripke; eassumption).
    change #(φ 0) with #0[φ]ʷ.
    mauto 5.
Qed.



(** The arguments of a constructor read back position by position. *)
Lemma read_cargs_nth : forall s p ups ρ gs vs Vs, read_cargs gc_deps gc_stack s p ups ρ gs vs Vs ->
    List.length (nfs_to_exps Vs) = List.length gs /\
    (forall gs1 A gs2 v, gs = gs1 ++ ca_arg A :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
       exists a (V : nf), ⟦ A ⟧ env_args ρ (nonrec_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
         Rnf ⇓ a v in s ↘ V /\ List.nth_error (nfs_to_exps Vs) (List.length gs1) = Some (V : exp)) /\
    (forall gs1 Pr gs2 v, gs = gs1 ++ ca_rec Pr :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
       exists a (V : nf), eval_shty gc_deps gc_stack p ups (env_args ρ (nonrec_vals gs1 (List.firstn (List.length gs1) vs))) Pr a /\
         Rnf ⇓ a v in s ↘ V /\ List.nth_error (nfs_to_exps Vs) (List.length gs1) = Some (V : exp)).
Proof.
  induction 1.
  - split; [ reflexivity | split; intros [] *; discriminate ].
  - destruct IHread_cargs as (IHl & IHa & IHr).
    split; [ cbn; congruence | split ].
    + intros [| g gs1] A0 gs2 v0 Heq Hv; cbn in Heq, Hv.
      * injection Heq as <- <-; injection Hv as <-; exists a, V; repeat split; assumption.
      * injection Heq as <- Heq; destruct (IHa _ _ _ _ Heq Hv) as (a0 & V0 & E0 & R0 & N0).
        exists a0, V0; repeat split; assumption.
    + intros [| g gs1] Pr gs2 v0 Heq Hv; cbn in Heq, Hv; [ discriminate |].
      injection Heq as <- Heq; destruct (IHr _ _ _ _ Heq Hv) as (b0 & V0 & E0 & R0 & N0).
      exists b0, V0; repeat split; assumption.
  - destruct IHread_cargs as (IHl & IHa & IHr).
    split; [ cbn; congruence | split ].
    + intros [| g gs1] A0 gs2 v0 Heq Hv; cbn in Heq, Hv; [ discriminate |].
      injection Heq as <- Heq; destruct (IHa _ _ _ _ Heq Hv) as (a0 & V0 & E0 & R0 & N0).
      exists a0, V0; repeat split; assumption.
    + intros [| g gs1] Pr gs2 v0 Heq Hv; cbn in Heq, Hv.
      * injection Heq as <- <-; injection Hv as <-; exists a, V; repeat split; assumption.
      * injection Heq as <- Heq; destruct (IHr _ _ _ _ Heq Hv) as (b0 & V0 & E0 & R0 & N0).
        exists b0, V0; repeat split; assumption.
Qed.


(** ** Inductive Types *)

(** The codomain of the type of an argument of a function shape, at an
    argument, is the type of the rest of the shape. *)
Lemma eval_fam_cod_shfam_inv : forall p ups ρ t x a,
    ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ t ↦ x ↘ a -> eval_shty gc_deps gc_stack p ups (ρ ↦ x) t a.
Proof.
  intros * H; unfold fam_cod in H; inversion H; subst.
  match goal with H1 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
  match goal with H0 : ⟦ #0 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H0; subst end.
  match goal with Ha : $| _ & _ | _ ⍮ _ ↘ _ |- _ => cbn in Ha; inversion Ha; subst; assumption end.
Qed.

Lemma glu_params_top_refl : forall D Δ Ps as', glu_params_top D Δ Ps as' -> exps_eq_at Δ (ind_params D) Ps Ps.
Proof.
  intros * (_ & Ht & _); split; [ reflexivity |].
  intros k X Y A HX HY HA; rewrite HX in HY; injection HY as <-.
  apply wf_exp_eq_refl; eapply Ht; eassumption.
Qed.

Section IndRealize.
  Variables (i : uidx) (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
    (elem_rel : relation domain) (P : glu_typ_pred) (El : glu_exp_pred).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hu : List.length ups = ind_nu D)
    (Hass : tele_ass (ind_params D))
    (Hper : DF d_ind p (ups ++ ns) ≈ d_ind p (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel)
    (HP : P <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl Typeω@(ulvl i))
    (HEl : El <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl elem_rel Typeω@(ulvl i)).

  Lemma ind_realize_typ : forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® glu_typ_top i (d_ind p (ups ++ ns)).
  Proof.
    intros Γ A HA; apply HP in HA; destruct HA as (Ps & HAPs & Hk).
    econstructor; [ gen_presups; assumption | exact (per_univ_then_per_top_typ Hper) |].
    intros Δ φ A' Hφ Hr.
    inversion Hr; subst.
    match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
    destruct (Hk Δ φ Hφ) as ((HPl & HPt & HPr) & Hs & _).
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢k wk_id : Δ) by mauto 3.
    match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ms |- _ => pose proof (HPr Δ wk_id Ms Hid H) as HMs end.
    rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id in HMs.
    destruct HMs as [HMl HMs].
    cbn [nf_to_exp]; transitivity (apps (a_ind p) (List.map (fun P => P[φ]ʷ) Ps)); [ rewrite <- wk_apps_ind; mauto 3 |].
    eapply wf_exp_eq_subtyp'; [| exact Hs ].
    eapply wf_exp_eq_ind_apps; [ exact Hl | exact HΔ | exact HPl | lia | exact HMs ].
  Qed.

  Lemma ind_realize_bot : forall Γ M A m,
      DG d_ind p (ups ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
      Γ ⊢ M : A ® m ∈ glu_elem_bot i (d_ind p (ups ++ ns)) ->
      Γ ⊢ M : A ® ⇑ (d_ind p (ups ++ ns)) m ∈ El.
  Proof.
    intros * Hglu [P' El' HM Hglu' HAP' Hm Hrb].
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
    assert (HA : Γ ⊢ A ® P) by (apply HPP; exact HAP').
    apply HEl; pose proof HA as HA'; apply HP in HA'; destruct HA' as (Ps & HPs).
    split; [ exact HM | split; [ eapply per_bot_then_per_elem; eassumption |] ].
    exists Ps; split; [ exact HPs |].
    intros Δ φ Ps' Hφ HPs'.
    pose proof (ind_typ_at_params_conv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HPs Hφ HPs') as HPeq.
    destruct HPs as [HAPs _].
    eapply glu_ind_neut; [ exact Hm |].
    intros Θ ψ M' Hψ Hr.
    pose proof (kripke_compose _ _ _ _ _ Hψ Hφ) as Hc.
    rewrite exp_wk_wk.
    eapply wf_exp_eq_conv'; [ exact (Hrb _ _ _ Hc Hr) |].
    transitivity ((apps (a_ind p) (List.map (fun P => P[φ]ʷ) Ps))[ψ]ʷ); [| mauto 3 ].
    rewrite wk_apps_ind, map_wk_wk, <- wk_apps_ind; mauto 3.
  Qed.

  Hypothesis
    (HeA : forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b)
    (HgA : forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem i ↘ AP ms c k vs ↘ AEl ms c k vs)
    (HtA : forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       forall Γ M A' m R, DG b ∈ glu_univ_elem i ↘ AP ms c k vs ↘ AEl ms c k vs ->
         Γ ⊢ M : A' ® m ∈ AEl ms c k vs -> DF b ≈ b ∈ per_univ_elem i ↘ R -> Dom m ≈ m ∈ R ->
         Γ ⊢ M : A' ® m ∈ glu_elem_top i b)
    (HeD : forall ms c gs gs1 t gs2 ws k B ys, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
       exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b)
    (HgD : forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
       ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
       DG b ∈ glu_univ_elem i ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B)
    (HrD : forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
       ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
       (forall Γ A R, DF b ≈ b ∈ per_univ_elem i ↘ R -> Γ ⊢ A ® DP (ms ++ ws ++ ys) B -> Γ ⊢ A ® glu_typ_top i b) /\
       (forall Γ M A m, Γ ⊢ M : A ® m ∈ glu_elem_bot i b -> Γ ⊢ M : A ® ⇑ b m ∈ DEl (ms ++ ws ++ ys) B)).

  Lemma glu_ind_readback : forall Γ Ps M m, glu_ind p D ups NEl AEl DP DEl Γ Ps M m -> ⊢ Γ ->
      forall ns', glu_params_top D Γ Ps (ups ++ ns') ->
      ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns' m m ->
      forall (w : nf), Rnf ⇓ (d_ind p (ups ++ ns')) m in length Γ ↘ w -> Γ ⊢ M ≈ w : apps (a_ind p) Ps.
  Proof.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as (_ & _ & Hcp & _ & _ & Hadm & _ & _).
    destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as (HevN & HevAr & HevD).
    pose proof Hcp as (HnP & HnI & HaP & HaI & HdP & HdI).
    pose proof Hadm as (_ & _ & Hcl & _).
    apply (glu_ind_mut_ind p D ups NEl AEl DP DEl
             (fun Γ Ps M m _ => ⊢ Γ -> forall ns', glu_params_top D Γ Ps (ups ++ ns') ->
                ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns' m m ->
                forall (w : nf), Rnf ⇓ (d_ind p (ups ++ ns')) m in length Γ ↘ w -> Γ ⊢ M ≈ w : apps (a_ind p) Ps)
             (fun Γ pre t A N v _ => ⊢ Γ -> Γ ⊢ N : A -> (exists Us' σ', A = ptyp_ty_at p Us' σ' t) ->
                forall ms ms' c0 gs1 t0 gs2 ws k ys, pre = ms ++ ws ++ ys ->
                tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
                ind_con D c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_pre (ind_ar D ups ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
                ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
                tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t0)) k ys ys ->
                ind_shape_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) (ms' ++ ws ++ ys) t v v ->
                forall a (V : nf), eval_shty gc_deps gc_stack p ups (env_args nil (ups ++ ms' ++ ws ++ ys)) t a ->
                Rnf ⇓ a v in length Γ ↘ V -> Γ ⊢ N ≈ V : A)).
    2:{ intros * Hm Hr HΓ ns' Hpt Hrel w Hw. clear - Hr Hw HΓ. inversion Hw; subst.
        assert (Hid : Γ ⊢k wk_id : Γ) by mauto 3.
        match goal with H : Rne m in _ ↘ ?M0 |- _ => pose proof (Hr _ _ _ Hid H) as Heq end.
        rewrite !exp_wk_id in Heq; exact Heq. }
    - (** A constructor: its parameters and arguments read back as the
          constructor's, at the type's parameters. *)
      intros * Hcon HPl Hbl Hvl HAl HM Hb Hv Hnp HAs Harg Hrec IH HΓ ns' Hpt Hrel w Hw.
      destruct (ind_rel_con_inv p D ups _ _ _ Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ Hrel Hbl)
        as (gs0 & bs' & vs' & Heqd & Hns & Hc0 & Hbl' & Hs & Hs' & Ha & Hia).
      rewrite Hcon in Hc0; injection Hc0 as <-.
      injection Heqd as Heqd.
      destruct (app_split_eq _ _ _ _ Heqd ltac:(congruence)) as [<- <-].
      clear Hs' Hbl' Hrel.
      inversion Hw; subst.
      match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
      match goal with H : ind_con D c = Some gs0 |- _ => rewrite Hcon in H; injection H as <- end.
      match goal with H : read_cargs _ _ _ _ _ _ _ _ _ |- _ => rename H into HRc end.
      rewrite firstn_app_exact in HRc by exact Hu.
      rewrite skipn_app_exact in HRc by exact Hbl.
      clear Hw Heqd.
      match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ps0 |- _ => rename H into HRps; rename Ps0 into PN end.
      assert (Hid : Γ ⊢k wk_id : Γ) by mauto 3.
      destruct Hpt as (HPsl & HPst & HPsr).
      pose proof (HPsr Γ wk_id PN Hid HRps) as HPsN.
      rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id in HPsN.
      destruct HPsN as [HlN HPcN].
      clear HPsr HPst.
      cbn [nf_to_exp]; rewrite nfs_to_exps_app.
      etransitivity; [ exact HM |].
      destruct (read_cargs_nth _ _ _ _ _ _ _ HRc) as (HArl & HArg & HArec).
      eapply wf_exp_eq_con_apps; [ exact Hl | exact Hcon | exact HΓ | exact HPl | lia | exact HPcN | exact HAl | lia |].
      intros k N V T HN HV HT.
      assert (Hk : k < length gs) by (rewrite <- HAl; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some gs k Hk) as [g Hg].
      destruct (List.nth_error_split gs k Hg) as (gs1 & gs2 & Heq & Hlg).
      subst k.
      destruct (nth_error_lt_some vs (length gs1) ltac:(lia)) as [v Hv0].
      set (ms := List.skipn (ind_nu D) bs) in *.
      set (pv := nonrec_vals gs1 (List.firstn (length gs1) vs)) in *.
      pose proof (canon_tnr_sym p D ups Hass Hcp _ _ Hs) as Hsm.
      destruct g as [A0 | Pr].
      + (** A non-recursive argument reads back by its gluing, at the type at
            the constructor's non-uniform parameters, related to the one at
            the type's. *)
        assert (HK : length (cargs_nonrec gs1) < length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
        assert (HA0' : List.nth_error (cargs_nonrec gs) (length (cargs_nonrec gs1)) = Some A0)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2 by lia;
              replace (length (cargs_nonrec gs1) - length (cargs_nonrec gs1)) with 0 by lia; reflexivity).
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpre.
        destruct (HeA _ _ _ _ _ _ Hb Hcon HA0' Hpre) as [b Eb].
        pose proof (HgA _ _ _ _ _ _ _ Hb Hcon HA0' Hpre Eb) as Hgb.
        destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
        pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq Hvl Hv0) as Hn1.
        pose proof Hv as Hv'; rewrite tele_full_iff in Hv'; destruct Hv' as (_ & _ & Hvr).
        pose proof (Hvr _ _ _ Hn1 Hn1) as Hvv0.
        rewrite (nonrec_firstn _ _ _ _ _ Heq Hvl) in Hvv0.
        pose proof Hvv0 as Hvv.
        unfold ind_ar in Hvv; rewrite (nth_atyp_eq _ _ _ _ _ Hcon HA0') in Hvv.
        pose proof (per_head_iff Eb Eb HRb) as HRh.
        assert (Hvv' : Rb v v) by (apply HRh; exact Hvv).
        pose proof (HtA _ _ _ _ _ _ _ Hb Hcon HA0' Hpre Eb _ _ _ _ _ Hgb (Harg _ _ _ _ _ _ Heq HN HT Hv0) HRb Hvv') as Htop.
        destruct Htop as [P' El' _ _ _ _ Hrbt].
        destruct (HArg _ _ _ _ Heq Hv0) as (a & V' & Ea & HRa & HnV).
        rewrite HV in HnV; injection HnV as ->.
        rewrite <- env_args_app, <- List.app_assoc in Ea.
        destruct (HevAr _ _ _ _ _ _ _ _ Hsm Hcon HA0' Hpre) as (a0 & a1 & Ea0 & Ea1 & Ha01).
        assert (a0 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (per_elem_then_per_top Ha01 Hvv0) as Htp.
        destruct (Htp (length Γ)) as (W & HW1 & HW2).
        pose proof (functional_read_nf _ _ _ _ HW2 HRa) as ->.
        pose proof (Hrbt Γ wk_id V' Hid HW1) as Heqn.
        rewrite !exp_wk_id in Heqn.
        exact Heqn.
      + (** A recursive argument, by induction on its shape. *)
        destruct (HArec _ _ _ _ Heq Hv0) as (a & V' & Ea & HRV & HnV).
        rewrite HV in HnV; injection HnV as ->.
        rewrite <- env_args_app, <- List.app_assoc in Ea.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpre.
        pose proof (ind_args_rel_rec _ _ _ _ _ _ _ _ _ _ Hia _ _ _ _ _ Heq Hv0 Hv0) as Hsh.
        assert (HTf : exists Us' σ', T = ptyp_ty_at p Us' σ' Pr)
          by (do 2 eexists; rewrite (cargs_rec_type p D gs gs1 Pr gs2 _ _ _ Heq HT), ptyp_ty_eq_at, ptyp_ty_at_sub; reflexivity).
        eapply (IH _ _ _ _ _ _ Heq HN HT Hv0 HΓ (HAs _ _ _ HN HT) HTf ms ns' c gs1 Pr gs2 pv 0 nil);
          [ rewrite List.app_nil_r; reflexivity | exact Hsm | rewrite <- Heq; exact Hcon | exact Hpre | reflexivity | lia
          | apply tele_pre_nil | rewrite List.app_nil_r; exact Hsh | rewrite List.app_nil_r; exact Ea | exact HRV ].
    - (** The end of a shape: the element read back at the parameters the
          shape evaluates to. *)
      intros * Hs1 Hs2 IH HΓ HN HAf ms ms' c0 gs1 t0 gs2 ws k1 ys Hpre Hm Hc Hw Hsk Hk Hy Hsh a V Ea HRV.
      inversion Ea; subst.
      match goal with Hbs : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs0 |- _ => rename Hbs into Ebt; rename bs0 into bt end.
      destruct (ptyp_skip_self _ _ _ _ Hsk) as [HkL HPs].
      assert (Hk1 : k1 = List.length (ptyp_doms t0)) by lia.
      assert (Hys : tele_full (shape_tr (ind_dr ups) ms ws (ptyp_doms t0)) (ptyp_doms t0) ys ys)
        by (apply tele_full_of_pre; rewrite <- Hk1; exact Hy).
      destruct HAf as (Us' & σ' & HA); cbn [ptyp_ty_at ptyp_ps] in HA.
      destruct (Hcl ms ms' c0 _ gs1 t0 gs2 ws ws ys ys Hm Hc eq_refl Hw Hys) as (b0 & b1 & E0 & E1 & H01).
      rewrite HPs in E0, E1.
      pose proof (functional_eval_exps' _ _ _ _ E1 Ebt) as ->.
      destruct (Hs1 _ _ E0 HA) as (HQl & _ & Hgn).
      destruct (Hgn _ H01) as [_ HQt].
      destruct (ind_shape_self_inv _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & Ebs & Hvv).
      pose proof (functional_eval_exps' _ _ _ _ Ebs Ebt) as ->.
      assert (Hid : Γ ⊢k wk_id : Γ) by mauto 3.
      pose proof (IH _ _ E0 HA Γ wk_id _ Hid (glu_params_top_refl _ _ _ _ (HQt Γ wk_id Hid)) HΓ bt (HQt Γ wk_id Hid) Hvv V HRV)
        as Heqn.
      rewrite exp_wk_id, (List.map_ext _ (fun P => P) exp_wk_id), List.map_id in Heqn.
      rewrite HA; exact Heqn.
    - (** A domain of a shape: the function η-expanded, its body read back
          at a fresh variable of the domain. *)
      intros * Hd He Hg IH HΓ HN HAf ms ms' c0 gs1 t0 gs2 ws k1 ys Hpre Hm Hc Hw Hsk Hk Hy Hsh a V Ea HRV.
      inversion Ea; subst.
      match goal with Eb : ⟦ B ⟧ env_args nil (ups ++ ms' ++ ws ++ ys) ↘ ?b0 |- _ => rename Eb into Ebt; rename b0 into bt end.
      inversion HRV; subst.
      match goal with HRT0 : Rtyp bt in _ ↘ ?A0 |- _ => rename HRT0 into HRT; rename A0 into A' end.
      match goal with Hvapp0 : $| v & ⇑! bt _ | _ ⍮ _ ↘ ?m1 |- _ => rename Hvapp0 into Hvapp; rename m1 into m' end.
      match goal with Ecod0 : ⟦ fam_cod ⟧ _ ⍮ _ ⍮ _ ↘ ?b2 |- _ => rename Ecod0 into Ecod; rename b2 into b2' end.
      match goal with HRM0 : Rnf ⇓ b2' m' in _ ↘ ?M1 |- _ => rename HRM0 into HRM; rename M1 into M' end.
      pose proof (eval_fam_cod_shfam_inv _ _ _ _ _ _ Ecod) as Ecod'.
      destruct HAf as (Us' & σ' & HA); cbn [ptyp_ty_at] in HA.
      pose proof (canon_tnr_refl_l' p D ups Hass Hcp _ _ Hm) as Hmm.
      destruct (shape_pi_step p D ups _ _ _ Hass HnP HnI HaP HaI HdP HdI ms c0 gs1 t0 gs2 ws ws k1 ys ys B t Hmm Hc Hw Hsk Hy)
        as (HB & Hs' & Hk' & HPd & Hstep).
      destruct (HeD _ _ _ _ _ _ _ _ _ _ Hmm Hc eq_refl Hw HB Hy) as [bg Ebg].
      pose proof (HgD _ _ _ _ _ _ _ _ _ _ _ Hmm Hc eq_refl Hw HB Hy Ebg) as Hgbg.
      destruct (HrD _ _ _ _ _ _ _ _ _ _ _ Hmm Hc eq_refl Hw HB Hy Ebg) as [HrT HrB].
      destruct (HevD ms ms' c0 _ gs1 t0 gs2 ws ws k1 B ys ys Hm Hc eq_refl Hw HB Hy) as (a0 & a1 & Ea0 & Ea1 & Ha01).
      pose proof (functional_eval_exp _ _ _ _ Ea0 Ebg) as ->; pose proof (functional_eval_exp _ _ _ _ Ea1 Ebt) as ->.
      assert (Hid : Γ ⊢k wk_id : Γ) by mauto 3.
      set (IT := B[σ']) in *.
      set (OT := ptyp_ty_at p (List.map (fun U => U[↑]ʷ) Us') (q σ') t) in *.
      (** The domain reads back as the type of the fresh variable. *)
      pose proof (Hd _ _ HA Γ wk_id Hid) as HITg; rewrite exp_wk_id in HITg.
      destruct (glu_univ_elem_per_univ _ _ _ _ Hgbg) as [Rg HRg].
      destruct (HrT Γ IT Rg HRg HITg) as [HITt _ HITrb].
      assert (HRT' : Rtyp bg in length Γ ↘ A')
        by (eapply per_top_typ_read_left; [ eapply per_univ_then_per_top_typ; exact Ha01 | exact HRT ]).
      pose proof (HITrb Γ wk_id A' Hid HRT') as HITeq; rewrite exp_wk_id in HITeq.
      (** The fresh variable, glued at the domain. *)
      set (c := ⇑! bt (length Γ)).
      assert (HΓIT : ⊢ Γ ▹ IT) by mauto 3.
      assert (Hwk : Γ ▹ IT ⊢k ↑ : Γ) by mauto 3.
      pose proof (HrB _ _ _ _ (var_glu_elem_bot _ _ _ _ _ _ Hgbg HITg)) as Hvg.
      pose proof (var_per_elem (length Γ) Ha01) as Hcc0.
      assert (ERg : ind_dr ups (ms ++ ws ++ ys) B <~> Rg) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (Hvc : Γ ▹ IT ⊢ #0 : IT[↑]ʷ ® c ∈ DEl (ms ++ ws ++ ys) B)
        by (eapply glu_univ_elem_trm_resp_per_elem; [ exact Hgbg | exact HRg | exact Hvg | apply ERg; exact Hcc0 ]).
      assert (Hcc : ind_dr ups (ms ++ ws ++ ys) B c c) by (etransitivity; [ symmetry |]; exact Hcc0).
      (** The rest of the shape, at the variable. *)
      pose proof (proj1 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc eq_refl Hw HB Hy _ _) Hcc) as Hcc'.
      destruct (ind_shape_pi_inv _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hcc') as (r & r' & Er & Er' & Hsh').
      pose proof (functional_eval_app _ _ _ _ Er Hvapp) as ->.
      pose proof (functional_eval_app _ _ _ _ Er' Hvapp) as ->.
      assert (HNw : Γ ▹ IT ⊢ N[↑]ʷ : Π IT[↑]ʷ OT[wk_q ↑]ʷ) by (rewrite <- exp_wk_pi; rewrite HA in HN; mauto 3).
      assert (HNapp : Γ ▹ IT ⊢ N[↑]ʷ $ #0 : OT[(ι ↑),,#0])
        by (rewrite <- exp_sub_wk_q_extend; eapply wf_app'; [ exact HNw | mauto 3 ]).
      assert (HOTf : exists Us'' σ'', OT[(ι ↑),,#0] = ptyp_ty_at p Us'' σ'' t)
        by (do 2 eexists; unfold OT; rewrite ptyp_ty_at_sub; reflexivity).
      assert (Ecod'' : eval_shty gc_deps gc_stack p ups (env_args nil (ups ++ ms' ++ ws ++ ys ++ c :: nil)) t b2')
        by (rewrite env_args_snoc3; exact Ecod').
      pose proof (IH _ _ HA (Γ ▹ IT) ↑ #0 c m' Hwk Hcc Hvc Hvapp HΓIT HNapp HOTf ms ms' c0 gs1 t0 gs2 ws (S k1) (ys ++ c :: nil)
                    ltac:(rewrite <- !List.app_assoc; reflexivity) Hm Hc Hw Hs' Hk' (Hstep _ _ Hcc)
                    ltac:(rewrite <- !List.app_assoc in Hsh'; exact Hsh') b2' M' Ecod'' HRM) as Hbody.
      assert (HNpi : Γ ⊢ N : Π IT OT) by (rewrite <- HA; exact HN).
      assert (HPI : exists j, Γ ⊢ Π IT OT : Typeω@j) by (gen_presups; eauto).
      destruct HPI as [j HPI].
      destruct (wf_pi_inversion' HPI) as [HITj HOTj].
      assert (HOT : Γ ▹ IT ⊢ OT[(ι ↑),,#0] ≈ OT : Typeω@j).
      { pose proof (kripke_q_var_eq Γ Γ IT (Typeω@j) OT wk_id j HOTj HITj Hid) as H.
        rewrite exp_wk_id in H; rewrite (exp_wk_id_ext OT _ wk_q_id) in H; cbn in H; exact H. }
      rewrite HA; cbn [nf_to_exp].
      etransitivity; [ eapply wf_exp_eq_fn_eta'; exact HNpi |].
      eapply wf_exp_eq_fn_cong'; [ exact HITeq | eapply wf_exp_eq_conv'; [ exact Hbody | exact HOT ] ].
  Qed.

  Lemma ind_realize_top : forall Γ M A m R,
      DG d_ind p (ups ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
      Γ ⊢ M : A ® m ∈ El ->
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups ++ ns) ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m ∈ R ->
      Γ ⊢ M : A ® m ∈ glu_elem_top i (d_ind p (ups ++ ns)).
  Proof.
    intros * Hglu HM HR Hm.
    pose proof HM as HM'; apply HEl in HM'; destruct HM' as (HMt & Hme & Qs & HQs & Hk).
    assert (HPt : Γ ⊢ A ® P) by (apply HP; exists Qs; exact HQs).
    destruct HQs as [HQ HQk].
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as (_ & _ & _ & _ & _ & _ & _ & Herel).
    assert (ER : R <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
    econstructor; [ exact HMt | exact Hglu | exact HPt | eapply per_elem_then_per_top; eassumption |].
    intros Δ φ w Hφ Hw.
    destruct (HQk Δ φ Hφ) as (Hpt & _ & _).
    pose proof (Hk Δ φ _ Hφ (glu_params_top_refl _ _ _ _ Hpt)) as Hg.
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    pose proof (glu_ind_readback _ _ _ _ Hg HΔ ns Hpt (proj1 (Herel _ _) (proj1 (ER _ _) Hm)) w Hw) as Hrb.
    eapply wf_exp_eq_conv'; [ exact Hrb |].
    rewrite <- wk_apps_ind; symmetry; mauto 3.
  Qed.
End IndRealize.

Theorem realize_glu_univ_elem_gen : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    (forall Γ A R,
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        Γ ⊢ A ® P ->
        Γ ⊢ A ® glu_typ_top i a) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          DG a ∈ glu_univ_elem i ↘ P ↘ El ->
          Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
          Γ ⊢ M : A ® ⇑ a m ∈ El) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          DG a ∈ glu_univ_elem i ↘ P ↘ El ->
          Γ ⊢ M : A ® m ∈ El ->
          DF a ≈ a ∈ per_univ_elem i ↘ R ->
          Dom m ≈ m ∈ R ->
          Γ ⊢ M : A ® m ∈ glu_elem_top i a).
Proof.
  simpl. glu_univ_elem_induction1.
  8:{ (** An inductive type. *)
      split; [| split]; intros.
      - eapply ind_realize_typ; eassumption.
      - eapply ind_realize_bot; eassumption.
      - eapply ind_realize_top with (elem_rel := elem_rel); try eassumption.
        + intros * Hm Hc HA Hp Eb; exact (proj2 (proj2 (H8 _ _ _ _ _ _ _ Hm Hc HA Hp Eb))).
        + intros * Hm Hc Heq Hw HB Hy Eb.
          destruct (H11 _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy Eb) as (Ht & Hbt & _).
          split; [ exact Ht | intros; eapply Hbt; [ eapply H10; eassumption | eassumption ] ]. }
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 per_univ_elem ltac:(fun H => pose proof (per_univ_then_per_top_typ H));
    match_by_head glu_elem_bot ltac:(fun H => destruct H as []);
    destruct_all.
  (** The two universe clauses, large then small.  The large one's equations
      are at the ambient [Typeω@(ulvl i)].  The small one's element predicate
      carries its own readback clause, at the element's type, so its top case
      is that clause, and its bottom case lifts the neutral's equations to the
      ambient [Typeω@0] by cumulativity. *)
  1:{ econstructor; eauto; intros.
      progressive_inversion.
      mauto 3. }
  1:{ handle_functional_glu_univ_elem.
      match_by_head glu_univ_elem invert_glu_univ_elem.
      clear_dups.
      apply_equiv_left.
      repeat split; eauto.
      repeat eexists.
      + glu_univ_elem_econstructor; eauto; reflexivity.
      + simpl. repeat split.
        * eapply wf_conv'; eassumption.
        * intros. saturate_kripke_escape.
          eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ]. }
  1:{ deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
      firstorder.
      specialize (H _ _ _ H10) as [? []].
      econstructor; mauto 3.
      + apply_equiv_left. trivial.
      + intros.
        saturate_kripke_escape.
        deepexec H ltac:(fun H => destruct H).
        progressive_invert H16.
        deepexec H20 ltac:(fun H => pose proof H).
        functional_read_rewrite_clear.
        eapply wf_exp_eq_conv'; [ eassumption | mauto 3 ]. }
  (** The small universe as a type: it reads back as the universe at the
      canonical form of its level, which its glued level term is equal to. *)
  1:{ econstructor; [ gen_presups; eassumption | eassumption |].
      intros Δ φ W Hφ Hr.
      assert (⊢ Δ) by (eapply kripke_dom; eassumption).
      inversion Hr; subst.
      match goal with Hg : glu_lvl ?n _ _ _ |- _ =>
        assert (Δ ⊢ H4[φ]ʷ ≈ nf_lvl_of L : Level@n) by (eapply glu_lvl_readback; eassumption) end.
      assert (Δ ⊢ A[φ]ʷ ≈ Type⟨H4[φ]ʷ⟩ : Typeω@(ulvl i)) by mauto 3.
      etransitivity; [ eassumption |].
      eapply wf_exp_eq_univ_cong_large_tm; [ assumption | gen_presups; eassumption | eassumption ]. }
  (** A neutral of a small universe: its type-level gluing is a neutral type's
      at the ambient [Typeω@0], which cumulativity reaches from the small
      universe, and its readback clause is the neutral's. *)
  1:{ handle_functional_glu_univ_elem.
      match_by_head glu_univ_elem invert_glu_univ_elem.
      clear_dups.
      apply_equiv_left.
      match goal with
      | H : suniv_glu_typ_pred _ _ _ _ |- _ => destruct H as (t & nt & Ht & HAt)
      | H : exists t n, glu_lvl n _ t _ /\ _ |- _ => destruct H as (t & nt & Ht & HAt)
      end.
      repeat apply conj; [ assumption | exists t, nt; split; assumption | |].
      + do 2 eexists; split; [ glu_univ_elem_econstructor; eauto; reflexivity |].
        cbn; split; [ eapply suniv_elem_large; eassumption |].
        intros Δ φ M' Hφ Hr.
        eapply suniv_elem_eq_large; [ eauto | mauto 3 ].
      + intros Δ φ W Hφ Hr.
        inversion Hr; subst; eauto. }
  (** An element of a small universe reads back by its own readback clause,
      which is at its type. *)
  1:{ deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
      match goal with Hx : per_univ _ m m |- _ => destruct Hx as [? Hx] end.
      match goal with
      | Hx : per_univ_elem (us _) ?x m m, Ht : glu_lvl ?nt _ ?t l |- _ =>
          econstructor; [ assumption | eassumption | apply_equiv_left; cbn; exists t, nt; split; assumption | |];
          [ intros s; destruct (per_univ_then_per_top_typ Hx s) as [W [HW _]];
            exists W; split; constructor; assumption
          | intros Δ φ w Hφ Hr; inversion Hr; subst; eauto ]
      end. }
  (* Level *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    assert (HA : Γ ⊢ A ≈ Level@n : Typeω@(ulvl i)) by eauto.
    split; [ exact HA | split; [ apply per_bot_then_per_lvl_at; assumption |] ].
    (** A neutral level reads back as the atom of its sort, a level of that
        sort by its readback equation. *)
    intros Δ φ L Hφ Hr.
    progressive_inversion.
    assert (HMeq : Δ ⊢ M[φ]ʷ ≈ M0 : Level@n) by (eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ]).
    split; [ exact HMeq |].
    cbn; split; [ lia | split; [ split; [ lia | gen_presups; eassumption ] | exact I ] ].
  - econstructor; mauto 3.
    + match goal with H : per_lvl_at _ ?m ?m |- _ => pose proof (per_lvl_at_lvl _ _ _ H) end.
      bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      eapply wf_exp_eq_conv';
        [ eapply glu_lvl_readback;
          [ eassumption | eassumption | eapply read_nf_level_sort; eassumption ]
        | mauto 3 ].
  (* True *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    mauto 3.
  - econstructor; mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      progressive_inversion.
      eapply wf_exp_eq_conv'; [ apply wf_exp_eq_true_eta; mauto 3 | mauto 3 ].
  (* False *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    intros.
    eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ].
  - econstructor; mauto 3.
    + bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      eapply wf_exp_eq_conv'; [ eapply glu_False_readback; eassumption | mauto 3 ].
  (* pi *)
  - match_by_head pi_glu_typ_pred progressive_invert.
    handle_per_univ_elem_irrel.
    invert_per_univ_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + saturate_kripke_escape.
      pose proof (H13 Γ wk_id ltac:(mauto 3)) as HIT.
      rewrite exp_wk_id in HIT.
      dir_inversion_clear_by_head read_typ.
      assert (Γ ⊢ IT ® glu_typ_top i a) as [] by mauto 3.
      assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HA' by (rewrite <- exp_wk_pi; mauto 3).
      rewrite HA'.
      simpl. apply wf_exp_eq_pi_cong'; [ firstorder | ].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      pose proof (H13 _ _ H16) as HIPφ.
      assert (IEl (Δ ▹ IT[φ]ʷ) IT[φ]ʷ[↑]ʷ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      assert (⊢ Δ ▹ IT[φ]ʷ) by mauto 3.
      assert (Δ ▹ IT[φ]ʷ ⊢k φ ⊙ ↑ : Γ) as Hk by mauto 3.
      pose proof (H14 _ _ _ _ Hk HEl H24) as HOP.
      assert (HOT : Δ ▹ IT[φ]ʷ ⊢ OT[ι (φ ⊙ ↑),,#0] ≈ OT[wk_q φ]ʷ : Typeω@(ulvl i))
        by (assert (Hqv := kripke_q_var_eq _ _ _ (Typeω@(ulvl i)) _ _ (ulvl i) H12 H17 H16);
            cbn in Hqv; exact Hqv).
      specialize (H8 _ _ _ H27 HOP) as [].
      eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact HOT |].
      rewrite <- (exp_wk_id OT[ι (φ ⊙ ↑),,#0]).
      mauto 3.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    invert_glu_rel1.
    econstructor; try eapply per_bot_then_per_elem; eauto.
    intros.
    saturate_kripke_escape.
    saturate_glu_info.
    match_by_head1 per_univ_elem invert_per_univ_elem.
    destruct_rel_mod_eval.
    simplify_evals.
    eexists; repeat split; mauto 3.
    eapply H2; eauto.
    assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
    assert (Δ ⊢ M[φ]ʷ : Π IT[φ]ʷ OT[wk_q φ]ʷ) as HM by mauto 3.
    assert (Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N]) as HMN
      by (rewrite <- exp_sub_wk_q_extend; eapply wf_app'; eassumption).
    pose proof (H10 _ _ _ _ H17 H18 equiv_n) as HOP.
    pose proof (H1 _ equiv_n _ H22) as HG.
    pose proof (H15 _ _ _ _ _ H H18 H0 equiv_n) as HNtop.
    destruct HNtop as [? ? ? ? ? HNtoprel HNrb].
    eapply glu_elem_bot_make with (P := OP n equiv_n) (El := OEl n equiv_n); try eassumption.
    + mauto 3 using domain_app_per.
    + intros Δ0 φ0 M' Hk Hrb.
      progressive_invert Hrb.
      assert (Δ0 ⊢k φ ⊙ φ0 : Γ) as Hkc by (eapply kripke_compose; eassumption).
      assert (Δ0 ⊢ A[φ ⊙ φ0]ʷ ≈ Π IT[φ ⊙ φ0]ʷ OT[wk_q (φ ⊙ φ0)]ʷ : Typeω@(ulvl i)) as HAeq'
        by (rewrite <- exp_wk_pi; mauto 3).
      rewrite exp_wk_sub_of_wk_extend, <- exp_sub_wk_q_extend, exp_wk_app, exp_wk_wk.
      eapply wf_exp_eq_app_cong'.
      * eapply wf_exp_eq_conv'; [ eapply H12; eassumption | eassumption ].
      * rewrite <- exp_wk_wk. eapply HNrb; eassumption.
  - handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    pose proof H8.
    invert_per_univ_elem H8.
    econstructor; mauto 3.
    + invert_glu_rel1. trivial.
    + eapply glu_univ_elem_trm_typ; eauto.
    + intros Δ φ w Hk Hrb.
      saturate_kripke_escape.
      invert_glu_rel1. clear_dups.
      progressive_invert Hrb.
      assert (⊢ Γ) by mauto 2.
      pose proof (H10 _ _ Hk) as HIPφ.
      pose proof (H10 Γ wk_id ltac:(mauto 3)) as HITId.
      rewrite exp_wk_id in HITId.
      assert (Γ ⊢ IT ® glu_typ_top i a) as [? ? HITrb] by mauto 3.
      assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
      assert (Δ ⊢ M[φ]ʷ : Π IT[φ]ʷ OT[wk_q φ]ʷ) as HM by mauto 3.
      eapply wf_exp_eq_conv'; [ | symmetry; eapply HAeq ].
      (** Read back a function by η-expanding it and recursing into the body. *)
      etransitivity; [ eapply wf_exp_eq_fn_eta'; eassumption | ].
      cbn [nf_to_exp].
      eapply wf_exp_eq_fn_cong'; [ eapply HITrb; eassumption | ].
      assert (⊢ Δ ▹ IT[φ]ʷ) by mauto 3.
      assert (Δ ▹ IT[φ]ʷ ⊢k φ ⊙ ↑ : Γ) as Hk' by mauto 3.
      pose proof (var_per_elem (length Δ) H0) as Hvar.
      assert (IEl (Δ ▹ IT[φ]ʷ) IT[φ]ʷ[↑]ʷ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      destruct (H14 _ _ _ _ Hk' HEl Hvar) as [mn [Happ HOEl]].
      rewrite exp_wk_wk.
      functional_eval_rewrite_clear.
      pose proof (H1 _ Hvar _ H20) as HG.
      destruct (H2 _ Hvar _ H20) as [? [? Htop]].
      apply_equiv_left.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      specialize (Htop _ _ _ _ _ HG HOEl ltac:(eassumption) ltac:(eassumption)) as [? ? ? ? ? ? Hrbtop].
      specialize (Hrbtop (Δ ▹ IT[φ]ʷ) wk_id M0 ltac:(mauto 3) Hrb).
      repeat rewrite exp_wk_id in Hrbtop.
      assert (HOT : Δ ▹ IT[φ]ʷ ⊢ OT[ι (φ ⊙ ↑),,#0] ≈ OT[wk_q φ]ʷ : Typeω@(ulvl i))
        by (assert (Hqv := kripke_q_var_eq Δ Γ IT (Typeω@(ulvl i)) OT φ (ulvl i) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption));
            cbn in Hqv; exact Hqv).
      eapply wf_exp_eq_conv'; [ exact Hrbtop | exact HOT ].
  (* neut *)
  - econstructor; eauto.
    intros.
    progressive_inversion.
    firstorder.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    econstructor; eauto.
  - handle_functional_glu_univ_elem.
    invert_glu_rel1.
    econstructor; eauto.
    + intros s. destruct (H3 s) as [? []].
      mauto.
    + intros.
      progressive_inversion.
      specialize (H11 (length Δ)) as [? []].
      firstorder.
Qed.

Corollary realize_glu_typ_top : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A ® glu_typ_top i a.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_bot : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m,
      Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
      Γ ⊢ M : A ® ⇑ a m ∈ El.
Proof.
  intros.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M : A ® m ∈ glu_elem_top i a.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
  eapply glu_univ_elem_per_elem; eauto.
Qed.

Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.

Corollary var0_glu_elem : forall {i : uidx} {a P El Γ A},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A[↑]ʷ ® ⇑! a (length Γ) ∈ El.
Proof.
  intros.
  eapply realize_glu_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.
