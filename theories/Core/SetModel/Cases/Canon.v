(** * Valid Units Are Their Canonical Units

    A valid unit, and a module expression valid in what it denotes, has
    the modules and the proofness of the unit its module part stands for,
    [mdesc_unit Rm], which is valid ([set_valid_unit_canon_all]): an alias of
    a literal is the literal over both telescopes, an alias of a filed
    module the alias of the filed module itself. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import ValidUnit MemberTypes ModuleCases Unit.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound Presup.
Import ListNotations.

Section Canon.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** The unit of the module part of what a well-formed module expression
    denotes is well formed. *)
Lemma mdesc_unit_wf_of : forall Γ H R Rm, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ H R ->
    mdesc_mod R = Some Rm -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ mdesc_unit Rm ≈ mdesc_unit Rm.
Proof.
  intros * Hw Hm Hmd.
  exact (proj1 (mdesc_unit_wf _ _ _ _ (presup_modexp_eq_ctx Hw) (desc_ok_mod _ _ Hgw _ _ _ (me_desc_ok _ _ _ _ _ _ Hw Hm) Hmd)
                  (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgw Hm) Hmd) (mdesc_mod_is_mod _ _ Hmd)
                  (wf_mdenote_mod_xp _ _ _ _ _ _ _ Hw Hm Hmd))).
Qed.

(** [set_canon_with Γ K Rm]: [K], of the module part [Rm], has the modules
    and the proofness of the unit [Rm] stands for, which is valid. *)
Record set_canon_with (Γ : ctx) (K : modexp) (Rm : mdesc) : Prop :=
  { (** Its modules are the unit's *)
    set_canon_rel : set_modexp_rel T γ Γ K (mdesc_unit Rm)
    (** The unit is valid *)
  ; set_canon_valid : set_valid_unit T γ Γ (mdesc_unit Rm)
    (** Its proofness is the unit's, at slots coherent with [Γ] *)
  ; set_canon_proofs : forall κs, set_slots_coherent γ Γ κs -> forall ys x,
      modexp_member_proofs γ κs K ys x = modexp_member_proofs γ κs (mdesc_unit Rm) ys x }.

Theorem set_valid_unit_canon_all :
  (forall Γ K, set_valid_unit T γ Γ K -> forall RK Rm, mdenote gc_deps gc_stack Γ K RK -> mdesc_mod RK = Some Rm ->
     set_canon_with Γ K Rm) /\
  (forall Γ H, set_valid_modexp T γ Γ H -> forall R Rm, mdenote gc_deps gc_stack Γ H R -> mdesc_mod R = Some Rm ->
     set_canon_with Γ H Rm).
Proof.
  apply (set_valid_unit_modexp_ind T γ).
  - (* a filed module at arguments: its own unit *)
    intros Γ p T0 Φ Tr Tf Ns Hw Hgl HΓ Ha RK Rm Hm Hmd.
    pose proof (set_valid_unit_filed T γ _ _ _ _ _ _ _ Hw Hgl HΓ Ha) as HK.
    destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm _ Hm1), Hmod1 in Hmd; injection Hmd as <-.
    cbn [mdesc_unit]. constructor; [exact (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HK) | exact HK | intros; reflexivity].
  - (* a body: its own literal *)
    intros Γ Δ Φ Φx Hb Hsub _ Hop _ RK Rm Hm Hmd.
    pose proof (set_valid_unit_body T γ _ _ _ _ Hb Hsub Hop) as HK.
    apply mdenote_lit_inv in Hm. inversion Hm; subst.
    match goal with Hb0 : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb0; injection Hb0 as <- end.
    cbn in Hmd; injection Hmd as <-. cbn [mdesc_unit].
    constructor; [exact (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HK) | exact HK | intros; reflexivity].
  - (* an alias: its target's unit, abstracted *)
    intros Γ Δ E Hal HE IHE RK Rm Hm Hmd.
    pose proof (set_valid_unit_alias T γ _ _ _ Hal HE) as HK0.
    pose proof (set_valid_unit_wf T γ _ _ HK0) as HwK.
    pose proof Hm as Hm0. apply mdenote_lit_inv in Hm.
    inversion Hm as [| ? ? ? ? RE REm HmE HmdE]; subst.
    pose proof (mdesc_mod_is_mod _ _ HmdE) as Him.
    rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ Him)) in Hmd; injection Hmd as <-.
    destruct (IHE _ _ HmE HmdE) as [HEu HKu HEp].
    pose proof Hal as [_ HΔ [l Hl] HΓ HΔΓ HrA _].
    destruct Δ as [| e Δ0].
    + (* with no parameter: the target's *)
      rewrite mdesc_up_nil. cbn [List.app] in *.
      constructor; [| exact HKu | intros κs Hκ ys x; exact (HEp κs Hκ ys x)].
      exact (set_modexp_rel_trans T γ _ _ _ _
               (set_alias0_rel T γ Hfn Hmods _ _ HΓ (set_modexp_rel_refl_left T γ _ _ _ HEu)) HEu).
    + set (Δ := e :: Δ0) in *.
      pose proof (presup_modexp_eq_ctx (set_valid_modexp_wf T γ _ _ HE)) as HcΔΓ.
      pose proof (mdesc_unit_wf_of _ _ _ _ HwK Hm0 (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ Him))) as Hwup.
      (* the alias of the target's unit *)
      assert (Halias : set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias (mdesc_unit REm)))) (me_lit (gu_mk Δ (md_alias (mdesc_unit REm))))).
      { exact (set_unit_rel_abs T γ Hfn Hmods Δ Γ nil _ HΔ HΔΓ HcΔΓ
                 (set_modexp_rel_refl_left T γ _ _ _
                    (set_alias0_rel T γ Hfn Hmods _ _ HΔΓ (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HKu)))). }
      pose proof (set_alias_rel_cong T γ Hfn Hmods _ _ _ _ HΔ HrA Halias HEu HEp) as Hcong.
      assert (Hpcong : forall κs, set_slots_coherent γ Γ κs -> forall ys x,
                 modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias E))) ys x =
                 modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias (mdesc_unit REm)))) ys x).
      { intros κs Hκ ys x. cbn [modexp_member_proofs]. rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
        exact (HEp _ (set_slots_coherent_tele_out γ _ _ _ HΔ Hκ) ys x). }
      destruct REm as [| Δe Φ Φx | [| e' Θ'] p T' Φ' Ns |]; cbn in Him; try contradiction.
      * (* a local body: the literal over both telescopes *)
        cbn [mdesc_up mdesc_unit] in HKu, Halias, Hcong, Hpcong, Hwup |- *.
        pose proof (set_valid_unit_abs T γ Hfn Hmods Δ Γ Δe _ l HKu HΔ Hl Hwup) as HKup.
        constructor; [| exact HKup |].
        -- exact (set_modexp_rel_trans T γ _ _ _ _ Hcong
                    (set_unit_rel_flatten T γ Hfn Hmods _ _ _ _ HΔ Halias (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HKup))).
        -- intros κs Hκ ys x. rewrite (Hpcong _ Hκ). cbn [mdesc_unit modexp_member_proofs]. rewrite !unit_member_proofs_tele_out.
           cbn [moddef_member_proofs modexp_member_proofs]. rewrite unit_member_proofs_tele_out, List.rev_app_distr, tele_out_proofs_app.
           reflexivity.
      * (* a filed module at arguments: the alias of it *)
        cbn [mdesc_up mdesc_unit List.app] in HKu, Halias, Hcong, Hpcong, Hwup |- *.
        constructor; [exact Hcong | | exact Hpcong].
        apply set_valid_unit_alias; [| exact (set_valid_modexp_of_unit T γ Hfn Hmods Hok _ _ HKu)].
        constructor; [exact Hwup | exact HΔ | exists l; exact Hl | exact HΓ | exact HΔΓ | exact Halias
                     | exact (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HKu)].
      * (* an alias of a filed module: the alias over both telescopes *)
        cbn [mdesc_up mdesc_unit] in HKu, Halias, Hcong, Hpcong, Hwup |- *.
        change (match (e' :: Θ') ++ Δ with
                | [] => me_apps (qname_mod p) Ns
                | _ :: _ => me_lit (gu_mk ((e' :: Θ') ++ Δ) (md_alias (me_apps (qname_mod p) Ns)))
                end) with (me_lit (gu_mk ((e' :: Θ') ++ Δ) (md_alias (me_apps (qname_mod p) Ns)))) in Hwup |- *.
        pose proof (set_valid_unit_abs T γ Hfn Hmods Δ Γ (e' :: Θ') _ l HKu HΔ Hl Hwup) as HKup.
        constructor; [| exact HKup |].
        -- exact (set_modexp_rel_trans T γ _ _ _ _ Hcong
                    (set_unit_rel_flatten T γ Hfn Hmods _ _ _ _ HΔ Halias (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HKup))).
        -- intros κs Hκ ys x. rewrite (Hpcong _ Hκ).
           change (modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk (e' :: Θ') (md_alias (me_apps (qname_mod p) Ns))))))) ys x
                   = modexp_member_proofs γ κs (me_lit (gu_mk ((e' :: Θ') ++ Δ) (md_alias (me_apps (qname_mod p) Ns)))) ys x).
           cbn [modexp_member_proofs]. rewrite !unit_member_proofs_tele_out.
           cbn [moddef_member_proofs modexp_member_proofs]. rewrite unit_member_proofs_tele_out, List.rev_app_distr, tele_out_proofs_app.
           reflexivity.
  - (* a module expression equal to a valid unit: the unit's *)
    intros Γ H K R Rm RK [HwH HmH HmodH HHK HmK HmodK Hpr] HK IHK R' Rm' Hm Hmd.
    rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm _ HmH), HmodH in Hmd; injection Hmd as <-.
    destruct (IHK _ _ HmK HmodK) as [HKu HKK HKp].
    constructor; [exact (set_modexp_rel_trans T γ _ _ _ _ HHK HKu) | exact HKK |].
    intros κs Hκ ys x. exact (eq_trans (Hpr κs Hκ ys x) (HKp κs Hκ ys x)).
Qed.

Corollary set_valid_modexp_canon : forall Γ H R Rm, set_valid_modexp T γ Γ H -> mdenote gc_deps gc_stack Γ H R ->
    mdesc_mod R = Some Rm -> set_canon_with Γ H Rm.
Proof. intros * HH Hm Hmd. exact (proj2 set_valid_unit_canon_all _ _ HH _ _ Hm Hmd). Qed.

End Canon.
