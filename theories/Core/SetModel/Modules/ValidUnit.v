(** * Valid Units Along Substitutions

    Valid units and module expressions stay valid along substitutions that
    send environments to environments ([set_valid_unit_modexp_moved]): the
    parts of a body or an alias move with the substitution lifted past the
    parameters and the entries before them, the descriptions by
    [mdenote_sub].  So a slot's unit is valid where the slot is
    ([set_slot_valid_unit]). *)

From Stdlib Require Import List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound.
From Mctt.Core.Completeness.Modules Require Import ValidUnit.
Import ListNotations.

Section ValidUnit.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

(** ** Moving Past an Extension *)

Lemma set_moves_ext : forall Ψ Δ Γ σ Fσ, set_gsub_with T γ Γ σ Δ Fσ -> set_ctx T γ Γ -> set_ctx T γ (Ψ ++ Δ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ -> set_moves_with T γ Ψ Δ Γ σ Fσ.
Proof.
  intros * Hg HΓ HΔ Hc. constructor; [exact Hg | exact HΓ | exact HΔ | | exact Hc].
  exact (set_ctx_moved T γ Hfn Hmods _ _ _ _ _ Hg HΓ HΔ Hc).
Qed.

(** The setting at the substitution lifted past [Ψ], from which it moves
    the extensions of [Ψ ++ Δ]. *)
Lemma set_moves_lift : forall Ψ Φ Δ Γ σ Fσ, set_moves_with T γ Ψ Δ Γ σ Fσ -> set_ctx T γ (Φ ++ Ψ ++ Δ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Φ ++ Ψ ++ Δ ->
    set_moves_with T γ Φ (Ψ ++ Δ) (tele_sub Ψ σ ++ Γ) (sb_qn (List.length Ψ) σ) (set_env_moved (List.length Ψ) Fσ).
Proof.
  intros * Hs HΦ Hc. pose proof Hs as [_ _ _ HΓ' _].
  apply set_moves_ext; [exact (set_gsub_lift T γ Hfn Hmods _ _ _ _ _ Hs) | exact HΓ' | exact HΦ | exact Hc].
Qed.

(** ** The Parts of Units Along Substitutions *)

(** The setting past the extension's tail. *)
Lemma set_moves_tail : forall e Ψ Δ Γ σ Fσ, set_moves_with T γ (e :: Ψ) Δ Γ σ Fσ -> set_moves_with T γ Ψ Δ Γ σ Fσ.
Proof.
  intros * [Hg HΓ [HΔ _] [HΓ' _] Hc]. constructor; [exact Hg | exact HΓ | exact HΔ | exact HΓ' | exact (ctx_decomp_tail Hc)].
Qed.

Lemma set_params_evaluated_nil : forall Γ l, set_params_evaluated T γ Γ nil l.
Proof. intros Γ l Δ1 κ A Δ2 H. destruct Δ1; discriminate. Qed.

Lemma set_params_evaluated_cons_iff : forall Γ e Δ l, set_params_evaluated T γ Γ (e :: Δ) l <->
    (forall κ A, e = ce_ass κ A -> set_rel_exp_eq T γ (Δ ++ Γ) (a_typ l) A A \/ set_rel_exp_eq T γ (Δ ++ Γ) a_level_sort A A) /\
    set_params_evaluated T γ Γ Δ l.
Proof.
  intros. split.
  - intros H. split; [intros κ A -> ; exact (H nil κ A Δ eq_refl) |].
    intros Δ1 κ A Δ2 HΔ. apply (H (e :: Δ1) κ). rewrite HΔ. reflexivity.
  - intros [Hh Ht] [| e1 Δ1] κ A Δ2 HΔ; cbn in HΔ; injection HΔ as He HΔ.
    + subst Δ. exact (Hh κ A He).
    + exact (Ht _ _ _ _ HΔ).
Qed.

Lemma set_params_evaluated_moved : forall Δu Δ Γ σ Fσ l, set_moves_with T γ Δu Δ Γ σ Fσ ->
    set_params_evaluated T γ Δ Δu l -> set_params_evaluated T γ Γ (tele_sub Δu σ) l.
Proof.
  induction Δu as [| e Δu IH]; intros * Hs Hl; cbn [tele_sub]; [apply set_params_evaluated_nil |].
  apply set_params_evaluated_cons_iff in Hl as [Hh Ht]. pose proof (set_moves_tail _ _ _ _ _ _ Hs) as Hs'.
  apply set_params_evaluated_cons_iff. split; [| exact (IH _ _ _ _ _ Hs' Ht)].
  intros κ A HA. destruct e as [κ0 A0 | | |]; cbn in HA; try discriminate. injection HA as <- <-.
  destruct (Hh _ _ eq_refl) as [Hp | Hp]; [left | right]; exact (set_exp_eq_moved T γ Hfn Hmods _ _ _ _ _ _ _ _ Hs' Hp).
Qed.

(** The sorts of a body's definitions, filled in, move along a
    substitution of the body's base: the moved body's filling is the
    filling followed by the substitution ([gm_fill_sub]). *)
Lemma set_body_sorts_valid_moved : forall Φ Ψ D G σ Fσ, set_body_sorts_valid T γ Φ (Ψ ++ D) ->
    set_moves_with T γ Ψ D G σ Fσ ->
    set_body_sorts_valid T γ (gmod_sub Φ (sb_qn (List.length Ψ) σ)) (tele_sub Ψ σ ++ G).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hv Hm; cbn [gmod_sub set_body_sorts_valid] in Hv |- *;
    [exact I | | exact (IH _ _ _ _ _ Hv Hm)].
  split; [exact (IH _ _ _ _ _ (proj1 Hv) Hm) |].
  intros A' M' τ' He Hf'.
  destruct (entry_tm_sub_inv _ _ _ _ He) as (A & M & HeA & -> & ->).
  destruct (gm_fill Φ) as [τ0 |] eqn:Hf0;
    [| exfalso; apply (proj2 (gm_fill_sub_none Φ (sb_qn (List.length Ψ) σ))) in Hf0; rewrite Hf0 in Hf'; discriminate].
  destruct (gm_fill_sub Φ (List.length Ψ) σ τ0 Hf0) as (τ1 & Hf1 & Heq). rewrite Hf' in Hf1. injection Hf1 as <-.
  destruct (proj2 Hv _ _ _ HeA eq_refl) as [i Hi]. exists i.
  pose proof (set_exp_eq_moved T γ Hfn Hmods _ _ _ _ _ _ _ _ Hm Hi) as H'.
  replace (entry_kind (gentry_sub E (sb_qn (gm_binders Φ) (sb_qn (List.length Ψ) σ)))) with (entry_kind E) by (destruct E; reflexivity).
  rewrite abs_kind_sort_sub in H'.
  rewrite exp_sub_sub, <- sb_qn_plus, (exp_sub_sb_eq A _ _ Heq), <- exp_sub_sub. exact H'.
Qed.

(** A context's tail denotes. *)
Lemma set_ctx_app_r : forall Ψ Γ, set_ctx T γ (Ψ ++ Γ) -> set_ctx T γ Γ.
Proof. induction Ψ as [| e Ψ IH]; intros Γ H; [exact H | exact (IH _ (proj1 H))]. Qed.

(** A valid unit is well formed. *)
Lemma set_valid_unit_wf : forall Γ K, set_valid_unit T γ Γ K -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ K ≈ K.
Proof. intros * HK. destruct HK as [? ? ? ? ? ? ? Hw | ? ? ? ? [Hw] | ? ? ? [Hw]]; exact Hw. Qed.

(** The setting moved past [Ψ], of an extension of [Ψ ++ Δ]'s denoting,
    well-formed context. *)
Lemma set_moves_of_ext : forall X Ψ Δ Γ σ Fσ, set_gsub_with T γ Γ σ Δ Fσ -> set_ctx T γ Γ ->
    set_ctx T γ (X ++ Ψ ++ Δ) -> ⊢ gc_deps ⍮ gc_stack ⍮ X ++ Ψ ++ Δ -> set_moves_with T γ Ψ Δ Γ σ Fσ.
Proof.
  intros * Hg HΓ HC Hc. apply set_moves_ext; [exact Hg | exact HΓ | exact (set_ctx_app_r _ _ HC) | exact (ctx_app_wf_tail _ _ _ _ Hc)].
Qed.

(** The lifted setting, in the shape the recursive premises read. *)
Lemma set_moves_nil_lift : forall Ψ Δ Γ σ Fσ, set_moves_with T γ Ψ Δ Γ σ Fσ ->
    set_moves_with T γ nil (Ψ ++ Δ) (tele_sub Ψ σ ++ Γ) (sb_qn (List.length Ψ) σ) (set_env_moved (List.length Ψ) Fσ).
Proof. intros * Hs. pose proof Hs as [_ _ HΔ _ Hc]. exact (set_moves_lift _ nil _ _ _ _ Hs HΔ Hc). Qed.

(** Coherent slots along the substitution lifted past the extension the
    setting moves past. *)
Lemma set_sub_slots_coherent_of_moves : forall Ψ Δ Γ σ Fσ, set_moves_with T γ Ψ Δ Γ σ Fσ -> set_sub_slots_coherent γ Δ Γ σ ->
    set_sub_slots_coherent γ (Ψ ++ Δ) (tele_sub Ψ σ ++ Γ) (sb_qn (List.length Ψ) σ).
Proof. intros * _ Hκ. exact (set_sub_slots_coherent_lift γ _ _ _ _ Hκ). Qed.

Lemma set_valid_unit_modexp_moved :
  (forall Δ K, set_valid_unit T γ Δ K -> forall Γ σ Fσ, set_moves_with T γ nil Δ Γ σ Fσ -> set_sub_slots_coherent γ Δ Γ σ ->
     set_valid_unit T γ Γ (modexp_sub K σ)) /\
  (forall Δ H, set_valid_modexp T γ Δ H -> forall Γ σ Fσ, set_moves_with T γ nil Δ Γ σ Fσ -> set_sub_slots_coherent γ Δ Γ σ ->
     set_valid_modexp T γ Γ (modexp_sub H σ)).
Proof.
  apply (set_valid_unit_modexp_ind T γ).
  - (* a filed module at arguments *)
    intros Δ p T0 Φ Tr Tf Ns Hw Hgl HΔ [-> Hl Ha Hsc HN HNr] Γ σ Fσ Hs Hκ. pose proof Hs as [[Hσ _ _] HΓ _ _ _].
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ Hw Hσ) as Hw'.
    rewrite me_apps_sub, qname_mod_sub in Hw' |- *.
    eapply set_valid_unit_filed; [exact Hw' | exact Hgl | exact HΓ |].
    constructor; [reflexivity | rewrite length_map; exact Hl | exact Ha | exact Hsc | |].
    + intros k N A HNk HAk.
      rewrite List.nth_error_map in HNk; destruct (nth_error Ns k) as [N0 |] eqn:HN0; [| discriminate]; injection HNk as <-.
      rewrite <- (tele_insts_sub Tf 0 sb_id sb_id σ Ns Ha Hsc ltac:(intros; lia)), List.nth_error_map in HAk.
      destruct (nth_error (tele_insts Tf sb_id Ns) k) as [A0 |] eqn:HA0; [| discriminate]; injection HAk as <-.
      exact (set_exp_eq_moved T γ Hfn Hmods nil _ _ _ _ _ _ _ Hs (HN _ _ _ HN0 HA0)).
    + intros k A HAk.
      rewrite <- (tele_insts_sub Tf 0 sb_id sb_id σ Ns Ha Hsc ltac:(intros; lia)), List.nth_error_map in HAk.
      destruct (nth_error (tele_insts Tf sb_id Ns) k) as [A0 |] eqn:HA0; [| discriminate]; injection HAk as <-.
      destruct (HNr _ _ HA0) as (Srt & [i |] & Hi); eexists; (split; [constructor |]);
        exact (set_exp_eq_moved T γ Hfn Hmods nil _ _ _ _ _ _ _ Hs Hi).
  - (* a body *)
    intros Δ Δu Φ Φx [Hw Hx HΔu [l HΔur] HΔ HC Hsv Hsh Hsx HK Hopr] Hsl IHsl Hops IHops Γ σ Fσ Hs Hκ.
    pose proof Hs as [Hg HΓ _ _ _]. pose proof (set_gsub_typed _ _ _ _ _ _ Hg) as Hσ.
    pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m unit_full] in Hf.
    destruct Hf as [Φx0 _ _ _ _ Hx0 HwCx _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgw)))) _ _ _ Hx _ Hx0) as <-.
    destruct (wf_modexp_eq_scoped _ _ _ _ _ Hw) as (HΔs & HUs & _); cbn in HUs.
    rewrite gunit_scoped_mk in HUs; destruct HUs as [_ HDs]; cbn in HDs.
    pose proof (wf_ctx_scoped _ _ _ HwCx) as HCxs.
    assert (HΔCs : ctx_scoped 0 (Δu ++ Δ)) by exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HCxs)).
    pose proof (wf_sub_mod_compat _ _ _ _ _ Hσ) as Hc.
    pose proof (body_xp_sub _ _ (wf_gstack_closed _ _ Hgw) _ _ _ Hx HΔCs
                  ltac:(rewrite length_app; exact (proj2 HDs)) _ _ (sub_mod_compat_ext Δu _ _ _ Hc)) as Hxσ.
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    pose proof (set_moves_of_ext _ _ _ _ _ _ Hg HΓ HC HwCx) as HsΔ.
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ Hw Hσ) as Hw'.
    pose proof (set_modexp_rel_moved T γ Hfn Hmods nil _ _ _ _ _ _ Hs HK) as HK'.
    cbn [modexp_sub] in Hw', HK' |- *; rewrite gunit_sub_mk in Hw', HK' |- *; cbn [moddef_sub] in Hw', HK' |- *.
    apply (set_valid_unit_body _ _ _ _ _ (gmod_sub Φx (sb_qn (List.length Δu) σ))); [constructor | |].
    + exact Hw'.
    + exact Hxσ.
    + apply all_assumptions_sub; exact HΔu.
    + exists l; exact (set_params_evaluated_moved _ _ _ _ _ _ HsΔ HΔur).
    + exact HΓ.
    + rewrite (body_ctx_sub _ _ Hn), app_assoc, <- tele_sub_app.
      rewrite app_assoc in HC, HwCx. exact (set_ctx_moved T γ Hfn Hmods _ _ _ _ _ Hg HΓ HC HwCx).
    + exact (set_body_sorts_valid_moved _ _ _ _ _ _ Hsv HsΔ).
    + apply body_shape_sub; exact Hsh.
    + apply body_shape_sub; exact Hsx.
    + exact HK'.
    + intros k Ψw Hw0 Hk.
      rewrite (body_opens_sub _ _ _ _ _ Hx), List.nth_error_map in Hk.
      destruct (List.nth_error (body_opens Φ Φx) k) as [[Ψ H] |] eqn:Ek; [| discriminate].
      cbn in Hk; injection Hk as <- <-.
      destruct (body_opens_prefix _ _ _ _ _ Hx _ _ _ Ek) as [Ψr HΨr].
      rewrite HΨr, <- !app_assoc, (app_assoc Ψ Δu Δ) in HC, HwCx.
      pose proof (set_moves_of_ext _ _ _ _ _ _ Hg HΓ HC HwCx) as HsΨ.
      pose proof (Hopr _ _ _ Ek) as HO. rewrite app_assoc in HO.
      pose proof (set_modexp_rel_moved T γ Hfn Hmods _ _ _ _ _ _ _ HsΨ HO) as HR.
      rewrite (modexp_sub_sb_eq H _ _ (sb_qn_add _ _ _)), tele_sub_app, <- app_assoc, length_app in *. exact HR.
    + (* the modules, each in the body before it, then substituted *)
      intros y Φ0w Ew Uw Hp HEu.
      destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ0 & E & Hp0 & -> & HE); subst Ew.
      pose proof (gm_prefix_upto_nopens _ _ _ Hp0 Hn) as Hn0; cbn [gm_nopens] in Hn0.
      destruct (prefix_body_ctx _ _ _ Hn Hp0) as (X & HX).
      destruct E as [| pv0 U | | pv0 A0 M0 U |]; cbn in HEu; try discriminate; injection HEu as <-;
        cbn [body_ctx] in HX; rewrite HX, <- !app_assoc in HC, HwCx; cbn [List.app] in HC, HwCx;
        rewrite app_assoc in HC, HwCx;
        pose proof (set_moves_of_ext (X ++ _ :: nil) _ _ _ _ _ Hg HΓ ltac:(rewrite <- app_assoc; exact HC)
                      ltac:(rewrite <- app_assoc; exact HwCx)) as Hs0;
        pose proof (set_moves_nil_lift _ _ _ _ _ Hs0) as Hs1; rewrite <- app_assoc in Hs1;
        pose proof (set_sub_slots_coherent_of_moves _ _ _ _ _ Hs0 Hκ) as Hκ1; rewrite <- app_assoc in Hκ1;
        pose proof (IHsl _ _ _ _ Hp0 eq_refl _ _ _ Hs1 Hκ1) as HK0;
        rewrite (body_ctx_sub _ _ Hn0), app_assoc, <- tele_sub_app;
        cbn [modexp_sub] in HK0;
        rewrite (gunit_sub_sb_eq U _ _ (sb_qn_add _ _ _)), <- (length_body_ctx _ Hn0), <- length_app;
        exact HK0.
    + intros k Ψw Hw0 Hk.
      rewrite (body_opens_sub _ _ _ _ _ Hx), List.nth_error_map in Hk.
      destruct (List.nth_error (body_opens Φ Φx) k) as [[Ψ H] |] eqn:Ek; [| discriminate].
      cbn in Hk; injection Hk as <- <-.
      destruct (body_opens_prefix _ _ _ _ _ Hx _ _ _ Ek) as [Ψr HΨr].
      rewrite HΨr, <- !app_assoc, (app_assoc Ψ Δu Δ) in HC, HwCx.
      pose proof (set_moves_of_ext _ _ _ _ _ _ Hg HΓ HC HwCx) as HsΨ.
      pose proof (set_moves_nil_lift _ _ _ _ _ HsΨ) as HsΨ'. rewrite <- app_assoc in HsΨ'.
      pose proof (set_sub_slots_coherent_of_moves _ _ _ _ _ HsΨ Hκ) as HκΨ. rewrite <- app_assoc in HκΨ.
      pose proof (IHops _ _ _ Ek _ _ _ HsΨ' HκΨ) as HR.
      rewrite (modexp_sub_sb_eq H _ _ (sb_qn_add _ _ _)), tele_sub_app, <- app_assoc, length_app in *. exact HR.
  - (* an alias *)
    intros Δ Δu E [Hw HΔu [l HΔur] HΔ HΔΔ HK HE] HEv IHE Γ σ Fσ Hs Hκ.
    pose proof Hs as [Hg HΓ _ _ _]. pose proof (set_gsub_typed _ _ _ _ _ _ Hg) as Hσ.
    pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m unit_full] in Hf.
    destruct Hf as [_ _ _ HwΔ _ _ _ _ _ _ _].
    pose proof (set_moves_ext _ _ _ _ _ Hg HΓ HΔΔ HwΔ) as HsΔ.
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ Hw Hσ) as Hw'.
    pose proof (set_modexp_rel_moved T γ Hfn Hmods nil _ _ _ _ _ _ Hs HK) as HK'.
    cbn [modexp_sub] in Hw', HK' |- *; rewrite gunit_sub_mk in Hw', HK' |- *; cbn [moddef_sub] in Hw', HK' |- *.
    apply set_valid_unit_alias; [constructor |].
    + exact Hw'.
    + apply all_assumptions_sub; exact HΔu.
    + exists l; exact (set_params_evaluated_moved _ _ _ _ _ _ HsΔ HΔur).
    + exact HΓ.
    + exact (set_ctx_moved T γ Hfn Hmods _ _ _ _ _ Hg HΓ HΔΔ HwΔ).
    + exact HK'.
    + exact (set_modexp_rel_moved T γ Hfn Hmods _ _ _ _ _ _ _ HsΔ HE).
    + exact (IHE _ _ _ (set_moves_nil_lift _ _ _ _ _ HsΔ) (set_sub_slots_coherent_of_moves _ _ _ _ _ HsΔ Hκ)).
  - (* a module expression equal to a valid unit *)
    intros Δ H K R Rm RK [HwH HmH HmodH HHK HmK HmodK Hpf] HK IHK Γ σ Fσ Hs Hκ.
    pose proof Hs as [Hg _ _ _ _]. pose proof (set_gsub_typed _ _ _ _ _ _ Hg) as Hσ.
    pose proof (set_valid_unit_wf _ _ HK) as HwK.
    destruct (wf_modexp_eq_scoped _ _ _ _ _ HwH) as (HΔs & HHs & _).
    destruct (wf_modexp_eq_scoped _ _ _ _ _ HwK) as (_ & HKs & _).
    pose proof (wf_sub_mod_compat _ _ _ _ _ Hσ) as Hc.
    pose proof (wf_gstack_closed _ _ Hgw) as Hcl.
    apply (set_valid_modexp_intro _ _ _ _ (modexp_sub K σ) (mdesc_sub R σ) (mdesc_sub Rm σ) (mdesc_sub RK σ));
      [constructor | exact (IHK _ _ _ Hs Hκ)].
    + exact (sub_preserves_modexp _ _ _ _ _ _ _ HwH Hσ).
    + exact (mdenote_sub _ _ Hcl _ _ _ HmH HΔs HHs _ _ Hc).
    + apply mdesc_mod_sub; exact HmodH.
    + exact (set_modexp_rel_moved T γ Hfn Hmods nil _ _ _ _ _ _ Hs HHK).
    + exact (mdenote_sub _ _ Hcl _ _ _ HmK HΔs HKs _ _ Hc).
    + apply mdesc_mod_sub; exact HmodK.
    + intros κs Hcoh ys x.
      rewrite !(proj1 (unit_member_proofs_sub_all γ) _ κs σ (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s))))
        by (intros s ys' x'; reflexivity).
      exact (Hpf _ (Hκ _ Hcoh) ys x).
Qed.

(** ** Valid Units Past One More Entry, and Slots *)

Lemma set_valid_unit_shift : forall e Γ K, set_valid_unit T γ Γ K -> set_ctx T γ (e :: Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ e :: Γ ->
    set_valid_unit T γ (e :: Γ) (modexp_wk K wk_shift).
Proof.
  intros * HK HC Hc. rewrite <- modexp_sub_of_wk.
  apply (proj1 set_valid_unit_modexp_moved _ _ HK _ _ set_env_tail).
  - constructor; [exact (set_gsub_shift T γ _ _ Hc) | exact HC | exact (proj1 HC) | exact HC | exact (ctx_decomp_tail Hc)].
  - exact (set_sub_slots_coherent_shift γ _ _).
Qed.

(** The unit of a slot of a context with valid slots is valid there. *)
Lemma set_slot_valid_unit : forall Γ x U, Γ ∋ #x ≔ₘ U -> set_ctx T γ Γ -> set_valid_slots T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_valid_unit T γ Γ (me_lit U).
Proof.
  induction 1 as [U0 Γ0 | U0 A M Γ0 | n U1 Γ0 e Hl IH]; intros HC Hok Hc.
  - exact (set_valid_unit_shift _ _ (me_lit U0) (proj2 Hok U0 eq_refl) HC Hc).
  - exact (set_valid_unit_shift _ _ (me_lit U0) (proj2 Hok U0 eq_refl) HC Hc).
  - exact (set_valid_unit_shift _ _ (me_lit U1) (IH (proj1 HC) (proj1 Hok) (ctx_decomp_tail Hc)) HC Hc).
Qed.

End ValidUnit.
