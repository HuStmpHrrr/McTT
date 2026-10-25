(** * Related Module Values Have the Same Kinds

    Related module values have the same kinds ([per_dmod_kequiv]): two unit
    closures are related through related arguments, and every parameter's
    type has some, the reflection of a variable ([var_per_elem]); a module
    expression has the kinds of its value ([kind_eval]).  So the
    environments a context PER relates match the context
    ([per_ctx_env_kmatch]). *)

From Stdlib Require Import Lia List String.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Semantic Require Import PER Realizability.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval.
Import Domain_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hg : ⊢ᵍ gc_deps ⍮ gc_stack.

  (** The environment a body makes, as kinds read it, has the kinds of the
      environment its expansion evaluates to. *)
  Lemma body_kenv : forall ρ Φ Φx, kbody gc_deps gc_stack ρ Φ Φx -> forall ρ1, ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 ->
      exists σ, kenv gc_deps gc_stack ρ Φ σ /\ kshape gc_deps gc_stack ρ1 σ.
  Proof.
    intros * Hb * He.
    destruct (kind_eval_benv _ _ _ _ _ He ρ (kshape_refl _ _ ρ)) as (σ & Hk & Hs).
    destruct (kenv_of_kbody _ _ _ _ _ Hb) as (σw & Hkw).
    pose proof (kenv_eq_kbody _ _ _ _ _ _ _ Hb Hkw Hk) as ->.
    exists σ; split; assumption.
  Qed.

  Lemma per_dmod_kequiv_all :
    (forall h h', per_dmod h h' -> kequiv gc_deps gc_stack h h') /\
    (forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' -> True) /\
    (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' ->
       forall sm sm' y ch k, ukind gc_deps gc_stack ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k <->
                          ukind gc_deps gc_stack ρ' (gu_mk nil (md_body sm' Φ')) (y :: ch) k).
  Proof.
    apply per_dmod_mut_ind_all; intros; try exact I.
    - (* global *)
      intros ch0 k0; split; apply dkind_global_args.
    - (* bodies *)
      intros [| y ch] kk; rewrite !dkind_local_iff; [ split; intros Hu; inversion Hu; subst; apply uk_self | apply H ].
    - (* a missing parameter: at the reflection of a variable *)
      match goal with Hu : per_univ_elem _ _ _ _ |- _ => pose proof (var_per_elem 0 Hu) as Hv end.
      match goal with E1 : forall c c', _ -> exists hc, $ᵐ| h & c | _ ⍮ _ ↘ hc,
                      E2 : forall c c', _ -> exists hc', $ᵐ| h' & c' | _ ⍮ _ ↘ hc' |- _ =>
        destruct (E1 _ _ Hv) as (hc & Hc); destruct (E2 _ _ Hv) as (hc' & Hc') end.
      intros ch k; rewrite <- (kind_eval_appm _ _ _ _ _ Hc), <- (kind_eval_appm _ _ _ _ _ Hc').
      eapply H; eassumption.
    - (* empty bodies *)
      split; intros Hu; inversion Hu; subst; cbn in *; discriminate.
    - (* a definition each *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (ukind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne), (ukind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        eapply uk_def; cbn [gm_prefix_upto]; rewrite Ex; reflexivity.
    - (* a submodule each: their closures have the same kinds *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (ukind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne), (ukind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      destruct (body_kenv _ _ _ k _ e) as (σ & Hk & Hs).
      destruct (body_kenv _ _ _ k0 _ e0) as (σ' & Hk' & Hs').
      assert (HUy : forall ch k, ukind gc_deps gc_stack σ (gu_mk Δy Dy) ch k <-> ukind gc_deps gc_stack σ' (gu_mk Δy' Dy') ch k).
      { intros chx kx; rewrite <- (ukind_id _ _ _ _ (proj1 Hs)), <- (ukind_id _ _ _ _ (proj1 Hs')),
          <- (kind_eval_close _ _ _ _ _ _ e1), <- (kind_eval_close _ _ _ _ _ _ e2); apply H0. }
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        match goal with Hp : Some _ = Some _ |- _ => inversion Hp; subst end.
      all: match goal with Hk1 : kenv _ _ _ _ ?r, Hu1 : ukind _ _ ?r _ _ _ |- _ =>
             first [ rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk _ Hk1) in Hu1
                   | rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk' _ Hk1) in Hu1 ] end.
      + eapply uk_mod; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk' | apply HUy; assumption ].
      + eapply uk_mod; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk | apply HUy; assumption ].
    - (* a definition with a module part each: their closures have the same
         kinds, at the empty chain as at a longer one *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (ukind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne), (ukind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      destruct (body_kenv _ _ _ k _ e) as (σ & Hk & Hs).
      destruct (body_kenv _ _ _ k0 _ e0) as (σ' & Hk' & Hs').
      assert (HUy : forall ch k, ukind gc_deps gc_stack σ (gu_mk Δy Dy) ch k <-> ukind gc_deps gc_stack σ' (gu_mk Δy' Dy') ch k).
      { intros chx kx; rewrite <- (ukind_id _ _ _ _ (proj1 Hs)), <- (ukind_id _ _ _ _ (proj1 Hs')),
          <- (kind_eval_close _ _ _ _ _ _ e1), <- (kind_eval_close _ _ _ _ _ _ e2); apply H0. }
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        match goal with Hp : Some _ = Some _ |- _ => inversion Hp; subst end.
      all: match goal with Hk1 : kenv _ _ _ _ ?r, Hu1 : ukind _ _ ?r _ _ _ |- _ =>
             first [ rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk _ Hk1) in Hu1
                   | rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk' _ Hk1) in Hu1 ] end.
      + eapply uk_dm_here; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk' | apply HUy; assumption ].
      + eapply uk_dm_step; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | assumption | exact Hk' | apply HUy; assumption ].
      + eapply uk_dm_here; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk | apply HUy; assumption ].
      + eapply uk_dm_step; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | assumption | exact Hk | apply HUy; assumption ].
    - (* an open each: their targets have the same kinds *)
      destruct (items_upto y its) as [[its1 it] |] eqn:Ey;
        [| rewrite (ukind_body_open_other _ _ _ _ _ _ _ _ _ _ Ey), (ukind_body_open_other _ _ _ _ _ _ _ _ _ _ Ey); apply H0 ].
      destruct (body_kenv _ _ _ k _ e) as (σ & Hk & Hs).
      destruct (body_kenv _ _ _ k0 _ e0) as (σ' & Hk' & Hs').
      assert (HH : forall ch k, skind gc_deps gc_stack σ H ch k <-> skind gc_deps gc_stack σ' H' ch k).
      { intros chx kx; rewrite <- (skind_id _ _ _ _ (proj1 Hs)), <- (skind_id _ _ _ _ (proj1 Hs')),
          <- (kind_eval_modexp _ _ _ _ _ e1), <- (kind_eval_modexp _ _ _ _ _ e2); apply H1. }
      assert (Hi : gm_item_upto (gm_open Φ H its) y = Some (Φ, H, its1, it)) by (cbn; rewrite Ey; reflexivity).
      assert (Hi' : gm_item_upto (gm_open Φ' H' its) y = Some (Φ', H', its1, it)) by (cbn; rewrite Ey; reflexivity).
      rewrite (ukind_body_item _ _ _ _ _ _ _ _ _ _ _ _ _ Hi Hk), (ukind_body_item _ _ _ _ _ _ _ _ _ _ _ _ _ Hi' Hk').
      destruct it as [[[n |] d] pv]; rewrite ?HH; reflexivity.
  Qed.

  Corollary per_dmod_kequiv : forall h h', per_dmod h h' -> kequiv gc_deps gc_stack h h'.
  Proof. exact (proj1 per_dmod_kequiv_all). Qed.

  Lemma per_ctx_env_kmatch : forall Γ Γ' R, EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
      forall ρ ρ', R ρ ρ' -> kmatch gc_deps gc_stack Γ ρ /\ kmatch gc_deps gc_stack Γ' ρ'.
  Proof.
    induction 1; intros ρ ρ' Hρ.
    - split; apply kmatch_nil.
    - apply H1 in Hρ as [Ht _].
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kmatch_drop_term; first [ assumption | discriminate ].
    - apply H2 in Hρ as [Ht _].
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kmatch_drop_term; first [ assumption | discriminate ].
    - apply H1 in Hρ as (Ht & P1 & P2 & P3 & P4).
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kmatch_drop_mod; try assumption.
      + destruct P1 as (h & Hh & Hr).
        eapply kequiv_trans; [ apply per_dmod_kequiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), skind_lit_iff, dkind_clo_iff; reflexivity.
      + destruct P4 as (h & Hh & Hr).
        eapply kequiv_trans; [ apply per_dmod_kequiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), skind_lit_iff, dkind_clo_iff; reflexivity.
    - (* a definition with a module part: its unit as a slot's *)
      apply H3 in Hρ as [Ht _ _ _ _ _ P1 _ _ P4].
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kmatch_drop_dm; try assumption.
      + destruct P1 as (h & Hh & Hr).
        eapply kequiv_trans; [ apply per_dmod_kequiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), skind_lit_iff, dkind_clo_iff; reflexivity.
      + destruct P4 as (h & Hh & Hr).
        eapply kequiv_trans; [ apply per_dmod_kequiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), skind_lit_iff, dkind_clo_iff; reflexivity.
  Qed.

End Fixed_GCtx.
