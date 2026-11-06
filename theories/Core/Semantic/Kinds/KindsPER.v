(** * Related Module Values Have the Same Kinds

    Related module values have the same kinds ([per_dmod_kinds_equiv]): two unit
    closures are related through related arguments, and every parameter's
    type has some ([per_univ_elem_inhabited]); a module
    expression has the kinds of its value ([kind_eval]).  So the
    environments a context PER relates match the context
    ([per_ctx_env_kinds_match]). *)

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

  (** Every type relates some elements: the reflection of a variable, or
      at [LevelSort], which has no variables, [Level@0]. *)
  Lemma per_univ_elem_inhabited : forall i R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R -> exists c c', R c c'.
  Proof.
    intros * H.
    assert (Hd : a = LevelSortᵈ \/ not_level_sort a) by (destruct a; first [ left; reflexivity | right; discriminate ]).
    destruct Hd as [-> | Hn]; [| exists (⇑! a 0), (⇑! a' 0); exact (var_per_elem 0 H Hn) ].
    basic_invert_per_univ_elem H.
    exists Levelᵈ@0, Levelᵈ@0; apply H.
    split; [ exists (per_lvl_at 0), Levelᵈ@0; left; constructor; reflexivity |].
    split; [ exists (per_lvl_at 0), Levelᵈ@0; left; constructor; reflexivity |].
    exists (per_lvl_at 0); simp per_univ_elem; apply per_univ_elem_core_level; reflexivity.
  Qed.

  (** The environment a body makes, as kinds read it, has the kinds of the
      environment it evaluates to. *)
  Lemma body_kinds_env : forall ρ Φ ρ1, ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 ->
      exists σ, kinds_env gc_deps gc_stack ρ Φ σ /\ kinds_shape gc_deps gc_stack ρ1 σ.
  Proof. intros * He; exact (kind_eval_body_env _ _ _ _ _ He ρ (kinds_shape_refl _ _ ρ)). Qed.

  (** Related bodies are expanded: they have no open. *)
  Lemma per_body_noopen : forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> gm_noopen Φ /\ gm_noopen Φ'.
  Proof. induction 1; cbn; tauto. Qed.

  Lemma per_dmod_kinds_equiv_all :
    (forall h h', per_dmod h h' -> kinds_equiv gc_deps gc_stack h h') /\
    (forall ts ρ ρ' args args', per_tele_args ts ρ ρ' args args' -> True) /\
    (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' ->
       forall sm sm' y ch k, gunit_member_kind gc_deps gc_stack ρ (gu_mk nil (md_body sm Φ)) (y :: ch) k <->
                          gunit_member_kind gc_deps gc_stack ρ' (gu_mk nil (md_body sm' Φ')) (y :: ch) k).
  Proof.
    apply per_dmod_mut_ind_all; intros; try exact I.
    - (* global *)
      intros ch0 k0; split; apply dmod_member_kind_global_args.
    - (* bodies *)
      destruct (per_body_noopen _ _ _ _ p) as [Hn Hn'].
      intros [| y ch] kk; rewrite !dmod_member_kind_local_iff; cbn [gunit_expand];
        rewrite (gm_expand_noopen _ Hn), (gm_expand_noopen _ Hn'); [ split; intros Hu; inversion Hu; subst; apply gunit_member_kind_self | apply H ].
    - (* a missing parameter: at some related arguments *)
      match goal with Hu : per_univ_elem _ _ _ _ |- _ => destruct (per_univ_elem_inhabited _ _ _ _ Hu) as (c0 & c0' & Hv) end.
      match goal with E1 : forall c c', _ -> exists hc, $ᵐ| h & c | _ ⍮ _ ↘ hc,
                      E2 : forall c c', _ -> exists hc', $ᵐ| h' & c' | _ ⍮ _ ↘ hc' |- _ =>
        destruct (E1 _ _ Hv) as (hc & Hc); destruct (E2 _ _ Hv) as (hc' & Hc') end.
      intros ch k; rewrite <- (kind_eval_appm _ _ _ _ _ Hc), <- (kind_eval_appm _ _ _ _ _ Hc').
      eapply H; eassumption.
    - (* empty bodies *)
      split; intros Hu; inversion Hu; subst; cbn in *; discriminate.
    - (* a definition each *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne), (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        match goal with Hp : Some _ = Some _ |- _ => injection Hp; intros; subst end;
        eapply gunit_member_kind_def; cbn [gm_prefix_upto]; rewrite Ex; reflexivity.
    - (* a submodule each: their closures have the same kinds *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne), (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      destruct (body_kinds_env _ _ _ e) as (σ & Hk & Hs).
      destruct (body_kinds_env _ _ _ e0) as (σ' & Hk' & Hs').
      assert (HUy : forall ch k, gunit_member_kind gc_deps gc_stack σ (gunit_expand (gu_mk Δy Dy)) ch k <->
                                     gunit_member_kind gc_deps gc_stack σ' (gunit_expand (gu_mk Δy' Dy')) ch k).
      { intros chx kx; rewrite <- (gunit_member_kind_id _ _ _ _ (proj1 Hs)), <- (gunit_member_kind_id _ _ _ _ (proj1 Hs')),
          <- (kind_eval_close _ _ _ _ _ _ e1), <- (kind_eval_close _ _ _ _ _ _ e2); apply H0. }
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        match goal with Hp : Some _ = Some _ |- _ => inversion Hp; subst end.
      all: match goal with Hk1 : kinds_env _ _ _ _ ?r, Hu1 : gunit_member_kind _ _ ?r _ _ _ |- _ =>
             first [ rewrite <- (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack))) _ _ _ Hk _ Hk1) in Hu1
                   | rewrite <- (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack))) _ _ _ Hk' _ Hk1) in Hu1 ] end.
      + eapply gunit_member_kind_mod; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk' | apply HUy; assumption ].
      + eapply gunit_member_kind_mod; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk | apply HUy; assumption ].
    - (* a definition with a module part each: their closures have the same
         kinds, at the empty chain as at a longer one *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne), (gunit_member_kind_body_ext_other _ _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      destruct (body_kinds_env _ _ _ e) as (σ & Hk & Hs).
      destruct (body_kinds_env _ _ _ e0) as (σ' & Hk' & Hs').
      assert (HUy : forall ch k, gunit_member_kind gc_deps gc_stack σ (gunit_expand (gu_mk Δy Dy)) ch k <->
                                     gunit_member_kind gc_deps gc_stack σ' (gunit_expand (gu_mk Δy' Dy')) ch k).
      { intros chx kx; rewrite <- (gunit_member_kind_id _ _ _ _ (proj1 Hs)), <- (gunit_member_kind_id _ _ _ _ (proj1 Hs')),
          <- (kind_eval_close _ _ _ _ _ _ e1), <- (kind_eval_close _ _ _ _ _ _ e2); apply H0. }
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        match goal with Hp : Some _ = Some _ |- _ => inversion Hp; subst end.
      all: match goal with Hk1 : kinds_env _ _ _ _ ?r, Hu1 : gunit_member_kind _ _ ?r _ _ _ |- _ =>
             first [ rewrite <- (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack))) _ _ _ Hk _ Hk1) in Hu1
                   | rewrite <- (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack))) _ _ _ Hk' _ Hk1) in Hu1 ] end.
      + eapply gunit_member_kind_dm_here; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk' | apply HUy; assumption ].
      + eapply gunit_member_kind_dm_step; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | assumption | exact Hk' | apply HUy; assumption ].
      + eapply gunit_member_kind_dm_here; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk | apply HUy; assumption ].
      + eapply gunit_member_kind_dm_step; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | assumption | exact Hk | apply HUy; assumption ].
  Qed.

  Corollary per_dmod_kinds_equiv : forall h h', per_dmod h h' -> kinds_equiv gc_deps gc_stack h h'.
  Proof. exact (proj1 per_dmod_kinds_equiv_all). Qed.

  Lemma per_ctx_env_kinds_match : forall Γ Γ' R, EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
      forall ρ ρ', R ρ ρ' -> kinds_match gc_deps gc_stack Γ ρ /\ kinds_match gc_deps gc_stack Γ' ρ'.
  Proof.
    induction 1; intros ρ ρ' Hρ.
    - split; apply kinds_match_nil.
    - apply H2 in Hρ as [Ht _].
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kinds_match_drop_term; first [ assumption | discriminate ].
    - apply H3 in Hρ as [Ht _].
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kinds_match_drop_term; first [ assumption | discriminate ].
    - apply H3 in Hρ as [Ht P1 P2 P3 P4 _ _].
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kinds_match_drop_mod; try assumption.
      + destruct P1 as (h & Hh & Hr).
        eapply kinds_equiv_trans; [ apply per_dmod_kinds_equiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), modexp_member_kind_lit_iff, dmod_member_kind_clo_iff; reflexivity.
      + destruct P4 as (h & Hh & Hr).
        eapply kinds_equiv_trans; [ apply per_dmod_kinds_equiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), modexp_member_kind_lit_iff, dmod_member_kind_clo_iff; reflexivity.
    - (* a definition with a module part: its unit as a slot's *)
      apply H4 in Hρ as [Ht _ _ P1 _ _ P4].
      destruct (IHper_ctx_env _ _ Ht) as (K1 & K2).
      split; apply kinds_match_drop_dm; try assumption.
      + destruct P1 as (h & Hh & Hr).
        eapply kinds_equiv_trans; [ apply per_dmod_kinds_equiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), modexp_member_kind_lit_iff, dmod_member_kind_clo_iff; reflexivity.
      + destruct P4 as (h & Hh & Hr).
        eapply kinds_equiv_trans; [ apply per_dmod_kinds_equiv, Hr |].
        intros ch k; rewrite (kind_eval_modexp _ _ _ _ _ Hh), modexp_member_kind_lit_iff, dmod_member_kind_clo_iff; reflexivity.
  Qed.

End Fixed_GCtx.
