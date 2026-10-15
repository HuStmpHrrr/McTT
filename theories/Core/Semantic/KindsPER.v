(** * Related Module Values Have the Same Kinds

    Related module values have the same kinds ([per_dmod_kequiv]): two unit
    closures are related through related arguments, and every parameter's
    type has some, the reflection of a variable ([var_per_elem]); a module
    expression has the kinds of its value ([kind_eval]).  So the
    environments a context PER relates match the context
    ([per_ctx_env_kmatch]). *)

From Stdlib Require Import List String.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Semantic Require Import PER Realizability Kinds KindsTyping KindsEval.
Import Domain_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hg : ⊢g gc_deps ⍮ gc_stack.

  Lemma kshape_refl : forall ρ, kshape gc_deps gc_stack ρ ρ.
  Proof. intros ρ; split; [ intros x; apply kequiv_refl | reflexivity ]. Qed.

  (** One more placeholder, against an argument. *)
  Lemma kshape_pad_S : forall n ρ a,
      kshape gc_deps gc_stack (kpad n (de_term a :: ρ)) (kpad (S n) ρ).
  Proof.
    intros; unfold kpad.
    replace (repeat (de_term d_true) (S n) ++ ρ) with (repeat (de_term d_true) n ++ de_term d_true :: ρ)
      by (clear; induction n as [| n IH]; cbn in *; [ reflexivity | rewrite IH; reflexivity ]).
    apply kshape_terms; [ reflexivity | | |].
    - apply Forall_forall; intros e He; apply repeat_spec in He as ->; reflexivity.
    - apply Forall_forall; intros e He; apply repeat_spec in He as ->; reflexivity.
    - apply kshape_cons_term, kshape_refl.
  Qed.

  Lemma per_dmod_kequiv_all :
    (forall h h', per_dmod h h' -> kequiv gc_deps gc_stack h h') /\
    (forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' -> True) /\
    (forall ts ρ D ts' ρ' D' args args', per_ltele ts ρ D ts' ρ' D' args args' ->
       forall ch k, ukind gc_deps gc_stack (kpad (List.length ts) ρ) (gu_mk nil D) ch k <->
                    ukind gc_deps gc_stack (kpad (List.length ts') ρ') (gu_mk nil D') ch k) /\
    (forall ρ D ρ' D', per_mdef ρ D ρ' D' ->
       forall ch k, ukind gc_deps gc_stack ρ (gu_mk nil D) ch k <-> ukind gc_deps gc_stack ρ' (gu_mk nil D') ch k) /\
    (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' ->
       forall y ch k, ukind gc_deps gc_stack ρ (gu_mk nil (md_body Φ)) (y :: ch) k <->
                      ukind gc_deps gc_stack ρ' (gu_mk nil (md_body Φ')) (y :: ch) k).
  Proof.
    apply per_dmod_mut_ind_all; intros; try exact I.
    - (* global *)
      intros ch0 k0; split; apply dkind_global_args.
    - (* local *)
      intros ch0 k0; rewrite !dkind_local_iff; destruct U as [Δ D], U' as [Δ' D'];
        rewrite (ukind_pad _ _ ρ Δ), (ukind_pad _ _ ρ' Δ'); cbn [gu_params gu_def] in *.
      rewrite <- (List.length_rev Δ), <- (List.length_rev Δ'); auto.
    - (* member *)
      intros ch0 k0; split; intros Hk; inversion Hk; subst; constructor; apply H; assumption.
    - (* a supplied parameter *)
      cbn [List.length]; rewrite <- (ukind_id _ _ _ _ (proj1 (kshape_pad_S (List.length ts) ρ a))),
        <- (ukind_id _ _ _ _ (proj1 (kshape_pad_S (List.length ts') ρ' a'))); apply H.
    - (* a missing parameter: at the reflection of a variable *)
      destruct r as [a a' Ha Ha' HR].
      cbn [List.length]; rewrite <- (ukind_id _ _ _ _ (proj1 (kshape_pad_S (List.length ts) ρ (⇑! a 0)))),
        <- (ukind_id _ _ _ _ (proj1 (kshape_pad_S (List.length ts') ρ' (⇑! a' 0)))).
      apply (H _ _ (var_per_elem 0 HR)).
    - (* all crossed *)
      apply H.
    - (* bodies *)
      destruct ch as [| y ch]; [ split; intros Hu; inversion Hu; subst; constructor | apply H ].
    - (* aliases *)
      rewrite (ukind_pad _ _ ρ nil), (ukind_pad _ _ ρ' nil), !ukind_alias_iff; cbn [List.length kpad repeat app].
      rewrite <- (kind_eval_modexp _ _ Hg _ _ _ e), <- (kind_eval_modexp _ _ Hg _ _ _ e0).
      apply H.
    - (* empty bodies *)
      split; intros Hu; inversion Hu; subst; cbn in *; discriminate.
    - (* a definition each *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (ukind_body_ext_other _ _ _ _ _ _ _ _ _ Hne), (ukind_body_ext_other _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        eapply uk_def; cbn [gm_prefix_upto]; rewrite Ex; reflexivity.
    - (* a submodule each: their closures have the same kinds *)
      destruct (String.eqb_spec y0 y) as [-> | Hne];
        [| rewrite (ukind_body_ext_other _ _ _ _ _ _ _ _ _ Hne), (ukind_body_ext_other _ _ _ _ _ _ _ _ _ Hne); apply H ].
      assert (Ex : String.eqb y y = true) by apply String.eqb_refl.
      destruct (kind_eval_benv _ _ Hg _ _ _ e ρ (kshape_refl ρ)) as (σ & Hk & Hs).
      destruct (kind_eval_benv _ _ Hg _ _ _ e0 ρ' (kshape_refl ρ')) as (σ' & Hk' & Hs').
      assert (HUy : forall ch k, ukind gc_deps gc_stack σ Uy ch k <-> ukind gc_deps gc_stack σ' Uy' ch k).
      { intros ch0 k0; rewrite <- (ukind_id _ _ _ _ (proj1 Hs)), <- (ukind_id _ _ _ _ (proj1 Hs')), <- !dkind_local_iff; apply H0. }
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ex in *; try discriminate;
        match goal with Hp : Some _ = Some _ |- _ => inversion Hp; subst end.
      all: match goal with Hk1 : kenv _ _ _ _ ?r, Hu1 : ukind _ _ ?r _ _ _ |- _ =>
             first [ rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk _ Hk1) in Hu1
                   | rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk' _ Hk1) in Hu1 ] end.
      + eapply uk_mod; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk' | apply HUy; assumption ].
      + eapply uk_mod; [ cbn [gm_prefix_upto]; rewrite Ex; reflexivity | exact Hk | apply HUy; assumption ].
    - (* an open each: their targets have the same kinds *)
      destruct (items_upto y its) as [[its1 it] |] eqn:Ey;
        [| rewrite (ukind_body_open_other _ _ _ _ _ _ _ _ _ Ey), (ukind_body_open_other _ _ _ _ _ _ _ _ _ Ey); apply H0 ].
      assert (Hex : existsb (String.eqb y) (map iitem_name its) = true) by (eapply items_upto_some; exact Ey).
      destruct (kind_eval_benv _ _ Hg _ _ _ e ρ (kshape_refl ρ)) as (σ & Hk & Hs).
      destruct (kind_eval_benv _ _ Hg _ _ _ e0 ρ' (kshape_refl ρ')) as (σ' & Hk' & Hs').
      assert (HH : forall ch k, skind gc_deps gc_stack σ H ch k <-> skind gc_deps gc_stack σ' H' ch k).
      { intros ch0 k0; rewrite <- (skind_id _ _ _ _ (proj1 Hs)), <- (skind_id _ _ _ _ (proj1 Hs')),
          <- (kind_eval_modexp _ _ Hg _ _ _ e1), <- (kind_eval_modexp _ _ Hg _ _ _ e2); apply H1. }
      split; intros Hu; inversion Hu; subst; cbn [gm_prefix_upto gm_item_upto] in *; rewrite ?Ey, ?Hex in *; try discriminate;
        match goal with Hp : Some _ = Some _ |- _ => inversion Hp; subst end.
      all: match goal with Hk1 : kenv _ _ _ _ ?r, Hu1 : skind _ _ ?r _ _ _ |- _ =>
             first [ rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk _ Hk1) in Hu1
                   | rewrite <- (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hk' _ Hk1) in Hu1 ] end.
      + eapply uk_item; [ cbn [gm_item_upto]; rewrite Ey; reflexivity | exact Hk' | apply HH; assumption ].
      + eapply uk_item; [ cbn [gm_item_upto]; rewrite Ey; reflexivity | exact Hk | apply HH; assumption ].
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
      split; [ apply kmatch_drop_mod; [ exact K1 | apply per_dmod_kequiv, P1 ]
             | apply kmatch_drop_mod; [ exact K2 | apply per_dmod_kequiv, P4 ] ].
  Qed.

End Fixed_GCtx.
