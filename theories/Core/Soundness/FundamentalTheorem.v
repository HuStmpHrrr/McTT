(** * The Fundamental Theorem of the Gluing Model

    Every judgment of a global context holds in the gluing model, along
    every sound embedding ([soundness_fundamental]): a context glues, a term
    glues at its type, a universe is one, and every other judgment glues its
    context.  By induction on the derivation, each rule is its gluing rule,
    stated and proved in the file of its construct; the case of each rule
    only applies its gluing rule.

    The theorem then gives the rest.  Each entry of a global context is
    valid where it is checked, so a well-formed global context embeds
    soundly into itself ([glu_emb_refl]), from what [Global/Embedding.v] makes of
    valid entries.  At that embedding the gluing judgments are the gluing
    relations at the global context, as the corollaries below state them for
    contexts and terms.  There is no part for substitutions, since the
    gluing model has no substitution judgment, and none for equalities,
    since the model relates a term to a value rather than two terms to each
    other. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Modules Require Import Values.
From Mctt.Core.Completeness.Global Require Import Embedding.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import ContextCases VariableCases UnitCases
  SubtypingCases UniverseCases FunctionCases LetCases TrueFalseCases.
From Mctt.Core.Soundness.Inductives Require Import Con.
From Mctt.Core.Soundness Require Import IndCases ModuleCases.
From Mctt.Core.Soundness.Global Require Import Embedding.
From Mctt.Core.Completeness.Inductives Require Con.
Require Import Mctt.Core.Soundness.Inductives.Elim.
Require Import Mctt.Core.Soundness.ElimCases.
Require Import Mctt.Core.Soundness.IotaCases.
From Mctt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Theorem soundness_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊩ M : A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> ⊩ Θ ⍮ Ξ ⍮ Γ).
Proof.
  (** A rule whose conclusion only glues the context leaves its other
      variables to its premises; where two premises have the same shape,
      the variables are named. *)
  apply syntactic_wf_mut_ind; intros;
    [ (** contexts *)
      eapply glu_ctx_empty | eapply glu_ctx_extend | eapply glu_ctx_extend_def | eapply glu_ctx_extend_mod
    | (** terms *)
      eapply glu_typ | eapply glu_univ | eapply glu_level | eapply glu_llit | eapply glu_succl | eapply glu_maxl
    | eapply glu_True | eapply glu_true | eapply glu_False | eapply glu_exfalso | eapply glu_ind | eapply glu_con
    | eapply glu_elim | eapply glu_pi | eapply glu_fn | eapply glu_app | eapply glu_let | eapply glu_let_mod
    | eapply glu_mem | eapply glu_vlookup | eapply glu_exp_subtyp
    | (** term equality *)
      eapply glu_exp_eq_typ_cong | eapply glu_exp_eq_univ_cong | eapply glu_exp_eq_level_cong
    | eapply glu_exp_eq_llit_cong | eapply glu_exp_eq_succl_cong | eapply glu_exp_eq_maxl_cong
    | eapply glu_exp_eq_llit_succl | eapply glu_exp_eq_maxl_absorb | eapply glu_exp_eq_maxl_zero
    | eapply glu_exp_eq_maxl_assoc | eapply glu_exp_eq_maxl_comm | eapply glu_exp_eq_maxl_idem
    | eapply glu_exp_eq_succl_maxl | eapply glu_exp_eq_maxl_succl
    | eapply glu_exp_eq_True_cong | eapply glu_exp_eq_true_cong | eapply glu_exp_eq_False_cong
    | eapply glu_exp_eq_exfalso_cong | eapply glu_exp_eq_ind_cong | eapply glu_exp_eq_con_cong
    | eapply glu_exp_eq_elim_cong | eapply glu_exp_eq_pi_cong | eapply glu_exp_eq_fn_cong
    | eapply glu_exp_eq_app_cong | eapply glu_exp_eq_let_cong | eapply glu_exp_eq_let_mod_cong
    | eapply glu_exp_eq_mem_cong with (R := R) (A := A) | eapply glu_exp_eq_var | eapply glu_exp_eq_pi_beta
    | eapply glu_exp_eq_elim_iota | eapply glu_exp_eq_elim_view | eapply glu_exp_eq_con_view
    | eapply glu_exp_eq_let_zeta | eapply glu_exp_eq_let_mod_zeta
    | eapply glu_exp_eq_mem_delta | eapply glu_exp_eq_var_delta | eapply glu_exp_eq_fn_eta
    | eapply glu_exp_eq_true_eta | eapply glu_exp_eq_subtyp | eapply glu_exp_eq_sym | eapply glu_exp_eq_trans
    | (** subtyping *)
      eapply glu_subtyp_refl | eapply glu_subtyp_trans | eapply glu_subtyp_univ | eapply glu_subtyp_suniv
    | eapply glu_subtyp_level | eapply glu_subtyp_small_large | eapply glu_subtyp_pi
    | (** universes *)
      eapply glu_is_univ_large | eapply glu_is_univ_small
    | (** extensions *)
      eapply glu_ext_eq_nil | eapply glu_ext_eq_ass with (Ψ := Ψ) (Ψ' := Ψ')
    | eapply glu_ext_eq_def with (Ψ := Ψ) (Ψ' := Ψ') | eapply glu_ext_eq_mod
    | (** units *)
      eapply glu_unit_eq_body with (Δ := Δ) (Δ' := Δ') (Φ := Φ) (Φ' := Φ') (Φx := Φx) (Φx' := Φx')
    | eapply glu_unit_eq_alias | eapply glu_unit_eq_flatten
    | eapply glu_unit_eq_sym | eapply glu_unit_eq_trans
    | (** module expressions *)
      eapply glu_me_unit | eapply glu_me_var | eapply glu_me_lit | eapply glu_me_mem | eapply glu_me_app
    | eapply glu_me_delta_slot | eapply glu_me_delta_sel | eapply glu_me_beta_body | eapply glu_me_beta_alias
    | eapply glu_me_beta_alias0 | eapply glu_me_sym | eapply glu_me_trans ];
    eassumption.
Qed.

(** A closed typed term, glued along a sound embedding. *)
Lemma glu_rel_exp_of_emb : forall Θ1 Ξ1 Θ2 Ξ2 A M,
    glu_emb Θ1 Ξ1 Θ2 Ξ2 ->
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ M A.
Proof. intros * Hμ HM; exact (proj1 (proj2 soundness_fundamental) _ _ _ _ _ HM _ _ Hμ). Qed.

(** ** Each entry is valid where it is checked *)

Lemma glu_entry_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> GoodV glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ Θ2 Ξ2 Θ -> gs_valid glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ Θ2 Ξ2 Ξ ->
    forall Θs Ξs, glu_entry Θs Ξs Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM _ He HΘ HΞ Θs Ξs.
  pose proof (glu_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) He HΘ HΞ) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  exists j; exact (glu_rel_exp_of_emb _ _ _ _ _ _ Hμ HT).
Qed.

Lemma glu_entry_ax : forall Θ Ξ A i b pv Θ2 Ξ2 Θs Ξs,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_entry Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He _.
  pose proof (glu_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HA)) HG He) as Hμ.
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  exists j; exact (glu_rel_exp_of_emb _ _ _ _ _ _ Hμ HT).
Qed.

Lemma glu_entry_alias : forall Θ Ξ pv Δ E Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_entry Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof. intros; exact I. Qed.

Lemma glu_entry_indalias : forall Θ Ξ pv Δ pm p k Ns D Mk Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk ->
    k < ind_ndecl D -> ind_mpath D k = Some pm -> ind_mlookup Θ Ξ pm = Some (p, k, D) ->
    List.length Ns <= ind_nu D ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps (a_ind p k) Ns : ind_ty_at D Mk Ns ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod pm) Ns ≈ me_apps (qname_mod pm) Ns ->
    GoodV glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_entry Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_ind_alias pv (Δ ++ gs_tele Ξ) pm p k Ns).
Proof. intros; exact I. Qed.

Lemma glu_mod_tele_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_mod_tele Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof. intros; exact I. Qed.

(** A declaration typed at the source glues at the target: its judgments,
    glued. *)
Lemma glu_entry_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> GoodV glu_entry glu_mod_tele glu_ind_decl_entry Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_ind_decl_entry Θ2 Ξ2 D /\ glu_mod_tele Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * Hdt HG He; split; [| exact I ]; unfold glu_ind_decl_entry.
  destruct (decl_typed_uparams _ _ _ Hdt) as [HUw _].
  pose proof (ctx_wf_gctx _ _ _ HUw) as Hg.
  pose proof (glu_emb_good _ _ _ _ Hg HG He) as Hμ.
  pose proof (em_res _ _ _ _ (Embx_emb _ _ _ _ He)) as Hs.
  destruct soundness_fundamental as (Kc & Ke & _).
  destruct (dt_sort_lvl _ _ _ Hdt) as [n Hn].
  constructor.
  - intros * HMk; exact (Kc _ _ _ (member_params_wf _ _ _ _ _ Hdt HMk) _ _ Hμ).
  - exists n; exact (Ke _ _ _ _ _ Hn _ _ Hμ).
  - intros * HMk; exists n.
    assert (Hn' : Θ ⍮ Ξ ⍮ im_params D Mk ⊢ (ind_sort_lvl (ind_sort D))[wk_shiftn (im_nn Mk)]ʷ : Level@n).
    { pose proof (member_params_wf _ _ _ _ _ Hdt HMk) as HΔ; unfold im_params in HΔ |- *.
      pose proof (wf_wk_shiftn_app' _ _ _ _ HΔ) as Hw.
      rewrite length_im_nparams in Hw.
      exact (wk_preserves_exp _ _ _ _ _ _ _ Hn Hw). }
    exact (Ke _ _ _ _ _ Hn' _ _ Hμ).
  - intros * HMk HA0.
    destruct (Completeness.Inductives.Model.nparams_nth_split _ _ _ HA0) as [Δ1 HΔ1].
    assert (Hk : j < im_nn Mk) by (unfold im_nn; rewrite <- List.length_rev; apply List.nth_error_Some; congruence).
    pose proof (dt_nparams _ _ _ Hdt _ _ _ _ _ HMk HΔ1) as HT.
    rewrite Completeness.Inductives.Model.length_nparams_prefix in HT by lia.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * HMk Hcon HA0.
    destruct (Completeness.Inductives.Model.nonrec_nth_split _ _ _ HA0) as (gs1 & gs2 & Heq & Hk).
    pose proof (dt_args _ _ _ Hdt _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq) as HT.
    assert (Hls : List.length (cargs_strat gs1) = j)
      by (rewrite Completeness.Inductives.Model.cargs_strat_nonrec, List.length_rev, List.length_map; exact Hk).
    rewrite Hls, (Completeness.Inductives.Model.nonrec_args_prefix_cargs_strat gs1 (ca_arg A :: gs2)), Hk, <- Heq in HT.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * HMk Hcon Heq HMj HPk HT.
    assert (Hls : List.length (cargs_nonrec gs1) = List.length (cargs_strat gs1))
      by (rewrite Completeness.Inductives.Model.cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hls in HT.
    pose proof (dt_rec_ps _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq HMj HPk HT) as H.
    rewrite (Completeness.Inductives.Model.nonrec_args_prefix_cargs_strat gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (Ke _ _ _ _ _ H _ _ Hμ).
  - intros * HMk Hcon Heq HB.
    assert (Hsplit : ptyp_doms t = List.firstn j (ptyp_doms t) ++ B :: List.skipn (S j) (ptyp_doms t))
      by (rewrite <- (skipn_nth_cons' _ _ _ HB), List.firstn_skipn; reflexivity).
    pose proof (dt_doms _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq Hsplit) as HT.
    assert (Hk : List.length (List.firstn j (ptyp_doms t)) = j)
      by (rewrite List.length_firstn; assert (j < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
    assert (Hls : List.length (cargs_strat gs1) = List.length (cargs_nonrec gs1))
      by (rewrite Completeness.Inductives.Model.cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hk, Hls, (Completeness.Inductives.Model.nonrec_args_prefix_cargs_strat gs1 (ca_rec t :: gs2)), <- Heq in HT.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * HMk Hcon Heq Hk.
    pose proof (doms_prefix_wf _ _ _ _ _ _ _ Hdt HMk (cons_lookup_in _ _ _ Hcon) _ _ _ Heq _ Hk) as H.
    rewrite (Completeness.Inductives.Model.nonrec_args_prefix_cargs_strat gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (Kc _ _ _ H _ _ Hμ).
  - destruct (dt_selfs _ _ _ Hdt) as [IsS HV]; exists IsS; constructor.
    + exact (vst_link _ _ _ _ HV).
    + intros * HMk Hh Hq HI HT.
      pose proof (decl_typed_container _ _ _ _ D Hs Hdt _ _ _ _ _ _ _ HMk Hh Hq) as HqS.
      eapply Ke; [| exact Hμ ].
      eapply (vst_is _ _ _ _ HV); [ exact HMk | exact Hh | exact HqS | exact HI | exact HT ].
Qed.

(** ** Every well-formed global context glues

    The identity is a sound embedding. *)
Theorem glu_emb_refl : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> glu_emb Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply glu_emb_good; [ exact Hg | | apply Embx_refl; exact Hg ].
  exact (global_valid glu_entry glu_mod_tele glu_ind_decl_entry glu_entry_def glu_entry_ax glu_entry_alias glu_entry_indalias glu_mod_tele_nil glu_entry_ind _ _ Hg).
Qed.

(** ** The fundamental theorem at the identity embedding *)

Section soundness_fundamental.
  Context {GC : GCtx}.

  (** The identity is sound at a well-formed global context. *)
  Lemma glu_emb_refl_gc : ⊢ᵍ gc_deps ⍮ gc_stack -> glu_emb gc_deps gc_stack gc_deps gc_stack.
  Proof. exact (glu_emb_refl _ _). Qed.

  Corollary soundness_fundamental_ctx : forall Γ, ⊢ Γ -> ⊩ Γ.
  Proof.
    intros * H; destruct soundness_fundamental as (Kc & _).
    pose proof (Kc _ _ _ H _ _ (glu_emb_refl_gc (ctx_wf_gctx _ _ _ H))) as H'; destruct GC; exact H'.
  Qed.

  Corollary soundness_fundamental_exp : forall Γ M A, Γ ⊢ M : A -> Γ ⊩ M : A.
  Proof.
    intros * H; destruct soundness_fundamental as (_ & Ke & _).
    pose proof (Ke _ _ _ _ _ H _ _ (glu_emb_refl_gc (ctx_wf_gctx _ _ _ (presup_exp_ctx H)))) as H'; destruct GC; exact H'.
  Qed.
End soundness_fundamental.

#[export]
Hint Resolve soundness_fundamental_ctx soundness_fundamental_exp : mctt.
