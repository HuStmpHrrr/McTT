(** * The Global Rules in the Gluing Model, at the Target

    The soundness counterpart of [Core/Completeness/ModuleCases.v]: the
    cases of the rules that read the global context, at the target of a
    sound embedding ([glu_emb]).  The declarations of the inductive types
    glue there, and so do the members of the stored bodies that have no
    δ-reduct, the axioms and abstract definitions read bare, as neutrals.
    Module values are not glued: a member with a δ-reduct glues as the
    reduct, which [wf_mem] premises typed, and one without is the filed
    member its module expression is equal to ([mem_alias_filed]).
    [KripkeCases.v] states them as the cases of the gluing judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules GlobalPaths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases ModuleSem ModuleCases GlobalSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases MemberCases
  SubtypingCases UniverseCases FunctionCases LetCases TrueFalseCases IndCases.
From Mctt.Core.Completeness Require IndCases.
Require Import Mctt.Core.Soundness.IndElimCases.
From Mctt.Core.Soundness Require Import Judgments.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Closed gluing at [⋅] weakens to every glued context

    Simpler than [closed_weaken_sem]: [nil_glu_sub_pred] does not constrain
    the environment, and the terms are the same, so no closedness is needed. *)

Section Weaken.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  Lemma wf_sub_nil : forall Δ σ, ⊢ Δ -> Δ ⊢ˢ σ : ⋅.
  Proof.
    intros * HΔ; constructor; [ exact HΔ | apply wf_ctx_empty; eapply ctx_wf_gctx; exact HΔ | | |];
      intros * Hx; inversion Hx.
  Qed.

  Lemma glu_rel_exp_nil_weaken : forall Γ N T, ⊩ Γ -> ⋅ ⊩ N : T -> Γ ⊩ N : T.
  Proof.
    intros * [SbΓ HΓ] [Sb0 H0 i Hi].
    eapply mk_glu_rel_exp with (gre_lvl := i); [ exact HΓ |]; intros Δ σ ρ Hσ.
    apply Hi.
    inversion H0 as [Sb' Heq Hg | | |]; subst.
    apply (Heq Δ σ ρ); cbn.
    apply wf_sub_nil, (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HΓ _ _ _ Hσ)).
  Qed.

  (** A type a glued context ends with is glued. *)
  Lemma glu_rel_typ_of_ctx_ext : forall Γ A, ⊩ Γ ▹ A -> exists i : nat, Γ ⊩ A : Typeω@i.
  Proof.
    intros * [Sb HS].
    assert (HΓ : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HS; subst; eexists; eassumption).
    destruct HΓ as [TSb HΓ].
    destruct (glu_ctx_env_cons_clean_inversion HΓ HS) as (i & _ & HAs & _).
    exists i; eapply mk_glu_rel_exp with (gre_lvl := S i); [ exact HΓ |]; intros Δ σ ρ Hσ.
    exact (glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub (glu_ctx_env_sub_escape HΓ _ _ _ Hσ) (HAs _ _ _ Hσ)).
  Qed.
End Weaken.


(** ** 2. The cases of the inductive types, at the target *)

Lemma k_decl : forall Θ Ξ Θ2 Ξ2 Γ p D, glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    ind_lookup Θ2 Ξ2 p = Some D /\ @glu_core (gc_mk Θ2 Ξ2) D /\ decl_closed D /\ ind_sort_univ (ind_sort D) /\
    decl_typed Θ2 Ξ2 D.
Proof.
  intros * He HΓ Hl.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [Hdt Hc].
  pose proof (decl_typed_emb _ _ _ _ _ (gme_emb _ _ _ _ He) Hdt) as Hdt2.
  pose proof (dt_sort_univ _ _ _ Hdt) as Hsu.
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ (gme_emb _ _ _ _ He)) Hl) as Hl2.
  split; [ exact Hl2 | split; [ exact (gme_ind _ _ _ _ He _ _ Hl) | split; [ exact Hc | split; [ exact Hsu | exact Hdt2 ] ] ] ].
Qed.

Lemma k_ind : forall Θ Ξ Θ2 Ξ2 Γ p D, glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_ind p) (ind_ty D).
Proof.
  intros * He HΓ Hl HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  apply (@glu_rel_exp_nil_weaken (gc_mk Θ2 Ξ2)); [ exact HΓ2 |].
  eapply (@glu_rel_exp_ind0 (gc_mk Θ2 Ξ2)); eassumption.
Qed.

Lemma k_con : forall Θ Ξ Θ2 Ξ2 Γ p D c gs (i : nat), glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ -> @glu_rel_ctx (gc_mk Θ2 Ξ2) (cargs_ctx p D gs ++ ind_params D) ->
    (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 ->
       @glu_rel_ctx (gc_mk Θ0 Ξ0) ((sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                                    ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t))) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@i -> @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ (con_ty p D gs) (Typeω@i) ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_con p c) (con_ty p D gs).
Proof.
  intros * He HΓ Hl Hcon HΓ2 HΨ2 Hsh Hty HTy.
  assert (HshV : forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       exists j : nat, @glu_rel_exp (gc_mk Θ2 Ξ2)
         (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
         (ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) (Typeω@j))
    by (intros * Heq Hk; apply (@glu_rel_typ_of_ctx_ext (gc_mk Θ2 Ξ2)); exact (Hsh _ _ _ _ Heq Hk _ _ He)).
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  pose proof (sme_ind _ _ _ _ (gctx_sem _ _ (em_wf _ _ _ _ (gme_emb _ _ _ _ He))) p D Hl2) as HDc.
  apply (@glu_rel_exp_nil_weaken (gc_mk Θ2 Ξ2)); [ exact HΓ2 |].
  eapply (@glu_rel_exp_con0 (gc_mk Θ2 Ξ2)); eassumption.
Qed.

Lemma k_elim : forall Θ Ξ Θ2 Ξ2 Γ p D Ps M nm A (i : nat) Bs,
    glu_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D -> List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 -> @glu_rel_exp (gc_mk Θ0 Ξ0) Γ P T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M (apps (a_ind p) Ps) ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) A (Typeω@i) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 ->
       @glu_rel_exp (gc_mk Θ0 Ξ0) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) B (elim_bty p D c gs A (List.firstn (ind_nu D) Ps))) ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_elim nm A Bs M) (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]).
Proof.
  intros * He Hl HPl HPt HPg HMt HMg Hnm HAt HAg HMx Hn HBx Hk HBt HBg.
  destruct (presup_exp HMt) as [HΓ _].
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  pose proof (sme_ind _ _ _ _ (gctx_sem _ _ (em_wf _ _ _ _ (gme_emb _ _ _ _ He))) p D Hl2) as HDc.
  destruct (emb_preserves_wf _ _ _ _ (gme_emb _ _ _ _ He)) as (_ & Hwe & _ & _ & Hwx & _).
  eapply (@glu_rel_exp_elim (gc_mk Θ2 Ξ2)); try eassumption; eauto.
Qed.

(** A term equal to one that glues glues, the equation moved to the target. *)
Lemma k_of_eq : forall Θ Ξ Θ2 Ξ2 Γ M N A,
    glu_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ N A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.
Proof.
  intros * He Heq Hg.
  destruct (emb_preserves_wf _ _ _ _ (gme_emb _ _ _ _ He)) as (_ & _ & Hwq & _).
  eapply (@glu_rel_exp_of_eq (gc_mk Θ2 Ξ2)); [ exact Hg | exact (Hwq _ _ _ _ Heq) ].
Qed.

(** ** 3. Members *)

Lemma ds_ats_term_none : forall Ns A R, ds_ats (ds_term A None) Ns = Some R -> exists A', R = ds_term A' None.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [ exact (IH _ _ Ha) | discriminate ].
Qed.

(** A member looked up as a term of no δ-reduct is an axiom or an abstract
    definition of a stored body, read bare: the module expression's module
    part is the body's path at no argument and no outside parameter. *)
Lemma mem_no_red : forall Θ Ξ Γ H x R A,
    mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A -> ds_red R = None ->
    exists R0 p T Φ Φ0 b pv oM,
      mdenote Θ Ξ Γ H R0 /\ ds_mod Θ Ξ R0 = Some (ds_closed nil p T Φ nil) /\
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) /\ (if b then oM else None) = None.
Proof.
  intros * Hm Ht Hr.
  assert (HR : R = ds_term A None)
    by (destruct R as [A' om | | | ]; cbn in Ht, Hr; try discriminate; subst; congruence).
  subst R.
  inversion Hm as [| | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hrd]; subst.
  destruct R0m as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in He; try discriminate.
  - (* an open body reads only transparent definitions and modules *)
    destruct (gm_prefix_upto Φx x) as [[| Φ' y E0 | ? ? ?] |]; try discriminate.
    destruct E0 as [[] pv A' [M |] | pv U | | ]; try discriminate; injection He as <- <- <-.
    + inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
    + inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn in Hrd; destruct (gm_fill Φ'); cbn in Hrd; [| discriminate ].
      injection Hrd as Heq; destruct Re; cbn in Hmm, Heq; try contradiction; discriminate.
  - destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    cbn [ds_read] in Hrd; destruct (ds_ats Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
    injection Hrd as Heq.
    destruct E0 as [b pv A' oM | pv [Δ [sm Φy | E'] ] | pv pq D ΦD | pv Δa pq Nsa ].
    + (* a definition: one of no body, read bare *)
      cbn [ge_read] in Hed; inversion Hed; subst.
      destruct (if b then oM else None) as [M |] eqn:Ho.
      * exfalso; destruct (ds_ats_some_red _ _ _ _ Hats) as (A1 & M1 & ->).
        rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
      * destruct (ds_ats_term_none _ _ _ Hats) as (A1 & ->).
        destruct (ds_named_term_none Θ' Ns (apps (a_mem (qname_mod p) x) Ns) A1) as [(Hn & -> & ->) | Hn];
          rewrite Hn in Heq; cbn in Heq; [| discriminate ].
        cbn in Hats; injection Hats as ->; injection Heq as ->.
        exists R0, p, T, Φ, Φ0, b, pv, oM; repeat split; assumption.
    + exfalso; assert (Hmm : ds_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; assert (Hmm : ds_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; cbn [ge_read] in Hed; inversion Hed; subst.
      destruct (ds_ats_ind _ _ _ _ _ Hats) as (? & ? & ->).
      rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; cbn [ge_read] in Hed; inversion Hed; subst.
      destruct (ds_ats_ind _ _ _ _ _ Hats) as (? & ? & ->).
      rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
Qed.

(** A member glues: as its δ-reduct, which glues by the premise of [wf_mem];
    without one, as the filed member it is equal to. *)
Lemma k_mem : forall Θ Ξ Θ2 Ξ2 Γ H x R A,
    glu_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
    (forall M, ds_red R = Some M -> forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 -> @glu_rel_exp (gc_mk Θ0 Ξ0) Γ M A) ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem H x) A.
Proof.
  intros * He HH Hm Ht HM HΓ.
  destruct (ds_red R) as [M |] eqn:Hr.
  - eapply k_of_eq; [ exact He | eapply wf_exp_eq_mem_delta; eassumption | exact (HM _ eq_refl _ _ He) ].
  - pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    destruct (mem_no_red _ _ _ _ _ _ _ Hm Ht Hr) as (R0 & p & T & Φ & Φ0 & b & pv & oM & Hm0 & Hmd & Hp & Hn).
    pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm0) Hmd) as Hl; cbn in Hl.
    eapply k_of_eq; [ exact He | eapply mem_alias_filed; eassumption |].
    eapply gme_glob; eassumption.
Qed.
