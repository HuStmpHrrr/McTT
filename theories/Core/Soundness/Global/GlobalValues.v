(** * Values of Global Modules, Glued

    The members of a stored body, read bare at the target of a sound
    embedding ([glu_gctx_embedding]), are glued at their stored types
    ([glu_bare_member_at]): a member with a δ-reduct as the reduct, which
    the embedding glues (a stored body, a type former of a group or of a
    record type), and one without as the filed axiom or abstract
    definition it is ([mem_alias_filed]).  The values of global modules
    are glued from them ([glu_dmod]). *)

From Stdlib Require Import Lia List PeanoNat RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System Records.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound Presup.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Modules Require Import Values Filed.
From Mctt.Core.Completeness.Global Require Import Embedding.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases Instances IndCases.
From Mctt.Core.Soundness.Inductives Require Import Args.
From Mctt.Core.Soundness.Records Require Import Former.
From Mctt.Core.Soundness Require Import RecordCases ModuleValues.
From Mctt.Core.Soundness.Global Require Import MemberValues.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require ContextCases.
From Mctt.Core.Completeness.Modules Require Import Mem.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.LogicalRelation Require Substitution.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Semantic.PER.Lemmas Require Import CanonicalContexts UniverseSubtyping.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** A Member Equal to a Closed Reduct *)

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  (** A member of a stored module, of an evaluated kind, equal in every
      context to a closed [N] glued at its type over no context, whose
      value at [nil] the member is at all the module's parameters, is
      glued over no context: its value applies as [N]'s value at [nil]
      does ([glob_member_sim]), glued there by [N]'s gluing at [nil] and
      the equation ([app_sim_glu]), then moved along the type's values
      with the type's gluing at the given environment as the witness. *)
  Lemma glu_closed_reduct : forall p T Φ x N A r (i : nat) f,
      ⊢ᵍ gc_deps ⍮ gc_stack ->
      gc_loc gc_deps gc_stack p = Some (T, Φ) ->
      evaluated_kind r ->
      ⋅ ⊨ᵗ A ≈ A at i ->
      Completeness.ContextCases.rel_type_kind ⋅ A r ->
      (forall σ, A[σ] = A) -> (forall σ, N[σ] = N) ->
      (forall Δ, ⊢ Δ -> Δ ⊢ a_mem (qname_mod p) x ≈ N : A) ->
      ⋅ ⊩ N : A ->
      ⟦ N ⟧ nil ↘ f ->
      (forall a, ⟦ A ⟧ nil ↘ a -> pi_kinds_depth (tele_kinds T) a) ->
      (forall args r0, List.length args = List.length T -> $*| f & args | gc_deps ⍮ gc_stack ↘ r0 ->
         dm_global p args ·ₜ x gc_deps ⍮ gc_stack ↘ r0) ->
      ⋅ ⊩ a_mem (qname_mod p) x : A.
  Proof.
    intros * Hg Hgl Hrk HAv HAk HAs HNs Hδ HN Ef Hpi Hsat.
    pose proof (qname_mod_qname p) as Hpm.
    destruct HN as [SbN HSbN kN HNb].
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := kN); [ exact HSbN |]; intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_sub_escape HSbN _ _ _ Hσ) as Hσt.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσt).
    assert (Hσ0 : Δ ⊢ˢ σ ® nil ∈ SbN) by (inversion HSbN as [Sb' ESb _ | | | | ]; subst; apply ESb; exact Hσt).
    destruct (HNb _ _ _ Hσ) as [aρ mρ Pρ Elρ Eaρ Hmρ HPρ HNσ].
    destruct (HNb _ _ _ Hσ0) as [a0 f0 P0 El0 Ea0 Hf0 HP0 HN0].
    rewrite HNs, HAs in HNσ, HN0.
    pose proof (glu_univ_elem_trm_typ _ _ _ _ HPρ _ _ _ _ HNσ) as HTPρ.
    pose proof (glu_univ_elem_trm_typ _ _ _ _ HP0 _ _ _ _ HN0) as HTP0.
    (** The type's values are of its kind *)
    destruct (HAk _ Completeness.Global.Args.per_ctx_env_nil_true ρ ρ I) as (aρ1 & Eaρ1 & Hkρ).
    assert (aρ1 = aρ) as -> by (eapply functional_eval_exp; eassumption).
    destruct (HAk _ Completeness.Global.Args.per_ctx_env_nil_true nil nil I) as (a01 & Ea01 & Hk0).
    assert (a01 = a0) as -> by (eapply functional_eval_exp; eassumption).
    rewrite Hk0 in Hf0; assert (f0 = f) as -> by (destruct Hrk; eapply functional_eval_exp; eassumption).
    (** The type's values at the two environments are related ([⋅] relates all) *)
    destruct (rel_type_inversion_simple_at Completeness.Global.Args.per_ctx_env_nil_true HAv ρ nil I)
      as (aρ' & a0' & Haρ' & Ha0' & Hrel).
    assert (aρ' = aρ) as -> by (eapply functional_eval_exp; eassumption).
    assert (a0' = a0) as -> by (eapply functional_eval_exp; eassumption).
    (** The member's value *)
    set (v := match T with nil => f | _ => d_member (dm_global p nil) (x :: nil) end).
    assert (Hv : ⟦ a_mem (qname_mod p) x ⟧ ρ ↘ v).
    { eapply eval_mem_of_sel; [ apply (gc_loc_path _ _ Hg _ _ ρ Hgl) |]; subst v.
      destruct T as [| e T'] eqn:ET.
      - apply Hsat; [ reflexivity | constructor ].
      - eapply eval_sel_global_unsat; [ exact Hgl | cbn; lia ]. }
    assert (Hsim : app_sim (tele_kinds T) v f).
    { eapply (glob_member_sim p T Φ x f Hgl Hsat) with (Tout := nil) (args := nil);
        [ rewrite List.app_nil_r; reflexivity | reflexivity | constructor | intros ->; reflexivity
        | intros Hne; subst v; destruct T; [ contradiction | reflexivity ] ]. }
    econstructor; [ exact Eaρ | rewrite Hkρ; destruct Hrk; cbn [glu_term_value]; exact Hv | exact HPρ |].
    cbn [exp_sub]; rewrite (mod_qname_sub _ _ _ Hpm), HAs.
    (** Glued at [nil]: [N]'s value there, moved to the member by the equation *)
    assert (HG0 : Δ ⊢ a_mem (qname_mod p) x : A ® f ∈ El0)
      by (eapply glu_univ_elem_trm_resp_exp_eq; [ exact HP0 | exact HN0 | apply wf_exp_eq_sym, Hδ; exact HΔ ]).
    pose proof (app_sim_glu _ _ _ _ _ (Hpi _ Ea0) HP0 _ _ _ _ _ HG0 Hsim) as HGv.
    exact (glu_univ_elem_exp_conv (per_univ_sym' _ _ _ Hrel) HP0 HPρ HGv HTPρ).
  Qed.

  (** The member of a global module given some of its arguments, applied
      to the rest, is the member of the module given all of them: a member
      closure passes each argument to the module, then selects again
      ([eval_app_member]). *)
  Lemma global_member_apps : forall p T Φ x rest args0 s r,
      gc_loc gc_deps gc_stack p = Some (T, Φ) ->
      dm_global p args0 ·ₜ x gc_deps ⍮ gc_stack ↘ s ->
      List.length (args0 ++ rest) = List.length T ->
      $*| s & rest | gc_deps ⍮ gc_stack ↘ r ->
      dm_global p (args0 ++ rest) ·ₜ x gc_deps ⍮ gc_stack ↘ r.
  Proof.
    intros p T Φ x rest; induction rest as [| c rest IH]; intros * Hl Hs Hlen Hr.
    - inversion Hr; subst; rewrite List.app_nil_r; exact Hs.
    - pose proof (@functional_eval gc_deps gc_stack) as (_ & _ & _ & _ & _ & _ & _ & _ & Fsel & _).
      inversion Hr as [| ? ? ? s1 ? Hs1 Hr']; subst.
      assert (Hlt : List.length args0 < List.length T) by (rewrite List.length_app in Hlen; cbn in Hlen; lia).
      assert (Hu : dm_global p args0 ·ₜ x gc_deps ⍮ gc_stack ↘ d_member (dm_global p args0) (x :: nil))
        by (eapply eval_sel_global_unsat; [ exact Hl | exact Hlt ]).
      pose proof (Fsel _ _ _ Hs _ Hu) as ->.
      inversion Hs1; subst.
      match goal with Ha : $ᵐ| dm_global p args0 & c | _ ⍮ _ ↘ _ |- _ => inversion Ha; subst end.
      match goal with Hc : _ ·ₜ* (x :: nil) _ ⍮ _ ↘ _ |- _ => inversion Hc; subst end.
      + replace (args0 ++ c :: rest) with ((args0 ++ c :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
        eapply IH; [ exact Hl | eassumption | rewrite <- List.app_assoc; exact Hlen | exact Hr' ].
      + match goal with Hn : _ ·ₜ* nil _ ⍮ _ ↘ _ |- _ => inversion Hn end.
  Qed.

  (** Glued arguments are as many as their values. *)
  Lemma glu_tele_args_length : forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> List.length Ns = List.length args.
  Proof. induction 1; cbn; congruence. Qed.

  (** Glued arguments are related to themselves at the telescope, its
      types valid over a context whose environments [ρ] is related to
      itself in: each is related at its type's value ([glu_univ_elem_per_elem]). *)
  Lemma glu_tele_args_per : forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args ->
      forall Tpre RT, all_assumptions ts -> ⊨ List.rev ts ++ Tpre -> EF Tpre ≈ Tpre ∈ per_ctx_env ↘ RT -> RT ρ ρ ->
      per_tele_args ts ρ ρ args args.
  Proof.
    induction 1 as [Δ ts ρ Ms | Δ κ A ts ρ Ms N Ns c args a i0 P0 El0 Ea Hga HAP HN Hrest IH];
      intros * Hts HC HRT Hρ; [ constructor |].
    cbn [List.rev] in HC; rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    assert (Hts' : all_assumptions ts) by (inversion Hts; assumption).
    destruct (rel_ctx_wf_ass_typ (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HC)) as [jA HAv].
    destruct (rel_type_inversion_simple_at HRT HAv _ _ Hρ) as (a' & a'' & Ea' & Ea'' & [R HR]).
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a'' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hga) as [R0 HR0].
    pose proof (glu_univ_elem_per_elem _ _ _ _ Hga _ _ _ _ _ HN HR0) as Hc0.
    assert (Hcc : R c c) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR0 HR); exact Hc0).
    destruct (entry_readable_of_elem_closure Ea Ea HR Hcc) as [Rd _].
    pose proof (per_env_extend_intro' Hρ (per_head_of Ea Ea HR Hcc) Rd Rd) as Hρ'.
    pose proof (Mctt.Core.Completeness.LogicalRelation.Substitution.per_ctx_env_of_typ (κ := κ) HRT HAv) as HRT'.
    econstructor; [ econstructor; [ exact Ea | exact Ea | exact HR ] | exact Hcc |].
    exact (IH _ _ Hts' HC HRT' Hρ').
  Qed.

  (** Glued arguments extended by one more, glued at the next parameter's
      type in the environment the arguments make. *)
  Lemma glu_tele_args_snoc : forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args ->
      forall κ A N c a (i : nat) P El,
        List.nth_error ts (List.length Ns) = Some (ce_ass κ A) ->
        ⟦ A ⟧ env_tele ρ ts args ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ A[sb_of_list sb_closed_base (Ms ++ Ns)] ® P -> Δ ⊢ N : A[sb_of_list sb_closed_base (Ms ++ Ns)] ® c ∈ El ->
        glu_tele_args Δ ts ρ Ms (Ns ++ N :: nil) (args ++ c :: nil).
  Proof.
    induction 1 as [Δ ts ρ Ms | Δ κ0 A0 ts ρ Ms N0 Ns c0 args a0 i0 P0 El0 Ea0 Hga0 HAP0 HN0 Hrest IH];
      intros * Hnth Ea Hga HAP HN.
    - destruct ts as [| e ts]; cbn in Hnth; [ discriminate | injection Hnth as -> ].
      rewrite List.app_nil_r in HAP, HN.
      econstructor; [ exact Ea | exact Hga | exact HAP | exact HN | constructor ].
    - cbn [List.app]; econstructor; [ exact Ea0 | exact Hga0 | exact HAP0 | exact HN0 |].
      eapply (IH κ A); [ cbn in Hnth; exact Hnth | exact Ea | exact Hga | rewrite <- List.app_assoc; exact HAP | rewrite <- List.app_assoc; exact HN ].
  Qed.

  (** Glued arguments for the rest [ts] of a telescope, the arguments before
      them glued as an environment of the telescope before ([Tpre]), make
      a glued environment of the telescope: each argument extends it at
      its type's closure ([cons_glu_sub_pred_closure]), moved to the
      context's own index. *)
  Lemma glu_tele_args_env : forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args ->
      forall Tpre Sb, all_assumptions ts -> List.length Ns = List.length ts ->
        EG Tpre ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ sb_of_list sb_closed_base Ms ® ρ ∈ Sb ->
        forall SbT, EG List.rev ts ++ Tpre ∈ glu_ctx_env ↘ SbT ->
        Δ ⊢ˢ sb_of_list sb_closed_base (Ms ++ Ns) ® env_tele ρ ts args ∈ SbT.
  Proof.
    induction 1 as [Δ ts ρ Ms | Δ κ A ts ρ Ms N Ns c args a i0 P0 El0 Ea Hga HAP HN Hrest IH];
      intros * Hts Hlen HSb Hσ * HSbT.
    - destruct ts; cbn in Hlen; [| discriminate ].
      cbn [List.rev List.app] in HSbT; rewrite List.app_nil_r.
      apply (functional_glu_ctx_env HSb HSbT); exact Hσ.
    - cbn [List.rev] in HSbT; rewrite <- List.app_assoc in HSbT; cbn [List.app] in HSbT.
      assert (Hts' : all_assumptions ts) by (inversion Hts; assumption).
      destruct (glu_rel_ctx_app_r _ _ (ex_intro _ _ HSbT)) as [SbA HSbA].
      destruct (glu_ctx_env_cons_clean_inversion HSb HSbA) as (iA & HAt & HAg & ESbA).
      destruct (HAg _ _ _ Hσ) as [a' P' El' Ea' Hg' HAP'].
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (glu_univ_elem_per_univ _ _ _ _ Hga) as [Ra HRa].
      pose proof (glu_univ_elem_exp_conv (ex_intro _ Ra HRa) Hga Hg' HN HAP') as HN'.
      pose proof (cons_glu_sub_pred_closure HSb Hσ HAt Ea Hg' HN') as Hσ'.
      apply ESbA in Hσ'.
      assert (EMs : sb_of_list sb_closed_base (Ms ++ N :: nil) = (sb_of_list sb_closed_base Ms),,N)
        by (rewrite sb_of_list_app; reflexivity).
      rewrite <- EMs in Hσ'.
      pose proof (IH _ _ Hts' ltac:(cbn in Hlen; lia) HSbA Hσ' _ HSbT) as H.
      rewrite <- List.app_assoc in H; exact H.
  Qed.

  (** Glued arguments for a telescope are glued arguments for its part they
      cover. *)
  Lemma glu_tele_args_firstn : forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args ->
      glu_tele_args Δ (List.firstn (List.length Ns) ts) ρ Ms Ns args.
  Proof.
    induction 1; cbn [List.length List.firstn]; [ destruct ts; constructor | econstructor; eassumption ].
  Qed.

  (** The next parameter of a telescope glued with its types, past glued
      arguments: its type is glued at its value in the environment the
      arguments make ([glu_tele_args_env]), at the substitution the
      arguments make. *)
  Lemma glu_tele_next_param : forall T Δ Ns args,
      ⊢ Δ -> all_assumptions T -> ⊩ T -> List.length args < List.length T ->
      glu_tele_args Δ (List.rev T) nil nil Ns args ->
      exists κ A a (i : nat) P El,
        List.nth_error (List.rev T) (List.length args) = Some (ce_ass κ A) /\
        ⟦ A ⟧ env_tele nil (List.rev T) args ↘ a /\ domain_kind a = κ /\
        DG a ∈ glu_univ_elem i ↘ P ↘ El /\ Δ ⊢ A[sb_of_list sb_closed_base Ns] ® P.
  Proof.
    intros * HΔ HTa HT Hlt Hargs.
    pose proof (glu_tele_args_length _ _ _ _ _ _ Hargs) as HlN.
    (** The telescope split at the next parameter *)
    assert (Hsplit : exists Tin κ A Tout, T = Tin ++ ce_ass κ A :: Tout /\ List.length Tout = List.length args).
    { destruct (List.nth_error (List.rev T) (List.length args)) as [e |] eqn:He.
      2:{ apply List.nth_error_None in He; rewrite List.length_rev in He; lia. }
      pose proof (List.nth_error_split _ _ He) as (l1 & l2 & Erev & Hl1).
      assert (ET : T = List.rev l2 ++ e :: List.rev l1)
        by (rewrite <- (List.rev_involutive T), Erev, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity).
      assert (Hee : exists κ A, e = ce_ass κ A).
      { rewrite ET in HTa; apply all_assumptions_app_inv in HTa as [_ HTa2]; inversion HTa2; assumption. }
      destruct Hee as (κ & A & ->).
      exists (List.rev l2), κ, A, (List.rev l1); split; [ exact ET | rewrite List.length_rev; exact Hl1 ]. }
    destruct Hsplit as (Tin & κ & A & Tout & -> & Hlo).
    assert (Erev : List.rev (Tin ++ ce_ass κ A :: Tout) = List.rev Tout ++ ce_ass κ A :: List.rev Tin)
      by (rewrite List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity).
    (** The arguments, an environment of the part before *)
    destruct (glu_rel_ctx_app_r _ _ HT) as [SbA HSbA].
    destruct (glu_rel_ctx_tail (ex_intro _ _ HSbA)) as [SbO HSbO].
    pose proof (glu_tele_args_firstn _ _ _ _ _ _ Hargs) as Hargs'.
    rewrite HlN, Erev, <- Hlo, <- List.length_rev, List.firstn_app, Nat.sub_diag, List.firstn_all in Hargs'.
    cbn [List.firstn] in Hargs'; rewrite List.app_nil_r in Hargs'.
    destruct (glu_ctx_env_cons_clean_inversion HSbO HSbA) as (iA & HAt & HAg & ESbA).
    pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HAt)) as Hg.
    assert (Hnil : EG ⋅ ∈ glu_ctx_env ↘ nil_glu_sub_pred) by (eapply glu_ctx_env_nil; [ reflexivity | exact Hg ]).
    assert (HTo : all_assumptions (List.rev Tout))
      by (apply List.Forall_rev; apply all_assumptions_app_inv in HTa as [_ H]; inversion H; assumption).
    assert (HSbO' : EG List.rev (List.rev Tout) ++ ⋅ ∈ glu_ctx_env ↘ SbO) by (rewrite List.rev_involutive, List.app_nil_r; exact HSbO).
    pose proof (glu_tele_args_env _ _ _ _ _ _ Hargs' ⋅ _ HTo ltac:(rewrite List.length_rev; lia) Hnil (wf_sub_nil' _ _ HΔ) _ HSbO') as Hσ.
    cbn [List.app] in Hσ.
    destruct (HAg _ _ _ Hσ) as [a P El Ea Hga HAP].
    pose proof (glu_ctx_env_sub_escape HSbO _ _ _ Hσ) as Hσt.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HAt Hσt) as HAσ; rewrite abs_kind_sort_sub in HAσ.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hga HAP HAσ) as [Hk _].
    exists κ, A, a, iA, P, El; repeat split; [ | | exact Hk | exact Hga | exact HAP ].
    - rewrite Erev, List.nth_error_app2 by (rewrite List.length_rev; lia).
      rewrite List.length_rev, Hlo, Nat.sub_diag; reflexivity.
    - rewrite env_tele_firstn, Erev, <- Hlo, <- List.length_rev, List.firstn_app, Nat.sub_diag, List.firstn_all.
      cbn [List.firstn]; rewrite List.app_nil_r; exact Ea.
  Qed.

  (** The telescope a stored module at fewer arguments than parameters
      still takes, viewed by its outermost parameter: the next parameter's
      type at the arguments. *)
  Lemma closed_tele_view : forall p T Φ Ns κ A,
      List.length Ns < List.length T ->
      List.nth_error (List.rev T) (List.length Ns) = Some (ce_ass κ A) ->
      exists T1, mdesc_tele (mdesc_closed nil p T Φ Ns) = Some (tele_sub T1 (q (sb_of_list Id Ns)) ++ ce_ass κ A[sb_of_list Id Ns] :: nil) /\
        tele_view (tele_sub T1 (q (sb_of_list Id Ns)) ++ ce_ass κ A[sb_of_list Id Ns] :: nil) =
          Some (A[sb_of_list Id Ns], tele_sub T1 (q (sb_of_list Id Ns))).
  Proof.
    intros * Hlt Hnth.
    pose proof (List.nth_error_split _ _ Hnth) as (l1 & l2 & Erev & Hl1).
    assert (ET : T = List.rev l2 ++ ce_ass κ A :: List.rev l1)
      by (rewrite <- (List.rev_involutive T), Erev, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity).
    exists (List.rev l2).
    assert (Hfn : List.firstn (List.length T - List.length Ns) T = List.rev l2 ++ ce_ass κ A :: nil).
    { rewrite ET, List.length_app; cbn [List.length]; rewrite !List.length_rev, Hl1.
      replace (List.length l2 + S (List.length Ns) - List.length Ns) with (List.length (List.rev l2) + 1) by (rewrite List.length_rev; lia).
      rewrite List.firstn_app, List.firstn_all2 by lia.
      replace (List.length (List.rev l2) + 1 - List.length (List.rev l2)) with 1 by lia; reflexivity. }
    cbn [mdesc_tele]; rewrite (proj2 (Nat.leb_le _ _)) by lia; rewrite Hfn, tele_sub_app.
    split; [ rewrite List.app_nil_r; cbn; reflexivity |].
    unfold tele_view; rewrite List.rev_app_distr; cbn; rewrite List.rev_involutive; reflexivity.
  Qed.

  (** A module expression lacking a parameter, weakened past the parameter
      and applied to it, is well formed. *)
  Lemma wf_me_app_shift : forall Γ H R T B T1 Srt κ,
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ H R -> mdesc_mod_tele R = Some T ->
      tele_view T = Some (B, T1) -> Γ ⊢ B : Srt -> evaluated_sort Srt -> sort_kind Srt κ ->
      gc_deps ⍮ gc_stack ⍮ Γ ▹{κ} B ⊢ᵐ me_app H[Wk]ᵐ #0 ≈ me_app H[Wk]ᵐ #0.
  Proof.
    intros * HH Hm HT Hv HB HS Hsk.
    assert (HΓB : ⊢ Γ ▹{κ} B) by (eapply wf_ctx_extend; eassumption).
    assert (HWk : Γ ▹{κ} B ⊢ˢ Wk : Γ) by (eapply wf_sub_shift; exact HΓB).
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH HWk) as HHw.
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HH Hm HWk) as Hmw.
    pose proof (mdesc_mod_tele_sub _ _ Wk _ (wf_mdenote_scoped _ _ _ _ _ _ HH Hm) HT) as HTw.
    pose proof (tele_view_sub T Wk) as Hvw; rewrite Hv in Hvw; cbn [option_map fst snd] in Hvw.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB HWk) as HBw.
    assert (EBS : Srt[Wk] = Srt) by (destruct HS; reflexivity).
    rewrite EBS in HBw.
    assert (H0t : Γ ▹{κ} B ⊢ #0 : B[Wk])
      by (rewrite exp_sub_of_shift; apply wf_vlookup; [ exact HΓB | constructor ]).
    eapply wf_me_app; [ exact HHw | exact Hmw | exact HTw | exact Hvw | exact HBw | exact HS | exact H0t
                      | apply wf_exp_eq_refl; exact H0t | exact Hmw | exact HTw | exact Hvw | exact HBw | exact HS | exact H0t ].
  Qed.

  (** A factorization of a substitution extended by an argument gives one
      of the substitution through the weakening past the argument. *)
  Lemma glu_sub_through_extend : forall {Δ' σ1 Γ1 κ B N Δ'' φ' Γ2 ζ' σ2},
      Δ' ⊢ˢ σ1 : Γ1 ->
      glu_sub_through Δ' (σ1,,N) (Γ1 ▹{κ} B) Δ'' φ' Γ2 ζ' σ2 ->
      glu_sub_through Δ' σ1 Γ1 Δ'' φ' Γ2 (Wk ⨟ ζ') σ2.
  Proof.
    intros * Hσ1 [Hφ Hζ Hσ2 E].
    pose proof (wf_sub_cod _ _ _ _ _ Hζ) as HΓB.
    assert (HWk : Γ1 ▹{κ} B ⊢ˢ Wk : Γ1) by (eapply wf_sub_shift; exact HΓB).
    constructor; [ exact Hφ | eapply wf_sub_compose; [ exact HWk | exact Hζ ] | exact Hσ2 |].
    pose proof (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ HWk E) as E'.
    eapply wf_sub_eq_trans; [ apply wf_sub_eq_of_sb_eq; [ exact (wf_sub_sb_wk Hσ1 Hφ) | intros n; reflexivity ] |].
    eapply wf_sub_eq_trans; [ exact E' |].
    apply wf_sub_eq_of_sb_eq; [ eapply wf_sub_compose; [ exact HWk | eapply wf_sub_compose; [ exact Hζ | exact Hσ2 ] ] | intros n; reflexivity ].
  Qed.

  (** A next parameter's type of a closed telescope is scoped by the
      parameters before it. *)
  Lemma tele_next_scoped : forall T k κ A, ctx_scoped 0 T ->
      List.nth_error (List.rev T) k = Some (ce_ass κ A) -> exp_scoped k A.
  Proof.
    intros * Hs Hnth.
    pose proof (List.nth_error_split _ _ Hnth) as (l1 & l2 & Erev & Hl1).
    assert (ET : T = List.rev l2 ++ ce_ass κ A :: List.rev l1)
      by (rewrite <- (List.rev_involutive T), Erev, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity).
    rewrite ET in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs.
    rewrite List.length_rev, Hl1, Nat.add_0_r in Hs; exact (proj1 Hs).
  Qed.

  (** A type over the parameters before, instantiated at arguments then
      substituted, is instantiated at the substituted arguments, read over
      any base. *)
  Lemma tele_type_inst_sub : forall A Ns σ, exp_scoped (List.length Ns) A ->
      A[sb_of_list Id Ns][σ] = A[sb_of_list sb_closed_base (List.map (fun N => N[σ]) Ns)].
  Proof.
    intros * Hs.
    rewrite exp_sub_sb_of_list.
    rewrite (exp_scoped_sub_agree _ _ _ Id Hs) by (intros x Hx; apply sb_qn_lt; exact Hx).
    rewrite exp_sub_id.
    apply (exp_scoped_sub_agree _ _ _ _ Hs).
    intros x Hx; rewrite <- (List.length_map (fun N => N[σ]) Ns) in Hx.
    rewrite !(sb_of_list_nth _ _ _ Propₘ Hx); reflexivity.
  Qed.

  (** The [Π] over a telescope with a last (outermost) parameter more is
      the [Π] of that parameter over the [Π] of the rest. *)
  Lemma ctx_pi_at_snoc : forall r T κ B A, ctx_pi_at r (T ++ ce_ass κ B :: nil) A = a_pi κ r B (ctx_pi_at r T A).
  Proof. intros r; induction T as [| [] T IH]; intros; cbn; [ reflexivity | apply IH | apply IH | apply IH | apply IH ]. Qed.

  (** A function glued at a [Π] over the rest [ts] of a telescope, the
      [Π]'s environment [ρv] storing the arguments before at the values of
      their types, applied to the rest's arguments glued at its types in
      the environment [ρ] storing them at their closures
      ([glu_tele_args]): the application is glued at the codomain, in the
      environment extended by the arguments at the values of their types.
      Each argument moves to the [Π]'s domain along the relation of the
      two environments ([tele_args_env_rel_typed] reads a context PER only
      through the readability of the stored types); the element is
      unchanged.  The extended environments stay related. *)
  Lemma glu_pi_apps_tele : forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args ->
      forall Tpre RT ρv r B M Y v b (i : nat) P El,
        all_assumptions ts -> ⊨ List.rev ts ++ Tpre -> EF Tpre ≈ Tpre ∈ per_ctx_env ↘ RT -> RT ρ ρv ->
        List.length Ns = List.length ts -> evaluated_kind r ->
        ⟦ ctx_pi_at r (List.rev ts) B ⟧ ρv ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M : Y ® v ∈ El ->
        exists v' ρv' b' (i' : nat) P' El' Y', $*| v & args | gc_deps ⍮ gc_stack ↘ v' /\ ⟦ B ⟧ ρv' ↘ b' /\
          DG b' ∈ glu_univ_elem i' ↘ P' ↘ El' /\ Δ ⊢ apps_exp M Ns : Y' ® v' ∈ El' /\
          exists R', EF List.rev ts ++ Tpre ≈ List.rev ts ++ Tpre ∈ per_ctx_env ↘ R' /\ R' (env_tele ρ ts args) ρv'.
  Proof.
    induction 1 as [Δ ts ρ Ms | Δ κ A ts ρ Ms N Ns c args a i0 P0 El0 Ea Hga HAP HN Hrest IH];
      intros * Hts HC HRT Hρ Hlen Hr Eb Hgb HM.
    2:{ (** The next argument, moved to the [Π]'s domain *)
      cbn [List.rev] in HC, Eb; rewrite ctx_pi_at_snoc in Eb.
      rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
      assert (Hts' : all_assumptions ts) by (inversion Hts; assumption).
      destruct (rel_ctx_wf_ass_typ (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HC)) as [jA HAv].
      destruct (rel_type_inversion_simple_at HRT HAv _ _ Hρ) as (a' & a1 & Ea' & Ea1 & Haa1).
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      inversion Eb; subst.
      assert (a0 = a1) as -> by (eapply functional_eval_exp; eassumption).
      (** The [Π]'s domain and codomain *)
      destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
      pose proof HRb as HRb0.
      basic_invert_per_univ_elem HRb0.
      match goal with Hm : forall c c' (equiv_c_c' : _), rel_mod_eval _ _ _ _ _ _ |- _ => rename Hm into HBB end.
      match goal with Ha : per_univ_elem _ ?ir a1 a1 |- _ => rename Ha into Ha1 end.
      destruct (glu_univ_elem_pi_clean_inversion1 Ha1 Hr Hgb) as (IP & IEl & OP & OEl & elr & HIg & HOg & Hel & _ & HEl).
      apply HEl in HM.
      destruct HM as [? ? ? ? IT OT HMt Hmm HΠ HIT HOT HIP Happ].
      assert (HΓ : ⊢ Γ) by exact (presup_exp_ctx HMt).
      pose proof (kripke_id _ HΓ) as Hid.
      pose proof (HIP _ _ Hid) as HITP; rewrite exp_wk_id in HITP.
      destruct Haa1 as [Raa HRaa].
      (** The argument at the domain *)
      assert (HN' : Γ ⊢ N : IT[wk_id]ʷ ® c ∈ IEl)
        by (rewrite exp_wk_id; exact (glu_univ_elem_per_subtyp_trm_conv (per_subtyp_refl1 _ _ _ _ HRaa) Hga HIg HITP HN)).
      pose proof (glu_univ_elem_per_elem _ _ _ _ HIg _ _ _ _ _ HN' Ha1) as equiv_c.
      destruct (Happ _ _ _ _ Hid HN' equiv_c) as (mn & Hmn & HMN).
      destruct (HBB c c equiv_c) as [b1 b1' Eb1 Eb1' Hbb1].
      pose proof (HOg c equiv_c _ Eb1) as Hgb1.
      rewrite exp_wk_id in HMN.
      (** The environments extended by it stay related *)
      assert (Hcc : Raa c c) by (apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRaa Ha1); exact equiv_c).
      pose proof (per_head_of Ea' Ea1 HRaa Hcc) as Hhead.
      destruct (entry_readable_of_elem_closure Ea' Ea1 HRaa Hcc) as [Rd1 _].
      destruct (entry_readable_of_elem Ha1 equiv_c) as [Rd2 _].
      pose proof (per_env_extend_intro' Hρ Hhead Rd1 Rd2) as Hρ'.
      pose proof (Mctt.Core.Completeness.LogicalRelation.Substitution.per_ctx_env_of_typ (κ := domain_kind a1) HRT HAv) as HRT'.
      destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ Hts' HC HRT' Hρ' x Hr Eb1 Hgb1 HMN)
        as (v' & ρv' & b' & i' & P' & El' & Y' & Happs & Eb' & Hgb' & HMs & R' & HR' & Hρ'').
      exists v', ρv', b', i', P', El', Y'.
      split; [ econstructor; [ exact Hmn | exact Happs ] |].
      split; [ exact Eb' |]; split; [ exact Hgb' |]; split; [ exact HMs |].
      exists R'; cbn [List.rev]; rewrite <- List.app_assoc; cbn [List.app]; split; [ exact HR' | exact Hρ'' ]. }
    (** No more arguments *)
    destruct ts; cbn in Hlen; [| discriminate ].
    exists v, ρv, b, i, P, El, Y; split; [ constructor |]; split; [ exact Eb |]; split; [ exact Hgb |].
    split; [ exact HM |]; exists RT; split; [ exact HRT | exact Hρ ].
  Qed.

End Fixed_GCtx.

(** ** A Member of a Stored Body, Read Bare *)

Section Bare.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  #[local] Instance GCb : GCtx := gc_mk Θ Ξ.
  Import Fixed_Notations.

  (** A term member of a stored body, of an evaluated kind, read bare over
      no context, is glued at its type when its δ-reduct is, and, if it has
      none, when it is: its type is a closed [Π] over the module's
      telescope ([valid_filed_term]), its reduct the stored body or a type
      former, whose value at [nil] is the member's at all the module's
      parameters ([eval_sel_global_apps]). *)
  Lemma glu_bare_member_of_reduct : forall p T Φ x R A,
      gc_loc Θ Ξ p = Some (T, Φ) ->
      mdenote Θ Ξ ⋅ (me_mem (qname_mod p) x) R -> mdesc_type R = Some A ->
      evaluated_kind (mdesc_kind R) ->
      (forall N, mdesc_reduct R = Some N -> ⋅ ⊩ N : A) ->
      (mdesc_reduct R = None -> ⋅ ⊩ a_mem (qname_mod p) x : A) ->
      ⋅ ⊩ a_mem (qname_mod p) x : A.
  Proof.
    intros * Hgl Hm Ht Hk HN Hne.
    destruct (mdesc_reduct R) as [N |] eqn:Hr; [| exact (Hne eq_refl) ].
    specialize (HN _ eq_refl); clear Hne.
    (** Closed, as a description over no context *)
    pose proof (wf_gstack_closed _ _ Hg) as Hc.
    assert (Hsl : slots_ok 0 ⋅) by (intros ? ? ? Hx; inversion Hx).
    assert (Hsc : modexp_scoped 0 (me_mem (qname_mod p) x)) by (cbn; apply qname_mod_scoped).
    pose proof (proj1 (mdenote_scoped_all _ _ Hc) _ _ _ Hm 0 Hsl Hsc) as HRs.
    assert (HAs : forall σ, A[σ] = A) by (intros; apply exp_closed_sub; exact (mdesc_type_scoped _ _ _ HRs Ht)).
    assert (HNs : forall σ, N[σ] = N) by (intros; apply exp_closed_sub; exact (mdesc_reduct_scoped _ _ _ HRs Hr)).
    pose proof (qname_mod_qname p) as Hpm.
    (** The member is its reduct in every context *)
    assert (Hδ : forall Δ, ⊢ Θ ⍮ Ξ ⍮ Δ -> Θ ⍮ Ξ ⍮ Δ ⊢ a_mem (qname_mod p) x ≈ N : A).
    { intros Δ HΔ.
      assert (Hcp : sub_mod_compat Id Δ ⋅) by (intros ? ? Hx; inversion Hx).
      pose proof (proj1 (mdenote_sub_all _ _ Hc) _ _ _ Hm 0 Hsl Hsc _ _ Hcp) as HmΔ.
      cbn [modexp_sub] in HmΔ; rewrite (mod_qname_sub _ _ _ Hpm) in HmΔ.
      eapply wf_exp_eq_mem_delta; [ exact (loc_modexp_wf _ _ _ HΔ _ _ _ (gc_loc_loc _ _ _ _ _ Hgl)) | exact HmΔ | |].
      - rewrite (mdesc_type_sub _ _ _ Ht), HAs; reflexivity.
      - rewrite (mdesc_reduct_sub _ _ _ Hr), HNs; reflexivity. }
    (** The stored description, valid *)
    destruct (filed_mem_desc _ _ Hg ⋅ p T Φ nil x R A Hgl Hm Ht) as (R0 & R1 & Hst & Ha & Hkd & HtR & HrR).
    cbn [mdesc_term_part_ats] in Ha; injection Ha as <-; rewrite mdesc_named_nil in HtR, HrR.
    rewrite Hkd in Hk; rewrite Ht in HtR; rewrite Hr in HrR.
    pose proof (valid_gctx_embedding_filed _ _ _ _ (valid_gctx_embedding_refl _ _ Hg)) as Hfm.
    pose proof (Hfm _ _ _ Hgl) as HfM.
    assert (Hvt : valid_filed_term p T x R0).
    { destruct Hst as [Φ0 E R0' Hp HE | pq k D Mk Hk' HMk | Rr Hr'];
        [ exact (valid_filed_mod_terms _ _ _ _ _ HfM x Φ0 _ _ Hp HE)
        | exact (valid_filed_mod_ind_frames _ _ _ _ _ HfM _ _ _ _ _ Hk' HMk)
        | exact (valid_filed_mod_record_frames _ _ _ _ _ HfM _ _ Hr') ]. }
    destruct Hvt as [A1 lv Htyped Hreads _ Hpk].
    destruct (Hreads nil _ T nil ltac:(rewrite List.app_nil_r; reflexivity) eq_refl eq_refl) as [EA _].
    cbn [sb_of_list] in EA; rewrite <- HtR in EA; injection EA as EA; rewrite exp_sub_id in EA; subst A.
    (** The type is valid, of the member's kind *)
    destruct (rel_type_at_kind_of_abs_kind_sort _ _ _ _ Htyped) as [[iA HA1] HA1k].
    destruct (valid_filed_mod_tele_evaluated _ _ _ _ _ HfM) as [l HTr].
    assert (HT0 : ⊨ T ++ ⋅) by (rewrite List.app_nil_r; exact (valid_filed_mod_tele_wf _ _ _ _ _ HfM)).
    assert (HA1' : T ++ ⋅ ⊨ᵗ A1 ≈ A1 at iA) by (rewrite List.app_nil_r; exact HA1).
    assert (HA1k' : Completeness.ContextCases.rel_type_kind (T ++ ⋅) A1 (mdesc_kind R0)) by (rewrite List.app_nil_r; exact HA1k).
    destruct (rel_type_ctx_pi _ _ _ _ _ _ (valid_filed_mod_tele_all_assumptions _ _ _ _ _ HfM) HT0 HTr Hpk Hk HA1' HA1k')
      as [HAv HAk].
    (** The reduct's value at [nil] *)
    destruct HN as [SbN HSbN kN HNb] eqn:EHN.
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; exact Hg).
    assert (Hnil : ⋅ ⊢ˢ Id ® nil ∈ SbN)
      by (inversion HSbN as [Sb' ESb _ | | | | ]; subst; apply ESb; apply wf_sub_nil'; exact HΔ0).
    destruct (HNb _ _ _ Hnil) as [a0 f P0 El0 Ea0 Hf _ _].
    destruct (HAk _ Completeness.Global.Args.per_ctx_env_nil_true nil nil I) as (a01 & Ea01 & Hk0).
    assert (a01 = a0) as -> by (eapply functional_eval_exp; eassumption).
    rewrite Hk0 in Hf; assert (Ef : ⟦ N ⟧ nil ↘ f) by (destruct Hk; exact Hf).
    (** It is the member's stored value *)
    assert (Hgv : global_member_value Θ Ξ p x f).
    { destruct Hst as [Φ0 E R0' Hp HE | pq k D Mk Hk' HMk | Rr Hr'].
      - destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg _ _ _ (gc_loc_loc _ _ _ _ _ Hgl) x _) Hent) as HeE.
        rewrite qname_in_app in HeE.
        destruct E as [b pv r A0 oM | pv U | pv pq k D ΦD | pv A0 M0 U | pv pr Rr ΦR]; cbn in HE; try discriminate.
        + injection HE as <-; cbn in HrR, Hk.
          destruct b; [| discriminate ]; subst oM.
          apply gc_entry_def in HeE.
          eapply global_member_value_term; [ exact (gc_term_of_resolve _ _ _ _ _ _ _ Hk HeE) | exact Ef ].
        + destruct (ind_member D k) as [Mk |] eqn:HMk; cbn in HE; [ injection HE as <- | discriminate ].
          cbn in HrR; injection HrR as ->.
          inversion Ef; subst.
          destruct (gc_entry_ind _ _ _ _ _ _ _ _ HeE) as [Hres Hind].
          eapply global_member_value_indty; [ exact Hres | exact Hind ].
        + injection HE as <-; cbn in HrR; injection HrR as ->.
          eapply global_member_value_term; [ exact (gc_term_of_def_mod _ _ _ _ _ _ _ HeE) | exact Ef ].
        + injection HE as <-; cbn in HrR; injection HrR as ->.
          inversion Ef; subst.
          rewrite qname_in_app.
          pose proof (gc_entry_record _ _ _ _ _ _ _ HeE) as Hrl.
          eapply global_member_value_record; [ exact (record_lookup_resolve _ _ _ _ Hrl) | exact Hrl ].
      - cbn in HrR; injection HrR as ->; inversion Ef; subst.
        assert (Hind : ind_mlookup Θ Ξ (qname_in p x) = Some (pq, k, D)) by (rewrite ind_mlookup_unfold, Hk'; reflexivity).
        rewrite qname_in_app in Hind.
        eapply global_member_value_indty; [ exact (ind_mlookup_resolve _ _ _ _ Hind) | exact Hind ].
      - cbn in HrR; injection HrR as ->; inversion Ef; subst.
        assert (Hrl : record_lookup Θ Ξ (qname_in p x) = Some Rr) by (unfold record_lookup; rewrite Hr'; reflexivity).
        rewrite qname_in_app in Hrl |- *.
        eapply global_member_value_record; [ exact (record_lookup_resolve _ _ _ _ Hrl) | exact Hrl ]. }
    eapply (@glu_closed_reduct GCb p T Φ x N _ (mdesc_kind R0) _ f Hg Hgl Hk HAv HAk HAs HNs Hδ HN Ef).
    - (** A [Π] over the telescope *)
      intros a Ea; rewrite <- (List.app_nil_r (tele_kinds T)).
      eapply eval_ctx_pi_kinds;
        [ exact Hk | exact (glob_tele_kinds _ _ _ _ _ Hg (gc_loc_loc _ _ _ _ _ Hgl))
        | exact (valid_filed_mod_tele_all_assumptions _ _ _ _ _ HfM) | intros; exact I | exact Ea ].
    - (** At all the module's parameters, the member is the value applied *)
      intros args r0 Hla Hr0.
      eapply eval_sel_global_apps; [ intros T' Φ' HT'; cbn in HT'; rewrite Hgl in HT'; injection HT' as <- _; lia | exact Hgv | exact Hr0 ].
  Qed.

  (** A term member of a module expression whose module part is a stored
      module at arguments, at a substitution sending the arguments to
      ones glued as a saturated global value's: glued at every type value
      related to the member types of the values related to it, at which
      the lookup type is glued.  Its value is the member's stored value
      applied to the arguments ([global_member_apps]): the member read
      bare is glued over no context, applied along the [Π]s of its stored
      type ([glu_pi_apps_tele]); the type it is glued at there is related
      to the member type of the value, the environments being related, and
      the lookup's term is the stored member applied ([mem_closed_part]). *)
  Lemma glu_global_member_at : forall p T Φ x R0 As Γ1 H1 RH Ns1 R A' Δ σ1 args m a (i : nat) P El,
      gc_loc Θ Ξ p = Some (T, Φ) -> List.length args = List.length T ->
      mdenote Θ Ξ ⋅ (me_mem (qname_mod p) x) R0 -> mdesc_type R0 = Some As -> evaluated_kind (mdesc_kind R0) ->
      ⋅ ⊩ a_mem (qname_mod p) x : As ->
      Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H1 ≈ H1 -> mdenote Θ Ξ Γ1 H1 RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
      mdenote Θ Ξ Γ1 (me_mem H1 x) R -> mdesc_type R = Some A' ->
      Δ ⊢ˢ σ1 : Γ1 ->
      glu_tele_args Δ (List.rev T) nil nil (List.map (fun N => N[σ1]) Ns1) args ->
      dm_global p args ·ₜ x Θ ⍮ Ξ ↘ m ->
      (forall h b, per_dmod h (dm_global p args) -> dmod_mem_type h x b -> exists j, Dom b ≈ a ∈ per_univ j) ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A'[σ1] ® P ->
      Δ ⊢ (a_mem H1 x)[σ1] : A'[σ1] ® m ∈ El.
  Proof.
    intros * Hgl Hlen Hm0 Ht0 Hk HGa HH1 HmH HRH Hm Ht Hσ1 Hargs Hsel Hrel Hga HTP.
    pose proof (@functional_eval Θ Ξ) as (_ & _ & _ & _ & _ & _ & _ & _ & Fsel & _).
    (** The stored description of the member read bare, valid *)
    pose proof (valid_gctx_embedding_filed _ _ _ _ (valid_gctx_embedding_refl _ _ Hg)) as Hfm.
    pose proof (Hfm _ _ _ Hgl) as HfM.
    destruct (filed_mem_desc _ _ Hg ⋅ p T Φ nil x R0 As Hgl Hm0 Ht0) as (S0 & S1 & Hst & Ha & Hkd & HtS & _).
    cbn [mdesc_term_part_ats] in Ha; injection Ha as <-; rewrite mdesc_named_nil in HtS.
    rewrite Hkd in Hk; rewrite Ht0 in HtS.
    assert (Hvt : valid_filed_term p T x S0).
    { destruct Hst as [Φ0 E R0' Hp HE | pq k D Mk Hk' HMk | Rr Hr'];
        [ exact (valid_filed_mod_terms _ _ _ _ _ HfM x Φ0 _ _ Hp HE)
        | exact (valid_filed_mod_ind_frames _ _ _ _ _ HfM _ _ _ _ _ Hk' HMk)
        | exact (valid_filed_mod_record_frames _ _ _ _ _ HfM _ _ Hr') ]. }
    destruct Hvt as [A1 lv Htyped Hreads _ Hpk].
    destruct (Hreads nil _ T nil ltac:(rewrite List.app_nil_r; reflexivity) eq_refl eq_refl) as [EA _].
    cbn [sb_of_list] in EA; rewrite <- HtS in EA; injection EA as EA; rewrite exp_sub_id in EA; subst As.
    destruct (rel_type_at_kind_of_abs_kind_sort _ _ _ _ Htyped) as [[iA HA1] HA1k].
    destruct (valid_filed_mod_tele_evaluated _ _ _ _ _ HfM) as [l HTr].
    pose proof (valid_filed_mod_tele_wf _ _ _ _ _ HfM) as HT.
    pose proof (valid_filed_mod_tele_all_assumptions _ _ _ _ _ HfM) as HTa.
    assert (HT0 : ⊨ T ++ ⋅) by (rewrite List.app_nil_r; exact HT).
    assert (HA1' : T ++ ⋅ ⊨ᵗ A1 ≈ A1 at iA) by (rewrite List.app_nil_r; exact HA1).
    assert (HA1k' : Completeness.ContextCases.rel_type_kind (T ++ ⋅) A1 (mdesc_kind S0)) by (rewrite List.app_nil_r; exact HA1k).
    destruct (rel_type_ctx_pi _ _ _ _ _ _ HTa HT0 HTr Hpk Hk HA1' HA1k') as [HAv HAk].
    (** The member read bare, glued at [nil] *)
    assert (HΔ : ⊢ Θ ⍮ Ξ ⍮ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ1).
    destruct HGa as [SbN HSbN kN HNb].
    assert (Hnil : Δ ⊢ˢ Id ® nil ∈ SbN)
      by (inversion HSbN as [Sb' ESb _ | | | | ]; subst; apply ESb; apply wf_sub_nil'; exact HΔ).
    destruct (HNb _ _ _ Hnil) as [b v Pb Elb Eb Hv Hgb HG].
    cbn [exp_sub] in HG; rewrite (mod_qname_sub _ _ _ (qname_mod_qname p)), exp_sub_id in HG.
    destruct (HAk _ Completeness.Global.Args.per_ctx_env_nil_true nil nil I) as (b1 & Eb1 & Hkb).
    assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
    rewrite Hkb in Hv; assert (Ev : ⟦ a_mem (qname_mod p) x ⟧ nil ↘ v) by (destruct Hk; exact Hv).
    (** Its value is the selection from the module given no argument *)
    assert (Hs0 : exists s, dm_global p nil ·ₜ x Θ ⍮ Ξ ↘ s).
    { destruct T as [| e T'] eqn:ET.
      - destruct args; [ exists m; exact Hsel | cbn in Hlen; discriminate ].
      - eexists; eapply eval_sel_global_unsat; [ exact Hgl | cbn; lia ]. }
    destruct Hs0 as (s & Hs).
    pose proof (eval_mem_of_sel _ _ _ _ _ (gc_loc_path _ _ Hg _ _ nil Hgl) Hs) as Es.
    pose proof (functional_eval_exp _ _ _ _ Ev Es) as ->.
    (** Applied along the [Π]s of its type *)
    assert (HTa' : all_assumptions (List.rev T)) by (apply List.Forall_rev; exact HTa).
    assert (HC : ⊨ List.rev (List.rev T) ++ ⋅) by (rewrite List.rev_involutive; exact HT0).
    assert (Hlen' : List.length (List.map (fun N => N[σ1]) Ns1) = List.length (List.rev T))
      by (rewrite (glu_tele_args_length _ _ _ _ _ _ Hargs), List.length_rev; exact Hlen).
    assert (Eb' : ⟦ ctx_pi_at (mdesc_kind S0) (List.rev (List.rev T)) A1 ⟧ nil ↘ b) by (rewrite List.rev_involutive; exact Eb).
    destruct (@glu_pi_apps_tele GCb _ _ _ _ _ _ Hargs ⋅ _ nil _ A1 _ _ _ _ _ _ _ HTa' HC
                Completeness.Global.Args.per_ctx_env_nil_true I Hlen' Hk Eb' Hgb HG)
      as (v' & ρv' & b' & i' & P' & El' & Y' & Happs & Eb2 & Hgb2 & HY & R' & HR' & Hρ').
    pose proof (global_member_apps p T Φ x args nil s v' Hgl Hs ltac:(cbn; exact Hlen) Happs) as Hm'.
    cbn [List.app] in Hm'; pose proof (Fsel _ _ _ Hm' _ Hsel) as ->.
    (** Its type there is related to the value's member type, so to [a] *)
    rewrite List.rev_involutive in HR'.
    destruct (rel_type_inversion_simple_at HR' HA1' _ _ Hρ') as (b0 & b0' & Eb0 & Eb0' & [R1 HR1]).
    assert (b0' = b') as -> by (eapply functional_eval_exp; eassumption).
    assert (Hmt : dmod_mem_type (dm_global p args) x b0)
      by (eapply dmod_mem_type_global; [ exact Hgl | exact Hlen | exact Hm0 | exact Ht0 | exact Eb0 ]).
    assert (Hper : per_dmod (dm_global p args) (dm_global p args)).
    { econstructor; [ exact Hgl | exact Hlen |].
      exact (@glu_tele_args_per GCb _ _ _ _ _ _ Hargs ⋅ _ HTa' HC Completeness.Global.Args.per_ctx_env_nil_true I). }
    destruct (Hrel _ _ Hper Hmt) as [j [R2 HR2]].
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR2) as E12.
    assert (HR2' : per_univ_elem j R1 b0 a) by (eapply per_univ_elem_resp_iff; [ exact HR2 | symmetry; exact E12 ]).
    pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR1) HR2') as HR'a.
    (** Moved to [a], then to the lookup's term, the stored member applied *)
    pose proof (glu_univ_elem_per_subtyp_trm_conv (per_subtyp_refl1 _ _ _ _ HR'a) Hgb2 Hga HTP HY) as HY'.
    pose proof (mem_closed_part _ _ _ _ _ _ _ _ _ _ _ _ _ HH1 HmH HRH Hm Ht) as Heq0; cbn [ctx_fn] in Heq0.
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Heq0 Hσ1) as Heq1.
    rewrite apps_exp_sub in Heq1; cbn [exp_sub] in Heq1 |- *; rewrite (mod_qname_sub _ _ _ (qname_mod_qname p)) in Heq1.
    exact (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hga _ _ _ _ _ HY' (wf_exp_eq_sym _ _ _ _ _ _ Heq1)).
  Qed.

End Bare.

(** ** Members Read Bare *)

Lemma mdesc_ats_term_none_eq : forall Ns κ A R, mdesc_ats (mdesc_term κ A None) Ns = Some R -> exists A', R = mdesc_term κ A' None.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [ exact (IH _ _ _ Ha) | discriminate ].
Qed.

(** A member looked up as a term of no δ-reduct is an axiom or an abstract
    definition of a stored body, read bare: the module expression's module
    part is the body's path at no argument and no outside parameter. *)
Lemma mem_no_red : forall Θ Ξ Γ H x R A,
    mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A -> mdesc_reduct R = None ->
    exists R0 p T Φ Φ0 b pv κ oM,
      mdenote Θ Ξ Γ H R0 /\ mdesc_mod R0 = Some (mdesc_closed nil p T Φ nil) /\
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv κ A oM)) /\ (if b then oM else None) = None.
Proof.
  intros * Hm Ht Hr.
  assert (HR : exists κ, R = mdesc_term κ A None)
    by (destruct R as [κ A' om | | | ]; cbn in Ht, Hr; try discriminate; subst; injection Ht as ->; eauto).
  destruct HR as [κ ->].
  inversion Hm as [| | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hrd |]; subst.
  destruct R0m as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in He; try discriminate.
  - (* an open body reads only transparent definitions and modules *)
    destruct (gm_prefix_upto Φx x) as [[| Φ' y E0 | ? ? ?] |]; try discriminate.
    destruct E0 as [[] pv κ' A' [M |] | pv U | | |]; try discriminate; injection He as <- <- <-.
    + inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
    + inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn in Hrd; destruct (gm_fill Φ'); cbn in Hrd; [| discriminate ].
      injection Hrd as Heq; destruct Re; cbn in Hmm, Heq; try contradiction; discriminate.
    + (* a definition with a module part reads as one, with both parts *)
      inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
  - destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
    injection Hrd as Heq.
    destruct E0 as [b pv κ' A' oM | pv [Δ [sm Φy | E'] ] | pv pq k' D ΦD | pv Ad Md Ud | pv Rr ΦR ].
    + (* a definition: one of no body, read bare *)
      cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read] in Hats.
      destruct (if b then oM else None) as [M |] eqn:Ho.
      * exfalso; destruct (mdesc_ats_some_red _ _ _ _ _ Hats) as (A1 & M1 & ->).
        rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
      * destruct (mdesc_ats_term_none_eq _ _ _ _ Hats) as (A1 & ->).
        destruct (mdesc_named_term_none Θ' Ns (apps (a_mem (qname_mod p) x) Ns) κ' A1) as [(Hn & -> & ->) | Hn];
          rewrite Hn in Heq; cbn in Heq; [| discriminate ].
        cbn in Hats; injection Hats as ->; injection Heq as -> ->.
        exists R0, p, T, Φ, Φ0, b, pv, κ, oM; repeat split; assumption.
    + exfalso; assert (Hmm : mdesc_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (mdesc_ats_read_mod _ _ Hmm) in Hats.
      pose proof (mdesc_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; assert (Hmm : mdesc_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (mdesc_ats_read_mod _ _ Hmm) in Hats.
      pose proof (mdesc_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a member of a group: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read ind_former_desc] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a definition with a module part: read with its module part, no term *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a record type: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read record_former_desc] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
Qed.

(** The type former of a member of a group of a stored body, read bare, is
    glued at every sound embedding, as the group's type former. *)
Lemma glu_ind_former_of_embedding : forall Θ Ξ Θ0 Ξ0 pm pq k D Mk,
    ⊢ᵍ Θ ⍮ Ξ -> glu_gctx_embedding Θ Ξ Θ0 Ξ0 -> ind_mlookup Θ Ξ pm = Some (pq, k, D) -> ind_member D k = Some Mk ->
    @glu_rel_exp (gc_mk Θ0 Ξ0) ⋅ (a_ind pq k) (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ).
Proof.
  intros * Hg He Hk HMk.
  pose proof (ind_mlookup_group _ _ Hg _ _ _ _ Hk) as Hl.
  pose proof (ind_selfpath_decl_field _ _ _ _ (ind_mlookup_selfpath _ _ Hg _ _ _ _ Hk)) as Hlt.
  exact (@glu_rel_exp_of_under_sub (gc_mk Θ0 Ξ0) _ _ _
           (glu_ind _ _ _ _ _ _ _ (wf_ctx_empty _ _ Hg) (glu_ctx_empty _ _ Hg) Hl HMk Hlt _ _ He)).
Qed.

(** The type former of a record type of a stored body, read bare, is
    glued at every sound embedding, as the record's type former. *)
Lemma glu_record_former_of_embedding : forall Θ Ξ Θ0 Ξ0 pr Rr,
    glu_gctx_embedding Θ Ξ Θ0 Ξ0 -> record_lookup Θ Ξ pr = Some Rr ->
    @glu_rel_exp (gc_mk Θ0 Ξ0) ⋅ (a_record pr) (ctx_pi (record_params Rr) (record_sort Rr)).
Proof.
  intros * He Hl.
  pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ He)) as Hg0.
  pose proof (record_lookup_of_glu_gctx_embedding _ _ _ _ _ _ He Hl) as Hl0.
  destruct (record_typed_ty _ _ _ (record_lookup_typed _ _ Hg0 (gctx_valid_syn _ _ Hg0) _ _ Hl0)) as [i Hty].
  exact (@glu_rel_exp_record0 (gc_mk Θ0 Ξ0) pr Rr Hg0 Hl0 (glu_gctx_embedding_record_field _ _ _ _ He _ _ Hl) i Hty).
Qed.

(** A term member of a stored body, of an evaluated kind, read bare over no
    context, is glued at the target at its type: its δ-reduct, if any, is
    a stored body, glued by the embedding, or a type former; one without
    is an axiom or an abstract definition, glued by the embedding. *)
Lemma glu_bare_member_at : forall Θ Ξ Θ2 Ξ2 p T Φ x R A,
    ⊢ᵍ Θ ⍮ Ξ -> glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> gc_loc Θ Ξ p = Some (T, Φ) ->
    mdenote Θ Ξ ⋅ (me_mem (qname_mod p) x) R -> mdesc_type R = Some A -> evaluated_kind (mdesc_kind R) ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ (a_mem (qname_mod p) x) A.
Proof.
  intros * Hg He Hl Hm Ht Hk.
  pose proof (gc_loc_loc _ _ _ _ _ Hl) as Hlc.
  pose proof (glu_gctx_embedding_embedding _ _ _ _ He) as Hem.
  pose proof (gctx_embedding_wf _ _ _ _ Hem) as Hg2.
  pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hs.
  destruct (gc_loc_grow _ _ _ _ Hg2 Hs _ _ _ Hl) as (Φ2 & Hl2 & _).
  destruct (proj1 (mdenote_grow_all _ _ _ _ Hg Hg2 Hs) _ _ _ Hm) as (R2 & Hm2 & Hgr).
  pose proof (mdesc_grows_ty _ _ _ _ _ _ _ Hgr Ht) as Ht2.
  pose proof (mdesc_grows_red _ _ _ _ _ _ Hgr) as Hr2.
  assert (Hk2 : mdesc_kind R2 = mdesc_kind R)
    by (destruct Hgr; [ reflexivity | cbn in Ht; discriminate | reflexivity ]).
  rewrite <- Hk2 in Hk.
  destruct (filed_mem_desc _ _ Hg ⋅ p T Φ nil x R A Hl Hm Ht) as (R0 & R1 & Hst & Ha & _ & HtR & HrR).
  cbn [mdesc_term_part_ats] in Ha; injection Ha as <-; rewrite mdesc_named_nil in HtR, HrR.
  apply (glu_bare_member_of_reduct Θ2 Ξ2 Hg2 p T Φ2 x R2 A Hl2 Hm2 Ht2 Hk).
  2:{ (** No reduct: an axiom or an abstract definition *)
      intros HN; rewrite <- Hr2, HrR in HN; rewrite HtR in Ht.
      destruct Hst as [Φ0 E R0' Hp HE | pq k D Mk Hk' HMk | Rr Hr]; [| cbn in HN; discriminate | cbn in HN; discriminate ].
      destruct E as [b pv r A0 oM | pv U | pv pq k D ΦD | pv A0 M0 U | pv pr Rr ΦR]; cbn in HE; try discriminate.
      - injection HE as <-; cbn in HN, Ht; injection Ht as ->.
        exact (glu_gctx_embedding_glob _ _ _ _ He _ _ _ _ _ _ _ _ _ _ ⋅ Hlc Hp HN
                 (glu_rel_ctx_types_ctx _ (@glu_rel_ctx_types_empty (gc_mk Θ2 Ξ2) Hg2))).
      - destruct (ind_member D k); cbn in HE; [ injection HE as <-; cbn in HN; discriminate | discriminate ].
      - injection HE as <-; cbn in HN; discriminate.
      - injection HE as <-; cbn in HN; discriminate. }
  intros M HM; rewrite <- Hr2, HrR in HM; rewrite HtR in Ht.
  pose proof He as He0.
  destruct Hst as [Φ0 E R0' Hp HE | pq k D Mk Hk' HMk | Rr Hr].
  - destruct E as [b pv r A0 oM | pv U | pv pq k D ΦD | pv A0 M0 U | pv pr Rr ΦR]; cbn in HE; try discriminate.
    + (* a definition: its body, stored *)
      injection HE as <-; cbn in HM, Ht; injection Ht as ->.
      destruct b; [| discriminate ]; subst oM.
      exact (glu_gctx_embedding_body _ _ _ _ He0 _ _ _ _ _ _ _ _ Hlc Hp eq_refl).
    + (* a member of a group: its type former *)
      destruct (ind_member D k) as [Mk |] eqn:HMk; cbn in HE; [ injection HE as <- | discriminate ].
      cbn in HM, Ht; injection HM as <-; injection Ht as <-.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
      pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hlc x _) Hent) as HeE.
      exact (glu_ind_former_of_embedding _ _ _ _ _ _ _ _ _ Hg He0 (proj2 (gc_entry_ind _ _ _ _ _ _ _ _ HeE)) HMk).
    + (* a definition with a module part: its term, stored *)
      injection HE as <-; cbn in HM, Ht; injection HM as <-; injection Ht as <-.
      exact (glu_gctx_embedding_body _ _ _ _ He0 _ _ _ _ _ _ _ _ Hlc Hp eq_refl).
    + (* a record type: its type former *)
      injection HE as <-; cbn in HM, Ht; injection HM as <-; injection Ht as <-.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
      pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hlc x _) Hent) as HeE.
      exact (glu_record_former_of_embedding _ _ _ _ _ _ He0 (gc_entry_record _ _ _ _ _ _ _ HeE)).
  - (* the open frame of a member's module: its type former *)
    cbn in HM, Ht; injection HM as <-; injection Ht as <-.
    assert (Hind : ind_mlookup Θ Ξ (qname_in p x) = Some (pq, k, D)) by (rewrite ind_mlookup_unfold, Hk'; reflexivity).
    exact (glu_ind_former_of_embedding _ _ _ _ _ _ _ _ _ Hg He0 Hind HMk).
  - (* the open frame of a record type's module: its type former *)
    cbn in HM, Ht; injection HM as <-; injection Ht as <-.
    assert (Hrl : record_lookup Θ Ξ (qname_in p x) = Some Rr) by (unfold record_lookup; rewrite Hr; reflexivity).
    exact (glu_record_former_of_embedding _ _ _ _ _ _ He0 Hrl).
Qed.
