(** * Every Well-Formed Global Context Glues

    The soundness counterpart of [Core/Completeness/GlobalSem.v]: a
    well-formed global context embeds soundly into itself ([gctx_glu]).  The
    validity of each entry where it is checked ([global_valid]) is that the
    type of a definition glues; a stored axiom or abstract definition then
    glues as the neutral of its path. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules GlobalPaths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases ModuleSem GlobalSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases MemberCases
  SubtypingCases UniverseCases FunctionCases LetCases TrueFalseCases IndCases ModuleCases KripkeCases.
From Mctt.Core.Completeness Require IndCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. A stored axiom or abstract definition is a neutral

    A global is a neutral annotated with its type evaluated at [nil]. Since
    [nil_glu_sub_pred] leaves the environment free, the [⋅]-judgment can be
    instantiated at [nil]. The only semantic fact needed is that the values
    of a closed type at two environments are related ([typ_nil_rel], from
    completeness at [⋅]), which [glu_univ_elem_resp_per_univ] consumes. *)

Section Cook.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  Lemma typ_nil_rel : forall T i ρ ρ',
      ⋅ ⊢ T : Typeω@i ->
      exists a a', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
  Proof.
    intros * HT%completeness_fundamental_exp.
    destruct (rel_exp_of_typ_inversion_simple HT) as [env_rel [Hnil H]].
    apply H.
    inversion Hnil as [? Heq | | |]; subst.
    apply Heq; exact I.
  Qed.

  (** A neutral: a closed [G] that evaluates anywhere to [⇑ a d], [a] the value
      of its type at [nil], and reads back to itself. *)
  Lemma glu_neut_nil : forall T G i d,
      ⋅ ⊩ T : Typeω@i ->
      (forall σ, T[σ] = T) -> (forall σ, G[σ] = G) ->
      (forall φ, T[φ]ʷ = T) -> (forall φ, G[φ]ʷ = G) ->
      (forall Δ, ⊢ Δ -> Δ ⊢ G : T) ->
      Dom d ≈ d ∈ per_bot ->
      (forall s (M' : ne), Rne d in s ↘ M' -> (M' : exp) = G) ->
      (forall ρ a, ⟦ T ⟧ nil ↘ a -> ⟦ G ⟧ ρ ↘ ⇑ a d) ->
      ⋅ ⊩ G : T.
  Proof.
    intros * HT HTs HGs HTw HGw HGty Hd Hrb Hev.
    pose proof (glu_rel_exp_to_wf_exp HT) as HTwf.
    pose proof HT as [Sb0 H0 _ _].
    pose proof (glu_rel_exp_clean_inversion2' H0 HT) as HTi.
    eapply mk_glu_rel_exp with (gre_lvl := i); [ exact H0 |]; intros Δ σ ρ Hσ.
    destruct (HTi _ _ _ Hσ) as [? ? ? ? Hevu HevT Hu HTσ].
    inversion Hevu; subst.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    destruct_glu_records; destruct_conjs.
    rename gta_typ into Pa, gta_exp into Ela, gta_elem into HPa, gta_glu into HTPa.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape H0 _ _ _ Hσ)).
    destruct (typ_nil_rel _ _ ρ nil HTwf) as (a1 & a0 & Ha1 & Ha0 & Hrel).
    functional_eval_rewrite_clear.
    assert (HPa0 : glu_univ_elem i Pa Ela a0) by (eapply glu_univ_elem_resp_per_univ; eassumption).
    rewrite HTs in HTPa.
    econstructor; [ exact HevT | apply Hev; exact Ha0 | exact HPa |].
    rewrite HGs, HTs.
    eapply realize_glu_elem_bot; [ exact HPa0 |].
    econstructor; [ apply HGty; exact HΔ | exact HPa0 | exact HTPa | exact Hd |].
    intros * Hk Hr; rewrite (Hrb _ _ Hr), HGw, HTw.
    pose proof (HGty _ (kripke_dom _ _ _ Hk)); mauto 3.
  Qed.
End Cook.

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** An axiom or an abstract definition of a stored body whose type glues
      at [⋅] glues there: it is the neutral of its path. *)
  Lemma glob_glu : forall p T Φ x Φ0 b pv A oM i,
      loc Θ Ξ p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) ->
      (if b then oM else None) = None ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ A (Typeω@i) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ (a_mem (qname_mod p) x) A.
  Proof.
    intros * Hl Hp Hn HA.
    pose proof (loc_closed _ _ Hg _ _ _ Hl) as [_ HcΦ].
    pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ [HsA _]].
    pose proof (qname_mod_qname p) as Hpm.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
    pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl x _) Hent) as HeE.
    apply gc_entry_def in HeE; rewrite qname_in_app in HeE.
    pose proof (@glu_rel_exp_to_wf_exp (gc_mk Θ Ξ) _ _ _ HA) as HAw.
    eapply (@glu_neut_nil (gc_mk Θ Ξ)) with (d := d_glob (qname_app p (x :: nil))); [ exact HA | | | | | | | |].
    - intros; apply exp_closed_sub; exact HsA.
    - intros; cbn; rewrite (mod_qname_sub _ _ _ Hpm); reflexivity.
    - intros; apply exp_closed_wk; exact HsA.
    - intros; cbn; rewrite (mod_qname_wk _ _ _ Hpm); reflexivity.
    - intros Δ HΔ.
      eapply (filed_def_wf _ _ Hg _ _ _ _ _ _ _ _ _ _ i HΔ Hl Hp Hn).
      exact (closed_weaken_exp _ _ _ _ _ HΔ HAw HsA ltac:(cbn; exact I)).
    - intros s; eexists; split; constructor.
    - intros * Hrb; inversion Hrb; subst; cbn [ne_to_exp]; apply qname_term_snoc.
    - intros * Hev.
      eapply (@eval_mem_of_sel (gc_mk Θ Ξ));
        [ apply (gc_loc_path _ _ Hg _ _ ρ (gc_loc_of_loc _ _ Hg _ _ _ Hl))
        | eapply eval_sel_global_neut; [ exact HeE | | exact Hev | constructor ] ].
      destruct b; [ right; exact Hn | left; reflexivity ].
  Qed.
End Raw.


(** ** 2. Every well-formed global context glues *)

(** What an entry is worth at [Θ2 ⍮ Ξ2]: a definition's type glues, in the
    empty context.  Bodies need nothing: a member with a δ-reduct glues as
    the reduct, which [wf_mem] premises typed. *)
Definition glu_V (_ : gdeps) (_ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (_ : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A _ => exists i, @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ A (Typeω@i)
  | _ => True
  end.

Definition glu_F (_ : gdeps) (_ : gstack) (_ : ctx) : Prop := True.

Definition glu_VD (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop := @glu_core (gc_mk Θ2 Ξ2) D.

(** A stored body of the source, valid. *)
Lemma glu_loc_valid : forall Θ Ξ Θs Ξs Θ2 Ξ2 p T Φ,
    gds_valid glu_V glu_F glu_VD Θs Ξs Θ2 Ξ2 Θ -> gs_valid glu_V glu_F glu_VD Θs Ξs Θ2 Ξ2 Ξ -> loc Θ Ξ p T Φ ->
    gm_valid glu_V glu_F glu_VD Θs Ξs Θ2 Ξ2 T Φ.
Proof.
  intros * HΘ HΞ [Hl | Hl].
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ1 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hl as <- <-; exact (proj2 (gs_valid_find _ _ _ _ _ _ _ _ _ _ _ _ HΞ Ef)).
  - exact (proj2 (good_body _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl)).
Qed.

(** A sound embedding, from the validity at the target of what the source
    files and has open. *)
Theorem glu_emb_of : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Θ -> gs_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Ξ -> glu_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg He HΘ HΞ; pose proof He as [Hg2 Hs].
  constructor; [ exact He | intros p D Hl; exact (good_ind _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) |].
  intros * Hl Hp Hn HΓ.
  apply glu_rel_exp_nil_weaken; [ exact HΓ |].
  (* the type glues, by the entry's validity *)
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ (glu_loc_valid _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) Hp) as [i HA].
  (* the entry, stored at the target where it is at the source *)
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
  pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl x _) Hent) as HeE.
  destruct (gc_sub_entry _ _ _ _ _ _ Hs HeE) as (E2 & HeE2 & Hgr); cbn in Hgr; subst E2.
  destruct (loc_grow _ _ _ _ Hs _ _ _ Hl) as (Φ2 & Hl2).
  pose proof (proj1 (loc_entry _ _ Hg2 _ _ _ Hl2 x _) HeE2) as Hent2.
  pose proof (loc_closed _ _ Hg2 _ _ _ Hl2) as [_ HcΦ2].
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ HcΦ2) Hent2) as (Φ0' & Hp2).
  exact (glob_glu _ _ Hg2 _ _ _ _ _ _ _ _ _ _ Hl2 Hp2 Hn HA).
Qed.

Corollary glu_emb_good : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (glu_emb_of _ _ _ _ Hg (Embx_emb _ _ _ _ He) HΘ HΞ).
Qed.

(** *** Each entry is valid where it is checked *)

Lemma glu_V_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> GoodV glu_V glu_F glu_VD Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Θ -> gs_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Ξ ->
    forall Θs Ξs, glu_V Θs Ξs Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM _ He HΘ HΞ Θs Ξs.
  pose proof (glu_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) He HΘ HΞ) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  exists j; exact (kglu_read _ _ _ _ _ _ Hμ HT).
Qed.

Lemma glu_V_ax : forall Θ Ξ A i b pv Θ2 Ξ2 Θs Ξs,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He _.
  pose proof (glu_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HA)) HG He) as Hμ.
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  exists j; exact (kglu_read _ _ _ _ _ _ Hμ HT).
Qed.

Lemma glu_V_alias : forall Θ Ξ pv Δ E Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof. intros; exact I. Qed.

Lemma glu_V_indalias : forall Θ Ξ pv Δ p Ns D Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> ind_lookup Θ Ξ p = Some D -> List.length Ns <= ind_nu D ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps (a_ind p) Ns : ind_ty_at D Ns ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns).
Proof. intros; exact I. Qed.

Lemma glu_F_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof. intros; exact I. Qed.

(** A declaration typed at the source glues at the target: its judgments,
    glued. *)
Lemma glu_V_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_VD Θ2 Ξ2 D /\ glu_F Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * Hdt HG He; split; [| exact I ]; unfold glu_VD.
  pose proof Hdt as [Hass _ Hle HΔ Hsu [i HS] [n Hn] HA HPl HP HN Hnd Hsh].
  pose proof (glu_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) HG He) as Hμ.
  destruct soundness_fundamental as (Kc & Ke & _).
  constructor.
  - exact (Kc _ _ _ HΔ _ _ Hμ).
  - exists n; exact (Ke _ _ _ _ _ Hn _ _ Hμ).
  - exists n.
    assert (Hn' : Θ ⍮ Ξ ⍮ ind_params D ⊢ (ind_sort_lvl (ind_sort D))[wk_shiftn (ind_nn D)]ʷ : Level@n).
    { pose proof HΔ as HΔ'; rewrite params_split in HΔ'.
      pose proof (wf_wk_shiftn_app' _ _ _ _ HΔ') as Hw.
      rewrite length_nparams in Hw; rewrite params_split.
      exact (wk_preserves_exp _ _ _ _ _ _ _ Hn Hw). }
    exact (Ke _ _ _ _ _ Hn' _ _ Hμ).
  - intros k A HA0.
    destruct (Completeness.IndCases.nparams_nth_split _ _ _ HA0) as [Δ1 HΔ1].
    assert (Hk : k < ind_nn D)
      by (rewrite <- (length_nparams D), <- List.length_rev; apply List.nth_error_Some; congruence).
    pose proof (HN _ _ _ HΔ1) as HT; rewrite Completeness.IndCases.length_npre in HT by lia.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * Hcon HA0.
    destruct (Completeness.IndCases.nonrec_nth_split _ _ _ HA0) as (gs1 & gs2 & Heq & Hk).
    pose proof (HA _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as HT.
    assert (Hls : List.length (cargs_strat gs1) = k)
      by (rewrite Completeness.IndCases.cargs_strat_nonrec, List.length_rev, List.length_map; exact Hk).
    rewrite Hls, (Completeness.IndCases.astrat_prefix gs1 (ca_arg A :: gs2)), Hk, <- Heq in HT.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * Hcon Heq HPk HT.
    assert (Hls : List.length (cargs_nonrec gs1) = List.length (cargs_strat gs1))
      by (rewrite Completeness.IndCases.cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hls in HT.
    pose proof (HP _ _ _ _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq HPk HT) as H.
    rewrite (Completeness.IndCases.astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (Ke _ _ _ _ _ H _ _ Hμ).
  - intros * Hcon Heq HB.
    destruct (Hsh _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as [_ Hs2].
    destruct (doms_split_nth _ _ _ HB) as [Hsplit _].
    pose proof (Hs2 _ _ _ Hsplit) as HT.
    assert (Hk : List.length (List.firstn k (ptyp_doms t)) = k)
      by (rewrite List.length_firstn; assert (k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
    assert (Hls : List.length (cargs_strat gs1) = List.length (cargs_nonrec gs1))
      by (rewrite Completeness.IndCases.cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hk, Hls, (Completeness.IndCases.astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in HT.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * Hcon Heq Hk.
    pose proof (doms_prefix_wf _ _ _ _ _ Hdt (cons_lookup_in _ _ _ Hcon) _ _ _ Heq _ Hk) as H.
    rewrite (Completeness.IndCases.astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (Kc _ _ _ H _ _ Hμ).
Qed.

(** Every well-formed global context glues: the identity is a sound
    embedding. *)
Theorem gctx_glu : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> glu_emb Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply glu_emb_good; [ exact Hg | | apply Embx_refl; exact Hg ].
  exact (global_valid glu_V glu_F glu_VD glu_V_def glu_V_ax glu_V_alias glu_V_indalias glu_F_nil glu_V_ind _ _ Hg).
Qed.
