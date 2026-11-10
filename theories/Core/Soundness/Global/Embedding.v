(** * Glued Global Contexts

    The soundness counterpart of [Core/Completeness/Global/Embedding.v]: what an
    entry of a global context is worth at a target ([glu_entry],
    [glu_mod_tele], [glu_ind_decl_entry]), and the sound embedding that the
    validity of every entry gives ([glu_gctx_embedding_of], [glu_gctx_embedding_of_bodies_valid]).  The
    validity of an entry is that the type of a definition glues; a stored
    axiom or abstract definition then glues as the neutral of its path.
    Nothing here uses the fundamental theorem; that each entry is valid
    where it is checked, and so that a well-formed global context embeds
    soundly into itself, is proved with it in [FundamentalTheorem.v]. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Modules Require Import Values.
From Mctt.Core.Completeness.Global Require Import Embedding.
From Mctt.Core.Completeness Require ContextCases.
From Mctt.Core.Completeness.Modules Require Filed.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases UnitCases
  SubtypingCases UniverseCases FunctionCases LetCases PropCases.
From Mctt.Core.Soundness.Inductives Require Import Args Con.
From Mctt.Core.Soundness Require Import IndCases.
From Mctt.Core.Soundness.Global Require Import MemberValues.
From Mctt.Core.Completeness.Inductives Require Con.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. A stored axiom or abstract definition is a neutral

    A global is a neutral annotated with its type evaluated at [nil]. Since
    [nil_glu_sub_pred] leaves the environment free, the [⋅]-judgment can be
    instantiated at [nil], where the type glues at the neutral's
    annotation.  The member's value applies as the neutral does
    ([app_sim]): it is the neutral at a saturated module, and a member
    closure at one lacking a parameter ([glob_member_sim]), glued as the
    neutral is ([app_sim_glu]); its gluing at the type's value in the
    given environment is then the move along the type values with the
    type's gluing there as the witness ([glu_univ_elem_exp_conv]). *)

Section Cook.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  (** A neutral: a closed [G] whose value anywhere applies as [⇑ a d] does,
      [a] the value of its type at [nil], [d] reading back to [G]. *)
  Lemma glu_neut_nil : forall T G κ i d,
      evaluated_kind κ ->
      ⋅ ⊩ T : abs_kind_sort κ Typeω@i ->
      (forall σ, T[σ] = T) -> (forall σ, G[σ] = G) ->
      (forall φ, T[φ]ʷ = T) -> (forall φ, G[φ]ʷ = G) ->
      (forall Δ, ⊢ Δ -> Δ ⊢ G : T) ->
      (forall a, not_level_sort a -> Dom d ≈ d ∈ neutral_at a) ->
      (forall s (M' : ne), Rne d in s ↘ M' -> (ne_annotate_proofs M' : exp) = G) ->
      (forall a, ⟦ T ⟧ nil ↘ a -> exists ks v, pi_kinds_depth ks a /\ app_sim ks v (⇑ a d) /\ forall ρ, ⟦ G ⟧ ρ ↘ v) ->
      ⋅ ⊩ G : T.
  Proof.
    intros * Hκ HT HTs HGs HTw HGw HGty Hd Hrb Hev.
    pose proof (glu_rel_exp_to_wf_exp HT) as HTwf.
    destruct (presup_ctx_glu_rel_exp HT) as [Sb0 H0].
    (** The type glues as the type of an assumption *)
    destruct (glu_rel_ctx_extend (ex_intro _ _ H0) HT (sort_kind_abs_kind_sort κ i)) as [SbT HSbT].
    destruct (glu_ctx_env_cons_clean_inversion H0 HSbT) as (i2 & _ & HT2 & _).
    pose proof (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HTwf)) as HTv.
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i2); [ exact H0 |]; intros Δ σ ρ Hσ.
    destruct (HT2 _ _ _ Hσ) as [m Pa Ela HevT HPa HTPa].
    pose proof (glu_ctx_env_sub_escape H0 _ _ _ Hσ) as Hσt.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσt).
    (** The type at [nil]: the substitution glues there too *)
    assert (Hσ0 : Δ ⊢ˢ σ ® nil ∈ Sb0).
    { inversion H0 as [Sb0' ESb _ | | | | ]; subst; apply ESb; exact Hσt. }
    destruct (HT2 _ _ _ Hσ0) as [a0 P0 El0 Ha0 HP0 HTP0].
    (** Its values at the two environments are related ([⋅] relates all) *)
    destruct (rel_type_inversion_simple_at Completeness.Global.Args.per_ctx_env_nil_true HTv ρ nil I)
      as (m' & a0' & Hm' & Ha0' & Hrel).
    assert (m' = m) as -> by (eapply functional_eval_exp; eassumption).
    assert (a0' = a0) as -> by (eapply functional_eval_exp; eassumption).
    rewrite HTs in HTPa, HTP0.
    assert (HTΔ : Δ ⊢ T : abs_kind_sort κ Typeω@i)
      by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ HTwf Hσt) as H; rewrite abs_kind_sort_sub, HTs in H; exact H).
    (** Its value is of the kind, and no type of levels *)
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ HPa HTPa HTΔ) as [Hk _].
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ HP0 HTP0 HTΔ) as [_ Hnl0].
    (** The term's value, applying as the neutral does *)
    destruct (Hev _ Ha0) as (ks & v & Hks & Hsim & HGv).
    econstructor; [ exact HevT | rewrite Hk; destruct Hκ; cbn [glu_term_value]; exact (HGv ρ) | exact HPa |].
    rewrite HGs, HTs.
    (** The neutral is glued at [a0] ([realize_glu_elem_bot]), so is the
        value, which then moves to [m] with [T]'s gluing there *)
    assert (Hn : El0 Δ T G (⇑ a0 d)).
    { eapply realize_glu_elem_bot; [ exact HP0 |].
      econstructor; [ apply HGty; exact HΔ | exact HP0 | exact HTP0 | exact (Hd _ Hnl0) |].
      intros * Hk' Hr; unfold glu_ne_eq; rewrite (Hrb _ _ Hr), HGw, HTw.
      pose proof (HGty _ (kripke_dom _ _ _ Hk')); mauto 3. }
    pose proof (app_sim_glu _ _ _ _ _ Hks HP0 _ _ _ _ _ Hn Hsim) as Hv.
    exact (glu_univ_elem_exp_conv (per_univ_sym' _ _ _ Hrel) HP0 HPa Hv HTPa).
  Qed.
End Cook.

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** An axiom or an abstract definition of a stored body whose type glues
      at [⋅] glues there: at an evaluated kind it is the neutral of its
      path; at a proposition, a proof, glued by its typing
      ([glu_rel_exp_proof]). *)
  Lemma glob_glu : forall p T Φ x Φ0 b pv r A oM i,
      loc Θ Ξ p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv r A oM)) ->
      (if b then oM else None) = None ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ A (abs_kind_sort r Typeω@i) ->
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
    (** The member is typed at its type, in every context *)
    assert (Hty : forall Δ, gc_deps (GCtx := gc_mk Θ Ξ) ⍮ gc_stack (GCtx := gc_mk Θ Ξ) ⍮ ⋅ ⊢ A : abs_kind_sort r Typeω@i ->
                   ⊢ Θ ⍮ Ξ ⍮ Δ -> Θ ⍮ Ξ ⍮ Δ ⊢ a_mem (qname_mod p) x : A).
    { intros Δ HAw' HΔ.
      eapply (filed_def_wf _ _ Hg Δ p T Φ x Φ0 b pv r A oM _ HΔ Hl Hp Hn (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort r i))).
      exact (closed_weaken_exp _ _ _ _ _ HΔ HAw' HsA ltac:(destruct r; cbn; exact I)). }
    destruct (evaluated_kind_or_propositional r) as [Hrk | ->].
    2:{ (** A proof *)
        apply (@glu_rel_exp_proof (gc_mk Θ Ξ)); [ exact HA |].
        exact (Hty _ HAw (wf_ctx_empty _ _ Hg)). }
    eapply (@glu_neut_nil (gc_mk Θ Ξ)) with (d := d_glob (qname_app p (x :: nil))); [ exact Hrk | exact HA | | | | | | | |].
    - intros; apply exp_closed_sub; exact HsA.
    - intros; cbn; rewrite (mod_qname_sub _ _ _ Hpm); reflexivity.
    - intros; apply exp_closed_wk; exact HsA.
    - intros; cbn; rewrite (mod_qname_wk _ _ _ Hpm); reflexivity.
    - intros Δ HΔ; exact (Hty _ HAw HΔ).
    - intros a Ha; exact (glob_neutral_at _ _ Ha).
    - intros * Hrb; inversion Hrb; subst; cbn [ne_annotate_proofs ne_to_exp]; apply qname_term_snoc.
    - (** The member's value applies as the neutral does: it is the
          neutral at a saturated module, and a member closure at one
          lacking a parameter ([glob_member_sim]); its type is a [Π] over
          the module's telescope *)
      intros a Hev.
      pose proof (valid_gctx_embedding_filed _ _ _ _ (valid_gctx_embedding_refl _ _ Hg)) as Hfm.
      pose proof (gc_loc_of_loc _ _ Hg _ _ _ Hl) as Hgl.
      pose proof (Hfm _ _ _ Hgl) as HfM.
      pose proof (valid_filed_mod_terms _ _ _ _ _ HfM x Φ0 _ _ Hp eq_refl) as Hvt.
      cbn [entry_term] in Hvt.
      destruct Hvt as [A0 lv Htyped Hreads _ Hpk].
      cbn [mdesc_kind] in *.
      destruct (Hreads nil _ T nil ltac:(rewrite List.app_nil_r; reflexivity) eq_refl eq_refl) as [EA _].
      cbn [mdesc_type sb_of_list] in EA; injection EA as EA; rewrite exp_sub_id in EA.
      (** At all its parameters, the module's member is the neutral applied *)
      assert (Hsat : forall args r0, List.length args = List.length T ->
                 $*| ⇑ a (d_glob (qname_app p (x :: nil))) & args | Θ ⍮ Ξ ↘ r0 -> dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r0).
      { intros args r0 Hla Hr0.
        eapply eval_sel_global_neut;
          [ intros T' Φ' HT'; rewrite Hgl in HT'; injection HT' as <- _; lia
          | exact HeE | exact Hrk | destruct b; [ right; exact Hn | left; reflexivity ] | exact Hev | exact Hr0 ]. }
      exists (tele_kinds T), (match T with nil => ⇑ a (d_glob (qname_app p (x :: nil)))
                                     | _ => d_member (dm_global p nil) (x :: nil) end).
      split; [| split ].
      + rewrite EA in Hev; rewrite <- (List.app_nil_r (tele_kinds T)).
        eapply (@eval_ctx_pi_kinds (gc_mk Θ Ξ));
          [ exact Hrk | exact (glob_tele_kinds _ _ _ _ _ Hg Hl) | exact (valid_filed_mod_tele_all_assumptions _ _ _ _ _ HfM)
          | intros; exact I | exact Hev ].
      + eapply (@glob_member_sim (gc_mk Θ Ξ)) with (Tout := nil) (args := nil);
          [ exact Hgl | exact Hsat | rewrite List.app_nil_r; reflexivity | reflexivity | constructor
          | intros ->; reflexivity | intros HT; destruct T; [ contradiction | reflexivity ] ].
      + intros ρ; eapply (@eval_mem_of_sel (gc_mk Θ Ξ)); [ apply (gc_loc_path _ _ Hg _ _ ρ Hgl) |].
        destruct T as [| e T'] eqn:ET.
        * apply Hsat; [ reflexivity | constructor ].
        * eapply eval_sel_global_unsat; [ exact Hgl | cbn; lia ].
  Qed.
End Raw.


(** ** 2. Valid entries make a sound embedding *)

(** What an entry is worth at [Θ2 ⍮ Ξ2]: a definition's type glues, in the
    empty context, at the sort of its kind ([abs_kind_sort]), and its body,
    if any, at its type: the value a member with a δ-reduct is read off is
    the body's ([eval_sel_global]).  A definition with a module part is
    valid as its term part, a definition ([ge_valid]). *)
Definition glu_entry (_ : gdeps) (_ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (_ : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ r A oM =>
      (exists i, @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ A (abs_kind_sort r Typeω@i)) /\
      forall M, oM = Some M -> @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ M A
  | _ => True
  end.

Definition glu_mod_tele (_ : gdeps) (_ : gstack) (_ : ctx) : Prop := True.

Definition glu_ind_decl_entry (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop := @glu_ind_decl (gc_mk Θ2 Ξ2) D.

(** A record declaration is glued at the target, as a group is: its
    tuples and projections move their parameters along the glued
    parameters' telescope ([glu_record_decl]). *)
Definition glu_record_decl_entry (Θ2 : gdeps) (Ξ2 : gstack) (R : record_decl) : Prop := @glu_record_decl (gc_mk Θ2 Ξ2) R.

(** A stored body of the source, valid. *)
Lemma glu_loc_valid : forall Θ Ξ Θs Ξs Θ2 Ξ2 p T Φ,
    gds_valid glu_entry glu_mod_tele glu_ind_decl_entry glu_record_decl_entry Θs Ξs Θ2 Ξ2 Θ -> gs_valid glu_entry glu_mod_tele glu_ind_decl_entry glu_record_decl_entry Θs Ξs Θ2 Ξ2 Ξ -> loc Θ Ξ p T Φ ->
    gm_valid glu_entry glu_mod_tele glu_ind_decl_entry glu_record_decl_entry Θs Ξs Θ2 Ξ2 T Φ.
Proof.
  intros * HΘ HΞ [Hl | Hl].
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ1 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hl as <- <-; exact (proj2 (gs_valid_find _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ Ef)).
  - exact (proj2 (gc_body_valid _ _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl)).
Qed.

(** A sound embedding, from the validity at the target of what the source
    files and has open. *)
Theorem glu_gctx_embedding_of : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> gctx_embedding Θ Ξ Θ2 Ξ2 ->
    gds_valid glu_entry glu_mod_tele glu_ind_decl_entry glu_record_decl_entry Θ Ξ Θ2 Ξ2 Θ -> gs_valid glu_entry glu_mod_tele glu_ind_decl_entry glu_record_decl_entry Θ Ξ Θ2 Ξ2 Ξ -> glu_gctx_embedding Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg He HΘ HΞ; pose proof He as [Hg2 Hs].
  constructor; [ exact He | intros p D Hl; exact (ind_lookup_valid _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl)
               | intros p R Hl; exact (record_lookup_valid _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) | |].
  2:{ (** A body glues at its type, by the entry's validity: a definition's,
          or a definition with a module part's as its term part *)
      intros * Hl Hp HE.
      pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ (glu_loc_valid _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) Hp) as Hv.
      destruct E as [b pv r A' [M' |] | | | pv A' M' U |]; cbn in HE, Hv; try discriminate; injection HE as <- <-.
      - exact (proj2 Hv _ eq_refl).
      - destruct Hv as (_ & [_ HM] & _); exact (HM _ eq_refl). }
  intros * Hl Hp Hn HΓ.
  apply glu_rel_exp_nil_weaken; [ exact HΓ |].
  (* the type glues, by the entry's validity *)
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ (glu_loc_valid _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) Hp) as [[i HA] _].
  (* the entry, stored at the target where it is at the source *)
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
  pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl x _) Hent) as HeE.
  destruct (gc_sub_entry _ _ _ _ _ _ Hs HeE) as (E2 & HeE2 & Hgr); cbn in Hgr; subst E2.
  destruct (loc_grow _ _ _ _ Hs _ _ _ Hl) as (Φ2 & Hl2).
  pose proof (proj1 (loc_entry _ _ Hg2 _ _ _ Hl2 x _) HeE2) as Hent2.
  pose proof (loc_closed _ _ Hg2 _ _ _ Hl2) as [_ HcΦ2].
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ HcΦ2) Hent2) as (Φ0' & Hp2).
  exact (glob_glu _ _ Hg2 _ _ _ _ _ _ _ _ _ _ _ Hl2 Hp2 Hn HA).
Qed.

Corollary glu_gctx_embedding_of_bodies_valid : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> bodies_valid_along_embeddings glu_entry glu_mod_tele glu_ind_decl_entry glu_record_decl_entry Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 ->
    glu_gctx_embedding Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (glu_gctx_embedding_of _ _ _ _ Hg (gctx_embedding_with_bodies_embedding _ _ _ _ He) HΘ HΞ).
Qed.
