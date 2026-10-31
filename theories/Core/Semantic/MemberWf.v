(** * What Well-Formed Module Expressions Look Up

    A member a well-formed module expression looks up is typed, at the
    type the lookup reads, and so is its δ-reduct ([member_wf]): what the
    lookup reads is typed ([mem_desc_ok], [desc_ok_ty]), so the premises of
    [wf_mem] hold of it.  The outermost parameter a module still takes is a
    type ([mtele_head_wf]), and the entries a local open generates extend a
    well-formed context ([gens_ext_wf]).  The checker reads all three off
    the lookup, without checking anything again. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf MemberLemmas DescTyping LookupSound Presup.
From Mctt.Core.Semantic Require Import Fixed.
Import Syntax_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** A member a module expression looks up, at the type it is looked up at:
    a type, with its δ-reduct, if any, of it. *)
Corollary member_wf : forall Γ H x R A,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ (me_mem H x) R ->
    mdesc_type R = Some A ->
    Γ ⊢ᵗ A /\ (forall M, mdesc_reduct R = Some M -> Γ ⊢ M : A) /\ Γ ⊢ a_mem H x : A.
Proof.
  intros * HH Hm Ht.
  pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hv.
  destruct (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht) as [Hi HM].
  split; [ exact Hi | split; [ exact HM | exact (wf_mem_desc _ _ _ _ _ _ _ HH Hm Ht) ] ].
Qed.

(** The next parameter of a closed telescope given typed arguments, at
    them, is a type of a universe, as a module's parameters are relevant. *)
Lemma args_ok_next : forall Γ T Ns C T1' l,
    args_ok gc_deps gc_stack Γ T Ns -> tele_ass T -> ctx_scoped 0 T -> ⊢ T ->
    params_relevant gc_deps gc_stack nil T l ->
    tele_view (List.firstn (length T - length Ns) T) = Some (C, T1') ->
    Γ ⊢ C[sb_of_list Id Ns] : Typeω@l.
Proof.
  intros * [T1 T2 -> Hl Ha2 Hs2 HT2 HN] Ha Hs HT HR Hv.
  replace (firstn (length (T1 ++ T2) - length Ns) (T1 ++ T2)) with T1 in Hv
    by (rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
  apply List.Forall_app in Ha as [Ha1 _].
  pose proof (tele_view_ass _ _ _ Ha1 Hv) as ->.
  pose proof (HR T1' C T2 ltac:(rewrite <- List.app_assoc; reflexivity)) as HC; rewrite List.app_nil_r in HC.
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs2 HC HT2) as HC'.
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha2 HT2 (eq_sym Hl) HN) as Hσ.
  pose proof (sub_preserves_typ _ _ _ _ _ _ _ HC' Hσ) as HB; cbn in HB; exact HB.
Qed.

(** The outermost parameter a typed module description still takes is a
    type of a universe. *)
Lemma desc_ok_tele_head : forall Γ Rm T B T1,
    desc_ok gc_deps gc_stack Γ Rm -> mdesc_tele Rm = Some T -> tele_view T = Some (B, T1) ->
    exists i, Γ ⊢ B : Typeω@i.
Proof.
  intros * HR Ht Hv.
  inversion HR as [Γ0 A om HA HM | Γ0 Δ Φw Φ lΔ HΦ Hn Hent HaΔ Hsh Hnd HUw HRΔ
                  | Γ0 Θ' T0 Φ Ns Θ0 Ξ0 p lΘ Hg0 Hsub0 Hloc Ha0 Hs0 HT0 HΘ' Hargs HaΘ HRΘ |];
    subst; cbn in Ht; try discriminate.
  - (* an open module: its parameters *)
    injection Ht as <-.
    unfold tele_view in Hv; destruct (tele_open_split _ _ _ Hv) as (τ & Es).
    destruct (tele_split_ass_eq _ _ _ _ HaΔ Es) as [EΔ _].
    exists lΔ; exact (HRΔ _ _ nil EΔ).
  - (* a closed module: its outside parameters, then the rest of its telescope *)
    destruct (Nat.leb (length Ns) (length T0)); [| discriminate ]; injection Ht as <-.
    unfold tele_view in Hv; rewrite List.rev_app_distr in Hv.
    pose proof (tele_split_wf gc_deps gc_stack (rev Θ') Γ ltac:(rewrite rev_involutive; exact HΘ')) as Hsw.
    rewrite rev_involutive in Hsw.
    destruct (tele_split (rev Θ')) as [[[B' Θ''] τ] | τ] eqn:Es.
    + destruct (tele_open_app_inl _ (rev (tele_sub (List.firstn (length T0 - length Ns) T0) (sb_of_list Id Ns))) _ _ _ Es)
        as (T' & Ho).
      rewrite Ho in Hv; injection Hv as <- _.
      destruct (tele_split_ass_eq _ _ _ _ HaΘ Es) as [EΘ _].
      exists lΘ; exact (HRΘ _ _ nil EΘ).
    + destruct (tele_open_app_inr _ _ _ _ _ Es Hv) as (B0 & T0' & Ho & ->).
      fold (tele_view (tele_sub (List.firstn (length T0 - length Ns) T0) (sb_of_list Id Ns))) in Ho.
      rewrite tele_view_sub in Ho.
      destruct (tele_view (List.firstn (length T0 - length Ns) T0)) as [[C T1'] |] eqn:HvC; cbn in Ho; [| discriminate ].
      injection Ho as <- _.
      (* the stored telescope is relevant where it is stored, so here *)
      pose proof (ctx_wf_gctx _ _ _ HΘ') as Hg.
      destruct (loc_relevant _ _ _ _ _ (gctx_valid_syn _ _ Hg0) Hloc) as [lT HRT].
      pose proof (params_relevant_embed _ _ _ _ _ _ _ (Build_gctx_embedding _ _ _ _ Hg Hsub0) HRT) as HRT'.
      exists lT; pose proof (sub_preserves_typ _ _ _ _ _ _ _ (args_ok_next _ _ _ _ _ _ Hargs Ha0 Hs0 HT0 HRT' HvC) Hsw) as HB.
      cbn in HB; exact HB.
Qed.

(** The outermost parameter a well-formed module expression still takes is
    a type of a universe. *)
Corollary mtele_head_wf : forall Γ H R T B T1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ H R ->
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    exists i, Γ ⊢ B : Typeω@i.
Proof.
  intros * HH Hm Ht Hv.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  unfold mdesc_mod_tele in Ht; destruct (mdesc_mod R) as [Rm |] eqn:Hmd; [| discriminate ].
  exact (desc_ok_tele_head _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) Hmd) Ht Hv).
Qed.

(** A well-formed module expression denotes a module with a telescope. *)
Lemma me_mtele : forall Γ H H',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H' ->
    exists R T, mdenote gc_deps gc_stack Γ H R /\ mdesc_mod_tele R = Some T.
Proof.
  intros * HH.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  destruct (me_denotes _ _ _ _ _ HH) as (R & Rm & Hm & Hmd).
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) Hmd) as Hok.
  destruct (desc_ok_tele _ _ _ _ Hok (mdesc_mod_is_mod _ _ Hmd)) as [T HT].
  exists R, T; split; [ exact Hm | unfold mdesc_mod_tele; rewrite Hmd; exact HT ].
Qed.

(** ** What a Local Open Generates Is Well-Formed

    The entries an open of a well-formed module generates are well-formed:
    a definition is the member at its type, an alias the module or its
    submodule, a definition with a module part both, each read past the
    entries generated before it. *)
Lemma gens_ext_wf_gen : forall Γ1 H its gs, items_gen gc_deps gc_stack Γ1 H its gs ->
    forall Γ0 Ψ, Γ1 = Ψ ++ Γ0 -> gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵐ H ≈ H ->
    forall Φg, gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φg ++ Ψ ≈ body_ctx Φg ++ Ψ ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx (gens_append Φg (List.length (body_ctx Φg)) gs) ++ Ψ ≈
                                body_ctx (gens_append Φg (List.length (body_ctx Φg)) gs) ++ Ψ.
Proof.
  induction 1 as [| Γ1 H d pv its gs _ IH | Γ1 H n d pv ra A om its gs Hm _ IH | Γ1 H n d pv R its gs Hm Hmod _ IH
                 | Γ1 H n d pv R A Rm its gs Hm Hty Hmd _ IH ];
    intros Γ0 Ψ -> HH Φg HX; cbn [gens_append generated_item_entry]; try exact HX.
  all: pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- app_assoc in HC.
  all: pose proof (wf_wk_shiftn_app' _ _ _ _ HC) as Hw.
  - (* the module itself *)
    assert (HU0 : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵘ gu_mk nil (md_alias H) ≈ gu_mk nil (md_alias H))
      by (eapply wf_unit_eq_alias with (param_level := 0);
          [ apply wf_ext_eq_nil; gen_presups; assumption | constructor | constructor | exact HH | exact HH
          | exact (params_relevant_nil _ _ _ 0) | exact (params_relevant_nil _ _ _ 0) ]).
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HU0 Hw) as HU1.
    cbn [gentry_wk].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_mod pv (gunit_wk (gu_mk nil (md_alias H)) (wk_shiftn (length (body_ctx Φg)))))))).
    apply (IH Γ0 Ψ eq_refl HH).
    cbn [body_ctx app]; apply wf_ext_eq_mod; [ exact HX | rewrite <- app_assoc; exact HU1 | rewrite <- app_assoc; exact HU1 ].
  - (* a term member: a definition of it, at its type *)
    destruct (member_wf _ _ _ _ _ HH Hm eq_refl) as ([Srt HS HA] & _ & HM).
    pose proof (wk_preserves_sort _ _ _ _ _ _ _ HA HS Hw) as HA1.
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ HM Hw) as HM1.
    cbn [gentry_wk option_map].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_def true pv ra A[wk_shiftn (length (body_ctx Φg))]ʷ
                                               (Some (a_mem H n)[wk_shiftn (length (body_ctx Φg))]ʷ))))).
    apply (IH Γ0 Ψ eq_refl HH).
    rewrite app_assoc in HA1, HM1; cbn [body_ctx app].
    eapply wf_ext_eq_def_same; [ exact HX | exact HA1 | exact HS | exact HA1 | exact HM1 | exact HM1 ].
  - (* a module member: an alias of it *)
    pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    destruct (desc_ok_tele _ _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Hmod) as [T HT].
    assert (Hmt : mdesc_mod_tele R = Some T) by (unfold mdesc_mod_tele; rewrite (mdesc_is_mod_mod _ Hmod); exact HT).
    assert (HE : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵐ me_mem H n ≈ me_mem H n)
      by (eapply wf_me_mem; [ exact HH | exact Hm | exact Hmt | exact Hm | exact Hmt ]).
    assert (HU0 : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵘ gu_mk nil (md_alias (me_mem H n)) ≈ gu_mk nil (md_alias (me_mem H n)))
      by (eapply wf_unit_eq_alias with (param_level := 0);
          [ apply wf_ext_eq_nil; gen_presups; assumption | constructor | constructor | exact HE | exact HE
          | exact (params_relevant_nil _ _ _ 0) | exact (params_relevant_nil _ _ _ 0) ]).
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HU0 Hw) as HU1.
    cbn [gentry_wk].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_mod pv (gunit_wk (gu_mk nil (md_alias (me_mem H n))) (wk_shiftn (length (body_ctx Φg)))))))).
    apply (IH Γ0 Ψ eq_refl HH).
    cbn [body_ctx app]; apply wf_ext_eq_mod; [ exact HX | rewrite <- app_assoc; exact HU1 | rewrite <- app_assoc; exact HU1 ].
  - (* a member with a term part and a module part: a definition with a
       module part, its term the selection, its module the alias of it *)
    destruct (member_wf _ _ _ _ _ HH Hm Hty) as ([Srt HS HA] & _ & HM).
    pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    pose proof (desc_ok_mod _ _ Hg _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Hmd) as Hok.
    destruct (desc_ok_tele _ _ _ _ Hok (mdesc_mod_is_mod _ _ Hmd)) as [T HT].
    assert (Hmt : mdesc_mod_tele R = Some T) by (unfold mdesc_mod_tele; rewrite Hmd; exact HT).
    assert (HE : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵐ me_mem H n ≈ me_mem H n)
      by (eapply wf_me_mem; [ exact HH | exact Hm | exact Hmt | exact Hm | exact Hmt ]).
    assert (HU0 : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵘ gu_mk nil (md_alias (me_mem H n)) ≈ gu_mk nil (md_alias (me_mem H n)))
      by (eapply wf_unit_eq_alias with (param_level := 0);
          [ apply wf_ext_eq_nil; gen_presups; assumption | constructor | constructor | exact HE | exact HE
          | exact (params_relevant_nil _ _ _ 0) | exact (params_relevant_nil _ _ _ 0) ]).
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HU0 Hw) as HU1.
    (* a member with a module part is relevant: its type is of a large universe *)
    destruct (desc_ok_ty_at _ _ _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Hty) as [iA HAi].
    assert (Hr : mdesc_relevance R = relevant) by (destruct R; cbn in Hmd |- *; congruence).
    rewrite Hr in HAi; cbn [relevance_sort] in HAi.
    clear HA HS; rename HAi into HA.
    pose proof (wk_preserves_typ _ _ _ _ _ _ _ HA Hw) as HA1.
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ HM Hw) as HM1.
    cbn [gentry_wk].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_def_mod pv A[wk_shiftn (length (body_ctx Φg))]ʷ
                                               (a_mem H n)[wk_shiftn (length (body_ctx Φg))]ʷ
                                               (gunit_wk (gu_mk nil (md_alias (me_mem H n))) (wk_shiftn (length (body_ctx Φg)))))))).
    apply (IH Γ0 Ψ eq_refl HH).
    rewrite app_assoc in HA1, HM1; cbn [body_ctx app].
    eapply wf_ext_eq_dm; [ exact HX | exact HA1 | apply wf_exp_eq_refl; exact HA1 | exact HM1 | apply wf_exp_eq_refl; exact HM1
                         | exact HA1 | exact HM1 | rewrite <- app_assoc; exact HU1 | rewrite <- app_assoc; exact HU1 ].
Qed.

(** An open's entries, after the body before it. *)
Corollary gens_ext_wf : forall Γ0 Ψ Φx H its gs,
    items_gen gc_deps gc_stack (body_ctx Φx ++ Ψ ++ Γ0) H its gs ->
    gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Ψ ++ Γ0 ⊢ᵐ H ≈ H ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φx ++ Ψ ≈ body_ctx Φx ++ Ψ ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx (gens_append Φx 0 gs) ++ Ψ ≈ body_ctx (gens_append Φx 0 gs) ++ Ψ.
Proof.
  intros * Hg HH HX.
  rewrite gens_body_ctx_base, <- app_assoc.
  rewrite app_assoc in Hg, HH.
  exact (gens_ext_wf_gen _ _ _ _ Hg Γ0 (body_ctx Φx ++ Ψ) eq_refl HH gm_nil HX).
Qed.

(** ** The Sorts of a Body's Definitions

    [body_tags Γ Φ L]: the type of every term part of the body [Φ] over [Γ]
    is, in the context of the entries before it, of the sort its relevance
    tag says, at the level [L] if relevant ([entry_relevance]).  This is
    what the premises on [entry_sort] of the unit rules need. *)
Definition body_tags (Γ : ctx) (Φ : gmod) (L : nat) : Prop :=
  forall y Φ0 E A M, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    (body_ctx Φ0 ++ Γ)%list ⊢ A : relevance_sort (entry_relevance E) Typeω@L.

(** A type of the sort at a tag is one at every larger level. *)
Lemma relevance_sort_lift : forall Γ A r i j,
    Γ ⊢ A : relevance_sort r Typeω@i -> i <= j -> Γ ⊢ A : relevance_sort r Typeω@j.
Proof. intros * HA Hij; destruct r; cbn [relevance_sort] in *; [ eapply lift_exp_ge; eassumption | exact HA ]. Qed.

Lemma body_tags_mono : forall Γ Φ L L', body_tags Γ Φ L -> L <= L' -> body_tags Γ Φ L'.
Proof. intros * HT HL y Φ0 E A M Hp HE; eapply relevance_sort_lift; [ exact (HT _ _ _ _ _ Hp HE) | exact HL ]. Qed.

Lemma body_tags_nil : forall Γ L, body_tags Γ gm_nil L.
Proof. intros * y Φ0 E A M Hp; discriminate. Qed.

(** An entry added, its term part, if any, of the sort at its tag. *)
Lemma body_tags_ext : forall Γ Φ x E L,
    body_tags Γ Φ L ->
    (forall A M, entry_tm E = Some (A, M) -> (body_ctx Φ ++ Γ)%list ⊢ A : relevance_sort (entry_relevance E) Typeω@L) ->
    body_tags Γ (gm_ext Φ x E) L.
Proof.
  intros * HT HE y Φ0 E0 A M Hp HE0; cbn [gm_prefix_upto] in Hp.
  destruct (String.eqb y x); [ injection Hp as HΦ0 _ HE1; subst Φ0 E0; exact (HE _ _ HE0) | exact (HT _ _ _ _ _ Hp HE0) ].
Qed.

(** The entries an open of a well-formed module generates are of the sorts
    at their tags: a definition's is the member's ([desc_ok_ty_at]), a
    definition with a module part is relevant.  Read past the [k] entries
    generated before, a weakening of the context the module is read in. *)
Lemma body_tags_gens : forall Γ1 H its gs, items_gen gc_deps gc_stack Γ1 H its gs ->
    forall Γ Φ, Γ1 = (body_ctx Φ ++ Γ)%list -> gc_deps ⍮ gc_stack ⍮ Γ1 ⊢ᵐ H ≈ H ->
    forall Φg Ψk L, body_ctx Φg = (Ψk ++ body_ctx Φ)%list ->
    ⊢ (body_ctx (gens_append Φg (List.length Ψk) gs) ++ Γ)%list ->
    body_tags Γ Φg L ->
    exists L', body_tags Γ (gens_append Φg (List.length Ψk) gs) L'.
Proof.
  induction 1 as [Γ1 H | Γ1 H d pv its gs _ IH | Γ1 H n d pv ra A om its gs Hm _ IH | Γ1 H n d pv R its gs Hm Hmod _ IH
                 | Γ1 H n d pv R A Rm its gs Hm Hty Hmd _ IH ];
    intros Γ Φ -> HH Φg Ψk L HΦg HC HT; cbn [gens_append generated_item_entry] in *; [ exists L; exact HT | .. ].
  (** The context of the entry being generated is well formed. *)
  all: assert (HCg : ⊢ (body_ctx Φg ++ Γ)%list)
         by (match type of HC with ⊢ (body_ctx (gens_append ?Φ' ?k' ?gs') ++ _)%list =>
               destruct (gens_append_body_ctx gs' Φ' k') as [Ψ' HΨ']; rewrite HΨ' in HC end;
             cbn [body_ctx gentry_wk option_map] in HC; rewrite <- List.app_assoc in HC;
             exact (ctx_decomp_tail (ctx_app_wf_tail _ _ _ _ HC))).
  all: assert (Hw : (body_ctx Φg ++ Γ)%list ⊢ʷ wk_shiftn (List.length Ψk) : (body_ctx Φ ++ Γ)%list)
         by (rewrite HΦg, <- List.app_assoc; apply wf_wk_shiftn_app'; rewrite List.app_assoc, <- HΦg; exact HCg).
  - (** The module itself: no term part. *)
    change (S (List.length Ψk)) with (List.length (ce_mod (gunit_wk (gu_mk nil (md_alias H)) (wk_shiftn (List.length Ψk))) :: Ψk)).
    eapply IH; [ reflexivity | exact HH | cbn [body_ctx]; rewrite HΦg; reflexivity | exact HC |].
    apply body_tags_ext; [ exact HT | intros * [=] ].
  - (** A term member, at the sort of its tag. *)
    pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    destruct (desc_ok_ty_at _ _ _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) eq_refl) as [i HAi]; cbn [mdesc_relevance] in HAi.
    assert (HA1 : (body_ctx Φg ++ Γ)%list ⊢ A[wk_shiftn (List.length Ψk)]ʷ : relevance_sort ra Typeω@i)
      by (destruct ra; cbn [relevance_sort] in *; [ exact (wk_preserves_typ _ _ _ _ _ _ _ HAi Hw)
                                                  | exact (wk_preserves_sort _ _ _ _ _ _ _ HAi type_sort_prop Hw) ]).
    set (E1 := gentry_wk (ge_def true pv ra A (Some (a_mem H n))) (wk_shiftn (List.length Ψk))) in *.
    change (S (List.length Ψk)) with (List.length (ce_def A[wk_shiftn (List.length Ψk)]ʷ (a_mem H n)[wk_shiftn (List.length Ψk)]ʷ :: Ψk)).
    eapply IH; [ reflexivity | exact HH | unfold E1; cbn [body_ctx gentry_wk option_map]; rewrite HΦg; reflexivity | exact HC |].
    apply body_tags_ext; [ exact (body_tags_mono _ _ _ _ HT (Nat.le_max_l L i)) |].
    intros A' M' HE; unfold E1 in HE; cbn [gentry_wk option_map entry_tm] in HE; injection HE as <- <-.
    unfold E1; cbn [entry_relevance gentry_wk].
    exact (relevance_sort_lift _ _ _ _ _ HA1 (Nat.le_max_r L i)).
  - (** A module member: no term part. *)
    change (S (List.length Ψk)) with (List.length (ce_mod (gunit_wk (gu_mk nil (md_alias (me_mem H n))) (wk_shiftn (List.length Ψk))) :: Ψk)).
    eapply IH; [ reflexivity | exact HH | cbn [body_ctx]; rewrite HΦg; reflexivity | exact HC |].
    apply body_tags_ext; [ exact HT | intros * [=] ].
  - (** A member with both parts: relevant. *)
    pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    destruct (desc_ok_ty_at _ _ _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Hty) as [i HAi].
    assert (Hr : mdesc_relevance R = relevant) by (destruct R; cbn in Hmd |- *; congruence).
    rewrite Hr in HAi; cbn [relevance_sort] in HAi.
    pose proof (wk_preserves_typ _ _ _ _ _ _ _ HAi Hw) as HA1.
    set (E1 := gentry_wk (ge_def_mod pv A (a_mem H n) (gu_mk nil (md_alias (me_mem H n)))) (wk_shiftn (List.length Ψk))) in *.
    change (S (List.length Ψk))
      with (List.length (ce_dm A[wk_shiftn (List.length Ψk)]ʷ (a_mem H n)[wk_shiftn (List.length Ψk)]ʷ
                           (gunit_wk (gu_mk nil (md_alias (me_mem H n))) (wk_shiftn (List.length Ψk))) :: Ψk)).
    eapply IH; [ reflexivity | exact HH | unfold E1; cbn [body_ctx gentry_wk]; rewrite HΦg; reflexivity | exact HC |].
    apply body_tags_ext; [ exact (body_tags_mono _ _ _ _ HT (Nat.le_max_l L i)) |].
    intros A' M' HE; unfold E1 in HE; cbn [gentry_wk entry_tm] in HE; injection HE as <- <-.
    unfold E1; cbn [entry_relevance gentry_wk relevance_sort].
    eapply lift_exp_ge; [| exact HA1 ]; lia.
Qed.

End Fixed_GCtx.
