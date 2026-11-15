(** * What Well-Formed Module Expressions Look Up

    A member a well-formed module expression looks up is typed, at the
    type the lookup reads, and so is its δ-reduct ([member_wf]): what the
    lookup reads is typed ([mem_desc_ok], [desc_ok_ty]), so the premises of
    [wf_mem] hold of it.  The outermost parameter a module still takes is a
    type ([mtele_head_wf]).  The checker reads both off the lookup, without
    checking anything again; the entries a local open stores it checks as
    a body ([alg_body_open]), at the sorts of their tags ([body_tags]). *)

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
    (exists S, type_sort S /\ Γ ⊢ A : S) /\ (forall M, mdesc_reduct R = Some M -> Γ ⊢ M : A) /\ Γ ⊢ a_mem H x : A.
Proof.
  intros * HH Hm Ht.
  pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hv.
  destruct (desc_ok_ty_sorted _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht) as [Hi HM].
  split; [ exact Hi | split; [ exact HM | exact (wf_mem_desc _ _ _ _ _ _ _ HH Hm Ht) ] ].
Qed.

(** The next parameter of a closed telescope given typed arguments, at
    them, is a type of a universe or of levels, as a module's parameters
    are relevant. *)
Lemma args_ok_next : forall Γ T Ns C T1' l,
    args_ok gc_deps gc_stack Γ T Ns -> all_assumptions T -> ctx_scoped 0 T -> ⊢ T ->
    params_evaluated gc_deps gc_stack nil T l ->
    tele_view (List.firstn (length T - length Ns) T) = Some (C, T1') ->
    param_typed gc_deps gc_stack Γ C[sb_of_list Id Ns] l.
Proof.
  intros * [T1 T2 -> Hl Ha2 Hs2 HT2 HN] Ha Hs HT HR Hv.
  replace (firstn (length (T1 ++ T2) - length Ns) (T1 ++ T2)) with T1 in Hv
    by (rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
  apply List.Forall_app in Ha as [Ha1 _].
  destruct (tele_view_ass _ _ _ Ha1 Hv) as [κ ->].
  pose proof (HR T1' κ C T2 ltac:(rewrite <- List.app_assoc; reflexivity)) as HC; rewrite List.app_nil_r in HC.
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha2 HT2 (eq_sym Hl) HN) as Hσ.
  destruct HC as [HC | HC]; [ left | right ];
    pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs2 HC HT2) as HC';
    exact (sub_preserves_sort _ _ _ _ _ _ _ HC' ltac:(constructor) Hσ).
Qed.

(** The outermost parameter a typed module description still takes is a
    type of a relevant sort: of a universe or of levels. *)
Lemma desc_ok_tele_head : forall Γ Rm T B T1,
    desc_ok gc_deps gc_stack Γ Rm -> mdesc_tele Rm = Some T -> tele_view T = Some (B, T1) ->
    exists Srt, evaluated_sort Srt /\ Γ ⊢ B : Srt.
Proof.
  intros * HR Ht Hv.
  inversion HR as [Γ0 A om HA HM | Γ0 Δ Φw Φ lΔ HΦ Hn Hent HaΔ Hsh Hnd HUw HRΔ
                  | Γ0 Θ' T0 Φ Ns Θ0 Ξ0 p lΘ Hg0 Hsub0 Hloc Ha0 Hs0 HT0 HΘ' Hargs HaΘ HRΘ |];
    subst; cbn in Ht; try discriminate.
  - (* an open module: its parameters *)
    injection Ht as <-.
    unfold tele_view in Hv; destruct (tele_open_split _ _ _ Hv) as (τ & Es).
    destruct (tele_split_ass_eq _ _ _ _ HaΔ Es) as [EΔ _].
    exact (param_typed_evaluated _ _ _ _ _ (HRΔ _ _ _ nil EΔ)).
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
      exact (param_typed_evaluated _ _ _ _ _ (HRΘ _ _ _ nil EΘ)).
    + destruct (tele_open_app_inr _ _ _ _ _ Es Hv) as (B0 & T0' & Ho & ->).
      fold (tele_view (tele_sub (List.firstn (length T0 - length Ns) T0) (sb_of_list Id Ns))) in Ho.
      rewrite tele_view_sub in Ho.
      destruct (tele_view (List.firstn (length T0 - length Ns) T0)) as [[C T1'] |] eqn:HvC; cbn in Ho; [| discriminate ].
      injection Ho as <- _.
      (* the stored telescope is relevant where it is stored, so here *)
      pose proof (ctx_wf_gctx _ _ _ HΘ') as Hg.
      destruct (loc_params_evaluated _ _ _ _ _ (gctx_valid_syn _ _ Hg0) Hloc) as [lT HRT].
      pose proof (params_evaluated_embed _ _ _ _ _ _ _ (Build_gctx_embedding _ _ _ _ Hg Hsub0) HRT) as HRT'.
      destruct (param_typed_evaluated _ _ _ _ _ (args_ok_next _ _ _ _ _ _ Hargs Ha0 Hs0 HT0 HRT' HvC)) as (Srt & HS & HC).
      exists Srt; split; [ exact HS |].
      exact (sub_preserves_sort _ _ _ _ _ _ _ HC (evaluated_sort_type_sort _ HS) Hsw).
Qed.

(** The outermost parameter a well-formed module expression still takes is
    a type of a relevant sort. *)
Corollary mtele_head_wf : forall Γ H R T B T1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ H R ->
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    exists Srt, evaluated_sort Srt /\ Γ ⊢ B : Srt.
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

(** ** The Sorts of a Body's Definitions

    [body_tags Γ Φ L]: the type of every term part of the body [Φ] over [Γ]
    is, in the context of the entries before it, of the sort of its kind
    ([entry_kind]) at the universe at the level [L] ([abs_kind_sort]): a
    type of that universe, a proposition, or a type of levels.  This is
    what the premises on [entry_sort] of the unit rules need: that sort is
    a sort of the entry's kind ([sort_kind_abs_kind_sort]). *)
Definition body_tags (Γ : ctx) (Φ : gmod) (L : nat) : Prop :=
  forall y Φ0 E A M, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    (body_ctx Φ0 ++ Γ)%list ⊢ A : abs_kind_sort (entry_kind E) Typeω@L.

Lemma body_tags_mono : forall Γ Φ L L', body_tags Γ Φ L -> L <= L' -> body_tags Γ Φ L'.
Proof.
  intros * HT HL y Φ0 E A M Hp HE.
  exact (abs_kind_sort_lift _ _ _ _ _ (HT _ _ _ _ _ Hp HE) HL).
Qed.

Lemma body_tags_nil : forall Γ L, body_tags Γ gm_nil L.
Proof. intros * y Φ0 E A M Hp; discriminate. Qed.

(** An entry added, its term part, if any, of the sort of its kind. *)
Lemma body_tags_ext : forall Γ Φ x E L,
    body_tags Γ Φ L ->
    (forall A M, entry_tm E = Some (A, M) ->
       (body_ctx Φ ++ Γ)%list ⊢ A : abs_kind_sort (entry_kind E) Typeω@L) ->
    body_tags Γ (gm_ext Φ x E) L.
Proof.
  intros * HT HE y Φ0 E0 A M Hp HE0; cbn [gm_prefix_upto] in Hp.
  destruct (String.eqb y x); [ injection Hp as HΦ0 _ HE1; subst Φ0 E0; exact (HE _ _ HE0) | exact (HT _ _ _ _ _ Hp HE0) ].
Qed.

(** A fragment with no open, its term parts of the sorts at their tags
    over the body it is grafted on, keeps the body's tags: what an open
    stores ([alg_body_open]). *)
Lemma body_tags_graft : forall Γ Φx Φg L L', gm_noopen Φg ->
    body_tags Γ Φx L -> body_tags (body_ctx Φx ++ Γ)%list Φg L' -> body_tags Γ (gm_graft Φx Φg) (max L L').
Proof.
  intros * Hn HT HTg y Φ0 E A M Hp HE.
  rewrite (gm_prefix_upto_graft _ _ _ Hn) in Hp.
  destruct (gm_prefix_upto Φg y) as [P |] eqn:EP.
  - injection Hp as HP; destruct (gm_prefix_upto_ext _ _ _ EP) as (P0 & E0 & ->); cbn [gm_graft] in HP.
    injection HP as <- <-.
    pose proof (gm_noopen_prefix_upto _ _ _ Hn EP) as HnP; cbn [gm_noopen] in HnP.
    rewrite (body_ctx_graft _ _ HnP), <- List.app_assoc.
    exact (abs_kind_sort_lift _ _ _ _ _ (HTg _ _ _ _ _ EP HE) (Nat.le_max_r L L')).
  - exact (abs_kind_sort_lift _ _ _ _ _ (HT _ _ _ _ _ Hp HE) (Nat.le_max_l L L')).
Qed.

End Fixed_GCtx.
