(** * Valid Global Contexts

    What an entry of a global context is worth at a target
    ([valid_entry], [valid_mod_tele], [valid_ind_decl_entry]), and the
    embedding that the validity of every entry gives: what the source files
    and has open is valid at the target, read from the source
    ([valid_filed_mods_of_valid]), and so are its declarations
    ([valid_gctx_embedding_of], [valid_gctx_embedding_of_bodies_valid]).  A unit valid read at a global
    context stays valid read at a bigger one ([valid_unit_grow_all]).
    Nothing here uses the fundamental theorem; that each entry is valid
    where it is checked, and so that a well-formed global context embeds
    soundly into itself, is proved with it in [FundamentalTheorem.v]. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import
  MemberLemmas MemberWf Modules Paths DescTyping LookupSound.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Completeness Require Import ContextCases FunctionCases LetCases LevelCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import
  SubtypingCases PropCases UniverseCases VariableCases LogicalRelation UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Con.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Elim.
From Mctt.Core.Completeness Require Import IndCases ElimCases.
From Mctt.Core.Completeness.Inductives Require Import Iota.
From Mctt.Core.Completeness Require Import IotaCases.
From Mctt.Core.Completeness.Modules Require Import ModuleVal Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Inductives Require Import Decl Model.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Mem Canon App Sel.
From Mctt.Core.Completeness Require Import ModuleCases.
From Mctt.Core.Syntactic Require Import Records.
From Mctt.Core.Syntactic.System.Records Require Import Syntax.
From Mctt.Core.Completeness.Records Require Import Model.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** ** 1. Valid units, read at a bigger global context *)

Section Grow.
  Context {GC : GCtx}.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg1 : ⊢ᵍ Θ1 ⍮ Ξ1.
  Hypothesis He : gctx_embedding Θ1 Ξ1 Θ2 Ξ2.

  Lemma valid_unit_grow_all :
    (forall Γ K, valid_unit Θ1 Ξ1 Γ K -> valid_unit Θ2 Ξ2 Γ K) /\ (forall Γ H, valid_modexp Θ1 Ξ1 Γ H -> valid_modexp Θ2 Ξ2 Γ H).
  Proof.
    pose proof He as [Hg2 Hs].
    destruct (gctx_embedding_preserves_wf _ _ _ _ He) as (_ & _ & _ & _ & _ & _ & Hwm & _).
    apply valid_unit_modexp_ind.
    - intros Γ p T Φ Ns Hw Hgl HΓ Hsa.
      destruct (gc_loc_grow _ _ _ _ Hg2 Hs _ _ _ Hgl) as (Φ2 & Hgl2 & _).
      exact (valid_unit_filed _ _ _ _ _ _ _ (Hwm _ _ _ Hw) Hgl2 HΓ Hsa).
    - intros Γ Δ Φ Φx Hw Hx HΔ HΔr HΓ HC Hsv _ IHsl Hsh Hshx HU Hopv _ IHops.
      exact (valid_unit_body _ _ _ _ _ _ (Hwm _ _ _ Hw) (gctx_embedding_body_xp _ _ _ _ Hg1 He _ _ _ Hx) HΔ HΔr HΓ HC Hsv IHsl Hsh Hshx HU Hopv IHops).
    - intros Γ Δ E Hw HΔ HΔr HΓ HΔΓ HU HE _ IHE.
      exact (valid_unit_alias _ _ _ _ _ (Hwm _ _ _ Hw) HΔ HΔr HΓ HΔΓ HU HE IHE).
    - intros Γ H R Rm K RK Hw HmH HmodH HHK _ IHK HmK HmodK.
      destruct (gctx_embedding_mdenote _ _ _ _ Hg1 He _ _ _ HmH) as (R2 & HmH2 & Hd).
      destruct (mdesc_grows_mod _ _ _ _ _ _ _ Hd HmodH) as (Rm2 & HmodH2 & Hdm).
      destruct (gctx_embedding_mdenote _ _ _ _ Hg1 He _ _ _ HmK) as (RK2 & HmK2 & HdK).
      destruct (mdesc_grows_mod _ _ _ _ _ _ _ HdK HmodK) as (Rm2' & HmodK2 & Hdm').
      pose proof (mdesc_grows_functional _ _ _ _ _ _ _ Hdm Hdm') as <-.
      exact (valid_modexp_intro _ _ _ _ _ _ _ _ (Hwm _ _ _ Hw) HmH2 HmodH2 HHK IHK HmK2 HmodK2).
  Qed.

  Corollary valid_unit_grow : forall Γ K, valid_unit Θ1 Ξ1 Γ K -> valid_unit Θ2 Ξ2 Γ K.
  Proof. exact (proj1 valid_unit_grow_all). Qed.
End Grow.

(** ** 2. Closed units, in any context *)

Section Closed.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.

  Lemma rel_wk_to_nil : forall Γ, ⊨ Γ -> Γ ⊨ʷ (wk_shiftn (length Γ)) : ⋅.
  Proof.
    intros * HΓ.
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
    eapply (rel_wk_under_ctx_intro (R' := fun _ _ => True)); [ exact HR | exact per_ctx_env_nil_true | | intros x Hx; cbn in Hx; lia
                                                             | intros ? ? _ x Hx; cbn in Hx; lia ].
    constructor; [ exact (wk_mono_shiftn _) | intros; exact I ].
  Qed.

  Lemma valid_unit_closed_weaken : forall Γ U, valid_unit Θm Ξm ⋅ (me_lit U) -> gunit_scoped 0 U -> ⊨ Γ -> ⊢ Θm ⍮ Ξm ⍮ Γ ->
      valid_unit Θm Ξm Γ (me_lit U).
  Proof.
    intros * HK HU HΓ Hw.
    assert (Hw' : ⊢ Θm ⍮ Ξm ⍮ Γ ++ ⋅) by (rewrite app_nil_r; exact Hw).
    pose proof (wf_wk_shiftn_app' _ _ _ _ Hw') as Hφ; rewrite app_nil_r in Hφ.
    pose proof (valid_unit_gsub Hgw _ _ Hgm Hsub _ _ _ _ HK (gsub_wk _ _ _ (rel_wk_to_nil _ HΓ) HΓ rel_ctx_wf_nil)
                  (wf_sub_of_wk _ _ _ _ _ Hφ)) as H.
    cbn [modexp_sub] in H.
    rewrite (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id))) U 0) in H by first [ exact HU | intros; lia ]; exact H.
  Qed.
End Closed.

(** ** 3. Descriptions abstracted over a telescope, at arguments *)

Lemma mdesc_reduct_sub_map : forall R σ, mdesc_reduct (mdesc_sub R σ) = option_map (fun M => M[σ]) (mdesc_reduct R).
Proof.
  intros R σ; destruct (mdesc_reduct R) as [M |] eqn:E; [ exact (mdesc_reduct_sub _ _ _ E) |].
  destruct R as [r A [M |] | | | ]; cbn in E |- *; congruence.
Qed.

(** An abstracted description, substituted under its parameters: the term
    part and the reduct, substituted. *)
Lemma mdesc_up_sub_parts : forall Θa R σ,
    (forall A, mdesc_type (mdesc_up Θa R) = Some A ->
       mdesc_type (mdesc_up (tele_sub Θa σ) (mdesc_sub R (sb_qn (length Θa) σ))) = Some A[σ]) /\
    mdesc_reduct (mdesc_up (tele_sub Θa σ) (mdesc_sub R (sb_qn (length Θa) σ))) = option_map (fun M => M[σ]) (mdesc_reduct (mdesc_up Θa R)).
Proof.
  intros Θa R σ; split.
  - intros A Ht; destruct (mdesc_type_up_inv _ _ _ Ht) as (A0 & Ht0 & ->).
    rewrite ctx_pi_sub, <- (mdesc_kind_sub R (sb_qn (length Θa) σ)); apply mdesc_type_up, mdesc_type_sub; assumption.
  - rewrite !mdesc_reduct_up, mdesc_reduct_sub_map; destruct (mdesc_reduct R) as [M |]; cbn; [ rewrite ctx_fn_sub |]; reflexivity.
Qed.

(** A description abstracted over [Θa] and then a telescope [T2], given
    arguments for all of [T2]: its term part and reduct are those of the
    description abstracted over [Θa], instantiated. *)
Lemma mdesc_ats_up_parts : forall Ns T2 Θa R R1,
    tele_ass T2 -> length T2 = length Ns -> mdesc_ats (mdesc_up (Θa ++ T2) R) Ns = Some R1 ->
    (forall A, mdesc_type (mdesc_up Θa R) = Some A -> mdesc_type R1 = Some A[sb_of_list Id Ns]) /\
    mdesc_reduct R1 = option_map (fun M => M[sb_of_list Id Ns]) (mdesc_reduct (mdesc_up Θa R)).
Proof.
  induction Ns as [| N Ns IH]; intros * HT Hl Ha.
  - destruct T2; [| cbn in Hl; discriminate ]; cbn in Ha; injection Ha as <-; rewrite app_nil_r.
    split; [ intros A Ht; rewrite Ht, exp_sub_id; reflexivity |].
    destruct (mdesc_reduct (mdesc_up Θa R)); cbn; rewrite ?exp_sub_id; reflexivity.
  - destruct (List.exists_last (l := T2)) as (T2' & e & ->); [ intros ->; cbn in Hl; discriminate |].
    destruct (tele_ass_app_inv _ _ HT) as [HT' He]; inversion He as [| ? ? (κ & B & ->) _]; subst.
    rewrite List.length_app in Hl; cbn in Hl.
    cbn [mdesc_ats] in Ha; rewrite app_assoc, mdesc_at_up, tele_sub_app, List.length_app, sb_qn_plus in Ha.
    set (σ := sb_qn (length T2') (Id,,N)) in Ha.
    destruct (IH _ _ _ _ (tele_ass_sub _ _ HT') ltac:(rewrite length_tele_sub; lia) Ha) as [Hty Hred].
    destruct (mdesc_up_sub_parts Θa R σ) as [Hty0 Hred0].
    assert (Hσ : forall M, M[σ][sb_of_list Id Ns] = M[sb_of_list Id (N :: Ns)]).
    { intros M; subst σ; cbn [sb_of_list]; rewrite exp_sub_sub; apply exp_sub_sb_eq.
      replace (length T2') with (length Ns) by lia.
      etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ]. }
    split.
    + intros A Ht; rewrite (Hty _ (Hty0 _ Ht)), Hσ; reflexivity.
    + rewrite Hred, Hred0; destruct (mdesc_reduct (mdesc_up Θa R)); cbn; rewrite ?Hσ; reflexivity.
Qed.

(** ** 4. What an entry is worth at the target *)

(** What an entry other than a body module is worth at [Θ2 ⍮ Ξ2], read from
    [Θs ⍮ Ξs]: a definition, checked over [T], is the [Π] and [λ] over [T]
    of a valid type and of a valid body of it; an alias is a valid unit in
    the empty context, read from any well-formed [Θs ⍮ Ξs].  A definition
    with a module part is valid as its two views, a transparent definition
    and an alias ([ge_valid]), so it asks nothing more here.  The modules
    of inductive and record types are bodies; their declarations are valid
    as [valid_ind_decl_entry] and [valid_record_decl_entry] say. *)

(** A definition of kind [r], of type [A] and body [oM], stored over the
    telescope [T], at [Θ2 ⍮ Ξ2]: [A] and [oM] are the [Π] at [r] and the
    [λ] over [T] of a type over [T] of the sort of [r] ([abs_kind_sort]: a
    universe, [Prop], or the types of levels, as [wf_gentry_def] asks) and
    of a body of it; the [Π]s over [T] into [r] are formed ([pi_kinds]). *)
#[warnings="-cannot-define-projection"]
Record valid_def_entry (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (r : abs_kind) (A : exp) (oM : option exp) : Prop := mk_valid_def_entry
  { (** The type over the telescope *)
    valid_def_entry_type : exp
    (** A universe index: the type is of [Typeω@valid_def_entry_level] at
        [ak_relevant]; at the other kinds the sort does not mention it *)
  ; valid_def_entry_level : nat
    (** The body over the telescope, if any *)
  ; valid_def_entry_body : option exp
    (** The stored type is the [Π] at [r] over the telescope of the type *)
  ; valid_def_entry_type_eq : A = ctx_pi_at r T valid_def_entry_type
    (** The stored body is the [λ] over the telescope of the body *)
  ; valid_def_entry_body_eq : oM = option_map (ctx_fn T) valid_def_entry_body
    (** The type is a valid type of the sort of [r] *)
  ; valid_def_entry_typed : @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (abs_kind_sort r Typeω@valid_def_entry_level)
                              valid_def_entry_type valid_def_entry_type
    (** The body is a valid term of the type *)
  ; valid_def_entry_body_typed : forall M0, valid_def_entry_body = Some M0 ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T valid_def_entry_type M0 M0
    (** The [Π]s over the telescope into [r] are formed: at [ak_level]
        every parameter is a level ([level_sorted_parameters]) *)
  ; valid_def_entry_pi_kinds : forall Δ1 κ B Δ2, T = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r }.

Definition valid_entry (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ r A oM => valid_def_entry Θ2 Ξ2 T r A oM
  | ge_mod _ U => ⊢ᵍ Θs ⍮ Ξs -> @valid_unit (gc_mk Θ2 Ξ2) Θs Ξs ⋅ (me_lit U)
  | ge_ind _ _ _ _ _ => True
  | ge_def_mod _ _ _ _ => True
  | ge_record _ _ _ _ => True
  end.

(** The telescope of a module: valid, of parameters only, and those
    relevant in the PER model, as modules take relevant parameters. *)
Record valid_mod_tele (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop := mk_valid_mod_tele
  { (** The telescope is valid *)
    valid_mod_tele_wf : @rel_ctx_wf (gc_mk Θ2 Ξ2) T
    (** It has parameters only *)
  ; valid_mod_tele_ass : tele_ass T
    (** They are types of a universe at one level *)
  ; valid_mod_tele_evaluated : exists l : nat, @rel_params_evaluated (gc_mk Θ2 Ξ2) nil T l }.

(** A declaration: valid, and the type of each member's type former,
    abstracted over the outer part of its parameters, a type over the inner
    part. *)
Definition valid_ind_decl_entry (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop :=
  @valid_ind_decl (gc_mk Θ2 Ξ2) D /\
  forall k Mk Δ1 Δ2, ind_member D k = Some Mk -> im_params D Mk = Δ1 ++ Δ2 -> exists i,
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Δ2 (Typeω@i) (ctx_pi Δ1 (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)
      (ctx_pi Δ1 (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ).

(** A record declaration: valid. *)
Definition valid_record_decl_entry (Θ2 : gdeps) (Ξ2 : gstack) (R : record_decl) : Prop :=
  @valid_record_decl (gc_mk Θ2 Ξ2) R.

(** ** 5. Syntactic facts about stored bodies *)

Lemma gm_entry_alias_submodule : forall Φ T x pv Δ E,
    gm_entry Φ (x :: nil) = Some (ge_mod pv (gu_mk Δ (md_alias E))) ->
    gm_submodule T Φ x nil = Some (mr_alias (gu_mk Δ (md_alias E))).
Proof.
  induction Φ as [| Φ IH y E0 | Φ IH H its]; intros * He; cbn in He |- *; [ discriminate | | eauto ].
  destruct (String.eqb x y); [| eauto ].
  destruct E0 as [? ? ? ? ? | ? [? [? ? | ?]] | ? ? ? ? | ? ? ? ? | ? ? ?]; try discriminate; injection He as -> -> ->; reflexivity.
Qed.

(** Every prefix of a stored body's path is a stored body. *)
Lemma gc_loc_prefix : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m2 p TΦ, gc_loc Θ Ξ p = Some TΦ ->
    forall m1, q_chain p = m1 ++ m2 -> m1 <> nil -> exists TΦ', gc_loc Θ Ξ (q_abs (q_unit p) m1) = Some TΦ'.
Proof.
  intros Θ Ξ Hg m2; induction m2 as [| z m2 IH] using rev_ind; intros p [T Φ] Hl m1 Hc Hne.
  - rewrite app_nil_r in Hc.
    replace (q_abs (q_unit p) m1) with p by (destruct p; cbn in *; subst; reflexivity); eauto.
  - set (p' := q_abs (q_unit p) (m1 ++ m2)).
    assert (Hp : p = qname_in p' z) by (destruct p; unfold p', qname_in; cbn in *; rewrite Hc, app_assoc; reflexivity).
    pose proof (gc_loc_loc _ _ _ _ _ Hl) as Hl'; rewrite Hp in Hl'.
    destruct (loc_parent _ _ Hg _ _ _ _ Hl') as (T' & Φ' & Hlp).
    pose proof (gc_loc_of_loc _ _ Hg _ _ _ Hlp) as Hgl.
    exact (IH p' _ Hgl m1 eq_refl Hne).
Qed.

(** A stored body is a module. *)
Lemma gc_loc_kind : forall Θ Ξ pl TΦ args, gc_loc Θ Ξ pl = Some TΦ -> dmod_member_kind Θ Ξ (dm_global pl args) nil member_kind_mod.
Proof.
  intros * Hl; apply dmod_member_kind_global_here_mod; unfold gc_loc in Hl; destruct (gc_frame Ξ pl) eqn:Hf; [ right; eauto |].
  destruct TΦ; left; destruct (gc_body_module _ _ _ _ _ Hl); eauto.
Qed.

(** The path of a stored body evaluates to it. *)
Lemma gc_loc_path : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall pl TΦ ρ, gc_loc Θ Ξ pl = Some TΦ ->
    ⟦ qname_mod pl ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global pl nil.
Proof.
  intros * Hg * Hl; apply eval_path_mod; intros m1 m2 Hc Hne; exact (gc_loc_prefix _ _ Hg _ _ _ Hl _ Hc Hne).
Qed.

(** A valid alias unit in the empty context is valid there in the PER model. *)
Lemma valid_unit_alias_rel0 : forall {GC : GCtx} Θs Ξs Ta Ea, valid_unit Θs Ξs ⋅ (me_lit (gu_mk Ta (md_alias Ea))) ->
    ⋅ ⊨ᵐ me_lit (gu_mk Ta (md_alias Ea)) ≈ me_lit (gu_mk Ta (md_alias Ea)).
Proof.
  intros * HK; inversion HK; subst; [ exfalso; eapply me_apps_qname_not_lit; eassumption | assumption ].
Qed.

Lemma entry_member_kind_grows : forall E1 E2, entry_grows E1 E2 -> entry_member_kind E1 = entry_member_kind E2.
Proof.
  intros [b pv r A B | pv [Δ [sm Φ | E']] | pv pq k D Φ | pv Ad Md Ud | pv pr R Φ]
    [b' pv' r' A' B' | pv' [Δ' [sm' Φ' | E'']] | pv' pq' k' D' Φ' | pv' Ad' Md' Ud' | pv' pr' R' Φ'] H; cbn in H |- *;
    try reflexivity; try discriminate; injection H; intros; subst; reflexivity.
Qed.

(** An entry grows only if it is a body module, an inductive type or a
    record type. *)
Lemma entry_grows_eq : forall E1 E2, entry_grows E1 E2 ->
    (forall pv Δ sm Φ, E2 <> ge_mod pv (gu_mk Δ (md_body sm Φ))) -> (forall pv pq k D Φ, E2 <> ge_ind pv pq k D Φ) ->
    (forall pv pr R Φ, E2 <> ge_record pv pr R Φ) -> E1 = E2.
Proof.
  intros [b pv r A B | pv [Δ [sm Φ | E']] | pv pq k D Φ | pv Ad Md Ud | pv pr R Φ]
    [b' pv' r' A' B' | pv' [Δ' [sm' Φ' | E'']] | pv' pq' k' D' Φ' | pv' Ad' Md' Ud' | pv' pr' R' Φ'] H Hb Hi Hr; cbn in H;
    try exact H; exfalso; first [ eapply Hb; reflexivity | eapply Hi; reflexivity | eapply Hr; reflexivity ].
Qed.

Lemma gc_body_loc : forall Θ Ξ p r, gc_body Θ Ξ p = Some r -> exists r', gc_loc Θ Ξ p = Some r'.
Proof. intros * H; unfold gc_loc; destruct (gc_frame Ξ p); eauto. Qed.

(** ** 6. Valid entries make valid global modules *)

(** The group tables of a group of a well-formed source, read at a target
    it embeds into. *)
Lemma grp_tele_ass_of_embedding : forall Θ Ξ Θ2 Ξ2 p G, ⊢ᵍ Θ ⍮ Ξ -> gctx_embedding Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some G ->
    @grp_tele_ass (gc_mk Θ2 Ξ2) G.
Proof.
  intros * Hg He Hlq.
  pose proof (gctx_embedding_resolution _ _ _ _ He) as Hs.
  destruct (decl_of_glookup _ _ _ _ Hg Hlq) as [Hdt _].
  apply (@grp_tele_ass_of_typed (gc_mk Θ2 Ξ2) G (gctx_embedding_preserves_decl_typed _ _ _ _ _ He Hdt)).
  intros * HM Hh Hq2.
  destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (D' & Mk' & Hq & _).
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hq) as Hq'.
  cbn in Hq2; rewrite Hq' in Hq2; injection Hq2 as <-.
  exact (gctx_embedding_preserves_decl_typed _ _ _ _ _ He (proj1 (decl_of_glookup _ _ _ _ Hg Hq))).
Qed.

Section ApplyTele.
  Context {GC : GCtx}.

(** The [λ] over a telescope at an environment, applied to arguments
    related at the telescope, against its body at the telescope's own
    extension of a related environment by them.  An application stores
    each argument at its type's value ([eval_app_fn]), the telescope's
    extension at its type's closure ([env_tele]): the two are related
    through the body's judgment.  The body's type is of an evaluated kind
    [r], each parameter abstractable at [r]. *)
Lemma ctx_fn_apps_tele : forall T Γ RΓ B M r l k, tele_ass T -> ⊨ T ++ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    rel_params_evaluated Γ T l -> (forall Δ1 κ A Δ2, T = Δ1 ++ ce_ass κ A :: Δ2 -> pi_kinds κ r) -> evaluated_kind r ->
    T ++ Γ ⊨ᵗ B ≈ B at k -> rel_type_kind (T ++ Γ) B r -> T ++ Γ ⊨ M : B ->
    forall ρ1 ρ2 ns g m, RΓ ρ1 ρ2 -> per_gargs (rev T) ρ1 ρ1 ns ns -> List.length ns = List.length T ->
      ⟦ ctx_fn T M ⟧ ρ2 ↘ g -> ⟦ M ⟧ env_tele ρ1 (rev T) ns ↘ m ->
      exists v, $*| g & ns | gc_deps ⍮ gc_stack ↘ v /\ per_head B B (env_tele ρ1 (rev T) ns) (env_tele ρ1 (rev T) ns) m v.
Proof.
  induction T as [| e T0 IH] using rev_ind; intros * HTa HC HΓ HTr Hpk Hev HB HBk HM ρ1 ρ2 ns g m Hρ Hg Hl Hgv Hm.
  - destruct ns; cbn in Hl; [| discriminate ]; cbn [List.app ctx_fn rev] in *.
    change (env_tele ρ1 nil nil) with ρ1 in Hm |- *.
    destruct (valid_at _ _ _ _ _ HM HB (ex_intro _ r (conj Hev HBk)) HΓ _ _ Hρ) as (m1 & v1 & a & i & R & Hm1 & Hv1 & Ha & HRa & Hmv).
    functional_eval_rewrite_clear.
    exists g; split; [ constructor |].
    eapply per_head_of; [ exact Ha | exact Ha | exact HRa | exact Hmv ].
  - destruct (tele_ass_app_inv _ _ HTa) as [HTa0 He]; inversion He as [| ? ? (κ & A & ->) _]; subst.
    assert (Hpk0 : forall Δ1 κ' A' Δ2, T0 = Δ1 ++ ce_ass κ' A' :: Δ2 -> pi_kinds κ' r)
      by (intros Δ1 κ' A' Δ2 ->; apply (Hpk Δ1 κ' A' (Δ2 ++ ce_ass κ A :: nil)); rewrite <- app_assoc; reflexivity).
    destruct ns as [| n ns0]; [ rewrite length_app in Hl; cbn in Hl; lia |].
    rewrite length_app in Hl; cbn in Hl; rewrite rev_app_distr in Hg, Hm |- *; cbn [rev List.app] in Hg, Hm |- *.
    inversion Hg; subst.
    rewrite ctx_fn_app in Hgv; cbn [ctx_fn] in Hgv; inversion Hgv; subst.
    match goal with
    | H6 : PER.Definitions.rel_typ _ A ρ1 A ρ1 ?R, H8 : ?R n n, H9 : per_gargs (rev T0) _ _ ns0 ns0, H3 : ⟦ A ⟧ ρ2 ↘ ?a |- _ =>
        rename H6 into HAr; rename H8 into Hn; rename H9 into Hg0; rename H3 into Ha2; rename R into RA0; rename a into a2
    end.
    destruct (rel_params_evaluated_snoc_inv _ _ _ _ _ HTr) as [HAp HT0r].
    pose proof (rel_param_typed_type _ _ _ HAp) as HAt.
    destruct (rel_type_inversion_simple_at HΓ HAt _ _ Hρ) as (a1 & a2' & Ha1 & Ha2' & [RA HRA]).
    pose proof (functional_eval_exp _ _ _ _ Ha2' Ha2) as ->.
    destruct HAr as [x x' Hx Hx' HRx].
    pose proof (functional_eval_exp _ _ _ _ Hx Ha1) as ->; pose proof (functional_eval_exp _ _ _ _ Hx' Ha1) as ->.
    assert (ER : RA0 <~> RA) by (eapply per_univ_elem_right_irrel; [ exact HRx | exact HRA ]).
    pose proof (proj1 (ER n n) Hn) as HnA.
    pose proof (entry_readable_of_elem_closure Ha1 Ha1 HRx Hn) as [Rc _].
    pose proof (entry_readable_of_elem HRA HnA) as [_ Rv].
    change (env_tele ρ1 (ce_ass κ A :: rev T0) (n :: ns0)) with (env_tele (ρ1 ↦ n ⦂ entry_type_closure A ρ1) (rev T0) ns0) in Hm |- *.
    assert (Hext : per_env_extend A A RΓ (ρ1 ↦ n ⦂ entry_type_closure A ρ1) (ρ2 ↦ n ⦂ entry_type_value a2)).
    { apply (mk_per_ctx_env_cons_rel _ _ _ _ (ρ1 ↦ n ⦂ entry_type_closure A ρ1) (ρ2 ↦ n ⦂ entry_type_value a2) Hρ);
        [ eapply per_head_of; [ exact Ha1 | exact Ha2 | exact HRA | exact HnA ] | intros _; eexists; reflexivity
        | intros _; eexists; reflexivity | split; [ exact Rc | cbn; lia ] | split; [ exact Rv | cbn; lia ] ]. }
    pose proof (per_ctx_env_of_typ (κ := κ) HΓ HAt) as HΓA.
    rewrite <- app_assoc in HC, HM, HBk, HB; cbn [List.app] in HC, HM, HBk, HB.
    pose proof (rel_exp_ctx_fn _ _ _ _ _ _ _ HTa0 HC HT0r Hpk0 Hev HB HBk HM) as Hfn.
    destruct (rel_type_ctx_pi _ _ _ _ _ _ HTa0 HC HT0r Hpk0 Hev HB HBk) as [HPt HPr].
    destruct (valid_at _ _ _ _ _ Hfn HPt (ex_intro _ r (conj Hev HPr)) HΓA _ _ Hext)
      as (g1l & g1 & b & j & Rb & Hg1l & Hg1 & Hb & HRb & Hgg).
    destruct (IH _ _ _ _ _ _ _ HTa0 HC HΓA HT0r Hpk0 Hev HB HBk HM _ _ ns0 g1 m Hext Hg0 ltac:(lia) Hg1 Hm) as (v & Hv & Hmv).
    exists v; split; [ econstructor; [ constructor; exact Hg1 | exact Hv ] | exact Hmv ].
Qed.

(** [valid_at] at a type of a universe. *)
Lemma valid_at_universe : forall Δ M A k RΔ, Δ ⊨ M : A -> Δ ⊨ A : Typeω@k -> per_ctx_env RΔ Δ Δ ->
    forall ρ ρ', RΔ ρ ρ' ->
      exists m m' a i R, ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ ⟦ A ⟧ ρ ↘ a /\ per_univ_elem i R a a /\ R m m'.
Proof.
  intros * HM HA HR.
  exact (valid_at _ _ _ _ _ HM (rel_type_of_typ HA) (rel_type_evaluated_of_typ HA) HR).
Qed.

(** A term of a type of a universe over a closed telescope, at the
    telescope's extension by related arguments: its value related to
    itself at the type. *)
Lemma tele_value_self : forall C M A k ns m, ⊨ C -> C ⊨ M : A -> C ⊨ A : Typeω@k ->
    List.length ns = List.length C -> per_gargs (rev C) nil nil ns ns -> ⟦ M ⟧ env_tele nil (rev C) ns ↘ m ->
    per_head A A (env_tele nil (rev C) ns) (env_tele nil (rev C) ns) m m.
Proof.
  intros * HC HM HA Hl Hg Hm.
  destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
  pose proof (gargs_env_rel _ _ _ _ _ _ HRC HC Hl Hg) as Hρ.
  destruct (valid_at_universe _ _ _ _ _ HM HA HRC _ _ Hρ) as (m1 & m1' & a & i & R & Hm1 & Hm1' & Ha & HRa & Hmm).
  functional_eval_rewrite_clear.
  eapply per_head_of; [ exact Ha | exact Ha | exact HRa | exact Hmm ].
Qed.

End ApplyTele.

Section FiledOk.
  Variables (Θm : gdeps) (Ξm : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis He : gctx_embedding Θm Ξm Θ2 Ξ2.
  Hypothesis HΘ : gds_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θm Ξm Θ2 Ξ2 Θm.
  Hypothesis HΞ : gs_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θm Ξm Θ2 Ξ2 Ξm.

  #[local] Instance GC2 : GCtx := gc_mk Θ2 Ξ2.

  Lemma filed_ok_wf : ⊢ᵍ Θ2 ⍮ Ξ2.
  Proof. exact (gctx_embedding_wf _ _ _ _ He). Qed.

  Lemma filed_ok_sub : gc_sub Θm Ξm Θ2 Ξ2.
  Proof. exact (gctx_embedding_resolution _ _ _ _ He). Qed.

  Lemma gc_loc_valid : forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) ->
      valid_mod_tele Θ2 Ξ2 T /\ gm_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θm Ξm Θ2 Ξ2 T Φ.
  Proof.
    intros * Hl; unfold gc_loc in Hl; destruct (gc_frame Ξm p) as [r |] eqn:Hf.
    - injection Hl as ->; unfold gc_frame in Hf.
      destruct (gs_find_tele Ξm p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
      injection Hf as <- <-; exact (gs_valid_find _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ Ef).
    - exact (gc_body_valid _ _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl).
  Qed.

  (** An entry of a stored body, read at both global contexts. *)
  Lemma filed_ok_entry : forall p T Φ x Φ0 E, gc_loc Θm Ξm p = Some (T, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      exists Φ2 E2, gc_loc Θ2 Ξ2 p = Some (T, Φ2) /\ gm_entry Φ2 (x :: nil) = Some E2 /\
        gc_entry Θ2 Ξ2 (qname_in p x) = Some E2 /\ entry_grows E E2 /\
        gc_entry Θm Ξm (qname_in p x) = Some E /\ gm_entry Φ (x :: nil) = Some E.
  Proof.
    intros * Hl Hp.
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0' & E' & Heq & Hent); injection Heq as <- <-.
    pose proof (gc_loc_loc _ _ _ _ _ Hl) as Hlc.
    pose proof (proj2 (loc_entry _ _ Hgm _ _ _ Hlc x E) Hent) as HeE.
    destruct (gc_sub_entry _ _ _ _ _ _ filed_ok_sub HeE) as (E2 & HeE2 & Hgr).
    destruct (gc_loc_grow _ _ _ _ filed_ok_wf filed_ok_sub _ _ _ Hl) as (Φ2 & Hl2 & _ & Hlc2).
    pose proof (proj1 (loc_entry _ _ filed_ok_wf _ _ _ Hlc2 x E2) HeE2) as Hent2.
    exists Φ2, E2; repeat split; assumption.
  Qed.

  (** An alias entry is an alias at the target. *)
  Lemma filed_ok_alias_module : forall p T Φ x Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua ->
      gc_module Θ2 Ξ2 (qname_in p x) = Some (mr_alias Ua).
  Proof.
    intros * Hl Hp HUa.
    destruct (filed_ok_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & Hl2 & Hent2 & HeE2 & Hgr & _).
    assert (HE : E = E2).
    { apply entry_grows_eq; [ exact Hgr | | | ]; intros * ->;
        destruct E as [| ? [? [? ?| ?]] | | | ]; cbn in Hgr, HUa; try discriminate; try contradiction; congruence. }
    subst E2.
    destruct E as [b pv r A B | pv [Ta [sm Φ1 | Ea]] | pv pq k D Φ1 | pv Ad Md [Ta [smd Φd | Ea]] | pv Rr Φr];
      cbn in HUa; try discriminate; injection HUa as <-.
    - destruct (gm_entry_head _ _ _ Hent2) as (z & ip & [= <- <-] & Hin).
      pose proof (gc_loc_loc _ _ _ _ _ Hl2) as Hlc2.
      rewrite qname_in_app, (proj1 (proj2 (proj2 (loc_read _ _ filed_ok_wf _ _ _ Hlc2 _ Hin nil)))).
      exact (gm_entry_alias_submodule _ _ _ _ _ _ Hent2).
    - exact (gc_entry_def_mod_alias _ _ _ _ _ _ _ _ HeE2).
  Qed.

  (** An alias entry is a valid unit in the empty context. *)
  Lemma filed_ok_alias_valid_unit : forall p T Φ x Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua -> valid_unit Θm Ξm ⋅ (me_lit Ua).
  Proof.
    intros * Hl Hp HUa.
    destruct (gc_loc_valid _ _ _ Hl) as [_ Hv].
    pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hp) as HE.
    destruct E as [b pv r A B | pv [Ta [sm Φ1 | Ea]] | pv pq k D Φ1 | pv Ad Md [Ta [smd Φd | Ea]] | pv Rr Φr];
      cbn in HUa; try discriminate; injection HUa as <-; cbn in HE.
    - exact (HE Hgm).
    - exact (proj1 HE Hgm).
  Qed.

  (** An alias entry has its kind at the target: a module, or, for a
      definition with a module part, a member with both parts. *)
  Lemma filed_ok_alias_kind : forall p T Φ x Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua ->
      dmod_member_kind Θ2 Ξ2 (dm_global p nil) (x :: nil) (entry_member_kind E).
  Proof.
    intros * Hl Hp HUa.
    pose proof (filed_ok_alias_module _ _ _ _ _ _ _ Hl Hp HUa) as Hm; rewrite qname_in_app in Hm.
    pose proof (filed_ok_alias_valid_unit _ _ _ _ _ _ _ Hl Hp HUa) as HK.
    destruct (filed_ok_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & _ & _ & HeE2 & Hgr & _).
    assert (HE : E = E2).
    { apply entry_grows_eq; [ exact Hgr | | | ]; intros * ->;
        destruct E as [| ? [? [? ?| ?]] | | | ]; cbn in Hgr, HUa; try discriminate; try contradiction; congruence. }
    subst E2; rewrite qname_in_app in HeE2.
    assert (HUa' : exists Ta Ea, Ua = gu_mk Ta (md_alias Ea))
      by (destruct E as [| pv [Ta [| Ea]] | | pv Ad Md [Ta [| Ea]] |]; cbn in HUa; try discriminate; injection HUa as <-; eauto).
    destruct HUa' as (Ta & Ea & ->).
    pose proof (valid_nil_kind _ _ _ (valid_unit_alias_rel0 _ _ _ _ HK) per_ctx_env_nil_true nil I) as Hk.
    inversion Hk; subst.
    destruct E as [| pv Ue | | pv Ad Md Ud |]; cbn in HUa; try discriminate; cbn [entry_member_kind].
    - eapply dmod_member_kind_global_alias_case; [ exact Hm | right; exact (module_alias_not_dm _ _ _ _ _ _ Hm HeE2) | eassumption ].
    - change member_kind_dm with (dm_of member_kind_mod).
      eapply dmod_member_kind_global_alias_dm; [ exact Hm | right; right; do 4 eexists; exact HeE2 | eassumption ].
  Qed.

  (** Each entry of a stored body has its kind at the target. *)
  Lemma filed_ok_kind : forall p T Φ x Φ0 E, gc_loc Θm Ξm p = Some (T, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      dmod_member_kind Θ2 Ξ2 (dm_global p nil) (x :: nil) (entry_member_kind E).
  Proof.
    intros * Hl Hp.
    destruct (filed_ok_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & Hl2 & Hent2 & HeE2 & Hgr & _).
    pose proof (gc_loc_loc _ _ _ _ _ Hl2) as Hlc2.
    rewrite (entry_member_kind_grows _ _ Hgr).
    pose proof HeE2 as HeE2'; rewrite qname_in_app in HeE2'.
    destruct E2 as [b pv r A B | pv [Δ [sm Φ' | Ea]] | pv pq k D ΦD | pv Ad Md Ud | pv pr Rr ΦR]; cbn [entry_member_kind].
    - apply gc_entry_def in HeE2; rewrite qname_in_app in HeE2.
      eapply dmod_member_kind_global_step; [ right; do 5 eexists; exact HeE2 | right; exact (gc_resolve_def_not_dm _ _ _ _ _ _ _ _ HeE2)
                             | eapply dmod_member_kind_global_here_def; exact HeE2 ].
    - (* a body module: a body stored at its path, which names no member with both parts *)
      destruct (loc_child_mod _ _ filed_ok_wf _ _ _ Hlc2 _ _ _ _ _ Hent2) as [Hb Hm].
      destruct (gc_body_loc _ _ _ _ Hb) as (r & Hr).
      rewrite qname_in_app in Hr, Hm.
      eapply dmod_member_kind_global_step; [ left; eexists; exact Hr | right | exact (gc_loc_kind _ _ _ _ _ Hr) ].
      exact (module_body_not_dm _ _ _ _ Hm (module_entry_no_record _ _ _ _ _ _ Hm HeE2')).
    - assert (HE : E = ge_mod pv (gu_mk Δ (md_alias Ea)))
        by (apply entry_grows_eq; [ exact Hgr | intros * [=] | intros * [=] | intros * [=] ]).
      subst E; exact (filed_ok_alias_kind _ _ _ _ _ _ _ Hl Hp eq_refl).
    - (* an inductive type: a member with both parts, its module a body stored at its path *)
      destruct (gc_body_loc _ _ _ _ (loc_child_ind _ _ filed_ok_wf _ _ _ _ _ _ _ _ _ Hlc2 Hent2)) as (r & Hr).
      rewrite qname_in_app in Hr.
      eapply dmod_member_kind_global_here_dm; [ left | exact Hr ].
      rewrite ind_mlookup_unfold; destruct (gs_find_ind Ξ2 (qname_app p (x :: nil))); [ eexists; reflexivity |].
      destruct (gm_entry_head _ _ _ Hent2) as (z & ip & [= <- <-] & Hin).
      rewrite (proj1 (proj2 (proj2 (loc_read _ _ filed_ok_wf _ _ _ Hlc2 _ Hin nil)))),
        (proj2 (gm_entry_subbody_ind _ T _ _ _ _ _ _ Hent2)).
      eexists; reflexivity.
    - (* a definition with a module part: a member with both parts, by its alias *)
      assert (HE : E = ge_def_mod pv Ad Md Ud)
        by (apply entry_grows_eq; [ exact Hgr | intros * [=] | intros * [=] | intros * [=] ]).
      subst E.
      pose proof (gm_coherent_prefix _ _ _ _ _ (loc_coherent _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) Hp) as (_ & Δ0 & Ea & -> & _).
      exact (filed_ok_alias_kind _ _ _ _ _ _ _ Hl Hp eq_refl).
    - (* a record type: a member with both parts, its module a body stored at its path *)
      destruct (gc_body_loc _ _ _ _ (loc_child_record _ _ filed_ok_wf _ _ _ _ _ _ _ _ Hlc2 Hent2)) as (r & Hr).
      rewrite qname_in_app in Hr.
      eapply dmod_member_kind_global_here_dm; [ right; left | exact Hr ].
      unfold record_lookup; destruct (gs_find_record Ξ2 (qname_app p (x :: nil))); [ eexists; reflexivity |].
      rewrite HeE2'; eexists; reflexivity.
  Qed.

  (** Each body stored below a stored body, the module of no member with a
      term part, is a module at the target. *)
  Lemma filed_ok_sub_kind : forall p x TΦ, gc_loc Θm Ξm (qname_app p (x :: nil)) = Some TΦ ->
      ~ dm_path Θ2 Ξ2 (qname_app p (x :: nil)) ->
      dmod_member_kind Θ2 Ξ2 (dm_global p nil) (x :: nil) member_kind_mod.
  Proof.
    intros * Hl Hdm; destruct TΦ as [T Φ].
    destruct (gc_loc_grow _ _ _ _ filed_ok_wf filed_ok_sub _ _ _ Hl) as (Φ2 & Hl2 & _).
    eapply dmod_member_kind_global_step; [ left; eexists; exact Hl2 | right; exact Hdm | exact (gc_loc_kind _ _ _ _ _ Hl2) ].
  Qed.

  (** Each alias stored in a stored body is a valid unit in any valid context. *)
  Lemma filed_ok_alias : forall p T Φ y Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua ->
      gc_module Θ2 Ξ2 (qname_in p y) = Some (mr_alias Ua) /\
      forall Γ, ⊨ Γ -> ⊢ Θm ⍮ Ξm ⍮ Γ -> valid_unit Θm Ξm Γ (me_lit Ua).
  Proof.
    intros * Hl Hp HUa; split; [ exact (filed_ok_alias_module _ _ _ _ _ _ _ Hl Hp HUa) |].
    intros Γ HΓ Hw.
    pose proof (loc_closed _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as [_ Hc].
    apply (@valid_unit_closed_weaken GC2 filed_ok_wf _ _ Hgm filed_ok_sub); [ exact (filed_ok_alias_valid_unit _ _ _ _ _ _ _ Hl Hp HUa) | | exact HΓ | exact Hw ].
    exact (entry_alias_unit_scoped _ _ _ _ _ _ 0 Hc Hp HUa).
  Qed.

  (** *** Term entries *)

  (** The closed type of a member of an evaluated kind [r], over a
      telescope of relevant parameters abstractable at [r], of a type of
      the sort of [r] over it: a type of kind [r]. *)
  Lemma filed_ok_closed_type : forall T A0 r i l, tele_ass T -> ⊨ T -> rel_params_evaluated ⋅ T l ->
      (forall Δ1 κ B Δ2, T = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r) -> evaluated_kind r ->
      T ⊨ A0 : abs_kind_sort r Typeω@i ->
      exists k, (⋅ ⊨ᵗ ctx_pi_at r T A0 ≈ ctx_pi_at r T A0 at k) /\ rel_type_kind ⋅ (ctx_pi_at r T A0) r.
  Proof.
    intros * HTa HT HTr Hpk Hev HA0.
    destruct (rel_type_at_kind_of_abs_kind_sort _ _ _ _ HA0) as [[iA HA0t] HA0k].
    assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
    assert (HA0t' : T ++ ⋅ ⊨ᵗ A0 ≈ A0 at iA) by (rewrite app_nil_r; exact HA0t).
    assert (HA0k' : rel_type_kind (T ++ ⋅) A0 r) by (rewrite app_nil_r; exact HA0k).
    destruct (rel_type_ctx_pi _ _ _ _ _ _ HTa HT0 HTr Hpk Hev HA0t' HA0k') as [HP HPr]; eauto.
  Qed.

  (** A term member of a type valid at the sort of its kind, each
      parameter abstractable at the kind, with a value: a filed term. *)
  Lemma valid_filed_term_of_value : forall p T x R0 A0 i,
      T ⊨ A0 : abs_kind_sort (mdesc_kind R0) Typeω@i ->
      (forall Δ1 κ B Δ2, T = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ (mdesc_kind R0)) ->
      valid_filed_value p T x R0 A0 -> valid_filed_term p T x R0.
  Proof.
    intros * HA0 Hpk Hv.
    apply mk_valid_filed_term with (valid_filed_term_typ := A0) (valid_filed_term_level := i);
      [ exact HA0 | | intros _; exact Hv | exact Hpk ].
    intros * HT12 Hlen Ha; destruct Hv as [g Hrd _ _].
    destruct (Hrd _ _ _ _ HT12 Hlen Ha) as [Hty [Hn | (M1 & HM1 & HMt & _)]]; split;
      [ exact Hty | left; exact Hn | exact Hty | right; exists M1; split; [ exact HM1 | exact HMt ] ].
  Qed.

  (** The value of a transparent member of an evaluated kind [r], a [λ]
      over the telescope of a valid body: related to itself at the closed
      type, and, applied to arguments, related to the value of its reduct
      at them. *)
  Lemma filed_ok_term_fn : forall T A0 r i l M0 R0,
      tele_ass T -> ⊨ T -> rel_params_evaluated ⋅ T l ->
      (forall Δ1 κ B Δ2, T = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r) -> evaluated_kind r ->
      T ⊨ A0 : abs_kind_sort r Typeω@i -> T ⊨ M0 : A0 ->
      (forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> mdesc_term_part_ats R0 Ns = Some R1 ->
         mdesc_type R1 = Some (ctx_pi_at r T1 A0)[sb_of_list Id Ns] /\
         mdesc_reduct R1 = Some (ctx_fn T1 M0)[sb_of_list Id Ns]) ->
      exists g, ⟦ ctx_fn T M0 ⟧ nil ↘ g /\
      (forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> mdesc_term_part_ats R0 Ns = Some R1 ->
         mdesc_type R1 = Some (ctx_pi_at r T1 A0)[sb_of_list Id Ns] /\
         (mdesc_reduct R1 = None \/
          exists M1, mdesc_reduct R1 = Some M1[sb_of_list Id Ns] /\ T2 ⊨ M1 : ctx_pi_at r T1 A0 /\
            forall ns m, List.length ns = List.length T2 -> per_gargs (rev T2) nil nil ns ns ->
              ⟦ M1 ⟧ env_tele nil (rev T2) ns ↘ m ->
              exists v, $*| g & ns | gc_deps ⍮ gc_stack ↘ v /\
                Dom m ≈ v ∈ per_head (ctx_pi_at r T1 A0) (ctx_pi_at r T1 A0) (env_tele nil (rev T2) ns) (env_tele nil (rev T2) ns))) /\
      rel_self r T A0 g.
  Proof.
    intros * HTa HT HTr Hpk Hev HA0 HM0 Hats.
    destruct (rel_type_at_kind_of_abs_kind_sort _ _ _ _ HA0) as [[iA HA0t] HA0k].
    assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
    assert (HA0t' : T ++ ⋅ ⊨ᵗ A0 ≈ A0 at iA) by (rewrite app_nil_r; exact HA0t).
    assert (HA0k' : rel_type_kind (T ++ ⋅) A0 r) by (rewrite app_nil_r; exact HA0k).
    assert (HM0' : T ++ ⋅ ⊨ M0 : A0) by (rewrite app_nil_r; exact HM0).
    pose proof (rel_exp_ctx_fn _ _ _ _ _ _ _ HTa HT0 HTr Hpk Hev HA0t' HA0k' HM0') as Hfn.
    destruct (rel_type_ctx_pi _ _ _ _ _ _ HTa HT0 HTr Hpk Hev HA0t' HA0k') as [HP HPr].
    destruct (valid_at _ _ _ _ _ Hfn HP (ex_intro _ r (conj Hev HPr)) per_ctx_env_nil_true nil nil I)
      as (g & g' & e & j & E0 & Hg & Hg' & He0 & HE0 & Hgg).
    pose proof (functional_eval_exp _ _ _ _ Hg' Hg) as ->.
    exists g; split; [ exact Hg |]; split; [| exact (mk_rel_self _ _ _ _ j E0 e He0 HE0 Hgg) ].
    intros * -> Hl Ha; destruct (Hats _ _ _ _ eq_refl Hl Ha) as [Hty Hred]; split; [ exact Hty | right ].
    destruct (tele_ass_app_inv _ _ HTa) as [HTa1 HTa2].
    pose proof (rel_params_evaluated_inner _ _ _ _ HTr) as HT1r; rewrite app_nil_r in HT1r.
    pose proof (rel_params_evaluated_outer _ _ _ _ HTr) as HT2r.
    (* each part of the telescope abstractable at [r] *)
    assert (Hpk1 : forall Δ1 κ B Δ2, T1 = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r)
      by (intros Δ1 κ B Δ2 ->; apply (Hpk Δ1 κ B (Δ2 ++ T2)); rewrite <- app_assoc; reflexivity).
    assert (Hpk2 : forall Δ1 κ B Δ2, T2 = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r)
      by (intros Δ1 κ B Δ2 ->; apply (Hpk (T1 ++ Δ1) κ B Δ2); rewrite <- app_assoc; reflexivity).
    pose proof (rel_exp_ctx_fn _ _ _ _ _ _ _ HTa1 HT HT1r Hpk1 Hev HA0t HA0k HM0) as Hfn1.
    destruct (rel_type_ctx_pi _ _ _ _ _ _ HTa1 HT HT1r Hpk1 Hev HA0t HA0k) as [HP1 HP1r].
    exists (ctx_fn T1 M0); split; [ exact Hred |]; split; [ exact Hfn1 |].
    intros ns m Hlen Hgs Hm.
    rewrite ctx_fn_app in Hg.
    assert (HT20 : ⊨ T2 ++ ⋅) by (rewrite app_nil_r; exact (rel_ctx_wf_app_r _ _ HT)).
    assert (HP1' : T2 ++ ⋅ ⊨ᵗ ctx_pi_at r T1 A0 ≈ ctx_pi_at r T1 A0 at max l iA) by (rewrite app_nil_r; exact HP1).
    assert (HP1k' : rel_type_kind (T2 ++ ⋅) (ctx_pi_at r T1 A0) r) by (rewrite app_nil_r; exact HP1r).
    assert (Hfn1' : T2 ++ ⋅ ⊨ ctx_fn T1 M0 : ctx_pi_at r T1 A0) by (rewrite app_nil_r; exact Hfn1).
    exact (ctx_fn_apps_tele _ _ _ _ _ _ _ _ HTa2 HT20 per_ctx_env_nil_true HT2r Hpk2 Hev HP1' HP1k' Hfn1' nil nil ns g m I Hgs Hlen Hg Hm).
  Qed.

  (** The reduct clause for an abstracted description, by its parts. *)
  Lemma filed_ok_ats_up : forall T R Ns R1 T1 T2, T = T1 ++ T2 -> tele_ass T -> List.length T2 = List.length Ns ->
      mdesc_ats (mdesc_up T R) Ns = Some R1 ->
      (forall A, mdesc_type (mdesc_up T1 R) = Some A -> mdesc_type R1 = Some A[sb_of_list Id Ns]) /\
      mdesc_reduct R1 = option_map (fun M => M[sb_of_list Id Ns]) (mdesc_reduct (mdesc_up T1 R)).
  Proof.
    intros * -> HTa Hl Ha.
    exact (mdesc_ats_up_parts _ _ _ _ _ (proj2 (tele_ass_app_inv _ _ HTa)) Hl Ha).
  Qed.

  Lemma per_bot_glob : forall pg, per_bot (d_glob pg) (d_glob pg).
  Proof. intros pg s; econstructor; [ constructor | constructor | reflexivity ]. Qed.

  (** The type former of the member [k] of the group [D], at [p.x], over the
      telescope [T] of [p]: what a filed member's entry and the open frame
      of a member's module both are. *)
  Lemma filed_ok_ind_term : forall p T Φ x pq k D Mk Δu, gc_loc Θm Ξm p = Some (T, Φ) ->
      ind_mlookup Θm Ξm (qname_in p x) = Some (pq, k, D) -> ind_selfpath pq k D (qname_in p x) ->
      ind_member D k = Some Mk -> ind_uparams D = Δu ++ T ->
      gc_resolve Θ2 Ξ2 (qname_in p x) = None -> ind_mlookup Θ2 Ξ2 (qname_in p x) = Some (pq, k, D) ->
      valid_filed_term p T x (mdesc_term ak_relevant (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (Some (a_ind pq k))).
  Proof.
    intros * Hl Hindm Hsp HMk HU Hres2 Hind2.
    destruct (gc_loc_valid _ _ _ Hl) as [[HT HTa HTr] _].
    pose proof (ind_mlookup_group _ _ Hgm _ _ _ _ Hindm) as HlD.
    pose proof (ind_lookup_gc_sub _ _ _ _ _ _ filed_ok_sub HlD) as HlD2.
    destruct (ind_lookup_valid _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ HlD) as [HD HDs].
    destruct (decl_of_lookup _ _ ⋅ _ _ (wf_ctx_empty _ _ Hgm) HlD) as [Hdt Hc].
    pose proof (decl_typed_sort_univ _ _ _ Hdt) as Hsu.
    destruct (member_lt_decl _ _ _ _ _ Hdt HMk (ind_selfpath_decl_field _ _ _ _ Hsp)) as [pm Hh].
    pose proof (grp_tele_ass_of_embedding _ _ _ _ _ _ Hgm He HlD) as Hass.
    set (Δp := im_nparams Mk ++ Δu).
    assert (Hpar : im_params D Mk = Δp ++ T) by (subst Δp; rewrite <- app_assoc, <- HU; reflexivity).
    set (S' := (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ).
    destruct (HDs _ _ _ _ HMk Hpar) as [i HA0].
    pose proof (@valid_exp_under_ctx_ind GC2 D HD Hc Hsu pq HlD2 Hass k Mk pm HMk Hh) as Hind0.
    assert (Hty : ind_ty D Mk = ctx_pi T (ctx_pi Δp S')) by (unfold ind_ty; rewrite Hpar, ctx_pi_app; reflexivity).
    rewrite Hty in Hind0.
    assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
    destruct (valid_exp_under_ctx_ctx_pi _ _ _ _ HTa HT0 ltac:(rewrite app_nil_r; exact HA0)) as [kt Hkt].
    destruct (valid_at_universe _ _ _ _ _ Hind0 Hkt per_ctx_env_nil_true nil nil I) as (g & g' & e & j & E0 & Hg & Hg' & He0 & HE0 & Hgg).
    assert (Hgd : ⟦ a_ind pq k ⟧ nil ↘ d_ind pq k nil) by constructor.
    pose proof (functional_eval_exp _ _ _ _ Hg Hgd) as ->; pose proof (functional_eval_exp _ _ _ _ Hg' Hgd) as ->.
    eapply (valid_filed_term_of_value _ _ _ _ _ i); [ exact HA0 | intros; constructor |].
    apply mk_valid_filed_value with (valid_filed_value_val := d_ind pq k nil).
    - intros Ns R1 T1 T2 HT12 Hlen Ha.
      assert (Hle : length Ns <= length (ind_uparams D)) by (rewrite HU, HT12, !length_app; lia).
      unfold S' in Ha; rewrite (mdesc_term_part_ats_ind _ _ _ _ _ (decl_closed_ass _ Hc) Hle) in Ha; injection Ha as <-.
      split.
      + cbn [mdesc_type]; f_equal.
        unfold ind_ty_at; rewrite <- length_im_params, Hpar, HT12, app_assoc, length_app, <- Hlen, Nat.add_sub, firstn_app,
          Nat.sub_diag, firstn_all; cbn [List.firstn]; rewrite app_nil_r, ctx_pi_app; reflexivity.
      + right; exists (apps_exp (a_ind pq k) (vars_from 0 (length T2))).
        split; [ cbn [mdesc_reduct]; rewrite apps_exp_sub; cbn [exp_sub]; rewrite Hlen, vars_from_sb_of_list; reflexivity |].
        destruct (tele_ass_app_inv T1 T2 ltac:(rewrite <- HT12; exact HTa)) as [HTa1 HTa2].
        assert (HT12' : ⊨ T1 ++ T2) by (rewrite <- HT12; exact HT).
        pose proof (rel_ctx_wf_app_r _ _ HT12') as HT2.
        assert (HA0' : T1 ++ T2 ⊨ ctx_pi Δp S' : Typeω@i) by (rewrite <- HT12; exact HA0).
        destruct (rel_exp_ctx_pi _ _ _ _ HTa1 HT12' HA0') as [kk Hk].
        assert (Hv0 : T2 ⊨ apps_exp (a_ind pq k) (vars_from 0 (length T2)) : ctx_pi T1 (ctx_pi Δp S')).
        { assert (HT20 : ⊨ T2 ++ ⋅) by (rewrite app_nil_r; exact HT2).
          assert (Hk0 : T2 ++ ⋅ ⊨ ctx_pi T1 (ctx_pi Δp S') : Typeω@kk) by (rewrite app_nil_r; exact Hk).
          assert (Hi0 : ⋅ ⊨ a_ind pq k : ctx_pi T2 (ctx_pi T1 (ctx_pi Δp S')))
            by (rewrite <- ctx_pi_app, <- HT12; exact Hind0).
          pose proof (valid_apps_vars _ _ _ _ _ _ eq_refl HTa2 HT20 Hk0 Hi0) as Hv0.
          rewrite app_nil_r in Hv0; cbn [exp_wk] in Hv0; exact Hv0. }
        split; [ exact Hv0 |].
        intros ns m Hns Hgs Hm.
        exists m; split; [| exact (tele_value_self _ _ _ _ _ _ HT2 Hv0 Hk Hns Hgs Hm) ].
        apply eval_apps_exp in Hm as (f & Hf & Hfa0).
        assert (Hgd' : ⟦ a_ind pq k ⟧ env_tele nil (rev T2) ns ↘ d_ind pq k nil) by constructor.
        pose proof (functional_eval_exp _ _ _ _ Hf Hgd') as ->.
        apply eval_app_args_ind in Hfa0 as (ns' & Hns' & Hfa).
        pose proof (eval_vars_from_args (tele_entries nil (rev T2) ns) nil nil) as Hvs.
        rewrite app_nil_r, tele_entries_values, tele_entries_length in Hvs; cbn [length] in Hvs; rewrite Hns in Hvs.
        pose proof (functional_eval_exps _ _ _ _ Hns' Hvs) as ->; exact Hfa.
    - rewrite qname_in_app in Hres2, Hind2.
      eapply global_member_value_indty; [ exact Hres2 | exact Hind2 ].
    - exact (mk_rel_self _ _ _ _ j E0 e He0 HE0 Hgg).
  Qed.

  (** The type former of the record type [R] at [p.x], its parameters [Δ0]
      then the telescope [T] of [p]: what a filed record entry and the open
      frame of a record type's module both are. *)
  Lemma filed_ok_record_term : forall p T Φ x R Δ0, gc_loc Θm Ξm p = Some (T, Φ) ->
      record_lookup Θm Ξm (qname_in p x) = Some R -> record_params R = Δ0 ++ T ->
      valid_filed_term p T x (mdesc_term ak_relevant (ctx_pi (record_params R) (record_sort R)) (Some (a_record (qname_in p x)))).
  Proof.
    intros * Hl Hrl HP.
    destruct (gc_loc_valid _ _ _ Hl) as [[HT HTa HTr] _].
    pose proof (record_lookup_gc_sub _ _ _ _ _ _ filed_ok_sub Hrl) as Hrl2.
    pose proof (record_lookup_resolve _ _ _ _ Hrl2) as Hres2.
    destruct (record_lookup_valid _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hrl) as [HPv HPr HSv HFv HTv].
    pose proof (record_lookup_typed _ _ Hgm (gctx_valid_syn _ _ Hgm) _ _ Hrl) as Hty.
    pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ filed_ok_wf) Hrl2) as Hc.
    pose proof (record_typed_sort_univ _ _ _ Hty) as Hsu.
    pose proof (typed_params_ass _ _ _ Hty) as Hass.
    pose proof (typed_nodup _ _ _ Hty) as Hnd.
    assert (Hrec0 : ⋅ ⊨ a_record (qname_in p x) : record_ty R) by (eapply valid_exp_under_ctx_record; eassumption).
    unfold record_ty in Hrec0; rewrite HP, ctx_pi_app in Hrec0.
    set (S := record_sort R) in *.
    destruct (tele_ass_app_inv Δ0 T ltac:(rewrite <- HP; exact Hass)) as [HaΔ0 _].
    destruct HSv as [i0 HS0]; rewrite HP in HS0.
    destruct (rel_exp_ctx_pi _ _ _ _ HaΔ0 ltac:(rewrite <- HP; exact HPv) HS0) as [i HA0].
    assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
    destruct (valid_exp_under_ctx_ctx_pi _ _ _ _ HTa HT0 ltac:(rewrite app_nil_r; exact HA0)) as [kt Hkt].
    destruct (valid_at_universe _ _ _ _ _ Hrec0 Hkt per_ctx_env_nil_true nil nil I) as (g & g' & e & j & E0 & Hg & Hg' & He0 & HE0 & Hgg).
    assert (Hgd : ⟦ a_record (qname_in p x) ⟧ nil ↘ d_record (qname_in p x) nil) by constructor.
    pose proof (functional_eval_exp _ _ _ _ Hg Hgd) as ->; pose proof (functional_eval_exp _ _ _ _ Hg' Hgd) as ->.
    eapply (valid_filed_term_of_value _ _ _ _ _ i); [ exact HA0 | intros; constructor |].
    apply mk_valid_filed_value with (valid_filed_value_val := d_record (qname_in p x) nil).
    - intros Ns R1 T1 T2 HT12 Hlen Ha.
      assert (Hle : length Ns <= length (record_params R)) by (rewrite HP, HT12, !length_app; lia).
      rewrite (mdesc_term_part_ats_record _ _ _ Hass Hle) in Ha; injection Ha as <-.
      split.
      + cbn [mdesc_type]; f_equal.
        unfold record_ty_at; rewrite HP, HT12, app_assoc, length_app, <- Hlen, Nat.add_sub, firstn_app,
          Nat.sub_diag, firstn_all; cbn [List.firstn]; rewrite app_nil_r, ctx_pi_app; reflexivity.
      + right; exists (apps_exp (a_record (qname_in p x)) (vars_from 0 (length T2))).
        split; [ cbn [mdesc_reduct]; rewrite apps_exp_sub; cbn [exp_sub]; rewrite Hlen, vars_from_sb_of_list; reflexivity |].
        destruct (tele_ass_app_inv T1 T2 ltac:(rewrite <- HT12; exact HTa)) as [HTa1 HTa2].
        assert (HT12' : ⊨ T1 ++ T2) by (rewrite <- HT12; exact HT).
        pose proof (rel_ctx_wf_app_r _ _ HT12') as HT2.
        assert (HA0' : T1 ++ T2 ⊨ ctx_pi Δ0 S : Typeω@i) by (rewrite <- HT12; exact HA0).
        destruct (rel_exp_ctx_pi _ _ _ _ HTa1 HT12' HA0') as [kk Hk].
        assert (Hv0 : T2 ⊨ apps_exp (a_record (qname_in p x)) (vars_from 0 (length T2)) : ctx_pi T1 (ctx_pi Δ0 S)).
        { assert (HT20 : ⊨ T2 ++ ⋅) by (rewrite app_nil_r; exact HT2).
          assert (Hk0 : T2 ++ ⋅ ⊨ ctx_pi T1 (ctx_pi Δ0 S) : Typeω@kk) by (rewrite app_nil_r; exact Hk).
          assert (Hi0 : ⋅ ⊨ a_record (qname_in p x) : ctx_pi T2 (ctx_pi T1 (ctx_pi Δ0 S)))
            by (rewrite <- ctx_pi_app, <- HT12; exact Hrec0).
          pose proof (valid_apps_vars _ _ _ _ _ _ eq_refl HTa2 HT20 Hk0 Hi0) as Hv0.
          rewrite app_nil_r in Hv0; cbn [exp_wk] in Hv0; exact Hv0. }
        split; [ exact Hv0 |].
        intros ns m Hns Hgs Hm.
        exists m; split; [| exact (tele_value_self _ _ _ _ _ _ HT2 Hv0 Hk Hns Hgs Hm) ].
        apply eval_apps_exp in Hm as (f & Hf & Hfa0).
        assert (Hgd' : ⟦ a_record (qname_in p x) ⟧ env_tele nil (rev T2) ns ↘ d_record (qname_in p x) nil) by constructor.
        pose proof (functional_eval_exp _ _ _ _ Hf Hgd') as ->.
        apply eval_app_args_record in Hfa0 as (ns' & Hns' & Hfa).
        pose proof (eval_vars_from_args (tele_entries nil (rev T2) ns) nil nil) as Hvs.
        rewrite app_nil_r, tele_entries_values, tele_entries_length in Hvs; cbn [length] in Hvs; rewrite Hns in Hvs.
        pose proof (functional_eval_exps _ _ _ _ Hns' Hvs) as ->; exact Hfa.
    - rewrite qname_in_app in Hres2, Hrl2 |- *.
      eapply global_member_value_record; [ exact Hres2 | exact Hrl2 ].
    - exact (mk_rel_self _ _ _ _ j E0 e He0 HE0 Hgg).
  Qed.

  Lemma filed_ok_term : forall p T Φ x Φ0 E R0, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_term (Some (qname_in p x)) E = Some R0 ->
      valid_filed_term p T x R0.
  Proof.
    intros * Hl Hp HR0.
    destruct (gc_loc_valid _ _ _ Hl) as [[HT HTa [lT HTr]] Hv].
    pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hp) as HV.
    destruct (filed_ok_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & Hl2 & Hent2 & HeE2 & Hgr & HeE & Hent).
    destruct E as [b pv r A oM | pv U | pv pq k D ΦD | pv Ad Md U | pv pr Rr ΦR]; cbn in HR0; try discriminate;
      try (injection HR0 as <-).
    - (* a definition *)
      cbn in HV; destruct HV as [A0 i oM0 -> -> HA0 HM0 Hpk].
      assert (HE2 : ge_def b pv r (ctx_pi_at r T A0) (option_map (ctx_fn T) oM0) = E2)
        by (apply entry_grows_eq; [ exact Hgr | intros * -> | intros * -> | intros * -> ]; cbn in Hgr; discriminate).
      subst E2; apply gc_entry_def in HeE2; rewrite qname_in_app in HeE2.
      assert (HR : mdesc_term r (ctx_pi_at r T A0) (if b then option_map (ctx_fn T) oM0 else None) =
                   mdesc_up T (mdesc_term r A0 (if b then oM0 else None))) by (destruct b; reflexivity).
      rewrite HR.
      assert (Hats : forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns ->
                mdesc_term_part_ats (mdesc_up T (mdesc_term r A0 (if b then oM0 else None))) Ns = Some R1 ->
                mdesc_type R1 = Some (ctx_pi_at r T1 A0)[sb_of_list Id Ns] /\
                mdesc_reduct R1 = option_map (fun M => (ctx_fn T1 M)[sb_of_list Id Ns]) (if b then oM0 else None)).
      { intros * HT12 Hlen Ha.
        rewrite (mdesc_term_part_ats_up Ns _ _ _ _ HTa ltac:(rewrite HT12, length_app; lia)) in Ha.
        destruct (filed_ok_ats_up _ _ _ _ _ _ HT12 HTa Hlen Ha) as [Hty Hred].
        split; [ apply Hty; reflexivity | rewrite Hred; cbn; destruct (if b then oM0 else None); reflexivity ]. }
      destruct (evaluated_kind_or_propositional r) as [Hrk | ->].
      2:{ (* a proof: no value, its reduct asked for nothing at values *)
        apply mk_valid_filed_term with (valid_filed_term_typ := A0) (valid_filed_term_level := i);
          [ exact HA0 | | intros Hk; cbn in Hk; inversion Hk | exact Hpk ].
        intros * HT12 Hlen Ha; destruct (Hats _ _ _ _ HT12 Hlen Ha) as [Hty Hred]; split; [ exact Hty |].
        destruct b; [ destruct oM0 as [M0 |] |]; cbn in Hred; [| left; exact Hred | left; exact Hred ].
        right; exists (ctx_fn T1 M0); split; [ exact Hred |].
        subst T; destruct (tele_ass_app_inv _ _ HTa) as [HTa1 _].
        exact (valid_exp_under_ctx_ctx_fn ak_propositional _ _ _ _ i ltac:(discriminate) HTa1 HT HA0 (HM0 _ eq_refl)). }
      destruct b; [ destruct oM0 as [M0 |] |].
      1:{ (* transparent: its body *)
        destruct (filed_ok_term_fn _ _ _ _ _ _ _ HTa HT HTr Hpk Hrk HA0 (HM0 _ eq_refl) Hats) as (g & Hg & Hred & Hper).
        eapply valid_filed_term_of_value; [ exact HA0 | exact Hpk |].
        apply (mk_valid_filed_value _ _ _ _ _ g Hred); [| exact Hper ].
        eapply global_member_value_term; [ exact (gc_term_of_resolve _ _ _ _ _ _ _ Hrk HeE2) | exact Hg ]. }
      all: (* an axiom or an abstract definition: its name, a neutral *)
        destruct (filed_ok_closed_type _ _ _ _ _ HTa HT HTr Hpk Hrk HA0) as (j & HP & HPr);
        destruct (rel_type_inversion_simple_at per_ctx_env_nil_true HP nil nil I) as (e & e' & Hev & Hev' & [E0 HE0]);
        pose proof (functional_eval_exp _ _ _ _ Hev' Hev) as ->;
        assert (Hself : rel_self r T A0 (⇑ e (d_glob (qname_app p (x :: nil)))))
          by exact (mk_rel_self _ _ _ _ j E0 e Hev HE0 (per_bot_then_per_elem HE0 (per_bot_glob _)));
        eapply valid_filed_term_of_value; [ exact HA0 | exact Hpk |];
        apply mk_valid_filed_value with (valid_filed_value_val := ⇑ e (d_glob (qname_app p (x :: nil))));
        [ intros * HT12 Hlen Ha; destruct (Hats _ _ _ _ HT12 Hlen Ha) as [Hty Hred]; cbn in Hred;
          split; [ exact Hty | left; exact Hred ]
        | eapply global_member_value_neut; [ exact HeE2 | exact Hrk | first [ left; reflexivity | right; reflexivity ] | exact Hev ]
        | exact Hself ].
    - (* a member of a group: its type former *)
      assert (HE2 : exists ΦD2, E2 = ge_ind pv pq k D ΦD2)
        by (destruct E2 as [b' pv' r' A' B' | pv' U' | pv' pq' k' D' ΦD2 | pv' Ad' Md' U'' | pv' R' ΦR']; cbn in Hgr; try discriminate;
            destruct Hgr as (-> & -> & -> & ->); eauto).
      destruct HE2 as (ΦD2 & ->).
      destruct (gc_entry_ind _ _ _ _ _ _ _ _ HeE2) as [Hres2 Hind2].
      destruct (gc_entry_ind _ _ _ _ _ _ _ _ HeE) as [_ Hindm].
      pose proof (gc_entry_selfpath _ _ Hgm _ _ _ _ _ _ HeE) as Hsp.
      pose proof (loc_coherent _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as Hcoh.
      destruct (gm_coherent_child _ _ _ _ Hcoh (gm_entry_submodule _ T _ _ _ _ _ _ _ Hent))
        as [(Δu & oD & [= HU _] & HΔu) | (? & ? & [=] & _)].
      destruct (ind_member D k) as [Mk |] eqn:HMk; cbn in HR0; [ injection HR0 as <- | discriminate ].
      exact (filed_ok_ind_term _ _ _ _ _ _ _ _ _ Hl Hindm Hsp HMk HU Hres2 Hind2).
    - (* a definition with a module part: its term part, as a transparent
         definition *)
      cbn in HV; destruct HV as [_ [[A0 i oM0 -> HoM HA0 HM0 Hpk] _]].
      destruct oM0 as [M0 |]; cbn in HoM; [ injection HoM as -> | discriminate ].
      assert (HE2 : ge_def_mod pv (ctx_pi T A0) (ctx_fn T M0) U = E2)
        by (apply entry_grows_eq; [ exact Hgr | intros * -> | intros * -> | intros * -> ]; cbn in Hgr; discriminate).
      subst E2; rewrite qname_in_app in HeE2.
      change (mdesc_term ak_relevant (ctx_pi T A0) (Some (ctx_fn T M0))) with (mdesc_up T (mdesc_term ak_relevant A0 (Some M0))).
      assert (Hats : forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns ->
                mdesc_term_part_ats (mdesc_up T (mdesc_term ak_relevant A0 (Some M0))) Ns = Some R1 ->
                mdesc_type R1 = Some (ctx_pi T1 A0)[sb_of_list Id Ns] /\
                mdesc_reduct R1 = option_map (fun M => (ctx_fn T1 M)[sb_of_list Id Ns]) (Some M0)).
      { intros * HT12 Hlen Ha.
        rewrite (mdesc_term_part_ats_up Ns _ _ _ _ HTa ltac:(rewrite HT12, length_app; lia)) in Ha.
        destruct (filed_ok_ats_up _ _ _ _ _ _ HT12 HTa Hlen Ha) as [Hty Hred].
        split; [ apply Hty; reflexivity | rewrite Hred; reflexivity ]. }
      destruct (filed_ok_term_fn _ _ _ _ _ _ _ HTa HT HTr Hpk evaluated_kind_relevant HA0 (HM0 _ eq_refl) Hats)
        as (g & Hg & Hred & Hper).
      eapply valid_filed_term_of_value; [ exact HA0 | exact Hpk |].
      apply (mk_valid_filed_value _ _ _ _ _ g Hred); [| exact Hper ].
      eapply global_member_value_term; [ exact (gc_term_of_def_mod _ _ _ _ _ _ _ HeE2) | exact Hg ].
    - (* a record type: its type former *)
      pose proof (gc_entry_record _ _ _ _ _ _ _ HeE) as Hrl.
      pose proof (loc_coherent _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as Hcoh.
      destruct (gm_coherent_prefix _ _ _ _ _ Hcoh Hp) as ((Δ0 & HP & _) & _).
      exact (filed_ok_record_term _ _ _ _ _ _ Hl Hrl HP).
  Qed.

  (** The open frame of a record type's module under a stored body is its
      type former, as a filed record entry is. *)
  Lemma filed_ok_record_frame : forall p T Φ x R, gc_loc Θm Ξm p = Some (T, Φ) ->
      gs_find_record Ξm (qname_in p x) = Some R ->
      valid_filed_term p T x (mdesc_term ak_relevant (ctx_pi (record_params R) (record_sort R)) (Some (a_record (qname_in p x)))).
  Proof.
    intros * Hl Hk.
    assert (Hrl : record_lookup Θm Ξm (qname_in p x) = Some R) by (unfold record_lookup; rewrite Hk; reflexivity).
    destruct (gs_find_record_tele _ _ _ Hk) as (U & T0 & Ht0).
    destruct (frame_parent _ _ Hgm _ _ _ _ Ht0) as (Tq & Φq & Hfq & _).
    assert (HTq : T = Tq) by (unfold gc_loc in Hl; rewrite Hfq in Hl; injection Hl as <- _; reflexivity).
    subst Tq; destruct (frame_record_split _ _ Hgm _ _ _ _ Hk Ht0) as (Δr & _ & HP).
    rewrite (frame_child_outer _ _ Hgm _ _ _ _ _ _ Ht0 Hfq) in HP.
    exact (filed_ok_record_term _ _ _ _ _ _ Hl Hrl HP).
  Qed.

  (** The open frame of a member's module under a stored body is its type
      former, as a filed member's entry is. *)
  Lemma filed_ok_ind_frame : forall p T Φ x pq k D Mk, gc_loc Θm Ξm p = Some (T, Φ) ->
      gs_find_ind Ξm (qname_in p x) = Some (pq, k, D) -> ind_member D k = Some Mk ->
      valid_filed_term p T x (mdesc_term ak_relevant (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (Some (a_ind pq k))).
  Proof.
    intros * Hl Hk HMk.
    assert (Hindm : ind_mlookup Θm Ξm (qname_in p x) = Some (pq, k, D)) by (rewrite ind_mlookup_unfold, Hk; reflexivity).
    pose proof (frame_ind_selfpath _ _ Hgm _ _ _ _ Hk) as Hsp.
    destruct (frame_ind_loc _ _ Hgm _ _ _ _ Hk) as (? & ? & Tx & Φx & ? & _ & Hfx & _ & _).
    pose proof (frame_ind_uparams _ _ Hgm _ _ _ _ _ _ Hk Hfx) as HTx.
    destruct (gs_find_ind_tele _ _ _ Hk) as (U & T0 & Ht0).
    destruct (frame_parent _ _ Hgm _ _ _ _ Ht0) as (Tq & Φq & Hfq & _).
    assert (HTq : T = Tq) by (unfold gc_loc in Hl; rewrite Hfq in Hl; injection Hl as <- _; reflexivity).
    subst Tq; destruct (frame_child_tele _ _ Hgm _ _ _ _ _ _ Hfx Hfq) as (Δu & ->).
    pose proof (gc_sub_frame_ind _ _ _ _ _ _ filed_ok_sub Hk) as Hind2.
    pose proof (ind_mlookup_resolve _ _ _ _ Hind2) as Hres2.
    exact (filed_ok_ind_term _ _ _ _ _ _ _ _ _ Hl Hindm Hsp HMk (eq_sym HTx) Hres2 Hind2).
  Qed.

End FiledOk.

(** What a global context files and has open is worth at a target, read
    from it, when each entry is. *)
Theorem valid_filed_mods_of_valid : forall Θm Ξm Θ2 Ξ2, ⊢ᵍ Θm ⍮ Ξm -> gctx_embedding Θm Ξm Θ2 Ξ2 ->
    gds_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θm Ξm Θ2 Ξ2 Θm -> gs_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θm Ξm Θ2 Ξ2 Ξm ->
    @valid_filed_mods (gc_mk Θ2 Ξ2) Θm Ξm.
Proof.
  intros * Hgm He HΘ HΞ p T Φ Hl.
  destruct (gc_loc_valid _ _ _ _ HΘ HΞ _ _ _ Hl) as [[HT HTa HTr] _].
  destruct (gc_loc_grow _ _ _ _ (gctx_embedding_wf _ _ _ _ He) (gctx_embedding_resolution _ _ _ _ He) _ _ _ Hl) as (Φ2 & Hl2 & _).
  pose proof (loc_closed _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as [HTs _].
  constructor;
    [ eauto | intros ρ; exact (gc_loc_path _ _ (gctx_embedding_wf _ _ _ _ He) _ _ ρ Hl2) | exact HT | exact HTa | exact HTs
    | intros; eapply filed_ok_kind; eassumption | intros; eapply filed_ok_sub_kind; eassumption
    | intros; eapply filed_ok_term; eassumption | intros; eapply filed_ok_ind_frame; eassumption
    | intros; eapply filed_ok_record_frame; eassumption | intros; eapply filed_ok_alias; eassumption | exact HTr ].
Qed.

(** A sound embedding, from the validity at the target of what the source
    files and has open, read from the source. *)
Theorem valid_gctx_embedding_of : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> gctx_embedding Θ Ξ Θ2 Ξ2 ->
    gds_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ Θ2 Ξ2 Θ -> gs_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ Θ2 Ξ2 Ξ -> valid_gctx_embedding Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg He HΘ HΞ; constructor; [ exact He | exact Hg | exact (valid_filed_mods_of_valid _ _ _ _ Hg He HΘ HΞ) | |].
  - intros p D Hl; exact (proj1 (ind_lookup_valid _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl)).
  - intros p R Hl; exact (record_lookup_valid _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl).
Qed.

Corollary valid_gctx_embedding_of_bodies_valid : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 ->
    valid_gctx_embedding Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (valid_gctx_embedding_of _ _ _ _ Hg (gctx_embedding_with_bodies_embedding _ _ _ _ He) HΘ HΞ).
Qed.

Lemma gs_valid_tele : forall Θs Ξs Θ2 Ξ2 Ξ, gs_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θs Ξs Θ2 Ξ2 Ξ -> tele_ass (gs_tele Ξ).
Proof. intros * HΞ; destruct Ξ as [| [[mp K] U] Ξ]; [ cbn; constructor | exact (valid_mod_tele_ass _ _ _ (proj1 HΞ)) ]. Qed.

Lemma gs_tele_ass_of_bodies_valid : forall Θ Ξ Θ2 Ξ2, bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> tele_ass (gs_tele Ξ).
Proof. intros * HG He; exact (gs_valid_tele _ _ _ _ _ (proj2 (HG _ _ He _ _ (gc_sub_refl _ _)))). Qed.
