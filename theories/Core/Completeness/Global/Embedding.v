(** * Valid Global Contexts

    What an entry of a global context is worth at a target
    ([valid_entry], [valid_mod_tele], [valid_ind_decl_entry]), and the
    embedding that the validity of every entry gives: what the source files
    and has open is valid at the target, read from the source
    ([valid_filed_mods_of_valid]), and so are its declarations
    ([valid_emb_of], [valid_emb_good]).  A unit valid read at a global
    context stays valid read at a bigger one ([valid_unit_grow_all]).
    Nothing here uses the fundamental theorem; that each entry is valid
    where it is checked, and so that a well-formed global context embeds
    soundly into itself, is proved with it in [FundamentalTheorem.v]. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import
  MemberLemmas MemberWf Modules Paths DescTyping LookupSound.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Completeness Require Import ContextCases FunctionCases LetCases LevelCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import
  SubtypingCases TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import IndCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness Require Import ElimCases IotaCases.
From Mctt.Core.Completeness.Modules Require Import ModuleVal Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Mem Canon App Sel.
From Mctt.Core.Completeness Require Import ModuleCases.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** ** 1. Valid units, read at a bigger global context *)

Section Grow.
  Context {GC : GCtx}.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg1 : ⊢ᵍ Θ1 ⍮ Ξ1.
  Hypothesis He : Emb Θ1 Ξ1 Θ2 Ξ2.

  Lemma valid_unit_grow_all :
    (forall Γ K, valid_unit Θ1 Ξ1 Γ K -> valid_unit Θ2 Ξ2 Γ K) /\ (forall Γ H, valid_modexp Θ1 Ξ1 Γ H -> valid_modexp Θ2 Ξ2 Γ H).
  Proof.
    pose proof He as [Hg2 Hs].
    destruct (emb_preserves_wf _ _ _ _ He) as (_ & _ & _ & _ & _ & _ & Hwm).
    apply valid_unit_modexp_ind.
    - intros Γ p T Φ Ns Hw Hgl HΓ Hsa.
      destruct (gc_loc_grow _ _ _ _ Hg2 Hs _ _ _ Hgl) as (Φ2 & Hgl2 & _).
      exact (valid_unit_filed _ _ _ _ _ _ _ (Hwm _ _ _ Hw) Hgl2 HΓ Hsa).
    - intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC _ IHsl Hsh Hshx HU Hopv _ IHops.
      exact (valid_unit_body _ _ _ _ _ _ (Hwm _ _ _ Hw) (emb_body_xp _ _ _ _ Hg1 He _ _ _ Hx) HΔ HΓ HC IHsl Hsh Hshx HU Hopv IHops).
    - intros Γ Δ E Hw HΔ HΓ HΔΓ HU HE _ IHE.
      exact (valid_unit_alias _ _ _ _ _ (Hwm _ _ _ Hw) HΔ HΓ HΔΓ HU HE IHE).
    - intros Γ H R Rm K RK Hw HmH HmodH HHK _ IHK HmK HmodK.
      destruct (emb_mdenote _ _ _ _ Hg1 He _ _ _ HmH) as (R2 & HmH2 & Hd).
      destruct (dsg_mod _ _ _ _ Hs _ _ _ Hd HmodH) as (Rm2 & HmodH2 & Hdm).
      destruct (emb_mdenote _ _ _ _ Hg1 He _ _ _ HmK) as (RK2 & HmK2 & HdK).
      destruct (dsg_mod _ _ _ _ Hs _ _ _ HdK HmodK) as (Rm2' & HmodK2 & Hdm').
      pose proof (dsg_functional _ _ _ _ _ _ _ Hdm Hdm') as <-.
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
    eapply (rel_wk_under_ctx_intro (R' := fun _ _ => True)); [ exact HR | exact per_ctx_env_nil_true |].
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

Lemma ds_red_sub_map : forall R σ, ds_red (ds_sub R σ) = option_map (fun M => M[σ]) (ds_red R).
Proof.
  intros R σ; destruct (ds_red R) as [M |] eqn:E; [ exact (ds_red_sub _ _ _ E) |].
  destruct R as [A [M |] | | | ]; cbn in E |- *; congruence.
Qed.

(** An abstracted description, substituted under its parameters: the term
    part and the reduct, substituted. *)
Lemma ds_up_sub_parts : forall Θ Ξ, gctx_closed Θ Ξ -> forall Θa R σ,
    (forall A, ds_ty Θ Ξ (ds_up Θa R) = Some A ->
       ds_ty Θ Ξ (ds_up (tele_sub Θa σ) (ds_sub R (sb_qn (length Θa) σ))) = Some A[σ]) /\
    ds_red (ds_up (tele_sub Θa σ) (ds_sub R (sb_qn (length Θa) σ))) = option_map (fun M => M[σ]) (ds_red (ds_up Θa R)).
Proof.
  intros * Hc Θa R σ; split.
  - intros A Ht; destruct (ds_ty_up_inv _ _ _ _ _ Ht) as (A0 & Ht0 & ->).
    rewrite ctx_pi_sub; apply ds_ty_up, ds_ty_sub; assumption.
  - rewrite !ds_red_up, ds_red_sub_map; destruct (ds_red R) as [M |]; cbn; [ rewrite ctx_fn_sub |]; reflexivity.
Qed.

(** A description abstracted over [Θa] and then a telescope [T2], given
    arguments for all of [T2]: its term part and reduct are those of the
    description abstracted over [Θa], instantiated. *)
Lemma ds_ats_up_parts : forall Θ Ξ, gctx_closed Θ Ξ -> forall Ns T2 Θa R R1,
    tele_ass T2 -> length T2 = length Ns -> ds_ats (ds_up (Θa ++ T2) R) Ns = Some R1 ->
    (forall A, ds_ty Θ Ξ (ds_up Θa R) = Some A -> ds_ty Θ Ξ R1 = Some A[sb_of_list Id Ns]) /\
    ds_red R1 = option_map (fun M => M[sb_of_list Id Ns]) (ds_red (ds_up Θa R)).
Proof.
  intros Θ Ξ Hc; induction Ns as [| N Ns IH]; intros * HT Hl Ha.
  - destruct T2; [| cbn in Hl; discriminate ]; cbn in Ha; injection Ha as <-; rewrite app_nil_r.
    split; [ intros A Ht; rewrite Ht, exp_sub_id; reflexivity |].
    destruct (ds_red (ds_up Θa R)); cbn; rewrite ?exp_sub_id; reflexivity.
  - destruct (List.exists_last (l := T2)) as (T2' & e & ->); [ intros ->; cbn in Hl; discriminate |].
    destruct (tele_ass_app_inv _ _ HT) as [HT' He]; inversion He as [| ? ? [B ->] _]; subst.
    rewrite List.length_app in Hl; cbn in Hl.
    cbn [ds_ats] in Ha; rewrite app_assoc, ds_at_up, tele_sub_app, List.length_app, sb_qn_plus in Ha.
    set (σ := sb_qn (length T2') (Id,,N)) in Ha.
    destruct (IH _ _ _ _ (tele_ass_sub _ _ HT') ltac:(rewrite length_tele_sub; lia) Ha) as [Hty Hred].
    destruct (ds_up_sub_parts _ _ Hc Θa R σ) as [Hty0 Hred0].
    assert (Hσ : forall M, M[σ][sb_of_list Id Ns] = M[sb_of_list Id (N :: Ns)]).
    { intros M; subst σ; cbn [sb_of_list]; rewrite exp_sub_sub; apply exp_sub_sb_eq.
      replace (length T2') with (length Ns) by lia.
      etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ]. }
    split.
    + intros A Ht; rewrite (Hty _ (Hty0 _ Ht)), Hσ; reflexivity.
    + rewrite Hred, Hred0; destruct (ds_red (ds_up Θa R)); cbn; rewrite ?Hσ; reflexivity.
Qed.

(** ** 4. What an entry is worth at the target *)

(** What an entry other than a body module is worth at [Θ2 ⍮ Ξ2], read from
    [Θs ⍮ Ξs]: a definition, checked over [T], is the [Π] and [λ] over [T]
    of a valid type and of a valid body of it; an alias is a valid unit in
    the empty context, read from any well-formed [Θs ⍮ Ξs]; an inductive
    alias is the [λ] over its parameters of the type former at its
    arguments, valid at the [Π] of the type former's type. *)
Definition valid_entry (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A oM =>
      exists A0 i oM0, A = ctx_pi T A0 /\ oM = option_map (ctx_fn T) oM0 /\
        @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (Typeω@i) A0 A0 /\
        (forall M0, oM0 = Some M0 -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T A0 M0 M0)
  | ge_mod _ U => ⊢ᵍ Θs ⍮ Ξs -> @valid_unit (gc_mk Θ2 Ξ2) Θs Ξs ⋅ (me_lit U)
  | ge_ind _ _ _ _ => True
  | ge_ind_alias _ Δ p Ns =>
      exists Δ0 D i, Δ = Δ0 ++ T /\ ind_lookup Θs Ξs p = Some D /\ ind_lookup Θ2 Ξ2 p = Some D /\
        @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (Typeω@i) (ctx_pi Δ0 (ind_ty_at D Ns)) (ctx_pi Δ0 (ind_ty_at D Ns)) /\
        @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (ctx_pi Δ0 (ind_ty_at D Ns))
          (ctx_fn Δ0 (apps_exp (a_ind p) Ns)) (ctx_fn Δ0 (apps_exp (a_ind p) Ns))
  end.

(** The telescope of a module. *)
Definition valid_mod_tele (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop :=
  @rel_ctx_wf (gc_mk Θ2 Ξ2) T /\ tele_ass T.

(** A declaration: valid, and the type of its type former, abstracted over
    the outer part of its parameters, a type over the inner part. *)
Definition valid_ind_decl_entry (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop :=
  @valid_ind_decl (gc_mk Θ2 Ξ2) D /\
  forall Δ1 Δ2, ind_params D = Δ1 ++ Δ2 -> exists i,
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Δ2 (Typeω@i) (ctx_pi Δ1 (ind_sort D)[wk_shiftn (ind_nn D)]ʷ)
      (ctx_pi Δ1 (ind_sort D)[wk_shiftn (ind_nn D)]ʷ).

(** ** 5. Syntactic facts about stored bodies *)

Lemma gm_entry_alias_submodule : forall Φ T x pv Δ E,
    gm_entry Φ (x :: nil) = Some (ge_mod pv (gu_mk Δ (md_alias E))) ->
    gm_submodule T Φ x nil = Some (mr_alias (gu_mk Δ (md_alias E))).
Proof.
  induction Φ as [| Φ IH y E0 | Φ IH H its]; intros * He; cbn in He |- *; [ discriminate | | eauto ].
  destruct (String.eqb x y); [| eauto ].
  destruct E0 as [? ? ? ? | ? [? [? ? | ?]] | ? ? ? ? | ? ? ? ?]; try discriminate; injection He as -> -> ->; reflexivity.
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
Lemma gc_loc_kind : forall Θ Ξ pl TΦ args, gc_loc Θ Ξ pl = Some TΦ -> dkind Θ Ξ (dm_global pl args) nil mk_mod.
Proof.
  intros * Hl; apply dk_global_here_mod; unfold gc_loc in Hl; destruct (gc_frame Ξ pl) eqn:Hf; [ right; eauto |].
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

Lemma entry_kind_grows : forall E1 E2, entry_grows E1 E2 -> entry_kind E1 = entry_kind E2.
Proof.
  intros [b pv A B | pv [Δ [sm Φ | E']] | pv pq D Φ | pv Δ pq Ns]
    [b' pv' A' B' | pv' [Δ' [sm' Φ' | E'']] | pv' pq' D' Φ' | pv' Δ' pq' Ns'] H; cbn in H |- *;
    try reflexivity; discriminate.
Qed.

(** An entry grows only if it is a body module or an inductive type. *)
Lemma entry_grows_eq : forall E1 E2, entry_grows E1 E2 ->
    (forall pv Δ sm Φ, E2 <> ge_mod pv (gu_mk Δ (md_body sm Φ))) -> (forall pv pq D Φ, E2 <> ge_ind pv pq D Φ) -> E1 = E2.
Proof.
  intros [b pv A B | pv [Δ [sm Φ | E']] | pv pq D Φ | pv Δ pq Ns]
    [b' pv' A' B' | pv' [Δ' [sm' Φ' | E'']] | pv' pq' D' Φ' | pv' Δ' pq' Ns'] H Hb Hi; cbn in H;
    try exact H; exfalso; first [ eapply Hb; reflexivity | eapply Hi; reflexivity ].
Qed.

Lemma gc_body_loc : forall Θ Ξ p r, gc_body Θ Ξ p = Some r -> exists r', gc_loc Θ Ξ p = Some r'.
Proof. intros * H; unfold gc_loc; destruct (gc_frame Ξ p); eauto. Qed.

(** ** 6. Valid entries make valid global modules *)

Section FiledOk.
  Variables (Θm : gdeps) (Ξm : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis He : Emb Θm Ξm Θ2 Ξ2.
  Hypothesis HΘ : gds_valid valid_entry valid_mod_tele valid_ind_decl_entry Θm Ξm Θ2 Ξ2 Θm.
  Hypothesis HΞ : gs_valid valid_entry valid_mod_tele valid_ind_decl_entry Θm Ξm Θ2 Ξ2 Ξm.

  #[local] Instance GC2 : GCtx := gc_mk Θ2 Ξ2.

  Lemma fo_wf : ⊢ᵍ Θ2 ⍮ Ξ2.
  Proof. exact (em_wf _ _ _ _ He). Qed.

  Lemma fo_sub : gc_sub Θm Ξm Θ2 Ξ2.
  Proof. exact (em_res _ _ _ _ He). Qed.

  Lemma good_loc : forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) ->
      valid_mod_tele Θ2 Ξ2 T /\ gm_valid valid_entry valid_mod_tele valid_ind_decl_entry Θm Ξm Θ2 Ξ2 T Φ.
  Proof.
    intros * Hl; unfold gc_loc in Hl; destruct (gc_frame Ξm p) as [r |] eqn:Hf.
    - injection Hl as ->; unfold gc_frame in Hf.
      destruct (gs_find_tele Ξm p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
      injection Hf as <- <-; exact (gs_valid_find _ _ _ _ _ _ _ _ _ _ _ _ HΞ Ef).
    - exact (good_body _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl).
  Qed.

  (** An entry of a stored body, read at both global contexts. *)
  Lemma fo_entry : forall p T Φ x Φ0 E, gc_loc Θm Ξm p = Some (T, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      exists Φ2 E2, gc_loc Θ2 Ξ2 p = Some (T, Φ2) /\ gm_entry Φ2 (x :: nil) = Some E2 /\
        gc_entry Θ2 Ξ2 (qname_in p x) = Some E2 /\ entry_grows E E2 /\
        gc_entry Θm Ξm (qname_in p x) = Some E /\ gm_entry Φ (x :: nil) = Some E.
  Proof.
    intros * Hl Hp.
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0' & E' & Heq & Hent); injection Heq as <- <-.
    pose proof (gc_loc_loc _ _ _ _ _ Hl) as Hlc.
    pose proof (proj2 (loc_entry _ _ Hgm _ _ _ Hlc x E) Hent) as HeE.
    destruct (gc_sub_entry _ _ _ _ _ _ fo_sub HeE) as (E2 & HeE2 & Hgr).
    destruct (gc_loc_grow _ _ _ _ fo_wf fo_sub _ _ _ Hl) as (Φ2 & Hl2 & _ & Hlc2).
    pose proof (proj1 (loc_entry _ _ fo_wf _ _ _ Hlc2 x E2) HeE2) as Hent2.
    exists Φ2, E2; repeat split; assumption.
  Qed.

  (** An alias entry is an alias at the target. *)
  Lemma fo_alias_module : forall p T Φ x Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua ->
      gc_module Θ2 Ξ2 (qname_in p x) = Some (mr_alias Ua).
  Proof.
    intros * Hl Hp HUa.
    destruct (fo_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & Hl2 & Hent2 & HeE2 & Hgr & _).
    assert (HE : E = E2).
    { apply entry_grows_eq; [ exact Hgr | | ]; intros * ->;
        destruct E as [| ? [? [? ?| ?]] | | ]; cbn in Hgr, HUa; try discriminate; try contradiction; congruence. }
    subst E2.
    destruct E as [b pv A B | pv [Ta [sm Φ1 | Ea]] | pv pq D Φ1 | pv Δ pq Ns]; cbn in HUa; try discriminate;
      injection HUa as <-.
    - destruct (gm_entry_head _ _ _ Hent2) as (z & ip & [= <- <-] & Hin).
      pose proof (gc_loc_loc _ _ _ _ _ Hl2) as Hlc2.
      rewrite qname_in_app, (proj1 (proj2 (proj2 (loc_read _ _ fo_wf _ _ _ Hlc2 _ Hin nil)))).
      exact (gm_entry_alias_submodule _ _ _ _ _ _ Hent2).
    - destruct (gc_entry_ind_alias _ _ _ _ _ _ _ HeE2) as [_ Hia].
      exact (ind_alias_lookup_module _ _ _ _ _ _ Hia).
  Qed.

  (** An alias entry is a valid unit in the empty context. *)
  Lemma fo_alias_valid_unit : forall p T Φ x Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua -> valid_unit Θm Ξm ⋅ (me_lit Ua).
  Proof.
    intros * Hl Hp HUa.
    destruct (good_loc _ _ _ Hl) as [_ Hv].
    pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ Hv Hp) as HE.
    destruct E as [b pv A B | pv [Ta [sm Φ1 | Ea]] | pv pq D Φ1 | pv Δ pq Ns]; cbn in HUa; try discriminate;
      injection HUa as <-; cbn in HE.
    - exact (HE Hgm).
    - exact (proj1 HE Hgm).
  Qed.

  Lemma fo_alias_kind : forall p T Φ x Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua ->
      dkind Θ2 Ξ2 (dm_global p nil) (x :: nil) mk_mod.
  Proof.
    intros * Hl Hp HUa.
    pose proof (fo_alias_module _ _ _ _ _ _ _ Hl Hp HUa) as Hm; rewrite qname_in_app in Hm.
    pose proof (fo_alias_valid_unit _ _ _ _ _ _ _ Hl Hp HUa) as HK.
    assert (HUa' : exists Ta Ea, Ua = gu_mk Ta (md_alias Ea))
      by (destruct E as [| pv [Ta [| Ea]] | | pv Δa pq Nsa]; cbn in HUa; try discriminate; injection HUa as <-; eauto).
    destruct HUa' as (Ta & Ea & ->).
    pose proof (valid_nil_kind _ _ _ (valid_unit_alias_rel0 _ _ _ _ HK) per_ctx_env_nil_true nil I) as Hk.
    inversion Hk; subst.
    eapply dk_global_alias; [ exact Hm | eassumption ].
  Qed.

  (** Each entry of a stored body has its kind at the target. *)
  Lemma fo_kind : forall p T Φ x Φ0 E, gc_loc Θm Ξm p = Some (T, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      dkind Θ2 Ξ2 (dm_global p nil) (x :: nil) (entry_kind E).
  Proof.
    intros * Hl Hp.
    destruct (fo_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & Hl2 & Hent2 & HeE2 & Hgr & _).
    pose proof (gc_loc_loc _ _ _ _ _ Hl2) as Hlc2.
    rewrite (entry_kind_grows _ _ Hgr).
    destruct E2 as [b pv A B | pv [Δ [sm Φ' | Ea]] | pv pq D ΦD | pv Δ pq Ns]; cbn [entry_kind].
    - apply gc_entry_def in HeE2; rewrite qname_in_app in HeE2.
      eapply dk_global_step; [ right; do 4 eexists; exact HeE2 | eapply dk_global_here_def; exact HeE2 ].
    - destruct (gc_body_loc _ _ _ _ (proj1 (loc_child_mod _ _ fo_wf _ _ _ Hlc2 _ _ _ _ _ Hent2))) as (r & Hr).
      rewrite qname_in_app in Hr.
      eapply dk_global_step; [ left; eexists; exact Hr | exact (gc_loc_kind _ _ _ _ _ Hr) ].
    - assert (HE : E = ge_mod pv (gu_mk Δ (md_alias Ea)))
        by (apply entry_grows_eq; [ exact Hgr | intros * [=] | intros * [=] ]).
      subst E; exact (fo_alias_kind _ _ _ _ _ _ _ Hl Hp eq_refl).
    - destruct (gc_body_loc _ _ _ _ (loc_child_ind _ _ fo_wf _ _ _ _ _ _ _ _ Hlc2 Hent2)) as (r & Hr).
      rewrite qname_in_app in Hr.
      eapply dk_global_step; [ left; eexists; exact Hr | exact (gc_loc_kind _ _ _ _ _ Hr) ].
    - assert (HE : E = ge_ind_alias pv Δ pq Ns)
        by (apply entry_grows_eq; [ exact Hgr | intros * [=] | intros * [=] ]).
      subst E; exact (fo_alias_kind _ _ _ _ _ _ _ Hl Hp eq_refl).
  Qed.

  (** Each body stored below a stored body is a module at the target. *)
  Lemma fo_sub_kind : forall p x TΦ, gc_loc Θm Ξm (qname_app p (x :: nil)) = Some TΦ ->
      dkind Θ2 Ξ2 (dm_global p nil) (x :: nil) mk_mod.
  Proof.
    intros * Hl; destruct TΦ as [T Φ].
    destruct (gc_loc_grow _ _ _ _ fo_wf fo_sub _ _ _ Hl) as (Φ2 & Hl2 & _).
    eapply dk_global_step; [ left; eexists; exact Hl2 | exact (gc_loc_kind _ _ _ _ _ Hl2) ].
  Qed.

  (** Each alias stored in a stored body is a valid unit in any valid context. *)
  Lemma fo_alias : forall p T Φ y Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua ->
      gc_module Θ2 Ξ2 (qname_in p y) = Some (mr_alias Ua) /\
      forall Γ, ⊨ Γ -> ⊢ Θm ⍮ Ξm ⍮ Γ -> valid_unit Θm Ξm Γ (me_lit Ua).
  Proof.
    intros * Hl Hp HUa; split; [ exact (fo_alias_module _ _ _ _ _ _ _ Hl Hp HUa) |].
    intros Γ HΓ Hw.
    pose proof (loc_closed _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as [_ Hc].
    apply (@valid_unit_closed_weaken GC2 fo_wf _ _ Hgm fo_sub); [ exact (fo_alias_valid_unit _ _ _ _ _ _ _ Hl Hp HUa) | | exact HΓ | exact Hw ].
    exact (entry_alias_unit_scoped _ _ _ _ _ _ 0 Hc Hp HUa).
  Qed.

  (** *** Term entries *)

  (** The reduct clause, for a reduct that is a [λ] over the telescope of a
      valid body, the member's value its value. *)
  Lemma fo_term_fn : forall T A0 i M0 R0 g, tele_ass T -> ⊨ T -> T ⊨ A0 : Typeω@i -> T ⊨ M0 : A0 ->
      ⟦ ctx_fn T M0 ⟧ nil ↘ g ->
      (forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> ds_ats R0 Ns = Some R1 ->
         ds_ty Θm Ξm R1 = Some (ctx_pi T1 A0)[sb_of_list Id Ns] /\
         ds_red R1 = Some (ctx_fn T1 M0)[sb_of_list Id Ns]) ->
      (forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> ds_ats R0 Ns = Some R1 ->
         ds_ty Θm Ξm R1 = Some (ctx_pi T1 A0)[sb_of_list Id Ns] /\
         (ds_red R1 = None \/
          exists M1, ds_red R1 = Some M1[sb_of_list Id Ns] /\ T2 ⊨ M1 : ctx_pi T1 A0 /\
            forall ns m, List.length ns = List.length T2 -> ⟦ M1 ⟧ env_args nil ns ↘ m ->
              $*| g & ns | gc_deps ⍮ gc_stack ↘ m)) /\
      rel_self T A0 g.
  Proof.
    intros * HTa HT HA0 HM0 Hg Hats; split.
    - intros * -> Hl Ha; destruct (Hats _ _ _ _ eq_refl Hl Ha) as [Hty Hred]; split; [ exact Hty | right ].
      destruct (tele_ass_app_inv _ _ HTa) as [HTa1 HTa2].
      exists (ctx_fn T1 M0); split; [ exact Hred |]; split; [ exact (valid_exp_under_ctx_ctx_fn _ _ _ _ HTa1 HT HM0) |].
      intros ns m Hlen Hm.
      destruct (eval_ctx_fn_apps _ _ _ _ _ HTa2 Hlen Hm) as (f & Hf & Hfa).
      rewrite <- ctx_fn_app in Hf; pose proof (functional_eval_exp _ _ _ _ Hf Hg) as ->; exact Hfa.
    - assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
      assert (HM0' : T ++ ⋅ ⊨ M0 : A0) by (rewrite app_nil_r; exact HM0).
      pose proof (valid_exp_under_ctx_ctx_fn _ _ _ _ HTa HT0 HM0') as Hfn.
      destruct (valid_at _ _ _ _ Hfn per_ctx_env_nil_true nil nil I) as (m & m' & e & j & E0 & Hm & Hm' & He0 & HE0 & Hmm).
      pose proof (functional_eval_exp _ _ _ _ Hm Hg) as ->; pose proof (functional_eval_exp _ _ _ _ Hm' Hg) as ->.
      exact (mk_rel_self _ _ _ j E0 e He0 HE0 Hmm).
  Qed.

  (** The reduct clause for an abstracted description, by its parts. *)
  Lemma fo_ats_up : forall T R Ns R1 T1 T2, T = T1 ++ T2 -> tele_ass T -> List.length T2 = List.length Ns ->
      ds_ats (ds_up T R) Ns = Some R1 ->
      (forall A, ds_ty Θm Ξm (ds_up T1 R) = Some A -> ds_ty Θm Ξm R1 = Some A[sb_of_list Id Ns]) /\
      ds_red R1 = option_map (fun M => M[sb_of_list Id Ns]) (ds_red (ds_up T1 R)).
  Proof.
    intros * -> HTa Hl Ha.
    exact (ds_ats_up_parts _ _ (wf_gstack_closed _ _ Hgm) _ _ _ _ _ (proj2 (tele_ass_app_inv _ _ HTa)) Hl Ha).
  Qed.

  Lemma per_bot_glob : forall pg, per_bot (d_glob pg) (d_glob pg).
  Proof. intros pg s; eexists; split; constructor. Qed.

  Lemma fo_term : forall p T Φ x Φ0 E R0, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_term E = Some R0 ->
      valid_filed_term Θm Ξm p T x R0.
  Proof.
    intros * Hl Hp HR0.
    destruct (good_loc _ _ _ Hl) as [[HT HTa] Hv].
    pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ Hv Hp) as HV.
    destruct (fo_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & Hl2 & Hent2 & HeE2 & Hgr & HeE & Hent).
    destruct E as [b pv A oM | pv U | pv pq D ΦD | pv Δf pq Ns']; cbn in HR0; try discriminate; injection HR0 as <-.
    - (* a definition *)
      cbn in HV; destruct HV as (A0 & i & oM0 & -> & -> & HA0 & HM0).
      assert (HE2 : ge_def b pv (ctx_pi T A0) (option_map (ctx_fn T) oM0) = E2)
        by (apply entry_grows_eq; [ exact Hgr | intros * -> | intros * -> ]; cbn in Hgr; discriminate).
      subst E2; apply gc_entry_def in HeE2; rewrite qname_in_app in HeE2.
      assert (HR : ds_term (ctx_pi T A0) (if b then option_map (ctx_fn T) oM0 else None) =
                   ds_up T (ds_term A0 (if b then oM0 else None))) by (destruct b; reflexivity).
      rewrite HR.
      assert (Hats : forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns ->
                ds_ats (ds_up T (ds_term A0 (if b then oM0 else None))) Ns = Some R1 ->
                ds_ty Θm Ξm R1 = Some (ctx_pi T1 A0)[sb_of_list Id Ns] /\
                ds_red R1 = option_map (fun M => (ctx_fn T1 M)[sb_of_list Id Ns]) (if b then oM0 else None)).
      { intros * HT12 Hlen Ha; destruct (fo_ats_up _ _ _ _ _ _ HT12 HTa Hlen Ha) as [Hty Hred].
        split; [ apply Hty; reflexivity | rewrite Hred; cbn; destruct (if b then oM0 else None); reflexivity ]. }
      destruct b; [ destruct oM0 as [M0 |] |].
      1:{ (* transparent: its body *)
        assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
        assert (HM0' : T ++ ⋅ ⊨ M0 : A0) by (rewrite app_nil_r; exact (HM0 _ eq_refl)).
        destruct (valid_at _ _ _ _ (valid_exp_under_ctx_ctx_fn _ _ _ _ HTa HT0 HM0') per_ctx_env_nil_true nil nil I)
          as (g & _ & _ & _ & _ & Hg & _).
        destruct (fo_term_fn _ _ _ _ _ g HTa HT HA0 (HM0 _ eq_refl) Hg Hats) as [Hred Hper].
        apply mk_valid_filed_term with (vft_typ := A0) (vft_lvl := i) (vft_val := g); [ exact HA0 | exact Hred | | exact Hper ].
        eapply eval_sel_global; [ exact HeE2 | exact Hg | constructor ]. }
      all: (* an axiom or an abstract definition: its name, a neutral *)
        assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT);
        assert (HA0' : T ++ ⋅ ⊨ A0 : Typeω@i) by (rewrite app_nil_r; exact HA0);
        destruct (rel_exp_ctx_pi _ _ _ _ HTa HT0 HA0') as [j HP];
        destruct (rel_exp_of_typ_inversion_simple_at per_ctx_env_nil_true HP nil nil I) as (e & e' & Hev & Hev' & [E0 HE0]);
        pose proof (functional_eval_exp _ _ _ _ Hev' Hev) as ->;
        apply mk_valid_filed_term with (vft_typ := A0) (vft_lvl := i) (vft_val := ⇑ e (d_glob (qname_app p (x :: nil))));
        [ exact HA0
        | intros * HT12 Hlen Ha; destruct (Hats _ _ _ _ HT12 Hlen Ha) as [Hty Hred]; cbn in Hred;
          split; [ exact Hty | left; exact Hred ]
        | eapply eval_sel_global_neut; [ exact HeE2 | first [ left; reflexivity | right; reflexivity ] | exact Hev | constructor ]
        | exact (mk_rel_self _ _ _ j E0 e Hev HE0 (per_bot_then_per_elem HE0 (per_bot_glob _))) ].
    - (* an inductive type: its type former *)
      assert (HE2 : exists ΦD2, E2 = ge_ind pv pq D ΦD2)
        by (destruct E2 as [b' pv' A' B' | pv' U' | pv' pq' D' ΦD2 | pv' Δ' pq' Ns'']; cbn in Hgr; try discriminate;
            destruct Hgr as (-> & -> & ->); eauto).
      destruct HE2 as (ΦD2 & ->).
      destruct (gc_entry_ind _ _ _ _ _ _ _ HeE2) as [Hres2 Hind2].
      destruct (gc_entry_ind _ _ _ _ _ _ _ HeE) as [_ Hindm].
      pose proof (gc_entry_selfpath _ _ Hgm _ _ _ _ _ HeE) as ->.
      destruct (good_ind _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hindm) as [HD HDs].
      destruct (decl_of_lookup _ _ ⋅ _ _ (wf_ctx_empty _ _ Hgm) Hindm) as [Hdt Hc].
      pose proof (dt_sort_univ _ _ _ Hdt) as Hsu.
      pose proof (loc_coh _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as Hcoh.
      destruct (gm_coh_child _ _ _ _ Hcoh (gm_entry_submodule _ T _ _ _ _ _ _ Hent))
        as [(Δu & oD & [= HU _] & HΔu) | (? & ? & [=] & _)].
      set (Δp := ind_nparams D ++ Δu).
      assert (Hpar : ind_params D = Δp ++ T)
        by (subst Δp; rewrite <- app_assoc, <- HU; unfold ind_nparams, ind_uparams; symmetry; apply firstn_skipn).
      set (S' := (ind_sort D)[wk_shiftn (ind_nn D)]ʷ).
      destruct (HDs _ _ Hpar) as [i HA0].
      pose proof (@valid_exp_under_ctx_ind GC2 D HD Hc Hsu (qname_in p x) Hind2) as Hind0.
      assert (Hty : ind_ty D = ctx_pi T (ctx_pi Δp S')) by (unfold ind_ty; rewrite Hpar, ctx_pi_app; reflexivity).
      rewrite Hty in Hind0.
      destruct (valid_at _ _ _ _ Hind0 per_ctx_env_nil_true nil nil I) as (g & g' & e & j & E0 & Hg & Hg' & He0 & HE0 & Hgg).
      assert (Hgd : ⟦ a_ind (qname_in p x) ⟧ nil ↘ d_ind (qname_in p x) nil) by constructor.
      pose proof (functional_eval_exp _ _ _ _ Hg Hgd) as ->; pose proof (functional_eval_exp _ _ _ _ Hg' Hgd) as ->.
      apply mk_valid_filed_term with (vft_typ := ctx_pi Δp S') (vft_lvl := i) (vft_val := d_ind (qname_in p x) nil);
        [ exact HA0 | | | ].
      + intros Ns R1 T1 T2 HT12 Hlen Ha.
        rewrite ds_ats_ind_nil in Ha; injection Ha as <-; cbn [app].
        split.
        * cbn [ds_ty]; rewrite Hindm; cbn [ctx_pi]; f_equal.
          unfold ind_ty_at, ind_np; rewrite Hpar, HT12, app_assoc, length_app, <- Hlen, Nat.add_sub, firstn_app,
            Nat.sub_diag, firstn_all; cbn [List.firstn]; rewrite app_nil_r, ctx_pi_app; reflexivity.
        * right; exists (apps_exp (a_ind (qname_in p x)) (vars_from 0 (length T2))).
          split; [ cbn [ds_red ctx_fn]; rewrite apps_exp_sub; cbn [exp_sub]; rewrite Hlen, vars_from_sb_of_list; reflexivity |].
          destruct (tele_ass_app_inv T1 T2 ltac:(rewrite <- HT12; exact HTa)) as [HTa1 HTa2].
          assert (HT12' : ⊨ T1 ++ T2) by (rewrite <- HT12; exact HT).
          pose proof (rel_ctx_wf_app_r _ _ HT12') as HT2.
          assert (HA0' : T1 ++ T2 ⊨ ctx_pi Δp S' : Typeω@i) by (rewrite <- HT12; exact HA0).
          destruct (rel_exp_ctx_pi _ _ _ _ HTa1 HT12' HA0') as [k Hk].
          split.
          -- assert (HT20 : ⊨ T2 ++ ⋅) by (rewrite app_nil_r; exact HT2).
             assert (Hk0 : T2 ++ ⋅ ⊨ ctx_pi T1 (ctx_pi Δp S') : Typeω@k) by (rewrite app_nil_r; exact Hk).
             assert (Hi0 : ⋅ ⊨ a_ind (qname_in p x) : ctx_pi T2 (ctx_pi T1 (ctx_pi Δp S')))
               by (rewrite <- ctx_pi_app, <- HT12; exact Hind0).
             pose proof (valid_apps_vars _ _ _ _ _ _ eq_refl HTa2 HT20 Hk0 Hi0) as Hv0.
             rewrite app_nil_r in Hv0; cbn [exp_wk] in Hv0; exact Hv0.
          -- intros ns m Hns Hm.
             apply eval_apps_exp in Hm as (f & ns' & Hf & Hns' & Hfa).
             assert (Hgd' : ⟦ a_ind (qname_in p x) ⟧ env_args nil ns ↘ d_ind (qname_in p x) nil) by constructor.
             pose proof (functional_eval_exp _ _ _ _ Hf Hgd') as ->.
             pose proof (eval_vars_from_args ns nil nil) as Hvs; rewrite app_nil_r in Hvs; cbn [length] in Hvs; rewrite Hns in Hvs.
             pose proof (functional_eval_exps _ _ _ _ Hns' Hvs) as ->; exact Hfa.
      + rewrite qname_in_app in Hres2, Hind2.
        eapply eval_sel_global_ind; [ exact Hres2 | exact Hind2 | constructor ].
      + exact (mk_rel_self _ _ _ j E0 e He0 HE0 Hgg).
    - (* an inductive alias: its type former at its arguments *)
      cbn in HV; destruct HV as [_ (Δ0 & D & i & -> & HlD & HlD2 & HA0 & HM0)].
      assert (HE2 : ge_ind_alias pv (Δ0 ++ T) pq Ns' = E2)
        by (apply entry_grows_eq; [ exact Hgr | intros * -> | intros * -> ]; cbn in Hgr; discriminate).
      subst E2; destruct (gc_entry_ind_alias _ _ _ _ _ _ _ HeE2) as [Hres2 Hia2]; rewrite qname_in_app in Hres2, Hia2.
      assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
      assert (HM0' : T ++ ⋅ ⊨ ctx_fn Δ0 (apps_exp (a_ind pq) Ns') : ctx_pi Δ0 (ind_ty_at D Ns'))
        by (rewrite app_nil_r; exact HM0).
      destruct (valid_at _ _ _ _ (valid_exp_under_ctx_ctx_fn _ _ _ _ HTa HT0 HM0') per_ctx_env_nil_true nil nil I)
        as (g & _ & _ & _ & _ & Hg & _).
      change (ds_ind (Δ0 ++ T) pq Ns') with (ds_up T (ds_ind Δ0 pq Ns')).
      assert (Hats : forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns ->
                ds_ats (ds_up T (ds_ind Δ0 pq Ns')) Ns = Some R1 ->
                ds_ty Θm Ξm R1 = Some (ctx_pi T1 (ctx_pi Δ0 (ind_ty_at D Ns')))[sb_of_list Id Ns] /\
                ds_red R1 = Some (ctx_fn T1 (ctx_fn Δ0 (apps_exp (a_ind pq) Ns')))[sb_of_list Id Ns]).
      { intros * HT12 Hlen Ha; destruct (fo_ats_up _ _ _ _ _ _ HT12 HTa Hlen Ha) as [Hty Hred].
        split; [ apply Hty; cbn [ds_up ds_ty]; rewrite HlD, <- ctx_pi_app; reflexivity |].
        rewrite Hred; cbn [ds_up ds_red option_map]; rewrite ctx_fn_app; reflexivity. }
      destruct (fo_term_fn _ _ _ _ _ g HTa HT HA0 HM0 Hg Hats) as [Hred Hper].
      apply mk_valid_filed_term with (vft_typ := ctx_pi Δ0 (ind_ty_at D Ns')) (vft_lvl := i) (vft_val := g);
        [ exact HA0 | exact Hred | | exact Hper ].
      rewrite <- ctx_fn_app in Hg.
      eapply eval_sel_global_ind_alias; [ exact Hres2 | exact Hia2 | exact Hg | constructor ].
  Qed.
End FiledOk.

(** What a global context files and has open is worth at a target, read
    from it, when each entry is. *)
Theorem valid_filed_mods_of_valid : forall Θm Ξm Θ2 Ξ2, ⊢ᵍ Θm ⍮ Ξm -> Emb Θm Ξm Θ2 Ξ2 ->
    gds_valid valid_entry valid_mod_tele valid_ind_decl_entry Θm Ξm Θ2 Ξ2 Θm -> gs_valid valid_entry valid_mod_tele valid_ind_decl_entry Θm Ξm Θ2 Ξ2 Ξm ->
    @valid_filed_mods (gc_mk Θ2 Ξ2) Θm Ξm.
Proof.
  intros * Hgm He HΘ HΞ p T Φ Hl.
  destruct (good_loc _ _ _ _ HΘ HΞ _ _ _ Hl) as [[HT HTa] _].
  destruct (gc_loc_grow _ _ _ _ (em_wf _ _ _ _ He) (em_res _ _ _ _ He) _ _ _ Hl) as (Φ2 & Hl2 & _).
  pose proof (loc_closed _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as [HTs _].
  constructor;
    [ eauto | intros ρ; exact (gc_loc_path _ _ (em_wf _ _ _ _ He) _ _ ρ Hl2) | exact HT | exact HTa | exact HTs
    | intros; eapply fo_kind; eassumption | intros; eapply fo_sub_kind; eassumption
    | intros; eapply fo_term; eassumption | intros; eapply fo_alias; eassumption ].
Qed.

(** A sound embedding, from the validity at the target of what the source
    files and has open, read from the source. *)
Theorem valid_emb_of : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid valid_entry valid_mod_tele valid_ind_decl_entry Θ Ξ Θ2 Ξ2 Θ -> gs_valid valid_entry valid_mod_tele valid_ind_decl_entry Θ Ξ Θ2 Ξ2 Ξ -> valid_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg He HΘ HΞ; constructor; [ exact He | exact Hg | exact (valid_filed_mods_of_valid _ _ _ _ Hg He HΘ HΞ) |].
  intros p D Hl; exact (proj1 (good_ind _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl)).
Qed.

Corollary valid_emb_good : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> GoodV valid_entry valid_mod_tele valid_ind_decl_entry Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    valid_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (valid_emb_of _ _ _ _ Hg (Embx_emb _ _ _ _ He) HΘ HΞ).
Qed.

Lemma gs_valid_tele : forall Θs Ξs Θ2 Ξ2 Ξ, gs_valid valid_entry valid_mod_tele valid_ind_decl_entry Θs Ξs Θ2 Ξ2 Ξ -> tele_ass (gs_tele Ξ).
Proof. intros * HΞ; destruct Ξ as [| [mp U] Ξ]; [ constructor | exact (proj2 (proj1 HΞ)) ]. Qed.

Lemma good_tele : forall Θ Ξ Θ2 Ξ2, GoodV valid_entry valid_mod_tele valid_ind_decl_entry Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> tele_ass (gs_tele Ξ).
Proof. intros * HG He; exact (gs_valid_tele _ _ _ _ _ (proj2 (HG _ _ He _ _ (gc_sub_refl _ _)))). Qed.
