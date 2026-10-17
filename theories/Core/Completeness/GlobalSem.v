(** * Valid Global Contexts

    A well-formed global context embeds soundly into itself ([gctx_sem]):
    what it files and has open is valid at it, read at it ([gfiled_ok]),
    and so are its declarations.  Validity is read from the validity of
    each entry, established when the entry is checked, along every
    embedding ([global_valid]); a unit valid read at a global context stays
    valid read at a bigger one ([semK_grow_all]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System IndCong.
From Mctt.Core.Syntactic.System Require Import MemberLemmas MemberWf GlobalModules GlobalPaths DescTyping LookupSound
  IndSyntax.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases LetCases LevelCases SubstitutionCases SubtypingCases
  TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases InstanceCases
  MemberReps IndCases TeleSem ElimCases ElimIota
  ModuleVal ModuleSem UnitSub ModexpRules GlobalArgs IndSem SemK UnitBody FiledSem UnitSem MemSem CanonSem AppSem SelSem
  ModuleCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** ** 1. Valid units, read at a bigger global context *)

Section Grow.
  Context {GC : GCtx}.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg1 : ⊢ᵍ Θ1 ⍮ Ξ1.
  Hypothesis He : Emb Θ1 Ξ1 Θ2 Ξ2.

  Lemma semK_grow_all :
    (forall Γ K, semK Θ1 Ξ1 Γ K -> semK Θ2 Ξ2 Γ K) /\ (forall Γ H, smt Θ1 Ξ1 Γ H -> smt Θ2 Ξ2 Γ H).
  Proof.
    pose proof He as [Hg2 Hs].
    destruct (emb_preserves_wf _ _ _ _ He) as (_ & _ & _ & _ & _ & _ & Hwm).
    apply semK_smt_ind.
    - intros Γ p T Φ Ns Hw Hgl HΓ Hsa.
      destruct (gc_loc_grow _ _ _ _ Hg2 Hs _ _ _ Hgl) as (Φ2 & Hgl2 & _).
      exact (sk_filed _ _ _ _ _ _ _ (Hwm _ _ _ Hw) Hgl2 HΓ Hsa).
    - intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC _ IHsl Hsh Hshx HU Hopv _ IHops.
      exact (sk_body _ _ _ _ _ _ (Hwm _ _ _ Hw) (emb_body_xp _ _ _ _ Hg1 He _ _ _ Hx) HΔ HΓ HC IHsl Hsh Hshx HU Hopv IHops).
    - intros Γ Δ E Hw HΔ HΓ HΔΓ HU HE _ IHE.
      exact (sk_alias _ _ _ _ _ (Hwm _ _ _ Hw) HΔ HΓ HΔΓ HU HE IHE).
    - intros Γ H R Rm K RK Hw HmH HmodH HHK _ IHK HmK HmodK.
      destruct (emb_mdenote _ _ _ _ Hg1 He _ _ _ HmH) as (R2 & HmH2 & Hd).
      destruct (dsg_mod _ _ _ _ Hs _ _ _ Hd HmodH) as (Rm2 & HmodH2 & Hdm).
      destruct (emb_mdenote _ _ _ _ Hg1 He _ _ _ HmK) as (RK2 & HmK2 & HdK).
      destruct (dsg_mod _ _ _ _ Hs _ _ _ HdK HmodK) as (Rm2' & HmodK2 & Hdm').
      pose proof (dsg_functional _ _ _ _ _ _ _ Hdm Hdm') as <-.
      exact (smt_intro _ _ _ _ _ _ _ _ (Hwm _ _ _ Hw) HmH2 HmodH2 HHK IHK HmK2 HmodK2).
  Qed.

  Corollary semK_grow : forall Γ K, semK Θ1 Ξ1 Γ K -> semK Θ2 Ξ2 Γ K.
  Proof. exact (proj1 semK_grow_all). Qed.
End Grow.

(** ** 2. Closed units, in any context *)

Section Closed.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.

  Lemma rel_wk_to_nil : forall Γ, ⊨ Γ -> rel_wk_under_ctx Γ (wk_shiftn (length Γ)) ⋅.
  Proof.
    intros * HΓ.
    destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
    eapply (rel_wk_under_ctx_intro (R' := fun _ _ => True)); [ exact HR | exact per_ctx_env_nil_true |].
    constructor; [ exact (wk_mono_shiftn _) | intros; exact I ].
  Qed.

  Lemma semK_closed_weaken : forall Γ U, semK Θm Ξm ⋅ (me_lit U) -> gunit_scoped 0 U -> ⊨ Γ -> wf_ctx Θm Ξm Γ ->
      semK Θm Ξm Γ (me_lit U).
  Proof.
    intros * HK HU HΓ Hw.
    assert (Hw' : wf_ctx Θm Ξm (Γ ++ ⋅)) by (rewrite app_nil_r; exact Hw).
    pose proof (wf_wk_shiftn_app' _ _ _ _ Hw') as Hφ; rewrite app_nil_r in Hφ.
    pose proof (semK_gsub Hgw _ _ Hgm Hsub _ _ _ _ HK (gsub_wk _ _ _ (rel_wk_to_nil _ HΓ) HΓ sem_ctx_nil)
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
Definition sem_V (Θs : gdeps) (Ξs : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A oM =>
      exists A0 i oM0, A = ctx_pi T A0 /\ oM = option_map (ctx_fn T) oM0 /\
        @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (Typeω@i) A0 A0 /\
        (forall M0, oM0 = Some M0 -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T A0 M0 M0)
  | ge_mod _ U => ⊢ᵍ Θs ⍮ Ξs -> @semK (gc_mk Θ2 Ξ2) Θs Ξs ⋅ (me_lit U)
  | ge_ind _ _ _ _ => True
  | ge_ind_alias _ Δ p Ns =>
      exists Δ0 D i, Δ = Δ0 ++ T /\ ind_lookup Θs Ξs p = Some D /\ ind_lookup Θ2 Ξ2 p = Some D /\
        @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (Typeω@i) (ctx_pi Δ0 (ind_ty_at D Ns)) (ctx_pi Δ0 (ind_ty_at D Ns)) /\
        @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (ctx_pi Δ0 (ind_ty_at D Ns))
          (ctx_fn Δ0 (apps_exp (a_ind p) Ns)) (ctx_fn Δ0 (apps_exp (a_ind p) Ns))
  end.

(** The telescope of a module. *)
Definition sem_F (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop :=
  @sem_ctx (gc_mk Θ2 Ξ2) T /\ tele_ass T.

(** A declaration: valid, and the type of its type former, abstracted over
    the outer part of its parameters, a type over the inner part. *)
Definition sem_VD (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop :=
  @sem_core (gc_mk Θ2 Ξ2) D /\
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
Lemma semK_alias_valid0 : forall {GC : GCtx} Θs Ξs Ta Ea, semK Θs Ξs ⋅ (me_lit (gu_mk Ta (md_alias Ea))) ->
    ⋅ ⊨ᵐ me_lit (gu_mk Ta (md_alias Ea)) ≈ me_lit (gu_mk Ta (md_alias Ea)).
Proof.
  intros * HK; inversion HK; subst; [ exfalso; eapply me_apps_qname_not_lit; eassumption | assumption ].
Qed.

Lemma ent_kind_grows : forall E1 E2, entry_grows E1 E2 -> ent_kind E1 = ent_kind E2.
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
  Hypothesis HΘ : gds_valid sem_V sem_F sem_VD Θm Ξm Θ2 Ξ2 Θm.
  Hypothesis HΞ : gs_valid sem_V sem_F sem_VD Θm Ξm Θ2 Ξ2 Ξm.

  #[local] Instance GC2 : GCtx := gc_mk Θ2 Ξ2.

  Lemma fo_wf : ⊢ᵍ Θ2 ⍮ Ξ2.
  Proof. exact (em_wf _ _ _ _ He). Qed.

  Lemma fo_sub : gc_sub Θm Ξm Θ2 Ξ2.
  Proof. exact (em_res _ _ _ _ He). Qed.

  Lemma good_loc : forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) ->
      sem_F Θ2 Ξ2 T /\ gm_valid sem_V sem_F sem_VD Θm Ξm Θ2 Ξ2 T Φ.
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
  Lemma fo_alias_semK : forall p T Φ x Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua -> semK Θm Ξm ⋅ (me_lit Ua).
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
    pose proof (fo_alias_semK _ _ _ _ _ _ _ Hl Hp HUa) as HK.
    assert (HUa' : exists Ta Ea, Ua = gu_mk Ta (md_alias Ea))
      by (destruct E as [| pv [Ta [| Ea]] | | pv Δa pq Nsa]; cbn in HUa; try discriminate; injection HUa as <-; eauto).
    destruct HUa' as (Ta & Ea & ->).
    pose proof (valid_nil_kind _ _ _ (semK_alias_valid0 _ _ _ _ HK) per_ctx_env_nil_true nil I) as Hk.
    inversion Hk; subst.
    eapply dk_global_alias; [ exact Hm | eassumption ].
  Qed.

  (** Each entry of a stored body has its kind at the target. *)
  Lemma fo_kind : forall p T Φ x Φ0 E, gc_loc Θm Ξm p = Some (T, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      dkind Θ2 Ξ2 (dm_global p nil) (x :: nil) (ent_kind E).
  Proof.
    intros * Hl Hp.
    destruct (fo_entry _ _ _ _ _ _ Hl Hp) as (Φ2 & E2 & Hl2 & Hent2 & HeE2 & Hgr & _).
    pose proof (gc_loc_loc _ _ _ _ _ Hl2) as Hlc2.
    rewrite (ent_kind_grows _ _ Hgr).
    destruct E2 as [b pv A B | pv [Δ [sm Φ' | Ea]] | pv pq D ΦD | pv Δ pq Ns]; cbn [ent_kind].
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
      forall Γ, ⊨ Γ -> wf_ctx Θm Ξm Γ -> semK Θm Ξm Γ (me_lit Ua).
  Proof.
    intros * Hl Hp HUa; split; [ exact (fo_alias_module _ _ _ _ _ _ _ Hl Hp HUa) |].
    intros Γ HΓ Hw.
    pose proof (loc_closed _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as [_ Hc].
    apply (@semK_closed_weaken GC2 fo_wf _ _ Hgm fo_sub); [ exact (fo_alias_semK _ _ _ _ _ _ _ Hl Hp HUa) | | exact HΓ | exact Hw ].
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
      (exists j E0 e, ⟦ ctx_pi T A0 ⟧ nil ↘ e /\ per_univ_elem j E0 e e /\ E0 g g).
  Proof.
    intros * HTa HT HA0 HM0 Hg Hats; split.
    - intros * -> Hl Ha; destruct (Hats _ _ _ _ eq_refl Hl Ha) as [Hty Hred]; split; [ exact Hty | right ].
      destruct (tele_ass_app_inv _ _ HTa) as [HTa1 HTa2].
      exists (ctx_fn T1 M0); split; [ exact Hred |]; split; [ exact (valid_ctx_fn _ _ _ _ HTa1 HT HM0) |].
      intros ns m Hlen Hm.
      destruct (eval_ctx_fn_apps _ _ _ _ _ HTa2 Hlen Hm) as (f & Hf & Hfa).
      rewrite <- ctx_fn_app in Hf; pose proof (functional_eval_exp _ _ _ _ Hf Hg) as ->; exact Hfa.
    - assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
      assert (HM0' : T ++ ⋅ ⊨ M0 : A0) by (rewrite app_nil_r; exact HM0).
      pose proof (valid_ctx_fn _ _ _ _ HTa HT0 HM0') as Hfn.
      destruct (valid_at _ _ _ _ Hfn per_ctx_env_nil_true nil nil I) as (m & m' & e & j & E0 & Hm & Hm' & He0 & HE0 & Hmm).
      pose proof (functional_eval_exp _ _ _ _ Hm Hg) as ->; pose proof (functional_eval_exp _ _ _ _ Hm' Hg) as ->.
      exists j, E0, e; repeat split; assumption.
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
      exists A0 i g, T ⊨ A0 : Typeω@i /\
        (forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> ds_ats R0 Ns = Some R1 ->
           ds_ty Θm Ξm R1 = Some (ctx_pi T1 A0)[sb_of_list Id Ns] /\
           (ds_red R1 = None \/
            exists M1, ds_red R1 = Some M1[sb_of_list Id Ns] /\ T2 ⊨ M1 : ctx_pi T1 A0 /\
              forall ns m, List.length ns = List.length T2 -> ⟦ M1 ⟧ env_args nil ns ↘ m ->
                $*| g & ns | gc_deps ⍮ gc_stack ↘ m)) /\
        dm_global p nil ·ₜ x gc_deps ⍮ gc_stack ↘ g /\
        (exists j E0 e, ⟦ ctx_pi T A0 ⟧ nil ↘ e /\ per_univ_elem j E0 e e /\ E0 g g).
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
        destruct (valid_at _ _ _ _ (valid_ctx_fn _ _ _ _ HTa HT0 HM0') per_ctx_env_nil_true nil nil I)
          as (g & _ & _ & _ & _ & Hg & _).
        destruct (fo_term_fn _ _ _ _ _ g HTa HT HA0 (HM0 _ eq_refl) Hg Hats) as [Hred Hper].
        exists A0, i, g; split; [ exact HA0 | split; [ exact Hred | split; [| exact Hper ] ] ].
        eapply eval_sel_global; [ exact HeE2 | exact Hg | constructor ]. }
      all: (* an axiom or an abstract definition: its name, a neutral *)
        assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT);
        assert (HA0' : T ++ ⋅ ⊨ A0 : Typeω@i) by (rewrite app_nil_r; exact HA0);
        destruct (rel_exp_ctx_pi _ _ _ _ HTa HT0 HA0') as [j HP];
        destruct (rel_exp_of_typ_inversion_simple_at per_ctx_env_nil_true HP nil nil I) as (e & e' & Hev & Hev' & [E0 HE0]);
        pose proof (functional_eval_exp _ _ _ _ Hev' Hev) as ->;
        exists A0, i, (⇑ e (d_glob (qname_app p (x :: nil)))); split; [ exact HA0 |]; split;
        [ intros * HT12 Hlen Ha; destruct (Hats _ _ _ _ HT12 Hlen Ha) as [Hty Hred]; cbn in Hred;
          split; [ exact Hty | left; exact Hred ] |];
        split; [ eapply eval_sel_global_neut; [ exact HeE2 | first [ left; reflexivity | right; reflexivity ] | exact Hev | constructor ] |];
        exists j, E0, e; split; [ exact Hev |]; split; [ exact HE0 | exact (per_bot_then_per_elem HE0 (per_bot_glob _)) ].
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
      pose proof Hdt as (_ & _ & _ & _ & Hsu & _).
      pose proof (loc_coh _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as Hcoh.
      destruct (gm_coh_child _ _ _ _ Hcoh (gm_entry_submodule _ T _ _ _ _ _ _ Hent))
        as [(Δu & oD & [= HU _] & HΔu) | (? & ? & [=] & _)].
      set (Δp := ind_nparams D ++ Δu).
      assert (Hpar : ind_params D = Δp ++ T)
        by (subst Δp; rewrite <- app_assoc, <- HU; unfold ind_nparams, ind_uparams; symmetry; apply firstn_skipn).
      set (S' := (ind_sort D)[wk_shiftn (ind_nn D)]ʷ).
      destruct (HDs _ _ Hpar) as [i HA0].
      pose proof (@valid_exp_ind0 GC2 D HD Hc Hsu (qname_in p x) Hind2) as Hind0.
      assert (Hty : ind_ty D = ctx_pi T (ctx_pi Δp S')) by (unfold ind_ty; rewrite Hpar, ctx_pi_app; reflexivity).
      rewrite Hty in Hind0.
      destruct (valid_at _ _ _ _ Hind0 per_ctx_env_nil_true nil nil I) as (g & g' & e & j & E0 & Hg & Hg' & He0 & HE0 & Hgg).
      assert (Hgd : ⟦ a_ind (qname_in p x) ⟧ nil ↘ d_ind (qname_in p x) nil) by constructor.
      pose proof (functional_eval_exp _ _ _ _ Hg Hgd) as ->; pose proof (functional_eval_exp _ _ _ _ Hg' Hgd) as ->.
      exists (ctx_pi Δp S'), i, (d_ind (qname_in p x) nil).
      split; [ exact HA0 |]; split; [| split ].
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
          pose proof (sem_ctx_app_r _ _ HT12') as HT2.
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
      + exists j, E0, e; repeat split; assumption.
    - (* an inductive alias: its type former at its arguments *)
      cbn in HV; destruct HV as [_ (Δ0 & D & i & -> & HlD & HlD2 & HA0 & HM0)].
      assert (HE2 : ge_ind_alias pv (Δ0 ++ T) pq Ns' = E2)
        by (apply entry_grows_eq; [ exact Hgr | intros * -> | intros * -> ]; cbn in Hgr; discriminate).
      subst E2; destruct (gc_entry_ind_alias _ _ _ _ _ _ _ HeE2) as [Hres2 Hia2]; rewrite qname_in_app in Hres2, Hia2.
      assert (HT0 : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
      assert (HM0' : T ++ ⋅ ⊨ ctx_fn Δ0 (apps_exp (a_ind pq) Ns') : ctx_pi Δ0 (ind_ty_at D Ns'))
        by (rewrite app_nil_r; exact HM0).
      destruct (valid_at _ _ _ _ (valid_ctx_fn _ _ _ _ HTa HT0 HM0') per_ctx_env_nil_true nil nil I)
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
      exists (ctx_pi Δ0 (ind_ty_at D Ns')), i, g; split; [ exact HA0 | split; [ exact Hred | split; [| exact Hper ] ] ].
      rewrite <- ctx_fn_app in Hg.
      eapply eval_sel_global_ind_alias; [ exact Hres2 | exact Hia2 | exact Hg | constructor ].
  Qed.
End FiledOk.

(** What a global context files and has open is worth at a target, read
    from it, when each entry is. *)
Theorem filed_ok_of_valid : forall Θm Ξm Θ2 Ξ2, ⊢ᵍ Θm ⍮ Ξm -> Emb Θm Ξm Θ2 Ξ2 ->
    gds_valid sem_V sem_F sem_VD Θm Ξm Θ2 Ξ2 Θm -> gs_valid sem_V sem_F sem_VD Θm Ξm Θ2 Ξ2 Ξm ->
    @gfiled_ok (gc_mk Θ2 Ξ2) Θm Ξm.
Proof.
  intros * Hgm He HΘ HΞ p T Φ Hl.
  destruct (good_loc _ _ _ _ HΘ HΞ _ _ _ Hl) as [[HT HTa] _].
  destruct (gc_loc_grow _ _ _ _ (em_wf _ _ _ _ He) (em_res _ _ _ _ He) _ _ _ Hl) as (Φ2 & Hl2 & _).
  pose proof (loc_closed _ _ Hgm _ _ _ (gc_loc_loc _ _ _ _ _ Hl)) as [HTs _].
  split; [ eauto |]; split; [ intros ρ; exact (gc_loc_path _ _ (em_wf _ _ _ _ He) _ _ ρ Hl2) |].
  split; [ exact HT |]; split; [ exact HTa |]; split; [ exact HTs |].
  split; [ intros; eapply fo_kind; eassumption |].
  split; [ intros; eapply fo_sub_kind; eassumption |].
  split; [ intros; eapply fo_term; eassumption |].
  intros; eapply fo_alias; eassumption.
Qed.

(** A sound embedding, from the validity at the target of what the source
    files and has open, read from the source. *)
Theorem sem_emb_of : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid sem_V sem_F sem_VD Θ Ξ Θ2 Ξ2 Θ -> gs_valid sem_V sem_F sem_VD Θ Ξ Θ2 Ξ2 Ξ -> sem_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg He HΘ HΞ; constructor; [ exact He | exact Hg | exact (filed_ok_of_valid _ _ _ _ Hg He HΘ HΞ) |].
  intros p D Hl; exact (proj1 (good_ind _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl)).
Qed.

Corollary sem_emb_good : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    sem_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (sem_emb_of _ _ _ _ Hg (Embx_emb _ _ _ _ He) HΘ HΞ).
Qed.

(** Judgments read along a sound embedding. *)
Lemma kread : forall Θ Ξ Θ2 Ξ2 Γ A M, sem_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M.
Proof.
  intros * Hμ HM; destruct kripke_fundamental as (_ & Ke & _).
  exact (proj2 (proj2 (Ke _ _ _ _ _ HM _ _ Hμ))).
Qed.

Lemma kread_ctx : forall Θ Ξ Θ2 Ξ2 Γ, sem_emb Θ Ξ Θ2 Ξ2 -> wf_ctx Θ Ξ Γ -> @sem_ctx (gc_mk Θ2 Ξ2) Γ.
Proof.
  intros * Hμ HΓ; destruct kripke_fundamental as (Kc & _).
  exact (proj1 (Kc _ _ _ HΓ _ _ Hμ)).
Qed.

Lemma svalid_tele : forall Θs Ξs Θ2 Ξ2 Ξ, gs_valid sem_V sem_F sem_VD Θs Ξs Θ2 Ξ2 Ξ -> tele_ass (gs_tele Ξ).
Proof. intros * HΞ; destruct Ξ as [| [mp U] Ξ]; [ constructor | exact (proj2 (proj1 HΞ)) ]. Qed.

Lemma good_tele : forall Θ Ξ Θ2 Ξ2, GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> tele_ass (gs_tele Ξ).
Proof. intros * HG He; exact (svalid_tele _ _ _ _ _ (proj2 (HG _ _ He _ _ (gc_sub_refl _ _)))). Qed.

(** ** 7. Each entry is valid where it is checked *)

Lemma sem_V_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> GoodV sem_V sem_F sem_VD Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid sem_V sem_F sem_VD Θ Ξ Θ2 Ξ2 Θ -> gs_valid sem_V sem_F sem_VD Θ Ξ Θ2 Ξ2 Ξ ->
    forall Θs Ξs, sem_V Θs Ξs Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM _ He HΘ HΞ Θs Ξs.
  pose proof (sem_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) He HΘ HΞ) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  exists A, i, (Some M); split; [ reflexivity |]; split; [ reflexivity |].
  split; [ exact (kread _ _ _ _ _ _ _ Hμ HA) | intros ? [= <-]; exact (kread _ _ _ _ _ _ _ Hμ HM) ].
Qed.

Lemma sem_V_ax : forall Θ Ξ A i b pv Θ2 Ξ2 Θs Ξs,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    sem_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He _.
  pose proof (sem_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HA)) HG He) as Hμ.
  exists A, i, None; split; [ reflexivity |]; split; [ reflexivity |].
  split; [ exact (kread _ _ _ _ _ _ _ Hμ HA) | discriminate ].
Qed.

Lemma sem_V_alias : forall Θ Ξ pv Δ E Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    sem_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * HΔ _ HE HG He Hs HgS; cbn.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  pose proof (sem_emb_good _ _ _ _ Hg HG He) as Hμ.
  assert (Ht : tele_ass (Δ ++ gs_tele Ξ)) by (apply List.Forall_app; split; [ exact HΔ | exact (good_tele _ _ _ _ HG He) ]).
  assert (HE' : Θ ⍮ Ξ ⍮ (Δ ++ gs_tele Ξ) ++ ⋅ ⊢ᵐ E ≈ E) by (rewrite app_nil_r; exact HE).
  assert (HC : wf_ctx Θ Ξ ((Δ ++ gs_tele Ξ) ++ ⋅)) by (rewrite app_nil_r; exact (presup_modexp_eq_ctx HE)).
  assert (HU : Θ ⍮ Ξ ⍮ ⋅ ⊢ᵘ gu_mk (Δ ++ gs_tele Ξ) (md_alias E) ≈ gu_mk (Δ ++ gs_tele Ξ) (md_alias E))
    by (apply wf_unit_eq_alias; [ exact (ext_of_ctx _ _ _ _ HC) | exact Ht | exact Ht | exact HE' | exact HE' ]).
  destruct kripke_fundamental as (_ & _ & _ & _ & _ & _ & Ku & _).
  destruct (Ku _ _ _ _ _ HU _ _ Hμ) as (_ & HK & _).
  exact (semK_grow _ _ _ _ Hg {| em_wf := HgS; em_res := Hs |} _ _ HK).
Qed.

Lemma sem_V_indalias : forall Θ Ξ pv Δ p Ns D Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> ind_lookup Θ Ξ p = Some D -> List.length Ns <= ind_nu D ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps_exp (a_ind p) Ns : ind_ty_at D Ns ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    sem_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns).
Proof.
  intros * _ _ Hl _ HM _ HG He Hs.
  pose proof (presup_exp_ctx HM) as HC.
  pose proof (sem_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ HC) HG He) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf _ _ _ _ _ _ HC HA) as [j HP].
  pose proof (ctx_fn_wf _ _ _ _ _ _ _ HC HA HM) as HF.
  exists Δ, D, j; split; [ reflexivity |]; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) |].
  split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ (gc_subx_sub _ _ _ _ (emx_res _ _ _ _ He)) Hl) |].
  split; [ exact (kread _ _ _ _ _ _ _ Hμ HP) | exact (kread _ _ _ _ _ _ _ Hμ HF) ].
Qed.

Lemma sem_F_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> wf_ctx Θ Ξ (Δ ++ gs_tele Ξ) -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    sem_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof.
  intros * HΔ HC HG He.
  pose proof (sem_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ HC) HG He) as Hμ.
  split; [ exact (kread_ctx _ _ _ _ _ Hμ HC) |].
  apply List.Forall_app; split; [ exact HΔ | exact (good_tele _ _ _ _ HG He) ].
Qed.

(** A type at a sort is a type. *)
Lemma sort_large_sem : forall {GC : GCtx} S φ Γ X, ind_sort_univ S -> Γ ⊨ X : S[φ]ʷ -> exists j : nat, Γ ⊨ X : Typeω@j.
Proof.
  intros * [[i ->] | [t ->]] H; cbn [exp_wk] in H; [ exists i; exact H | exists 0; eapply rel_exp_suniv_tm_large; exact H ].
Qed.

(** A declaration typed at the source is valid at the target: its
    judgments, read in the PER model. *)
Lemma sem_core_of_typed : forall Θ Ξ D Θ2 Ξ2, decl_typed Θ Ξ D -> sem_emb Θ Ξ Θ2 Ξ2 -> @sem_core (gc_mk Θ2 Ξ2) D.
Proof.
  intros * Hdt Hμ.
  pose proof Hdt as (Hass & _ & Hle & HΔ & Hsu & [i HS] & _ & HA & HPl & HP & HN & Hnd & Hsh).
  destruct kripke_fundamental as (Kc & _).
  assert (Harg : forall c gs k A, ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (astrat gs k ++ ind_params D) ((ind_sort D)[wk_shiftn (k + ind_nn D)]ʷ) A A /\
             exists j : nat, @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (astrat gs k ++ ind_params D) (Typeω@j) A A).
  { intros * Hcon HA0.
    destruct (nonrec_nth_split _ _ _ HA0) as (gs1 & gs2 & Heq & Hk).
    pose proof (HA _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as HT.
    assert (Hls : List.length (cargs_strat gs1) = k) by (rewrite cargs_strat_nonrec, List.length_rev, List.length_map; exact Hk).
    rewrite Hls, (astrat_prefix gs1 (ca_arg A :: gs2)), Hk, <- Heq in HT.
    pose proof (kread _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ]. }
  assert (Hstrat : forall c gs k, ind_con D c = Some gs -> k <= List.length (cargs_nonrec gs) ->
             @sem_ctx (gc_mk Θ2 Ξ2) (astrat gs k ++ ind_params D)).
  { intros c gs k Hcon; induction k as [| k IH]; intros Hk.
    + unfold astrat; cbn [List.firstn List.rev List.app]; exact (proj1 (Kc _ _ _ HΔ _ _ Hμ)).
    + destruct (nth_error_lt_some' (cargs_nonrec gs) k ltac:(lia)) as [A HA0].
      assert (Hst : astrat gs (S k) = ce_ass A :: astrat gs k).
      { unfold astrat; rewrite (firstn_S_snoc _ _ (ce_ass A)) by (rewrite List.nth_error_map, HA0; reflexivity).
        rewrite List.rev_app_distr; reflexivity. }
      rewrite Hst; cbn [List.app].
      destruct (Harg _ _ _ _ Hcon HA0) as (_ & j & Hj).
      exact (@sem_ctx_ext_typ (gc_mk Θ2 Ξ2) _ _ _ (IH ltac:(lia)) Hj). }
  assert (Hdom : forall c gs gs1 t gs2 k B, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             List.nth_error (ptyp_doms t) k = Some B ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (doms_ctx (List.firstn k (ptyp_doms t)) ++ astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D)
               ((ind_sort D)[wk_shiftn (k + List.length (cargs_nonrec gs1) + ind_nn D)]ʷ) B B /\
             exists j : nat, @rel_exp_under_ctx (gc_mk Θ2 Ξ2)
               (doms_ctx (List.firstn k (ptyp_doms t)) ++ astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D) (Typeω@j) B B).
  { intros * Hcon Heq HB.
    destruct (Hsh _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as [_ Hs2].
    assert (Hsplit : ptyp_doms t = List.firstn k (ptyp_doms t) ++ B :: List.skipn (S k) (ptyp_doms t))
      by (rewrite <- (skipn_nth_cons' _ _ _ HB), List.firstn_skipn; reflexivity).
    pose proof (Hs2 _ _ _ Hsplit) as HT.
    assert (Hk : List.length (List.firstn k (ptyp_doms t)) = k)
      by (rewrite List.length_firstn; assert (k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
    assert (Hls : List.length (cargs_strat gs1) = List.length (cargs_nonrec gs1))
      by (rewrite cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hk, Hls, (astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in HT.
    pose proof (kread _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ]. }
  constructor.
  - exact (proj1 (Kc _ _ _ HΔ _ _ Hμ)).
  - exists i; exact (kread _ _ _ _ _ _ _ Hμ HS).
  - destruct (ind_ty_typed0 _ _ _ Hdt) as [j Hj]; exists j; exact (kread _ _ _ _ _ _ _ Hμ Hj).
  - intros k A HA0.
    destruct (nparams_nth_split _ _ _ HA0) as [Δ1 HΔ1].
    assert (Hk : k < ind_nn D)
      by (rewrite <- (length_nparams D), <- List.length_rev; apply List.nth_error_Some; congruence).
    pose proof (HN _ _ _ HΔ1) as HT; rewrite length_npre in HT by lia.
    pose proof (kread _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ].
  - exact Hstrat.
  - exact Harg.
  - exact Hnd.
  - intros * Hcon Heq HPk HT.
    assert (Hls : List.length (cargs_nonrec gs1) = List.length (cargs_strat gs1))
      by (rewrite cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hls in HT.
    pose proof (HP _ _ _ _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq HPk HT) as H.
    rewrite (astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (kread _ _ _ _ _ _ _ Hμ H).
  - exact Hdom.
  - intros * Hcon Heq; exact (proj1 (Hsh _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq)).
  - intros * Hcon Heq; exact (HPl _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq).
  - intros c gs gs1 t gs2 k Hcon Heq; induction k as [| k IH]; intros Hk.
    + cbn [List.firstn doms_ctx List.map List.rev List.app].
      apply Hstrat with (c := c); [ exact Hcon | rewrite Heq, cargs_nonrec_app, List.length_app; lia ].
    + destruct (nth_error_lt_some' (ptyp_doms t) k ltac:(lia)) as [B HB].
      rewrite (firstn_S_snoc _ _ _ HB), doms_ctx_snoc; cbn [List.app].
      destruct (Hdom _ _ _ _ _ _ _ Hcon Heq HB) as (_ & j & Hj).
      exact (@sem_ctx_ext_typ (gc_mk Θ2 Ξ2) _ _ _ (IH ltac:(lia)) Hj).
Qed.

Lemma sem_V_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> sem_VD Θ2 Ξ2 D /\ sem_F Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * Hdt HG He.
  pose proof Hdt as (Hass & _ & _ & HΔ & _).
  pose proof (sem_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) HG He) as Hμ.
  split; [ split; [ exact (sem_core_of_typed _ _ _ _ _ Hdt Hμ) |] |].
  - intros Δ1 Δ2 Hpar.
    destruct (ind_ty_typed0 _ _ _ Hdt) as [j Hj]; unfold ind_ty in Hj.
    pose proof (proj1 (ctx_pi_split_typed _ _ _ _ Hass Hj) _ _ Hpar) as H; rewrite app_nil_r in H.
    exists j; exact (kread _ _ _ _ _ _ _ Hμ H).
  - destruct (decl_typed_uparams _ _ _ Hdt) as [HUw HUa].
    split; [ exact (kread_ctx _ _ _ _ _ Hμ HUw) | exact HUa ].
Qed.

(** ** 8. Every well-formed global context embeds soundly into itself *)

Theorem gctx_sem : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> sem_emb Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply sem_emb_good; [ exact Hg | | apply Embx_refl; exact Hg ].
  exact (global_valid sem_V sem_F sem_VD sem_V_def sem_V_ax sem_V_alias sem_V_indalias sem_F_nil sem_V_ind _ _ Hg).
Qed.
