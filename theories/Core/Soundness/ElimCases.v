(** * The Eliminator in the Gluing Model

    The gluing rules of the eliminator and of its congruence and view
    rules.  An elimination is glued at the target of a sound embedding,
    where the groups of the source are valid groups
    ([valid_groups_of_glu_gctx_embedding], [Inductives/Elim.v]), at each
    instance of its context: its parts are glued at the instances of their
    contexts, and the motive and branch contexts are extensions glued at
    the instances ([glu_rel_ext_under_sub]), so that the instance lifted
    through them is one of theirs. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Elim.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution Instance.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Completeness.Modules Require MemberTypes.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases
  Instances
  Extensions.
Require Import Mctt.Core.Soundness.Inductives.Con.
Require Import Mctt.Core.Soundness.Inductives.Bridge.
Require Import Mctt.Core.Soundness.Inductives.Elim.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes.
Require Import Mctt.Core.Soundness.Inductives.ArgTypes.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

(** The non-uniform parameters and the scrutinee of an eliminator, at the
    instances of its motive's context: the parameters at the instances of
    their telescope, the scrutinee at the member's type.  For any property
    [Q] of a term at a type. *)
Lemma elim_mctx_insts_of_params : forall p D, decl_closed D ->
    forall (Q : exp -> typ -> Prop) m Mm Ps M, ind_member D m = Some Mm ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Q Pk T) ->
    Q M (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) ->
    forall j N T, List.nth_error (List.skipn (ind_nu D) Ps ++ M :: nil) j = Some N ->
      List.nth_error (tele_insts (elim_mctx p D m Mm (List.firstn (ind_nu D) Ps)) Id (List.skipn (ind_nu D) Ps ++ M :: nil)) j = Some T ->
      Q N T.
Proof.
  intros p D Hc Q m Mm Ps M HMm HPl HPg HM.
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  assert (Hti : tele_insts (im_params D Mm) Id Ps
                = tele_insts (ind_uparams D) Id Us ++ tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns).
  { unfold Us, Ns; rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
      [ exact (decl_closed_ass _ Hc) | fold Us; rewrite HUl; reflexivity ]. }
  assert (HlTU : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in *; lia).
  (** The non-uniform parameters, at their instances *)
  assert (HNs : forall j N T0, List.nth_error Ns j = Some N ->
             List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T0 -> Q N T0).
  { intros j N T0 HN HT; apply (HPg (ind_nu D + j)).
    - unfold Ns in HN; rewrite List.nth_error_skipn in HN; exact HN.
    - rewrite Hti, List.nth_error_app2, HlTU by lia; replace (ind_nu D + j - ind_nu D) with j by lia; exact HT. }
  assert (Hrass : all_assumptions (tele_sub (im_nparams Mm) (sb_of_list Id Us)))
    by (apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMm)).
  intros j N T0 HN HT.
  unfold elim_mctx in HT; change (ce_ass ?κ0 ?H0 :: ?R) with ((ce_ass κ0 H0 :: nil) ++ R) in HT.
  rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub; exact HNl).
  assert (Hl2 : List.length (tele_insts (tele_sub (im_nparams Mm) (sb_of_list Id Us)) Id Ns) = im_nn Mm)
    by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_im_nparams; lia).
  destruct (Nat.lt_ge_cases j (im_nn Mm)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HN by lia.
    rewrite List.nth_error_app1 in HT by lia.
    rewrite tele_insts_tele_sub in HT.
    rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT by (intros x; cbn; apply sentry_sub_id).
    exact (HNs _ _ _ HN HT).
  - rewrite List.nth_error_app2 in HN by lia.
    rewrite List.nth_error_app2, Hl2 in HT by lia.
    rewrite HNl in HN.
    destruct (j - im_nn Mm) as [| j'] eqn:Hk'; cbn in HN, HT; [| destruct j'; discriminate ].
    injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
    rewrite ind_head_inst by (try exact Hc; try exact HUl; exact HNl).
    rewrite (List.map_ext (fun U => U[Id]) (fun U => U)), List.map_id by (intros; apply exp_sub_id).
    exact HM.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The motive's instance at the non-uniform parameters and the scrutinee,
    at an instance of the context: the motive at the instance extended by
    their instances, an instance of the motive's context
    ([glu_rel_sub_inst_of_list]).  As [rel_exp_motive_instance_prop]. *)
Lemma glu_rel_exp_motive_instance_at : forall p D, decl_closed D ->
    forall Γ m Mm A S Ps M Γ' τ, ind_member D m = Some Mm ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       glu_rel_exp_under_sub Γ Pk T) ->
    glu_rel_exp_under_sub Γ M (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) ->
    glu_rel_exp_under_sub (elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ) A S ->
    type_sort S ->
    glu_rel_sub_inst Γ' τ Γ ->
    Γ' ⊩ A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)][τ] : S.
Proof.
  intros p D Hc * HMm HPl HPg HM HA HS Hτ.
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  set (Ps' := List.map (fun P => P[τ]) Ps).
  assert (E : A[sb_of_list Id (Ns ++ M :: nil)][τ] = A[sb_of_list τ (List.skipn (ind_nu D) Ps' ++ M[τ] :: nil)]).
  { rewrite exp_sub_sub; apply exp_sub_sb_eq; intros x.
    rewrite sb_of_list_compose_gen.
    unfold Ps'; rewrite List.skipn_map, List.map_app; fold Ns; cbn [List.map].
    apply sb_of_list_cong; intros y; reflexivity. }
  rewrite E.
  assert (HΨ : ⊢ elim_mctx p D m Mm Us ++ Γ)
    by (destruct (glu_rel_ctx_types_ctx _ (glu_rel_exp_under_sub_ctx _ _ _ HA)) as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb)).
  assert (Hinst : glu_rel_sub_inst Γ' (sb_of_list τ (List.skipn (ind_nu D) Ps' ++ M[τ] :: nil)) (elim_mctx p D m Mm Us ++ Γ)).
  { apply glu_rel_sub_inst_of_list; [ exact (elim_mctx_ass p D m Mm Us Hc HMm) | exact Hτ | exact HΨ
                                    | unfold Ps'; rewrite List.length_app, List.skipn_map, List.length_map, length_elim_mctx;
                                      fold Ns; cbn; lia |].
    intros k N T HN HT.
    rewrite (tele_insts_sb_eq _ _ (τ ⨟ Id)) in HT by (intros x; symmetry; apply sb_compose_id_right).
    rewrite <- tele_insts_tele_sub in HT; erewrite elim_mctx_sub in HT by eassumption.
    replace (List.map (fun U => U[τ]) Us) with (List.firstn (ind_nu D) Ps') in HT by (unfold Ps', Us; apply List.firstn_map).
    revert k N T HN HT; apply elim_mctx_insts_of_params; [ exact Hc | exact HMm | unfold Ps'; rewrite List.length_map; exact HPl | |].
    - intros k Pk T HP HT; unfold Ps' in HP, HT.
      rewrite <- (params_insts_sub D m Mm Ps τ Hc HMm) in HT; rewrite List.nth_error_map in HP, HT.
      destruct (List.nth_error Ps k) as [P0 |] eqn:HP0; cbn in HP; [| discriminate ]; injection HP as <-.
      destruct (List.nth_error (tele_insts (im_params D Mm) Id Ps) k) as [T0 |] eqn:HT0; cbn in HT; [| discriminate ]; injection HT as <-.
      exact (glu_rel_exp_under_sub_inst_renaming (HPg _ _ _ HP0 HT0) Hτ).
    - unfold Ps'; rewrite List.firstn_map, List.skipn_map; fold Us Ns.
      rewrite <- ind_mty_sub by (try exact Hc; exact HUl).
      exact (glu_rel_exp_under_sub_inst_renaming HM Hτ). }
  pose proof (glu_rel_exp_under_sub_inst _ _ _ HA _ _ Hinst) as H.
  rewrite (type_sort_sub S _ HS) in H; exact H.
Qed.

End Fixed_GCtx.

(** ** The Rules

    The eliminator reads syntactic premises of its rule: its parts are
    typed by their derivations, moved to the target of the embedding. *)

#[local] Generalizable All Variables.

(** An elimination, at an instance of its context: into a universe, glued
    at the target by [glu_rel_exp_elim], its parts at the instance lifted
    through their contexts; into propositions, a proof of its motive's
    instance, a glued proposition ([glu_rel_exp_motive_instance_at],
    [glu_rel_exp_proof]). *)
Lemma glu_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊩ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹{ak_relevant} eb_scrutinee_type b
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r Typeω@i) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊩ eb_motive b : abs_kind_sort r Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊩ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊩ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
        /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B
          : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     motive_kind r ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_elim r p Us m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl HMm Hbm HLb HPl HPt HPg HMt HMg -> Hnm Hann HAt HAg HMx HMxg Hna HBx HBxg Har HBt HBg Hmk.
  assert (Hel : Θ ⍮ Ξ ⍮ Γ ⊢ a_elim r p (List.firstn (ind_nu D) Ps) m Bks M
                  : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])
    by (eapply wf_elim; eauto).
  intros Θ2 Ξ2 Hμ.
  pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & Hwe & _ & _ & Hwx & _ & _).
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HMt)) as Hg.
  pose proof (valid_groups_of_glu_gctx_embedding _ _ _ _ Hg Hem) as HVP.
  pose proof (glu_gctx_embedding_ind_field _ _ _ _ Hμ) as HGall.
  pose proof (valid_groups_valid _ HVP p D Hl) as Hvg.
  pose proof (valid_group_closed _ _ Hvg) as Hc.
  pose proof (valid_group_lookup _ _ Hvg) as Hl2.
  econstructor; [ exact (glu_rel_exp_under_sub_ctx _ _ _ (HMg _ _ Hμ)) | intros Γ' τ Hτ ].
  pose proof (glu_rel_sub_inst_typed _ _ _ Hτ) as Hτt.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ (Hwe _ _ _ Hel) Hτt) as Helτ.
  assert (HSi : type_sort (abs_kind_sort r Typeω@i)) by (apply type_sort_abs_kind; constructor).
  pose proof (glu_rel_exp_motive_instance_at p D Hc Γ m Mm (eb_motive bm) _ Ps M Γ' τ HMm HPl
                (fun k P T HP HT => HPg _ _ _ HP HT _ _ Hμ) (HMg _ _ Hμ) (HAg _ _ _ HMm Hbm _ _ Hμ) HSi Hτ) as HAi.
  destruct Hmk.
  2:{ (** Into propositions: a proof of a glued proposition *)
      exact (glu_rel_exp_proof HAi Helτ). }
  (** Into a universe: the parts at the instance *)
  rewrite exp_sub_elim in Helτ |- *.
  rewrite (elim_type_sub D Mm bm Ps M τ HPl (Hnm _ _ _ HMm Hbm)) in Helτ, HAi |- *.
  set (Ps' := List.map (fun P => P[τ]) Ps) in *.
  rewrite <- List.firstn_map in Helτ |- *; fold Ps' in Helτ |- *.
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (EUs : List.map (fun U => U[τ]) Us = List.firstn (ind_nu D) Ps') by (unfold Ps', Us; symmetry; apply List.firstn_map).
  assert (ENs : List.map (fun N => N[τ]) Ns = List.skipn (ind_nu D) Ps') by (unfold Ps', Ns; symmetry; apply List.skipn_map).
  (** The blocks are typed at the instance *)
  assert (HBt0 : blocks_typed Θ2 Ξ2 Γ p D Us Bks ak_relevant i).
  { constructor; intros; first [ exact motive_kind_relevant | exact HLb | exact Hnm | eapply Hwe; eauto | eapply Hwx; eauto | eauto ]. }
  pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl2 HUl HBt0 Hτt) as HBt1; rewrite EUs in HBt1.
  destruct HBt1 as [HLb' Hnm' Hann' HAt' HMx' Hna' HBx' Har' HBt' _].
  (** The parameters at the instance *)
  assert (HPs' : forall k P T, List.nth_error Ps' k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps') k = Some T ->
             exists P0 T0, List.nth_error Ps k = Some P0 /\ List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T0 /\
                           P = P0[τ] /\ T = T0[τ]).
  { intros k P T HP HT; unfold Ps' in HP, HT.
    rewrite <- (params_insts_sub D m Mm Ps τ Hc HMm) in HT; rewrite List.nth_error_map in HP, HT.
    destruct (List.nth_error Ps k) as [P0 |] eqn:HP0; cbn in HP; [| discriminate ]; injection HP as <-.
    destruct (List.nth_error (tele_insts (im_params D Mm) Id Ps) k) as [T0 |] eqn:HT0; cbn in HT; [| discriminate ]; injection HT as <-.
    eauto 6. }
  assert (Emty : (ind_mty p D m Us Ns)[τ] = ind_mty p D m (List.firstn (ind_nu D) Ps') (List.skipn (ind_nu D) Ps'))
    by (rewrite ind_mty_sub, EUs, ENs by (try exact Hc; exact HUl); reflexivity).
  eapply (@glu_rel_exp_elim (gc_mk Θ2 Ξ2) _ p D HVP HGall (valid_group_self_ends _ HVP HGall)
            (glu_rview_records_of_glu_gctx_embedding _ _ _ _ Hg Hμ) Hl Γ' m Mm (eblock_sub bm τ) (blocks_sub Bks τ) Ps' M[τ] i
            HMm); try eassumption.
  - rewrite nth_error_blocks_sub, Hbm; reflexivity.
  - unfold Ps'; rewrite List.length_map; exact HPl.
  - intros k P T HP HT; destruct (HPs' _ _ _ HP HT) as (P0 & T0 & HP0 & HT0 & -> & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (Hwe _ _ _ (HPt _ _ _ HP0 HT0)) Hτt).
  - intros k P T HP HT; destruct (HPs' _ _ _ HP HT) as (P0 & T0 & HP0 & HT0 & -> & ->).
    exact (glu_rel_exp_under_sub_inst _ _ _ (HPg _ _ _ HP0 HT0 _ _ Hμ) _ _ Hτ).
  - rewrite <- Emty; exact (sub_preserves_exp _ _ _ _ _ _ _ (Hwe _ _ _ HMt) Hτt).
  - rewrite <- Emty; exact (glu_rel_exp_under_sub_inst _ _ _ (HMg _ _ Hμ) _ _ Hτ).
  - (** The motives, at the instance lifted through their contexts *)
    intros k Mk b' HMk Hb'.
    rewrite nth_error_blocks_sub in Hb'.
    destruct (List.nth_error Bks k) as [[nm Z0 A Bs] |] eqn:Hb; cbn in Hb'; [| discriminate ]; injection Hb' as <-.
    pose proof (Hnm _ _ _ HMk Hb) as Enm; cbn in Enm; subst nm; cbn [eb_motive].
    rewrite <- EUs; erewrite <- elim_mctx_sub by eassumption.
    pose proof (glu_rel_exp_under_sub_ext_inst (proj1 (HMxg _ _ HMk) _ _ Hμ) (HAg _ _ _ HMk Hb _ _ Hμ) Hτ) as H.
    rewrite length_elim_mctx in H; exact H.
  - (** The branches, at the instance lifted through their contexts *)
    intros k Mk b' c gs n B' HMk Hb' Hcon Hin.
    rewrite nth_error_blocks_sub in Hb'.
    destruct (List.nth_error Bks k) as [[nm Z0 A Bs] |] eqn:Hb; cbn in Hb'; [| discriminate ]; injection Hb' as <-.
    pose proof (Hnm _ _ _ HMk Hb) as Enm; cbn in Enm; subst nm.
    cbn [eblock_sub eb_brs eb_motive] in Hin |- *; unfold brs_sub in Hin; apply brs_in_map in Hin as (B & Hin & ->); cbn [fst snd].
    pose proof (Har _ _ _ _ _ _ _ HMk Hb Hcon Hin) as En; cbn in En; subst n.
    rewrite <- EUs.
    erewrite <- elim_branch_type_sub by eassumption.
    erewrite <- elim_bctx_sub; [| eassumption | eassumption | apply cons_lookup_in; eassumption | eassumption |].
    2:{ intros j Mj HMj; eapply blocks_motives_sub; eassumption. }
    pose proof (glu_rel_exp_under_sub_ext_inst (proj1 (HBxg _ _ _ _ HMk Hcon) _ _ Hμ) (HBg _ _ _ _ _ _ _ HMk Hb Hcon Hin _ _ Hμ) Hτ) as H.
    rewrite length_elim_bctx in H; replace (cargs_nrec D gs + List.length gs + im_nn Mk)%nat
      with (im_nn Mk + List.length gs + cargs_nrec D gs)%nat in H by lia; exact H.
  - exact (blocks_scoped_of_elim _ _ _ _ _ _ _ _ _ _ Helτ).
Qed.

(** The congruence and the view rule glue their context. *)
Lemma glu_exp_eq_elim_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_elim_view :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
