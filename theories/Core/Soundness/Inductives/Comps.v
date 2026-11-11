(** * The Telescopes and the Type Former of a Group in the Gluing Model

    The types of the telescopes of a group's members, at uniform
    parameters glued to [ups], are glued at the gluings of the clause of
    [d_ind] ([components_of_uparams]); a declared member's type at glued
    parameters is then glued at its universe ([ind_typ_at_of_args]), and its
    type former at its type ([glu_rel_exp_ind0]).  The families of the
    clause are named by [ind_fams_glu]. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  Instances
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Families of a Group's Clause

    The gluings the clause of [d_ind] gives the types of the telescopes of
    the members of [D] at [ups], at the canonical relations, at the index
    [u]: the types evaluate, and their values are glued at the families. *)
Record ind_fams_glu (D : ind_decl) (ups : list domain) (u : universe_index)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred)
    (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred) : Prop :=
  mk_ind_fams_glu
  { (** Each non-uniform parameter's type evaluates *)
    ind_fams_glu_nparams_eval : forall m Mm j κ A vs, ind_member D m = Some Mm ->
      List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
      tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
      exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b
    (** and its value is glued at [NP] and [NEl] *)
  ; ind_fams_glu_nparams_glu : forall m Mm j κ A vs b, ind_member D m = Some Mm ->
      List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
      tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
      ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b ->
      DG b ∈ glu_univ_elem u ↘ NP m j vs ↘ NEl m j vs
    (** Each non-recursive argument's type evaluates *)
  ; ind_fams_glu_arg_eval : forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
      tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
      exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b
    (** and its value is glued at [AP] and [AEl] *)
  ; ind_fams_glu_arg_glu : forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
      tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
      ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b ->
      DG b ∈ glu_univ_elem u ↘ AP m ms c j vs ↘ AEl m ms c j vs
    (** Each shape domain evaluates *)
  ; ind_fams_glu_dom_eval : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
      List.nth_error (ptyp_doms t) j = Some B ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
      exists b, ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                                  (ms ++ ws ++ ys) ↘ b
    (** and its value is glued at [DP] and [DEl] *)
  ; ind_fams_glu_dom_glu : forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
      List.nth_error (ptyp_doms t) j = Some B ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
      ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ b ->
      DG b ∈ glu_univ_elem u
        ↘ DP m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B
        ↘ DEl m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B }.

(** ** The Components of an Inductive Type at Glued Parameters

    The types of the telescopes of a valid declaration, at uniform
    parameters glued to [ups], are glued at the gluings of the clause of
    [d_ind] at the index of the sort's universe. *)
(** ** The Parameters of a Recursive Argument's Type *)

Section RecParams.
  Variable (D : ind_decl).
  Hypothesis (HD : valid_ind_decl D) (Hc : decl_closed D) (Hass : group_structure D).
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).

  (** The substitution of the uniform parameters and the parameters of a
      recursive argument before a position, over the context the recursive
      argument's parameters are typed in. *)
  Lemma rec_sub_valid : forall gs1 t gs2 Mj, gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
      forall m, m <= im_nn Mj ->
        ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk ⊨ˢ
          sb_of_list (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk))) (List.firstn m (ptyp_ps t))
          ≈ sb_of_list (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk))) (List.firstn m (ptyp_ps t))
          : nparams_prefix Mj m ++ ind_uparams D.
  Proof.
    intros gs1 t gs2 Mj Heq HMj.
    set (K := List.length (cargs_nonrec gs1)).
    set (L := ptyp_depth t + K + im_nn Mk).
    set (Ξ0 := ptyp_tele t ++ nonrec_args_prefix gs K ++ im_params D Mk).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (HΞ0 : ⊨ Ξ0).
    { pose proof (valid_ind_decl_dctx _ HD _ _ _ _ _ _ _ (List.length (ptyp_doms t)) HM Hcon Heq (le_n _)) as H.
      rewrite List.firstn_all in H; exact H. }
    destruct (length_rec_ps D HD k Mk HM c gs gs1 t gs2 Hcon Heq) as (Mj' & HMj' & HPl).
    rewrite HMj in HMj'; injection HMj' as <-.
    induction m as [| m IH]; intros Hmn.
    - cbn [List.firstn sb_of_list]; unfold nparams_prefix; cbn [List.firstn List.rev List.app].
      apply rel_sub_of_wk.
      assert (HL : L = List.length (ptyp_tele t ++ nonrec_args_prefix gs K ++ im_nparams Mk))
        by (unfold L, ptyp_tele, ptyp_depth; rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams, doms_ctx_length
              by exact HK; lia).
      assert (HΞe : Ξ0 = (ptyp_tele t ++ nonrec_args_prefix gs K ++ im_nparams Mk) ++ ind_uparams D)
        by (unfold Ξ0, im_params; rewrite <- !List.app_assoc; reflexivity).
      fold L; rewrite HΞe, HL; apply Completeness.UnitCases.rel_wk_under_ctx_shiftn; rewrite <- HΞe; exact HΞ0.
    - pose proof (IH ltac:(lia)) as Hτ.
      destruct (nth_error_lt_some (ptyp_ps t) m ltac:(lia)) as [P HP].
      assert (HT : exists T, List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) (ptyp_ps t)) m = Some T).
      { apply nth_error_lt_some.
        rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMj).
        rewrite length_im_nparams; lia. }
      destruct HT as [T HT].
      destruct (tele_insts_nth _ _ _ _ _ HT) as (κ & A & HA & ->).
      pose proof (valid_ind_decl_rec_field _ HD _ _ _ _ _ _ _ _ _ _ _ HM Hcon Heq HMj HP HT) as HPv.
      destruct (valid_ind_decl_nparams _ HD _ _ _ _ _ HMj HA) as (_ & j & HAv).
      assert (HPs : exp_scoped (List.length Ξ0) P).
      { pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ HM) _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as Ht.
        pose proof (proj1 (List.Forall_forall _ _) (ptyp_scoped_ps _ _ Ht) P (List.nth_error_In _ _ HP)) as HsP.
        replace (List.length Ξ0) with (ptyp_depth t + (List.length (cargs_nonrec_ctx gs1) + im_np D Mk)); [ exact HsP |].
        unfold Ξ0, ptyp_tele, ptyp_depth; rewrite !List.length_app, doms_ctx_length, length_nonrec_args_prefix, length_im_params by exact HK.
        rewrite cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele; unfold K; lia. }
      rewrite (firstn_S_snoc _ _ _ HP), sb_of_list_app, (nparams_prefix_S _ _ _ _ HA); cbn [sb_of_list List.app].
      eapply Completeness.LogicalRelation.Substitution.rel_sub_under_ctx_extend;
        [ exact Hτ | exact (rel_type_of_typ HAv) | exact HPv | exact HPs | exact HPs ].
  Qed.
End RecParams.

(** The ends of the recursive arguments' shapes of [D], glued at every
    substitution glued into their context whose uniform parameters are
    glued to [ups]: the parameters of the member a shape ends in are glued
    at their values ([glu_self_params]).  The constructors' clauses
    establish it from the declaration's validity; the components of a type
    at glued uniform parameters take it. *)
Definition glu_self_ends_ok (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred) : Prop :=
  forall m Mm c gs gs1 t gs2 ns nv ys Δ τ Us Ys SbC,
    ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
    tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) nv nv ->
    List.length ns = im_nn Mm -> List.length nv = List.length (cargs_nonrec gs1) ->
    tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ns nv t)
      (List.length (ptyp_doms t)) ys ys ->
    ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
    List.length Ys = List.length (ptyp_doms t) + List.length (cargs_nonrec gs1) + im_nn Mm ->
    EG ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm ∈ glu_ctx_env ↘ SbC ->
    Δ ⊢ˢ sb_of_list τ (Us ++ Ys)
      ® components_env D ups (List.rev (ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
          (ns ++ nv ++ ys) ∈ SbC ->
    glu_self_params p D ups NEl Δ Us (ns ++ nv ++ ys)
      (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ptyp_mem t) (ptyp_ps t)
      (ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) (pt_self (ptyp_mem t) (ptyp_ps t))).

Section Comps.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_ind_decl D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)) (Hass : group_structure D).
  Variable (ups : list domain) (bu : domain) (u : universe_index)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred)
    (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hbu : ⟦ ind_sort D ⟧ decl_env D ups ↘ bu)
    (Hule : universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).
  (** The ends of the recursive arguments' shapes are glued *)
  Hypothesis (Hself : glu_self_ends_ok p D ups NEl).

  Let HeN := ind_fams_glu_nparams_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HNP := ind_fams_glu_nparams_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeA := ind_fams_glu_arg_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HAP := ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeD := ind_fams_glu_dom_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HDP := ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf.

  (** A type of a context ending in the uniform parameters at the sort's
      universe, glued at the sort's universe's index at uniform parameters
      [ups]. *)
  Lemma sort_typ_glued_at : forall Pre r A Sb Δ σ zs, carg_kind r -> ⊢ Pre ++ ind_uparams D -> List.length zs = List.length Pre ->
      EG Pre ++ ind_uparams D ∈ glu_ctx_env ↘ Sb ->
      Pre ++ ind_uparams D ⊩ A : abs_kind_sort r (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      Δ ⊢ˢ σ ® components_env D ups (List.rev Pre) zs ∈ Sb ->
      exists a, ⟦ A ⟧ components_env D ups (List.rev Pre) zs ↘ a /\
        Dom a ≈ a ∈ per_univ (Completeness.Inductives.Decl.univ_idx bu) /\
        forall P El, DG a ∈ glu_univ_elem (Completeness.Inductives.Decl.univ_idx bu) ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
  Proof.
    intros * Hr HPre Hzs HSb HA Hσ.
    destruct Hr; cbn [abs_kind_sort] in HA.
    2:{ (* a proposition: glued at every index by the clause of propositions *)
      destruct (glu_rel_exp_prop_inversion HSb HA _ _ _ Hσ) as (a & Ha & Hpa & HP).
      exists a; split; [ exact Ha | split; [ eexists; apply per_univ_elem_of_prop; exact Hpa |] ].
      intros P El Hg; destruct (glu_univ_elem_prop_inv _ _ _ _ Hpa Hg) as [EP _]; apply EP; exact HP. }
    pose proof (decl_typed_sort _ _ _ Hdt) as [iS HS].
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in HA, HS, Hbu; cbn [exp_wk] in HA.
    - destruct (glu_rel_exp_of_univ_inversion (u := ul i0) HSb HA _ _ _ Hσ) as (_ & a & Ha & Hpa & HP & _).
      inversion Hbu; subst; cbn [Completeness.Inductives.Decl.univ_idx].
      exists a; split; [ exact Ha | split; [ exact Hpa | exact HP ] ].
    - destruct (glu_rel_exp_of_suniv_tm_inversion' HSb HA _ _ _ Hσ) as (l & Hlv & _ & _ & a & Ha & Hpa & HP & _).
      exists a; split; [ exact Ha |].
      assert (Hidx : Completeness.Inductives.Decl.univ_idx bu = us (domain_level_real l)).
      { assert (HCs : ⊨ Pre ++ ind_uparams D) by (apply completeness_fundamental_ctx; exact HPre).
        assert (HSs : ind_uparams D ⊨ Type⟨t⟩ : Typeω@iS) by (apply completeness_fundamental_exp; exact HS).
        destruct (rel_ctx_wf_per_ctx_env HCs) as [R HR].
        pose proof (glu_ctx_env_per_env HSb HR Hσ) as HE.
        assert (Eb : ⟦ Type⟨t⟩[wk_shiftn (List.length Pre)]ʷ ⟧ components_env D ups (List.rev Pre) zs ↘ d_suniv l)
          by (cbn [exp_wk]; econstructor; exact Hlv).
        assert (Ea : ⟦ Type⟨t⟩ ⟧ ⟪wk_shiftn (List.length Pre)⟫ (components_env D ups (List.rev Pre) zs) ↘ bu)
          by (rewrite <- Hzs, Completeness.Inductives.Decl.eval_wk_shiftn_components_env; exact Hbu).
        pose proof (Completeness.Inductives.Decl.univ_idx_wk _ _ _ _ _ _ _ _ _ HCs HSs HR HE Eb Ea ltac:(right; eauto)) as Hi.
        rewrite Hi; reflexivity. }
      rewrite Hidx; split; [ exact Hpa | exact HP ].
  Qed.

  Lemma sort_typ_glued : forall Pre A Sb Δ σ zs, ⊢ Pre ++ ind_uparams D -> List.length zs = List.length Pre ->
      EG Pre ++ ind_uparams D ∈ glu_ctx_env ↘ Sb -> Pre ++ ind_uparams D ⊩ A : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      Δ ⊢ˢ σ ® components_env D ups (List.rev Pre) zs ∈ Sb ->
      exists a, ⟦ A ⟧ components_env D ups (List.rev Pre) zs ↘ a /\
        Dom a ≈ a ∈ per_univ (Completeness.Inductives.Decl.univ_idx bu) /\
        forall P El, DG a ∈ glu_univ_elem (Completeness.Inductives.Decl.univ_idx bu) ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
  Proof. intros; eapply (sort_typ_glued_at _ ak_relevant); eauto using carg_kind_relevant. Qed.

  (** The components of a prefix of a telescope, at as few values as the
      prefix has entries, are those of the telescope. *)
  Lemma components_env_firstn_ge : forall T k vs, List.length vs <= k ->
      components_env D ups (List.firstn k T) vs = components_env D ups T vs.
  Proof.
    intros * Hk; unfold components_env.
    rewrite (env_tele_firstn _ (List.firstn k T)), (env_tele_firstn _ T), List.firstn_firstn, Nat.min_l by exact Hk; reflexivity.
  Qed.

  (** The same after a full prefix [T0]. *)
  Lemma components_env_app_firstn_ge : forall T0 T k ns X, List.length ns = List.length T0 -> List.length X <= k ->
      List.length X <= List.length T ->
      components_env D ups (T0 ++ List.firstn k T) (ns ++ X) = components_env D ups (T0 ++ T) (ns ++ X).
  Proof.
    intros * Hn HXk HXT.
    rewrite (Completeness.Inductives.Decl.components_env_app_firstn D ups T0 (List.firstn k T))
      by (try exact Hn; rewrite List.length_firstn; lia).
    rewrite (Completeness.Inductives.Decl.components_env_app_firstn D ups T0 T) by (try exact Hn; lia).
    rewrite List.firstn_firstn, Nat.min_l by exact HXk; reflexivity.
  Qed.

  (** A telescope after a member's parameters, from the empty
      environment: the components after the non-uniform parameters. *)
  Lemma env_tele_params : forall Mm ns T X, List.length ns = im_nn Mm ->
      env_tele (env_tele nil (List.rev (im_params D Mm)) (ups ++ ns)) T X
      = components_env D ups (List.rev (im_nparams Mm) ++ T) (ns ++ X).
  Proof.
    intros * Hns.
    rewrite rev_im_params, env_tele_app by (rewrite List.length_rev; exact Hu).
    unfold components_env, decl_env; rewrite env_tele_app by (rewrite List.length_rev, length_im_nparams; exact Hns).
    reflexivity.
  Qed.

  (** One more component, of the next entry's type. *)
  Lemma components_env_snoc : forall T κ B vs v, List.length vs = List.length T ->
      components_env D ups (T ++ ce_ass κ B :: nil) (vs ++ v :: nil)
      = components_env D ups T vs ↦ v ⦂ entry_type_closure B (components_env D ups T vs).
  Proof.
    intros * Hlv; unfold components_env.
    rewrite (Completeness.Inductives.Decl.env_tele_snoc_at _ _ _ κ B)
      by (rewrite List.nth_error_app2, Hlv, Nat.sub_diag by lia; reflexivity).
    rewrite env_tele_prefix by lia; reflexivity.
  Qed.

  (** The non-recursive arguments of a constructor before a position, as a
      telescope. *)
  Lemma cargs_nonrec_tele_firstn : forall gs1 g gs2,
      List.firstn (List.length (cargs_nonrec gs1)) (cargs_nonrec_tele (gs1 ++ g :: gs2)) = cargs_nonrec_tele gs1.
  Proof. intros; rewrite cargs_nonrec_tele_app; apply firstn_app_exact, length_cargs_nonrec_tele. Qed.

  (** The kind of a non-recursive argument. *)
  Lemma cargs_nonrec_kinds_at : forall gs1 r A gs2,
      List.nth_error (cargs_nonrec_kinds (gs1 ++ ca_arg r A :: gs2)) (List.length (cargs_nonrec gs1)) = Some r.
  Proof. induction gs1 as [| [r0 B | t] gs1 IH]; intros; cbn; [ reflexivity | apply IH | apply IH ]. Qed.

  Lemma nparams_prefix_ass_member : forall m Mm k, ind_member D m = Some Mm -> all_assumptions (nparams_prefix Mm k ++ ind_uparams D).
  Proof.
    intros * HM; destruct (nparams_prefix_suffix D Mm k) as [Δ HΔ].
    pose proof (decl_closed_params_ass D m Mm Hc HM) as H; rewrite HΔ in H.
    apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  Lemma nparams_prefix_wf : forall m Mm k, ind_member D m = Some Mm -> ⊢ nparams_prefix Mm k ++ ind_uparams D.
  Proof.
    intros * HM; destruct (nparams_prefix_suffix D Mm k) as [Δ HΔ].
    pose proof (member_params_wf _ _ _ _ _ Hdt HM) as H; rewrite HΔ in H; eapply ctx_app_wf_tail; exact H.
  Qed.

  Lemma nparams_prefix_split_member : forall Mm k, exists Δ, im_nparams Mm = Δ ++ nparams_prefix Mm k.
  Proof.
    intros; exists (List.rev (List.skipn k (List.rev (im_nparams Mm)))).
    unfold nparams_prefix; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
  Qed.

  Lemma components_nparams : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm k Ns ns T, ind_member D m = Some Mm -> List.length ns = k -> k < im_nn Mm ->
        List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
        (forall j N T' n, j < k -> List.nth_error Ns j = Some N ->
           List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T' ->
           List.nth_error ns j = Some n -> Δ ⊢ N : T' ® n ∈ NEl m j (List.firstn j ns)) ->
        tele_prefix_rel (canon_nparams_rel D ups m) k ns ns -> Δ ⊢ T ® NP m k ns.
  Proof.
    intros Δ Us HΔ HUs m Mm k Ns ns T HM Hlk Hk HT Hpre Hp.
    pose proof (group_structure_uparams _ Hass) as HassU.
    pose proof (decl_closed_nparams_ass D Hc m Mm HM) as HassN0.
    assert (Hk' : k < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, length_im_nparams; lia).
    destruct (nparams_lt_ass D m Mm k Hass HM Hk') as (κ & A & HA).
    pose proof (glu_rel_exp_of_under_sub (glu_ind_decl_nparams _ HG m Mm k κ A HM HA)) as HV.
    pose proof HV as [SbC HSbC _ _].
    pose proof (nparams_prefix_ass_member m Mm k HM) as HassC.
    pose proof (length_nparams_prefix Mm k ltac:(lia)) as Hlpre.
    destruct (nparams_prefix_split_member Mm k) as [Δy HΔy].
    assert (HassN : all_assumptions (nparams_prefix Mm k)) by (unfold all_assumptions in HassC; apply List.Forall_app in HassC as [H _]; exact H).
    assert (HlNs : k < List.length Ns).
    { assert (Hs : List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k <> None) by congruence.
      apply List.nth_error_Some in Hs; rewrite length_tele_insts in Hs by exact HassN0; lia. }
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    assert (Hσ : Δ ⊢ˢ sb_of_list Id (Us ++ List.firstn k Ns) ® components_env D ups (List.rev (nparams_prefix Mm k)) ns ∈ SbC).
    { rewrite <- (Completeness.Inductives.Decl.env_tele_uparams D _ ups ns Hu).
      eapply glu_sub_of_list with (C := nparams_prefix Mm k ++ ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact HassC | rewrite List.app_nil_r; exact HSbC | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ |].
      apply glu_args_app; [ exact HassU | exact LU | exact Hu |].
      split; [ exact HUs |].
      constructor; [ rewrite List.length_firstn; lia | lia |].
      intros j M T' v κ' A' HM' HT' Hv HA'.
      assert (Hj : j < k) by (rewrite <- Hlk; apply List.nth_error_Some; congruence).
      rewrite List.nth_error_firstn in HM'; destruct (Nat.ltb_spec j k); [| lia ].
      assert (HT'' : List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T').
      { rewrite HΔy, <- (List.firstn_skipn k Ns), tele_insts_app by (try exact HassN; rewrite List.length_firstn, Hlpre; lia).
        rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact HassN; rewrite List.length_firstn; lia); exact HT'. }
      assert (HA'' : List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ' A')).
      { unfold nparams_prefix in HA'; rewrite List.rev_involutive, List.nth_error_firstn in HA'.
        destruct (Nat.ltb_spec j k); [ exact HA' | lia ]. }
      pose proof (Hpre _ _ _ _ Hj HM' HT'' Hv) as HMg.
      assert (Hpj : tele_prefix_rel (canon_nparams_rel D ups m) j (List.firstn j ns) (List.firstn j ns))
        by (eapply tele_prefix_rel_of_pre; [ exact Hp | lia ]).
      destruct (HeN _ _ _ _ _ _ HM HA'' Hpj) as [b Hb].
      pose proof (HNP _ _ _ _ _ _ _ HM HA'' Hpj Hb) as Hgb.
      rewrite <- (components_env_firstn_ge _ k) in Hb by (rewrite List.length_firstn; lia).
      apply (mk_glu_arg _ _ _ _ _ _ u b (NP m j (List.firstn j ns)) (NEl m j (List.firstn j ns)));
        [ unfold nparams_prefix; rewrite List.rev_involutive; exact Hb
        | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ]. }
    destruct (sort_typ_glued (nparams_prefix Mm k) A SbC Δ _ ns (nparams_prefix_wf m Mm k HM) ltac:(lia) HSbC
                ltac:(rewrite Hlpre; exact HV) Hσ) as (a & Ha & Hpb & HP).
    unfold nparams_prefix in Ha; rewrite List.rev_involutive, components_env_firstn_ge in Ha by lia.
    pose proof (HNP _ _ _ _ _ _ _ HM HA Hp Ha) as Hga.
    destruct (per_univ_glu_univ_elem _ _ Hpb) as (Pb & Elb & Hgb).
    destruct (tele_insts_nth _ _ _ _ _ HT) as (κ0 & A0 & HA0 & ->).
    rewrite HA in HA0; injection HA0 as <- <-.
    rewrite <- sb_of_list_app.
    eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hule | exact Hgb | exact Hga | exact (HP _ _ Hgb) ].
  Qed.

  Lemma glu_args_of_nparams : forall m Mm Δ Us Ns ns, ind_member D m = Some Mm -> glu_nparams m Mm NEl Δ Us Ns ns ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
      glu_args Δ (im_nparams Mm) (sb_of_list Id Us) (decl_env D ups) Ns ns.
  Proof.
    intros * HM [L1 L2 H] Hns.
    constructor; [ rewrite L1; reflexivity | rewrite L2; reflexivity |].
    intros j M T v κ A HM' HT Hv HA.
    pose proof (H _ _ _ _ HM' HT Hv) as HMg.
    assert (Hj : j <= List.length (List.rev (im_nparams Mm)))
      by (rewrite List.length_rev, length_im_nparams, <- L2; apply Nat.lt_le_incl, List.nth_error_Some; congruence).
    pose proof (tele_prefix_rel_of_full _ _ _ _ _ Hns Hj) as Hpj.
    destruct (HeN _ _ _ _ _ _ HM HA Hpj) as [b Hb].
    pose proof (HNP _ _ _ _ _ _ _ HM HA Hpj Hb) as Hgb.
    apply (mk_glu_arg _ _ _ _ _ _ u b (NP m j (List.firstn j ns)) (NEl m j (List.firstn j ns)));
      [ exact Hb | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ].
  Qed.

  Lemma nonrec_args_prefix_ass : forall gs k, all_assumptions (nonrec_args_prefix gs k).
  Proof.
    intros; unfold nonrec_args_prefix, all_assumptions; apply List.Forall_rev, Forall_firstn'.
    apply all_assumptions_cargs_nonrec_tele.
  Qed.

  (** The substitution of the parameters and the non-recursive arguments
      before a position, glued at the context of the types there. *)
  Lemma nonrec_args_prefix_glu_sub : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm c gs gs1 g gs2 Ns ns As vs SbC, ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ g :: gs2 ->
        glu_nparams m Mm NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
        List.length vs = List.length gs1 -> List.length gs1 <= List.length As ->
        (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs) (nonrec_arg_vals gs1 vs) ->
        EG nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))
          ® components_env D ups (List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
              (ns ++ nonrec_arg_vals gs1 vs) ∈ SbC.
  Proof.
    intros Δ Us HΔ HUs m Mm c gs gs1 g gs2 Ns ns As vs SbC HM Hcon Heq Hnp Hns Hvl HlAs Hpre Hp HSbC.
    rewrite <- (Completeness.Inductives.Decl.env_tele_uparams D _ ups _ Hu).
    rewrite (List.app_assoc ups ns), <- (List.app_assoc (nonrec_args_prefix gs _) (im_nparams Mm)).
    set (k := List.length (cargs_nonrec gs1)) in *.
    pose proof (decl_closed_params_ass D m Mm Hc HM) as HassP.
    pose proof (group_structure_uparams _ Hass) as HassU.
    pose proof (decl_closed_nparams_ass D Hc m Mm HM) as HassN.
    assert (Hkn : k <= List.length (cargs_nonrec gs)) by (unfold k; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    set (As1 := List.firstn (List.length gs1) As).
    assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
    set (Ns' := nonrec_exps gs1 As1); set (vs' := nonrec_arg_vals gs1 vs).
    assert (HlNs' : List.length Ns' = k) by (unfold Ns'; apply length_nonrec_exps; exact HlAs1).
    assert (Hlvs' : List.length vs' = k) by (unfold vs'; apply length_nonrec_arg_vals; exact Hvl).
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (Hlast : List.length (nonrec_args_prefix gs k) = k) by (apply length_nonrec_args_prefix; lia).
    eapply glu_sub_of_list with (C := nonrec_args_prefix gs k ++ im_params D Mm) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ unfold all_assumptions; apply List.Forall_app; split; [ apply nonrec_args_prefix_ass | exact HassP ]
      | rewrite List.app_nil_r; exact HSbC | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
      | cbn; apply wf_sub_nil'; exact HΔ |].
    apply glu_args_app; [ exact HassP | rewrite List.length_app, LU, LN, length_im_params; unfold im_np, ind_nu in *; lia
                        | rewrite List.length_app, Hu, LNn, length_im_params; unfold im_np, ind_nu in *; lia |].
    split.
    - unfold im_params; apply glu_args_app; [ exact HassU | exact LU | exact Hu |].
      split; [ exact HUs | exact (glu_args_of_nparams _ _ _ _ _ _ HM Hnp Hns) ].
    - constructor; [ lia | lia |].
      intros j M T' v κ' A' HM' HT' Hv HA'.
      assert (Hj : j < k) by (rewrite <- Hlvs'; apply List.nth_error_Some; congruence).
      assert (HA1 : List.nth_error (cargs_nonrec gs1) j = Some A').
      { unfold nonrec_args_prefix in HA'; rewrite List.rev_involutive, List.nth_error_firstn in HA'.
        destruct (Nat.ltb_spec j k); [| lia ].
        destruct (cargs_nonrec_tele_nth _ _ _ _ HA') as [HA2 _].
        rewrite Heq, cargs_nonrec_app, List.nth_error_app1 in HA2 by lia; exact HA2. }
      destruct (nonrec_nth_split _ _ _ HA1) as (hs1 & hs2 & rh & Heq1 & Hlh).
      assert (Hh : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As (List.length hs1) ltac:(lia)) as [N HN].
      assert (HN1 : List.nth_error As1 (List.length hs1) = Some N)
        by (unfold As1; rewrite List.nth_error_firstn; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [ exact HN | lia ]).
      pose proof (nonrec_exps_nth_arg _ _ _ _ _ _ _ Heq1 HlAs1 HN1) as HN'.
      rewrite Hlh in HN'; fold Ns' in HN'; rewrite HN' in HM'; injection HM' as <-.
      destruct (nth_error_lt_some vs (List.length hs1) ltac:(lia)) as [v' Hv'].
      pose proof (nonrec_nth_arg _ _ _ _ _ _ _ Heq1 Hvl Hv') as Hv''.
      rewrite Hlh in Hv''; fold vs' in Hv''; rewrite Hv'' in Hv; injection Hv as <-.
      assert (HTc : exists Tc, List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some Tc).
      { apply nth_error_lt_some; rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx, Heq, List.length_app; cbn; lia. }
      destruct HTc as [Tc HTc].
      pose proof (Hpre _ _ _ _ _ _ _ Heq1 HN HTc Hv') as HNg.
      assert (Heqgs : gs = hs1 ++ ca_arg rh A' :: (hs2 ++ g :: gs2)) by (rewrite Heq, Heq1, <- List.app_assoc; reflexivity).
      pose proof (cargs_arg_type _ _ _ _ _ _ _ _ _ _ _ Heqgs HTc) as ETc.
      rewrite exp_wk_pat_sb_of_list in ETc by (rewrite List.length_firstn; lia).
      destruct (tele_insts_nth _ _ _ _ _ HT') as (κ2 & A2 & HA2 & ET').
      rewrite HA' in HA2; injection HA2 as <- <-.
      assert (Efn : List.firstn j Ns' = nonrec_exps hs1 (List.firstn (List.length hs1) As)).
      { unfold Ns'; rewrite <- Hlh, (nonrec_exps_firstn _ _ _ _ _ Heq1 HlAs1); unfold As1; rewrite List.firstn_firstn, Nat.min_l by lia; reflexivity. }
      assert (Tc = T') as <- by (rewrite ETc, ET', Efn; reflexivity).
      assert (Efv : List.firstn j vs' = nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))
        by (unfold vs'; rewrite <- Hlh; exact (nonrec_firstn _ _ _ _ _ Heq1 Hvl)).
      assert (Hpj : tele_prefix_rel (canon_args_rel D ups m ns c) j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))
                      (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)))
        by (rewrite <- Efv; eapply tele_prefix_rel_of_pre; [ exact Hp | lia ]).
      assert (HAj : List.nth_error (cargs_nonrec gs) j = Some A') by (rewrite Heq, cargs_nonrec_app, List.nth_error_app1 by lia; exact HA1).
      destruct (HeA _ _ _ _ _ _ _ _ HM Hns Hcon HAj Hpj) as [b Hb].
      pose proof (HAP _ _ _ _ _ _ _ _ _ HM Hns Hcon HAj Hpj Hb) as Hgb.
      rewrite Hlh in HNg.
      apply (mk_glu_arg _ _ _ _ _ _ u b (AP m ns c j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)))
        (AEl m ns c j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))));
        [| exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HNg ].
      rewrite env_tele_params by exact LNn; unfold nonrec_args_prefix; rewrite List.rev_involutive.
      rewrite components_env_app_firstn_ge
        by first [ rewrite List.length_rev, length_im_nparams; exact LNn | rewrite List.length_firstn; lia
                 | rewrite List.length_firstn, length_cargs_nonrec_tele; lia ].
      rewrite Efv; exact Hb.
  Qed.

  Lemma components_arg : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm c gs gs1 r0 A0 gs2 Ns ns As vs T, ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
        glu_nparams m Mm NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
        List.length vs = List.length gs1 ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
        (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs) (nonrec_arg_vals gs1 vs) ->
        Δ ⊢ T ® AP m ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs).
  Proof.
    intros Δ Us HΔ HUs m Mm c gs gs1 r0 A0 gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (decl_typed_args_kind _ _ _ Hdt _ _ _ _ _ _ _ _ HM (cons_lookup_in _ _ _ Hcon) Heq) as Hr0.
    assert (Hk0 : List.nth_error (cargs_nonrec_kinds gs) (List.length (cargs_nonrec gs1)) = Some r0)
      by (rewrite Heq; apply cargs_nonrec_kinds_at).
    set (k := List.length (cargs_nonrec gs1)) in *.
    pose proof (decl_closed_params_ass D m Mm Hc HM) as HassP.
    assert (HA0 : List.nth_error (cargs_nonrec gs) k = Some A0)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2 by lia; unfold k; rewrite Nat.sub_diag; reflexivity).
    pose proof (glu_rel_exp_of_under_sub (glu_ind_decl_arg _ HG m Mm c gs k r0 A0 HM Hcon HA0 Hk0)) as HV.
    pose proof HV as [SbC HSbC _ _].
    assert (HlAs : List.length gs1 < List.length As).
    { assert (Hs : List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) <> None) by congruence.
      apply List.nth_error_Some in Hs; rewrite length_tele_insts in Hs by apply cargs_ctx_aux_ass; lia. }
    set (As1 := List.firstn (List.length gs1) As).
    set (Ns' := nonrec_exps gs1 As1); set (vs' := nonrec_arg_vals gs1 vs).
    assert (Hkn : k <= List.length (cargs_nonrec gs)) by (apply Nat.lt_le_incl, List.nth_error_Some; congruence).
    assert (Hlast : List.length (nonrec_args_prefix gs k) = k) by (apply length_nonrec_args_prefix; lia).
    pose proof Hnp as [LN LNn _].
    pose proof (nonrec_args_prefix_glu_sub Δ Us HΔ HUs m Mm c gs gs1 (ca_arg r0 A0) gs2 Ns ns As vs SbC HM Hcon Heq Hnp Hns Hvl
                  ltac:(lia) Hpre Hp HSbC) as Hσ.
    assert (HPre : ⊢ (nonrec_args_prefix gs k ++ im_nparams Mm) ++ ind_uparams D)
      by (rewrite <- List.app_assoc; eapply presup_exp_ctx; eapply glu_rel_exp_to_wf_exp; exact HV).
    assert (HSbC' : EG (nonrec_args_prefix gs k ++ im_nparams Mm) ++ ind_uparams D ∈ glu_ctx_env ↘ SbC)
      by (rewrite <- List.app_assoc; exact HSbC).
    assert (HV' : (nonrec_args_prefix gs k ++ im_nparams Mm) ++ ind_uparams D
                  ⊩ A0 : abs_kind_sort r0 (ind_sort D)[wk_shiftn (List.length (nonrec_args_prefix gs k ++ im_nparams Mm))]ʷ)
      by (rewrite <- List.app_assoc, List.length_app, Hlast, length_im_nparams; exact HV).
    assert (Hlvs' : List.length vs' = k) by (unfold vs'; apply length_nonrec_arg_vals; exact Hvl).
    destruct (sort_typ_glued_at _ r0 A0 SbC Δ _ (ns ++ vs') Hr0 HPre
                ltac:(rewrite !List.length_app, Hlast, length_im_nparams; lia) HSbC' HV' Hσ) as (a & Ha & Hpb & HP).
    rewrite List.rev_app_distr in Ha; unfold nonrec_args_prefix in Ha; rewrite List.rev_involutive in Ha.
    rewrite components_env_app_firstn_ge in Ha
      by first [ rewrite List.length_rev, length_im_nparams; exact LNn | lia | rewrite length_cargs_nonrec_tele; lia ].
    pose proof (HAP _ _ _ _ _ _ _ _ _ HM Hns Hcon HA0 Hp Ha) as Hga.
    destruct (per_univ_glu_univ_elem _ _ Hpb) as (Pb & Elb & Hgb).
    pose proof (cargs_arg_type _ _ _ _ _ _ _ _ _ _ _ Heq HT) as ET.
    rewrite exp_wk_pat_sb_of_list in ET by (rewrite List.length_firstn; lia).
    fold As1 in ET; fold Ns' in ET.
    rewrite ET, <- !sb_of_list_app.
    eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hule | exact Hgb | exact Hga | exact (HP _ _ Hgb) ].
  Qed.

  (** Glued arguments of the non-uniform parameters' telescope are glued
      at the gluings of the clause, given the components. *)
  Lemma nparams_of_glu_args : forall m Mm Δ Us Ns ns, ind_member D m = Some Mm -> ind_glu_components p D ups NP NEl AP AEl DP DEl Δ Us ->
      glu_args Δ (im_nparams Mm) (sb_of_list Id Us) (decl_env D ups) Ns ns ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
      glu_nparams m Mm NEl Δ Us Ns ns.
  Proof.
    intros * HM Hc0 Hg Hns.
    pose proof Hc0 as [HCN _ _].
    pose proof Hg as [L1 L2 H].
    rewrite length_im_nparams in L1, L2.
    constructor; [ exact L1 | exact L2 |].
    enough (forall n, n <= im_nn Mm -> forall j N T v, j < n -> List.nth_error Ns j = Some N ->
              List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T ->
              List.nth_error ns j = Some v -> Δ ⊢ N : T ® v ∈ NEl m j (List.firstn j ns)) as Hm.
    { intros j N T v HN HT Hv.
      assert (Hj : j < im_nn Mm) by (rewrite <- L2; apply List.nth_error_Some; congruence).
      exact (Hm (im_nn Mm) ltac:(lia) _ _ _ _ Hj HN HT Hv). }
    induction n as [| n IH]; intros Hn j N T v Hj HN HT Hv; [ lia |].
    destruct (Nat.eq_dec j n) as [-> | Hne]; [| eapply IH; eauto; lia ].
    assert (Hk' : n < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, length_im_nparams; lia).
    destruct (nparams_lt_ass D m Mm n Hass HM Hk') as (κ & A & HA).
    destruct (H _ _ _ _ _ _ HN HT Hv HA) as [i' a P' El' Ha Hglu' HP' HM'].
    assert (Hpm : tele_prefix_rel (canon_nparams_rel D ups m) n (List.firstn n ns) (List.firstn n ns))
      by (eapply tele_prefix_rel_of_full; [ exact Hns | rewrite List.length_rev, length_im_nparams; lia ]).
    pose proof (HNP _ _ _ _ _ _ _ HM HA Hpm Ha) as Hgu.
    assert (HTP : Δ ⊢ T ® NP m n (List.firstn n ns)).
    { eapply (HCN m Mm n Ns (List.firstn n ns) T HM); [ rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
      intros j' N' T' v' Hj' HN' HT' Hv'.
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec j' n); [| discriminate ].
      eapply IH; eauto; lia. }
    eapply glu_univ_elem_exp_conv_universe_index; [ eapply glu_univ_elem_per_univ; exact Hglu' | exact Hglu' | exact Hgu | exact HM' | exact HTP ].
  Qed.

  (** The same at glued uniform parameters, the types of the non-uniform
      parameters glued by [components_nparams]: no gluing of the ends of
      the shapes is needed ([valid_group_self_ends] uses it). *)
  Lemma nparams_of_uparams_glu : forall m Mm Δ Us Ns ns, ind_member D m = Some Mm -> ⊢ Δ ->
      glu_args Δ (ind_uparams D) Id nil Us ups ->
      glu_args Δ (im_nparams Mm) (sb_of_list Id Us) (decl_env D ups) Ns ns ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
      glu_nparams m Mm NEl Δ Us Ns ns.
  Proof.
    intros * HM HΔ HUs Hg Hns.
    pose proof (components_nparams Δ Us HΔ HUs) as HCN.
    pose proof Hg as [L1 L2 H].
    rewrite length_im_nparams in L1, L2.
    constructor; [ exact L1 | exact L2 |].
    enough (forall n, n <= im_nn Mm -> forall j N T v, j < n -> List.nth_error Ns j = Some N ->
              List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T ->
              List.nth_error ns j = Some v -> Δ ⊢ N : T ® v ∈ NEl m j (List.firstn j ns)) as Hm.
    { intros j N T v HN HT Hv.
      assert (Hj : j < im_nn Mm) by (rewrite <- L2; apply List.nth_error_Some; congruence).
      exact (Hm (im_nn Mm) ltac:(lia) _ _ _ _ Hj HN HT Hv). }
    induction n as [| n IH]; intros Hn j N T v Hj HN HT Hv; [ lia |].
    destruct (Nat.eq_dec j n) as [-> | Hne]; [| eapply IH; eauto; lia ].
    assert (Hk' : n < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, length_im_nparams; lia).
    destruct (nparams_lt_ass D m Mm n Hass HM Hk') as (κ & A & HA).
    destruct (H _ _ _ _ _ _ HN HT Hv HA) as [i' a P' El' Ha Hglu' HP' HM'].
    assert (Hpm : tele_prefix_rel (canon_nparams_rel D ups m) n (List.firstn n ns) (List.firstn n ns))
      by (eapply tele_prefix_rel_of_full; [ exact Hns | rewrite List.length_rev, length_im_nparams; lia ]).
    pose proof (HNP _ _ _ _ _ _ _ HM HA Hpm Ha) as Hgu.
    assert (HTP : Δ ⊢ T ® NP m n (List.firstn n ns)).
    { eapply (HCN m Mm n Ns (List.firstn n ns) T HM); [ rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
      intros j' N' T' v' Hj' HN' HT' Hv'.
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec j' n); [| discriminate ].
      eapply IH; eauto; lia. }
    eapply glu_univ_elem_exp_conv_universe_index; [ eapply glu_univ_elem_per_univ; exact Hglu' | exact Hglu' | exact Hgu | exact HM' | exact HTP ].
  Qed.

  (** The components of the context of a shape's domains before the [k]th,
      read at the telescope of all the shape's domains. *)
  Lemma shape_env_eq : forall Mm gs gs1 t gs2 k ns nv ys, gs = gs1 ++ ca_rec t :: gs2 ->
      List.length ns = im_nn Mm -> List.length nv = List.length (cargs_nonrec gs1) -> List.length ys <= k ->
      k <= List.length (ptyp_doms t) ->
      components_env D ups
        (List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
        (ns ++ nv ++ ys)
      = components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv ++ ys).
  Proof.
    intros * Heq Hns Hnv Hys Hk.
    rewrite !List.rev_app_distr; unfold nonrec_args_prefix, doms_ctx; rewrite !List.rev_involutive, Heq, cargs_nonrec_tele_firstn.
    rewrite <- List.firstn_map; fold (shape_doms_tele t).
    rewrite !List.app_assoc.
    apply components_env_app_firstn_ge;
      [ rewrite !List.length_app, List.length_rev, length_im_nparams, length_cargs_nonrec_tele; lia | lia
      | unfold shape_doms_tele; rewrite List.length_map; lia ].
  Qed.

  (** A glued instance of a shape's context after [k] domains, weakened and
      extended by an argument glued at the next domain's gluing. *)
  Lemma shape_sub_step : forall m Mm c gs gs1 t gs2 k B ns nv ys Δ τ Us Ys SbC SbC' Δ' φ b b0 c' Pd Eld,
      ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) k = Some B ->
      List.length (ns ++ nv ++ ys)
        = List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm) ->
      EG doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm
        ∈ glu_ctx_env ↘ SbC ->
      EG doms_ctx (List.firstn (S k) (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm
        ∈ glu_ctx_env ↘ SbC' ->
      Δ ⊢ˢ sb_of_list τ (Us ++ Ys)
        ® components_env D ups
            (List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
            (ns ++ nv ++ ys) ∈ SbC -> Δ' ⊢ᵏ φ : Δ ->
      ⟦ B ⟧ components_env D ups
            (List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
            (ns ++ nv ++ ys) ↘ b0 ->
      DG b0 ∈ glu_univ_elem u ↘ Pd ↘ Eld ->
      Δ' ⊢ B[sb_of_list τ (Us ++ Ys)][φ]ʷ ® Pd ->
      Δ' ⊢ b : B[sb_of_list τ (Us ++ Ys)][φ]ʷ ® c' ∈ Eld ->
      Δ' ⊢ˢ sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))
        ® components_env D ups
            (List.rev (doms_ctx (List.firstn (S k) (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
            (ns ++ nv ++ ys ++ c' :: nil) ∈ SbC'.
  Proof.
    intros * HM Hcon Heq HB Hlen HSbC HSbC' Hσ Hφ Hb0 Hgb0 HTy Hb.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    pose proof HSbC' as HSbC''.
    rewrite (firstn_S_snoc _ _ _ HB), doms_ctx_snoc in HSbC''; cbn [List.app] in HSbC''.
    set (E := components_env D ups
                (List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
                (ns ++ nv ++ ys)) in *.
    assert (Hσ' : Δ' ⊢ˢ (sb_wk σ φ),,b ® E ↦ c' ⦂ entry_type_closure B E ∈ SbC').
    { eapply glu_sub_snoc; [ exact HSbC | exact HSbC'' | eapply glu_ctx_env_sub_monotone; eassumption |].
      rewrite <- exp_wk_sub.
      exact (mk_glu_arg _ _ _ _ _ _ u b0 Pd Eld Hb0 Hgb0 HTy Hb). }
    assert (Esb : sb_eq ((sb_wk σ φ),,b) (sb_of_list (sb_wk τ φ) (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys) ++ b :: nil))).
    { rewrite (sb_of_list_app (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys)) (b :: nil)); cbn [sb_of_list].
      apply sb_extend_cong; unfold σ; apply sb_wk_sb_of_list. }
    rewrite List.map_app, <- List.app_assoc in Esb.
    replace (ns ++ nv ++ ys ++ c' :: nil) with ((ns ++ nv ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
    rewrite (firstn_S_snoc _ _ _ HB), doms_ctx_snoc; cbn [List.app].
    change (List.rev (ce_ass ak_relevant B :: ?P)) with (List.rev P ++ ce_ass ak_relevant B :: nil).
    rewrite components_env_snoc by (rewrite List.length_rev; exact Hlen).
    eapply glu_ctx_env_sub_resp_sub_eq; [ exact HSbC' | exact Hσ' |].
    eapply wf_sub_eq_of_sb_eq; [ eapply glu_ctx_env_sub_escape; eassumption | exact Esb ].
  Qed.

  (** The type of a recursive argument after [k] of its shape's domains, at
      an instance [Us ++ Ys] of the shape's context glued to its values, is
      glued at the gluings of the domains. *)
  Lemma shape_typ_glu : forall m Mm c gs gs1 t gs2 ns nv, ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
      gs = gs1 ++ ca_rec t :: gs2 ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
      tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) nv nv ->
      List.length ns = im_nn Mm -> List.length nv = List.length (cargs_nonrec gs1) ->
      forall t' k ys Δ τ Us Ys SbC, ptyp_skip k t = t' -> k <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ns nv t) k ys ys ->
        ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
        List.length Us = ind_nu D -> List.length Ys = k + List.length (cargs_nonrec gs1) + im_nn Mm ->
        EG doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm
          ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list τ (Us ++ Ys)
          ® components_env D ups
              (List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mm))
              (ns ++ nv ++ ys) ∈ SbC ->
        glu_shape_typ (canon_doms_rel D ups m) (DP m) (DEl m) (glu_self_params p D ups NEl) Δ Us (ns ++ nv ++ ys)
          (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t)) t'
          (ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) t').
  Proof.
    intros m Mm c gs gs1 t gs2 ns nv HM Hcon Heq Hns Hnv Hnsl Hnvl t'.
    set (K := List.length (cargs_nonrec gs1)) in *.
    assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    induction t' as [j Ps | B t'' IH]; intros k ys Δ τ Us Ys SbC Hsk Hk Hy HΔ HUs HUl HYl HSbC Hσ;
      cbn [glu_shape_typ].
    { (** The end, glued by the ends' hypothesis *)
      destruct (Tele.ptyp_skip_self _ _ _ _ Hsk) as (Hkd & <- & <-).
      assert (k = List.length (ptyp_doms t)) as -> by lia.
      rewrite List.firstn_all in HSbC, Hσ.
      rewrite (List.firstn_all2 (n := List.length (ptyp_doms t))) by (unfold shape_doms_tele; rewrite List.length_map; lia).
      exact (Hself m Mm c gs gs1 t gs2 ns nv ys Δ τ Us Ys SbC HM Hcon Heq Hns Hnv Hnsl Hnvl Hy HΔ HUs HYl HSbC Hσ). }
    intros IT OT HT; cbn [ptyp_ty_at] in HT; injection HT as <- <-.
    destruct (Tele.ptyp_skip_pi _ _ _ _ Hsk) as [HB Hs'].
    assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
    assert (Hyl : List.length ys = k) by (destruct Hy as [Hyl _]; exact Hyl).
    pose proof (glu_rel_exp_of_under_sub (glu_ind_decl_dom _ HG _ _ _ _ _ _ _ _ _ HM Hcon Heq HB)) as HBv.
    destruct (HeD _ _ _ _ _ _ _ _ _ _ _ _ HM Hns Hcon Heq Hnv HB Hy) as [b0 Hb0].
    pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hns Hcon Heq Hnv HB Hy Hb0) as Hgb0.
    rewrite <- (shape_env_eq Mm gs gs1 t gs2 k) in Hb0 by (first [ exact Heq | exact Hnsl | exact Hnvl | lia ]).
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (Pre := doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ im_nparams Mm) in *.
    assert (EPre : doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ im_params D Mm = Pre ++ ind_uparams D)
      by (unfold Pre, im_params; rewrite <- !List.app_assoc; reflexivity).
    assert (HlPre : List.length Pre = k + K + im_nn Mm)
      by (unfold Pre; rewrite !List.length_app, doms_ctx_length, List.length_firstn, length_nonrec_args_prefix, length_im_nparams
            by exact HKl; lia).
    assert (HPre : ⊢ Pre ++ ind_uparams D)
      by (rewrite <- EPre; eapply presup_exp_ctx; eapply glu_rel_exp_to_wf_exp; exact HBv).
    assert (HSbCp : EG Pre ++ ind_uparams D ∈ glu_ctx_env ↘ SbC) by (rewrite <- EPre; exact HSbC).
    assert (HBvp : Pre ++ ind_uparams D ⊩ B : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ) by (rewrite <- EPre, HlPre; exact HBv).
    set (Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t)) in *.
    (** The domain, glued at its gluing at every weakening. *)
    assert (HTy : forall Δ' φ, Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ B[σ][φ]ʷ ® DP m (ns ++ nv ++ ys) Ts B).
    { intros Δ' φ Hφ.
      pose proof (glu_ctx_env_sub_monotone _ _ HSbC _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (sort_typ_glued Pre B SbC Δ' (sb_wk σ φ) (ns ++ nv ++ ys) HPre
                  ltac:(rewrite HlPre, !List.length_app; lia) HSbCp HBvp Hσφ) as (a & Ha & Hpa & HP).
      assert (a = b0) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_glu_univ_elem _ _ Hpa) as (Pb & Elb & Hgb).
      rewrite exp_wk_sub.
      eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hule | exact Hgb | exact Hgb0 | exact (HP _ _ Hgb) ]. }
    split; [ exact HTy |].
    intros Δ' φ b c' Hφ Hc' Hb.
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    destruct (glu_rel_ctx_types_ctx _ (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ (S k) HM Hcon Heq ltac:(lia))) as [SbC' HSbC'].
    pose proof (shape_sub_step m Mm c gs gs1 t gs2 k B ns nv ys Δ τ Us Ys SbC SbC' Δ' φ b b0 c' _ _ HM Hcon Heq HB
                  ltac:(change (List.length (ns ++ nv ++ ys) = List.length Pre); rewrite HlPre, !List.length_app; lia)
                  HSbC HSbC' Hσ Hφ Hb0 Hgb0 (HTy _ _ Hφ) Hb) as Hσ''.
    unfold σ; rewrite ptyp_ty_at_shape_step by assumption.
    replace ((ns ++ nv ++ ys) ++ c' :: nil) with (ns ++ nv ++ ys ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
    assert (Hsd : List.nth_error (shape_doms_tele t) k = Some (ce_ass ak_relevant B))
      by (unfold shape_doms_tele; rewrite List.nth_error_map, HB; reflexivity).
    replace (Ts ++ ce_ass ak_relevant B :: nil)
      with (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn (S k) (shape_doms_tele t))
      by (unfold Ts; rewrite (firstn_S_snoc _ _ _ Hsd), <- !List.app_assoc; reflexivity).
    apply (IH (S k) (ys ++ c' :: nil) Δ' (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us) (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil) SbC');
      [ exact Hs' | lia | | exact HΔ'
      | exact (glu_args_wk _ _ _ _ _ _ _ (group_structure_uparams _ Hass) (decl_closed_uparams _ Hc) Hφ HUs)
      | rewrite List.length_map; exact HUl
      | rewrite List.length_app, List.length_map; cbn; lia | exact HSbC' | exact Hσ'' ].
    apply tele_prefix_rel_snoc; [ exact Hy |].
    unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hc'.
  Qed.

  (** The types of the recursive arguments, at uniform parameters glued to
      [ups], are glued at the gluings of the domains of their shapes. *)
  Lemma components_rec : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm c gs gs1 t gs2 Ns ns As vs T, ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        glu_nparams m Mm NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
        List.length vs = List.length gs1 ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
        (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs) (nonrec_arg_vals gs1 vs) ->
        glu_shape_typ (canon_doms_rel D ups m) (DP m) (DEl m) (glu_self_params p D ups NEl) Δ Us (ns ++ nonrec_arg_vals gs1 vs)
          (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1) t T.
  Proof.
    intros Δ Us HΔ HUs m Mm c gs gs1 t gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (HlAs : List.length gs1 < List.length As).
    { destruct (Nat.lt_ge_cases (List.length gs1) (List.length As)) as [| Hge]; [ assumption |].
      rewrite (proj2 (List.nth_error_None _ _)) in HT; [ discriminate |].
      rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; subst gs; rewrite List.length_app; cbn; lia. }
    destruct (glu_rel_ctx_types_ctx _ (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ 0 HM Hcon Heq ltac:(lia))) as [SbC0 HSbC0].
    cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0.
    pose proof (nonrec_args_prefix_glu_sub Δ Us HΔ HUs m Mm c gs gs1 (ca_rec t) gs2 Ns ns As vs SbC0 HM Hcon Heq Hnp Hns Hvl
                  ltac:(lia) Hpre Hp HSbC0) as Hσ.
    pose proof (cargs_rec_type_shape p D Mm gs gs1 t gs2 (Us ++ Ns) As T Heq Hc
                  ltac:(rewrite List.length_app, LU, LN; unfold im_np, ind_nu in *; lia) HT) as ET.
    rewrite firstn_app_exact in ET by exact LU.
    assert (Hlnv : List.length (nonrec_arg_vals gs1 vs) = List.length (cargs_nonrec gs1)) by (apply length_nonrec_arg_vals; exact Hvl).
    rewrite ET, <- List.app_assoc.
    replace (ns ++ nonrec_arg_vals gs1 vs) with (ns ++ nonrec_arg_vals gs1 vs ++ nil) by (rewrite List.app_nil_r; reflexivity).
    replace (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1)
      with (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn 0 (shape_doms_tele t))
      by (cbn [List.firstn]; rewrite List.app_nil_r; reflexivity).
    apply (shape_typ_glu m Mm c gs gs1 t gs2 ns (nonrec_arg_vals gs1 vs) HM Hcon Heq Hns Hp LNn Hlnv t 0 nil Δ Id Us
             (Ns ++ nonrec_exps gs1 (List.firstn (List.length gs1) As)) SbC0 eq_refl ltac:(lia) (tele_prefix_rel_nil _) HΔ HUs LU).
    - rewrite List.length_app, length_nonrec_exps by (rewrite List.length_firstn; lia); lia.
    - exact HSbC0.
    - rewrite List.app_nil_r; rewrite <- List.app_assoc in Hσ; exact Hσ.
  Qed.

  (** The components, at uniform parameters glued to [ups]. *)
  Lemma components_of_uparams : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      ind_glu_components p D ups NP NEl AP AEl DP DEl Δ Us.
  Proof.
    intros * HΔ HUs; constructor.
    - intros m Mm k Ns ns T HM Hl' Hk HT Hpre Hp; eapply components_nparams; eassumption.
    - intros m Mm c gs gs1 r0 A0 gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp; eapply components_arg; eassumption.
    - intros m Mm c gs gs1 t gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp; eapply components_rec; eassumption.
  Qed.

End Comps.

(** ** A Declared Member's Type at Glued Parameters *)

(** The gluing of a declared member's type in the PER model: its families,
    and the type and element predicates at them. *)
#[warnings="-cannot-define-projection"]
Record ind_glu_of_type (p : qname) (D : ind_decl) (ups ns : list domain) (u : universe_index) (k : nat) (Mk : imember)
    (R : relation domain) : Prop := mk_ind_glu_of_type
  { (** The non-uniform parameters' type predicates *)
    ind_glu_of_type_NP : nat -> nat -> list domain -> glu_typ_pred
    (** The non-uniform parameters' element predicates *)
  ; ind_glu_of_type_NEl : nat -> nat -> list domain -> glu_exp_pred
    (** The non-recursive arguments' type predicates *)
  ; ind_glu_of_type_AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred
    (** The non-recursive arguments' element predicates *)
  ; ind_glu_of_type_AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred
    (** The shape domains' type predicates *)
  ; ind_glu_of_type_DP : nat -> list domain -> list centry -> exp -> glu_typ_pred
    (** The shape domains' element predicates *)
  ; ind_glu_of_type_DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred
    (** The type's type predicate *)
  ; ind_glu_of_type_P : glu_typ_pred
    (** The type's element predicate *)
  ; ind_glu_of_type_El : glu_exp_pred
    (** The element relation of the type's clause *)
  ; ind_glu_of_type_R : relation domain
    (** The type is glued at them *)
  ; ind_glu_of_type_glu : DG d_ind p k (ups ++ ns) ∈ glu_univ_elem u ↘ ind_glu_of_type_P ↘ ind_glu_of_type_El
    (** The type predicate is the inductive one *)
  ; ind_glu_of_type_typ : ind_glu_of_type_P <∙> ind_glu_typ_pred p D ups ns ind_glu_of_type_NP ind_glu_of_type_NEl ind_glu_of_type_AP ind_glu_of_type_AEl ind_glu_of_type_DP ind_glu_of_type_DEl k Mk Typeω@(large_level u)
    (** The element predicate is the inductive one *)
  ; ind_glu_of_type_exp : ind_glu_of_type_El <∙> ind_glu_exp_pred p D ups ns ind_glu_of_type_NP ind_glu_of_type_NEl ind_glu_of_type_AP ind_glu_of_type_AEl ind_glu_of_type_DP ind_glu_of_type_DEl k Mk ind_glu_of_type_R Typeω@(large_level u)
    (** [R] is the clause's relation *)
  ; ind_glu_of_type_rel : R <~> ind_glu_of_type_R
    (** The families are glued *)
  ; ind_glu_of_type_fams : ind_fams_glu D ups u ind_glu_of_type_NP ind_glu_of_type_NEl ind_glu_of_type_AP ind_glu_of_type_AEl ind_glu_of_type_DP ind_glu_of_type_DEl }.

(** The type former of a member applied to its parameters, value by value. *)
Lemma eval_apps_indty : forall p D k Mk ys xs, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    List.length xs + List.length ys <= im_np D Mk ->
    $*| d_ind p k xs & ys | gc_deps ⍮ gc_stack ↘ d_ind p k (xs ++ ys).
Proof.
  intros p D k Mk; induction ys as [| y ys IH]; intros xs Hl HM Hlen; [ rewrite List.app_nil_r; constructor |].
  econstructor; [ eapply eval_app_indty; [ exact Hl | exact HM | cbn in *; lia ] |].
  replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
  apply IH; [ exact Hl | exact HM | rewrite List.length_app; cbn in *; lia ].
Qed.

(** The records of the record views of the groups of [VP] are glued: the
    records the gluing of a record view's elements reads.  Only these:
    a sound embedding glues the records of its source, which these are,
    not every record of the target. *)
Definition glu_rview_records (VP : qname -> ind_decl -> Prop) : Prop :=
  forall qn G j Mj qr Is fl R, VP qn G -> ind_member G j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    record_lookup gc_deps gc_stack qr = Some R -> glu_record_decl R.

(** The ends of the recursive arguments' shapes of [D] are glued at every
    admissible uniform parameters, at the gluings of the clause there
    ([glu_self_ends_ok]). *)
Definition glu_self_ends_all (p : qname) (D : ind_decl) : Prop :=
  forall ups bu (u : universe_index) NP NEl AP AEl DP DEl,
    List.length ups = ind_nu D -> per_tele_args (List.rev (ind_uparams D)) nil nil ups ups ->
    ⟦ ind_sort D ⟧ decl_env D ups ↘ bu -> universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u ->
    ind_fams_glu D ups u NP NEl AP AEl DP DEl -> glu_self_ends_ok p D ups NEl.

Section Former.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_ind_decl D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)) (Hass : group_structure D).
  (** The ends of the recursive arguments' shapes are glued *)
  Hypothesis (Hselfs : glu_self_ends_all p D).

  Lemma ind_sort_le : forall k Mk Δ Ms bu ups, ind_member D k = Some Mk -> ⊢ Δ -> List.length Ms = im_np D Mk ->
      (forall j M T, List.nth_error Ms j = Some M -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T -> Δ ⊢ M : T) ->
      ⟦ ind_sort D ⟧ decl_env D ups ↘ bu ->
      Δ ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms] ⊆ Typeω@(large_level (Completeness.Inductives.Decl.univ_idx bu)).
  Proof.
    intros * HM HΔ HMl HMs Hbu.
    assert (HUl : List.length (List.firstn (ind_nu D) Ms) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in *; lia).
    destruct (params_typed_split _ _ D Hc k Mk Δ Ms HM HMl HMs) as [HU _].
    pose proof (wf_sub_uparams _ _ D Hdt Hc Δ _ HΔ HUl HU) as Hσ.
    destruct (sort_lvl_at _ _ D Hdt Hc _ _ HΔ Hσ) as [n Hn].
    rewrite <- (List.firstn_skipn (ind_nu D) Ms) at 1.
    replace (im_nn Mk) with (List.length (List.skipn (ind_nu D) Ms)) by (rewrite List.length_skipn; unfold im_np in *; lia).
    rewrite exp_shift_past.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hbu, Hn |- *; inversion Hbu; subst; cbn [Completeness.Inductives.Decl.univ_idx large_level exp_sub].
    - eapply wf_subtyp_refl'; apply wf_exp_eq_refl; mauto 3.
    - cbn in Hn; eapply wf_subtyp_small_large; eassumption.
  Qed.

  Lemma glu_args_uparams_of_params : forall Mk Δ Ms vs, glu_args Δ (im_params D Mk) Id nil Ms vs ->
      glu_args Δ (ind_uparams D) Id nil (List.firstn (ind_nu D) Ms) (List.firstn (ind_nu D) vs).
  Proof.
    intros * Hg.
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2].
    rewrite length_im_params in L1, L2.
    rewrite <- (List.firstn_skipn (ind_nu D) Ms), <- (List.firstn_skipn (ind_nu D) vs) in Hg; unfold im_params in Hg.
    apply glu_args_app in Hg; [ exact (proj1 Hg) | exact (group_structure_uparams _ Hass) | |];
      rewrite List.length_firstn; unfold im_np, ind_nu in *; lia.
  Qed.

  (** A declared member's type at parameters glued to [ups ++ ns], at
      gluings of the clause at [ups]. *)
  Lemma ind_typ_at_of_args : forall k Mk Δ Ms ups ns bu (u : universe_index) NP NEl AP AEl DP DEl,
      ind_member D k = Some Mk -> k < ind_ndecl D -> ⊢ Δ ->
      glu_args Δ (im_params D Mk) Id nil Ms (ups ++ ns) -> List.length ups = ind_nu D ->
      ⟦ ind_sort D ⟧ decl_env D ups ↘ bu -> universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u ->
      ind_fams_glu D ups u NP NEl AP AEl DP DEl -> glu_self_ends_ok p D ups NEl ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
      ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@(large_level u) Δ (apps (a_ind p k) Ms) Ms.
  Proof.
    intros * HM Hlt HΔ Hg Hu Hbu Hule Hf Hself Hns.
    assert (Hsub : forall Δ' Ms', ⊢ Δ' -> List.length Ms' = im_np D Mk ->
              (forall j M T, List.nth_error Ms' j = Some M -> List.nth_error (tele_insts (im_params D Mk) Id Ms') j = Some T -> Δ' ⊢ M : T) ->
              Δ' ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms'] ⊆ Typeω@(large_level u)).
    { intros Δ' Ms' HΔ'0 HMl' HMs'.
      eapply wf_subtyp_trans; [ eapply ind_sort_le; eassumption |].
      pose proof (universe_index_le_large_level_le _ _ Hule) as Hlv.
      destruct (Nat.eq_dec (large_level (Completeness.Inductives.Decl.univ_idx bu)) (large_level u)) as [-> | Hne].
      - eapply wf_subtyp_refl'; apply wf_exp_eq_refl; mauto 3.
      - apply wf_subtyp_univ; [ exact HΔ'0 | lia ]. }
    pose proof (decl_closed_params_ass D k Mk Hc HM) as HassP.
    pose proof (decl_closed_params D k Mk Hc HM) as Hs.
    destruct (glu_args_params_top _ _ _ _ _ HassP Hs Hg) as [HMl HMs _].
    split.
    - eapply wf_exp_eq_subtyp'; [| eapply Hsub; eassumption ].
      eapply wf_exp_eq_ind_apps; [ exact Hl | exact HM | exact Hlt | exact HΔ | exact HMl | exact HMl |].
      intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; eapply HMs; eassumption.
    - intros Δ' φ Hφ.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      pose proof (glu_args_wk _ _ _ _ _ _ _ HassP Hs Hφ Hg) as Hg'.
      pose proof (glu_args_params_top _ _ _ _ _ HassP Hs Hg') as Htop.
      (** The uniform and the non-uniform parameters, apart *)
      pose proof (glu_args_uparams_of_params _ _ _ _ Hg') as HUs'.
      rewrite firstn_app_exact in HUs' by exact Hu.
      destruct (glu_args_length _ _ _ _ _ _ Hg') as [HlM _].
      rewrite length_im_params in HlM.
      assert (HNs' : glu_args Δ' (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ms)))
                       (decl_env D ups) (List.skipn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ms)) ns).
      { pose proof Hg' as Hg0.
        rewrite <- (List.firstn_skipn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ms)) in Hg0; unfold im_params in Hg0.
        apply glu_args_app in Hg0; [ exact (proj2 Hg0) | exact (group_structure_uparams _ Hass) | |];
          rewrite ?List.length_firstn; unfold im_np, ind_nu in *; lia. }
      constructor.
      + exact Htop.
      + destruct Htop as [HMl' HMs' _]; eapply Hsub; eassumption.
      + intros Ps' HPs'.
        pose proof (glu_args_resp_eq _ _ _ _ _ _ HassP (member_params_wf _ _ _ _ _ Hdt HM) HΔ' HPs' Hg') as Hg''.
        pose proof (glu_args_uparams_of_params _ _ _ _ Hg'') as HUs.
        rewrite firstn_app_exact in HUs by exact Hu.
        eapply components_of_uparams; eassumption.
      + eapply nparams_of_glu_args; try eassumption.
        eapply components_of_uparams; eassumption.
  Qed.

  (** The gluing of a declared member's type in the PER model. *)
  Lemma ind_glu_of_per : forall (u : universe_index) R k Mk pm ups ns, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem u ↘ R -> List.length ups = ind_nu D ->
      ind_glu_of_type p D ups ns u k Mk R.
  Proof.
    intros * HM Hh HR Hu.
    destruct (per_univ_glu_univ_elem u _ (ex_intro _ R HR)) as (P & El & Hglu).
    pose proof Hglu as Hglu'.
    invert_glu_univ_elem Hglu'.
    match goal with H : ind_lookup _ _ p = Some ?D0 |- _ => assert (D0 = D) as -> by congruence end.
    match goal with H : ind_member D k = Some ?M0 |- _ => assert (M0 = Mk) as -> by congruence end.
    match goal with H : ?w ++ ?x = ups ++ ns, H' : List.length ?w = ind_nu D |- _ =>
      destruct (app_split_eq _ _ _ _ H ltac:(congruence)) as [-> ->] end.
    handle_per_univ_elem_irrel.
    econstructor; [ exact Hglu | eassumption | eassumption | eassumption |].
    constructor; eassumption.
  Qed.

  Lemma glu_sub_params : forall k Mk Δ Ms vs Sb, ind_member D k = Some Mk -> ⊢ Δ -> EG im_params D Mk ∈ glu_ctx_env ↘ Sb ->
      glu_args Δ (im_params D Mk) Id nil Ms vs -> Δ ⊢ˢ sb_of_list Id Ms ® env_tele nil (List.rev (im_params D Mk)) vs ∈ Sb.
  Proof.
    intros * HM HΔ HSb Hg.
    eapply glu_sub_of_list with (C := im_params D Mk) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ exact (decl_closed_params_ass D k Mk Hc HM) | rewrite List.app_nil_r; exact HSb
      | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ] | cbn; apply wf_sub_nil'; exact HΔ | exact Hg ].
  Qed.

  Lemma glu_sub_uparams : forall Δ Us ups Sb, ⊢ Δ -> EG ind_uparams D ∈ glu_ctx_env ↘ Sb ->
      glu_args Δ (ind_uparams D) Id nil Us ups -> Δ ⊢ˢ sb_of_list Id Us ® decl_env D ups ∈ Sb.
  Proof.
    intros * HΔ HSb Hg; unfold decl_env.
    eapply glu_sub_of_list with (C := ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ exact (group_structure_uparams _ Hass) | rewrite List.app_nil_r; exact HSb | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
      | cbn; apply wf_sub_nil'; exact HΔ | exact Hg ].
  Qed.

  (** The universe of the sort at the parameters' values is the one at the
      uniform ones. *)
  Lemma sort_idx_params : forall k Mk Δ Ms vs b, ind_member D k = Some Mk -> ⊢ Δ -> glu_args Δ (im_params D Mk) Id nil Ms vs ->
      ⟦ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ ⟧ env_tele nil (List.rev (im_params D Mk)) vs ↘ b ->
      exists bu, ⟦ ind_sort D ⟧ decl_env D (List.firstn (ind_nu D) vs) ↘ bu /\
        Completeness.Inductives.Decl.univ_idx bu = Completeness.Inductives.Decl.univ_idx b.
  Proof.
    intros * HM HΔ Hg Hb.
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [_ Hvl]; rewrite length_im_params in Hvl.
    pose proof (member_params_wf _ _ _ _ _ Hdt HM) as HΔP; pose proof (decl_typed_sort _ _ _ Hdt) as [iS HS].
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hb, HS |- *; cbn [exp_wk] in Hb.
    - inversion Hb; subst; exists (d_univ i0); split; [ constructor | reflexivity ].
    - inversion Hb; subst.
      match goal with Hlv : ⟦ t[wk_shiftn _]ʷ ⟧ _ ↘ ?l |- _ => rename l into lv; rename Hlv into Hlv0 end.
      destruct (glu_ind_decl_lvl _ HG) as [n HLu]; apply glu_rel_exp_of_under_sub in HLu; rewrite Heq in HLu; cbn [ind_sort_lvl] in HLu.
      pose proof HLu as [SbU HSbU _ _].
      pose proof (glu_sub_uparams _ _ _ _ HΔ HSbU (glu_args_uparams_of_params _ _ _ _ Hg)) as Hσu.
      destruct (glu_rel_exp_level_elim HSbU HLu _ _ _ Hσu) as (l' & Hl' & _).
      exists (d_suniv l'); split; [ econstructor; exact Hl' |].
      pose proof (glu_rel_ctx_types_ctx _ (glu_ind_decl_params _ HG _ _ HM)) as [SbP HSbP].
      pose proof (glu_sub_params _ _ _ _ _ _ HM HΔ HSbP Hg) as Hσ.
      assert (HCs : ⊨ im_nparams Mk ++ ind_uparams D) by (apply completeness_fundamental_ctx; exact HΔP).
      assert (HSs : ind_uparams D ⊨ Type⟨t⟩ : Typeω@iS) by (apply completeness_fundamental_exp; exact HS).
      destruct (rel_ctx_wf_per_ctx_env HCs) as [R HR].
      pose proof (glu_ctx_env_per_env HSbP HR Hσ) as HE.
      assert (Eb : ⟦ Type⟨t⟩[wk_shiftn (List.length (im_nparams Mk))]ʷ ⟧ env_tele nil (List.rev (im_params D Mk)) vs ↘ d_suniv lv)
        by (rewrite length_im_nparams; cbn [exp_wk]; econstructor; exact Hlv0).
      assert (Ea : ⟦ Type⟨t⟩ ⟧ ⟪wk_shiftn (List.length (im_nparams Mk))⟫ (env_tele nil (List.rev (im_params D Mk)) vs) ↘ d_suniv l').
      { replace (env_tele nil (List.rev (im_params D Mk)) vs)
          with (components_env D (List.firstn (ind_nu D) vs) (List.rev (im_nparams Mk)) (List.skipn (ind_nu D) vs))
          by (unfold im_params; rewrite <- Completeness.Inductives.Decl.env_tele_uparams, List.firstn_skipn
                by (rewrite List.length_firstn; unfold im_np in *; lia); reflexivity).
        replace (List.length (im_nparams Mk)) with (List.length (List.skipn (ind_nu D) vs))
          by (rewrite List.length_skipn, length_im_nparams; unfold im_np in *; lia).
        rewrite Completeness.Inductives.Decl.eval_wk_shiftn_components_env; econstructor; exact Hl'. }
      exact (Completeness.Inductives.Decl.univ_idx_wk _ _ _ _ _ _ _ _ _ HCs HSs HR HE Eb Ea ltac:(right; eauto)).
  Qed.

  Lemma sort_shift_scoped : forall Mk, exp_scoped (im_np D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ.
  Proof.
    intros; eapply exp_scoped_wk; [ exact (decl_closed_sort _ Hc) |]; intros x Hx.
    unfold wk_shiftn, im_np; lia.
  Qed.

  Lemma scoped_inst_wk : forall n M Ms φ, exp_scoped n M -> List.length Ms = n ->
      M[sb_of_list Id Ms][φ]ʷ = M[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ms)].
  Proof.
    intros * Hs Hlen.
    rewrite <- exp_sub_of_wk, exp_sub_sub.
    rewrite <- (List.map_ext _ _ (fun N => exp_sub_of_wk N φ)).
    eapply exp_scoped_sub_agree; [ exact Hs |]; intros x Hx; cbn [sb_compose].
    apply sb_of_list_lt_compose; lia.
  Qed.

  (** The type former of a declared member applied to glued parameters is
      glued at the sort's universe. *)
  Lemma ind_former_base : forall k Mk pm Δ Ms vs (i : nat) b P El, ind_member D k = Some Mk -> im_head Mk = mh_decl pm -> ⊢ Δ ->
      glu_args Δ (im_params D Mk) Id nil Ms vs ->
      ⟦ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ ⟧ env_tele nil (List.rev (im_params D Mk)) vs ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
      (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R (d_ind p k vs) (d_ind p k vs)) ->
      Δ ⊢ apps (a_ind p k) Ms : (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms] ® d_ind p k vs ∈ El.
  Proof.
    intros * HM Hh HΔ Hg Hb Hglu HPER.
    assert (Hlt : k < ind_ndecl D) by (eapply decl_member_lt; eassumption).
    pose proof (decl_closed_params_ass D k Mk Hc HM) as HassP.
    pose proof (decl_closed_params D k Mk Hc HM) as Hs.
    pose proof (glu_args_params_top _ _ _ _ _ HassP Hs Hg) as Htop.
    pose proof Htop as [HMl HMs HMr].
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [_ Hvl]; rewrite length_im_params in Hvl.
    destruct (sort_idx_params _ _ _ _ _ _ HM HΔ Hg Hb) as (bu & Hbu & Hidx).
    assert (Hvs : vs = List.firstn (ind_nu D) vs ++ List.skipn (ind_nu D) vs) by (symmetry; apply List.firstn_skipn).
    set (ups := List.firstn (ind_nu D) vs) in *; set (ns := List.skipn (ind_nu D) vs) in *.
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; unfold im_np in *; lia).
    assert (HAeq : Δ ⊢ apps (a_ind p k) Ms ≈ apps (a_ind p k) Ms : (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms]).
    { eapply wf_exp_eq_ind_apps; [ exact Hl | exact HM | exact Hlt | exact HΔ | exact HMl | exact HMl |].
      intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; eapply HMs; eassumption. }
    assert (HAt : Δ ⊢ apps (a_ind p k) Ms : (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms]) by (gen_presups; assumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
    pose proof (HPER _ HRb) as Hdind.
    assert (Hub : Completeness.Inductives.Decl.is_univ b)
      by (destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hb; cbn in Hb; inversion Hb; [ left | right ]; eauto).
    destruct (Completeness.Inductives.Decl.per_univ_elem_univ _ _ _ _ HRb Hub) as [_ HRb'].
    apply HRb' in Hdind; destruct Hdind as [[R' HR'] _ _ _ _].
    rewrite <- Hidx in HR'; rewrite Hvs in HR', Hg.
    destruct (ind_glu_of_per _ R' k Mk pm ups ns HM Hh HR' Hu) as [NP NEl AP AEl DP DEl Pd Eld R'' Hglud HPd HEd HRR Hf].
    assert (Hgu : per_tele_args (List.rev (ind_uparams D)) nil nil ups ups).
    { pose proof (glu_args_uparams_of_params _ _ _ _ Hg) as HUs.
      rewrite firstn_app_exact in HUs by exact Hu.
      exact (glu_args_per_tele_args _ _ _ _ _ _ (group_structure_uparams _ Hass) HUs). }
    pose proof (Hselfs ups bu _ NP NEl AP AEl DP DEl Hu Hgu Hbu (universe_index_le_refl _) Hf) as Hself.
    assert (Hns : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns).
    { pose proof (ind_canon_clause_ns _ _ _ _ _ _ _ _ (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HR' Hl Hu Hu)) as H.
      unfold member_nparams in H; rewrite HM in H; exact H. }
    pose proof (ind_typ_at_of_args k Mk Δ Ms ups ns bu _ NP NEl AP AEl DP DEl HM Hlt HΔ Hg Hu Hbu (universe_index_le_refl _) Hf
                  Hself Hns) as Hit.
    assert (Hgd : glu_univ_typ (Completeness.Inductives.Decl.univ_idx bu) (d_ind p k vs) Δ (apps (a_ind p k) Ms))
      by (rewrite Hvs; apply (mk_glu_typ_at _ _ _ _ Pd Eld); [ exact Hglud | apply HPd; exists Ms; exact Hit ]).
    clear HPER.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hb, HAt |- *; cbn [exp_wk exp_sub] in Hb, HAt |- *; inversion Hb; subst b.
    - invert_glu_univ_elem Hglu.
      apply_predicate_equivalence.
      cbn [Completeness.Inductives.Decl.univ_idx] in Hidx; rewrite Hidx in Hgd.
      econstructor; [ exact HAt | apply wf_exp_eq_refl; mauto 3 | exact Hgd ].
    - invert_glu_univ_elem Hglu.
      apply_predicate_equivalence.
      cbn [Completeness.Inductives.Decl.univ_idx] in Hidx; rewrite Hidx in Hgd.
      destruct (glu_ind_decl_lvlP _ HG _ _ HM) as [n HLv]; apply glu_rel_exp_of_under_sub in HLv; rewrite Heq in HLv; cbn [ind_sort_lvl exp_wk] in HLv.
      pose proof HLv as [SbP HSbP _ _].
      rewrite <- Hvs in Hg.
      pose proof (glu_sub_params _ _ _ _ _ _ HM HΔ HSbP Hg) as Hσ.
      destruct (glu_rel_exp_level_elim HSbP HLv _ _ _ Hσ) as (m & Hm & _ & Hglul).
      assert (m = l) as -> by (eapply functional_eval_exp; eassumption).
      assert (Htl : Δ ⊢ t[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms] : Level@n)
        by (eapply glu_lvl_escape; [ eassumption | exact Hglul | exact HΔ ]).
      econstructor; [ exact HAt | | exact Hgd |].
      + apply (mk_suniv_glu_typ _ _ _ _ (t[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms]) n); [ exact Hglul |].
        apply wf_exp_eq_refl; mauto 3.
      + intros Δ' φ W Hφ HW.
        inversion HW.
        match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
        match goal with H : ind_member D k = Some ?M1 |- _ => assert (M1 = Mk) as -> by congruence end.
        match goal with HR : Rps vs at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Rs |- _ =>
          destruct (HMr _ _ _ Hφ HR) as [HRl HRs] end.
        unfold glu_nf_eq; cbn [nf_to_exp].
        rewrite apps_wk; cbn [exp_wk].
        assert (HS' : exp_scoped (im_np D Mk) (Type⟨t[wk_shiftn (im_nn Mk)]ʷ⟩))
          by (pose proof (sort_shift_scoped Mk) as Hss; rewrite Heq in Hss; exact Hss).
        change (Type⟨t[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms][φ]ʷ⟩) with ((Type⟨t[wk_shiftn (im_nn Mk)]ʷ⟩)[sb_of_list Id Ms][φ]ʷ).
        rewrite (scoped_inst_wk _ _ _ _ HS' HMl).
        assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
        assert (Hl1 : List.length (List.map (fun N => N[φ]ʷ) Ms) = im_np D Mk) by (rewrite List.length_map; exact HMl).
        pose proof (wf_exp_eq_ind_apps _ _ _ _ _ _ _ Hl HM Hlt HΔ' Hl1 ltac:(rewrite <- HRl; exact Hl1) HRs) as Heqn.
        rewrite Heq in Heqn; exact Heqn.
  Qed.

  (** The sort, past the non-uniform parameters, is a valid entry over the
      parameters at any index it is a type of: a large universe, or a small
      one at the glued level ([glu_ind_decl_lvlP]). *)
  Lemma sort_entry_valid : forall k Mk (i : nat), ind_member D k = Some Mk ->
      im_params D Mk ++ ⋅ ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ : Typeω@i ->
      glu_entry_valid_at i (im_params D Mk ++ ⋅) ak_relevant (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ.
  Proof.
    intros * HM HT.
    apply glu_entry_valid_of_rel.
    destruct (glu_rel_ctx_types_ctx _ (glu_ind_decl_params _ HG _ _ HM)) as [SbP HSbP].
    rewrite List.app_nil_r in HT |- *.
    assert (HΓ : ⊩ im_params D Mk) by (eexists; exact HSbP).
    destruct Hsu as [[j Heq] | [t Heq]]; rewrite Heq in HT |- *; cbn [exp_wk] in HT |- *.
    - eapply glu_rel_exp_subtyp; [ exact (glu_rel_exp_typ HΓ) | exact (glu_rel_exp_typ HΓ) | constructor | exact (wf_typ_inversion HT) ].
    - destruct (glu_ind_decl_lvlP _ HG _ _ HM) as [n HLv]; apply glu_rel_exp_of_under_sub in HLv; rewrite Heq in HLv; cbn [ind_sort_lvl] in HLv.
      eapply glu_rel_exp_subtyp; [ eapply glu_rel_exp_univ_lvl; exact HLv | exact (glu_rel_exp_typ HΓ) | constructor
                                 | exact (wf_univ_inversion HT) ].
  Qed.

  Lemma sb_of_list_scoped_base : forall M Ms σ τ, exp_scoped (List.length Ms) M ->
      M[sb_of_list σ Ms] = M[sb_of_list τ Ms].
  Proof.
    intros * Hs; eapply exp_scoped_sub_agree; [ exact Hs |]; intros x Hx.
    rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by exact Hx; reflexivity.
  Qed.

  (** The PER of the closed constant [a_ind p k] at its type. *)
  Lemma ind_former_per : forall k Mk (i : nat) R a, ind_member D k = Some Mk -> k < ind_ndecl D ->
      ⟦ ind_ty D Mk ⟧ nil ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> R (d_ind p k nil) (d_ind p k nil).
  Proof.
    intros * HM Hlt Ha HR.
    assert (HΔ0 : ⊢ ⋅) by (constructor; eapply ctx_wf_gctx; exact (member_params_wf _ _ _ _ _ Hdt HM)).
    assert (Hty : ⋅ ⊢ a_ind p k : ind_ty D Mk) by (eapply wf_ind; eassumption).
    destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Hty)) as (env_rel & Henv & j & Hsimp).
    assert (Hnil : env_rel nil nil) by (inversion Henv; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
    destruct (ind_ty_typed0 _ _ _ _ _ Hdt HM) as [j0 Hj0].
    destruct (Completeness.ContextCases.rel_type_kind_of_typ (completeness_fundamental_exp _ _ _ Hj0) _ Henv _ _ Hnil) as (a0 & Ea0 & Hk0).
    destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & [Hp | (m1 & m2 & Hm1 & Hm2 & Hmm)]).
    { (* the type of a type former is relevant *)
      assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption); congruence. }
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
    inversion Hm1; subst; inversion Hm2; subst.
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR); exact Hmm.
  Qed.

  (** The type former of a declared member is glued at its type. *)
  Lemma glu_rel_exp_ind0 : forall k Mk pm, ind_member D k = Some Mk -> im_head Mk = mh_decl pm -> ⋅ ⊩ a_ind p k : ind_ty D Mk.
  Proof.
    intros k Mk pm HM Hh.
    assert (Hg0 : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact (member_params_wf _ _ _ _ _ Hdt HM)).
    assert (HΔ0 : ⊢ ⋅) by (constructor; exact Hg0).
    assert (Hlt : k < ind_ndecl D) by (eapply decl_member_lt; [ exact HΔ0 | eassumption | eassumption | eassumption ]).
    pose proof (decl_closed_params_ass D k Mk Hc HM) as HassP.
    pose proof (decl_closed_params D k Mk Hc HM) as Hs.
    destruct (ind_ty_typed0 _ _ _ _ _ Hdt HM) as [j Hj].
    destruct (glu_rel_ctx_types_ctx _ (glu_ind_decl_params _ HG _ _ HM)) as [SbP HSbP].
    assert (HSbP0 : EG im_params D Mk ++ ⋅ ∈ glu_ctx_env ↘ SbP) by (rewrite List.app_nil_r; exact HSbP).
    destruct (glu_ctx_env_entries_valid _ _ _ HassP HSbP0 j) as (i & Hji & HAents).
    assert (Hi : ⋅ ⊢ ind_ty D Mk : Typeω@i) by (eapply lift_exp_ge; [ exact Hji | exact Hj ]).
    eapply (glu_closed_const _ _ i (d_ind p k nil)); [ reflexivity | intros; eapply ind_ty_sub; eassumption | exact Hi | intros; constructor |].
    intros Δ σ Hσ ρ a P El Ha Hglu.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
    pose proof Hi as Hi'; unfold ind_ty in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ HassP Hi') as [HCs _].
    unfold ind_ty in Ha |- *.
    replace (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)
      with ((ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[σ])
      by (change (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) with (ind_ty D Mk); eapply ind_ty_sub; eassumption).
    change (a_ind p k) with (apps (a_ind p k) nil).
    eapply (ctx_pi_glu_elem_by_closed (fun xs w => w = d_ind p k xs) (a_ind p k) (im_params D Mk ++ ⋅)) with (Sb := SbP);
      [ reflexivity | | exact HassP | exact Hg0 | exact HSbP0
      | exists nil; reflexivity
      | intros; eapply HAents; eassumption
      | intros; eapply HCs; eassumption
      | eapply sort_entry_valid; [ exact HM | exact (HCs nil _ eq_refl) ]
      | exact Hσ | reflexivity | | | | exact Ha | exact Hglu ].
    - intros Δ1 Γ' Sb' Δ' σ' xs x w HT _ _ HlΓ ->.
      exists (d_ind p k (xs ++ x :: nil)); split; [| reflexivity ].
      eapply eval_app_indty; [ exact Hl | exact HM |].
      assert (List.length Γ' <= List.length (im_params D Mk ++ ⋅)) by (rewrite HT, List.length_app; lia).
      rewrite List.app_nil_r, length_im_params in *; lia.
    - cbn [apps_exp]; change (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) with (ind_ty D Mk).
      erewrite ind_ty_sub by eassumption; eapply wf_ind; eassumption.
    - intros R a' Ha' HR; exact (ind_former_per _ _ _ _ _ HM Hlt Ha' HR).
    - intros Δ' φ Ms vs w' Hφ Hg -> b P' El' Hb Hglub HPb; cbn [List.map List.app] in *.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      apply (glu_args_closed_base _ _ _ Id _ _ _ HassP Hs) in Hg.
      rewrite List.app_nil_r in Hb.
      destruct (glu_args_length _ _ _ _ _ _ Hg) as [HMl _].
      rewrite (sb_of_list_scoped_base _ _ _ Id) by (rewrite HMl, length_im_params; exact (sort_shift_scoped Mk)).
      exact (ind_former_base _ _ _ _ _ _ _ _ _ _ HM Hh HΔ' Hg Hb Hglub HPb).
  Qed.

End Former.

End Fixed_GCtx.
