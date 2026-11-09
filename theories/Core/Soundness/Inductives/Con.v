(** * The Constructors of a Group in the Gluing Model

    A constructor of a member [k] of a group, applied to parameters and
    arguments glued along its telescopes, is an element of the member at the
    gluings of the clause ([con_ind_glu_elem]): its non-uniform parameters
    and non-recursive arguments are glued at the families of the clause, a
    recursive argument at its shape ([con_rec_glu]).  A recursive argument
    ending in a declared member is an element of it by the gluing of its
    type; one ending in a view by [glu_view_end_ok], which the coherence of
    the view with its container gives.  Then the constructor is glued at its
    type ([glu_rel_exp_con0]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes.
From Mctt.Core.Completeness.Inductives Require Con ViewArgs CargsRel.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Semantic Require Import Realizability RetagReadable.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
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
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args Comps.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_univ_of_elem : forall (i : universe_index) R a b, DF a ≈ b ∈ per_univ_elem i ↘ R -> Dom a ≈ b ∈ per_univ i.
Proof. intros * H; exists R; exact H. Qed.

(** A record type former applied to arguments determines them, as
    [apps_ind_inj] for an inductive type former. *)
Lemma apps_record_inj : forall qr Q Q', apps (a_record qr) Q = apps (a_record qr) Q' -> Q = Q'.
Proof.
  intros qr Q; induction Q as [| N Q IH] using List.rev_ind; intros Q' H;
    destruct Q' as [| N' Q' _] using List.rev_ind; try reflexivity;
    rewrite ?apps_exp_snoc in H; cbn in H; try discriminate.
  injection H as H ->; rewrite (IH _ H); reflexivity.
Qed.


Lemma cargs_rev_nth_arg : forall p D Mk gs gs1 r B gs2, gs = gs1 ++ ca_arg r B :: gs2 ->
    List.nth_error (List.rev (cargs_ctx p D Mk gs)) (List.length gs1) = Some (ce_ass r B[wk_pat (cargs_pat gs1)]ʷ).
Proof.
  intros * ->.
  unfold cargs_ctx; rewrite cargs_ctx_aux_app; cbn [cargs_ctx_aux].
  rewrite !List.rev_app_distr; cbn [List.rev List.app].
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag, List.app_nil_r; reflexivity.
Qed.

Lemma cargs_rev_nth_rec : forall p D Mk gs gs1 Pr gs2, gs = gs1 ++ ca_rec Pr :: gs2 ->
    List.nth_error (List.rev (cargs_ctx p D Mk gs)) (List.length gs1)
      = Some (ce_ass ak_relevant (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) Pr)).
Proof.
  intros * ->.
  unfold cargs_ctx; rewrite cargs_ctx_aux_app; cbn [cargs_ctx_aux].
  rewrite !List.rev_app_distr; cbn [List.rev List.app].
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag, !List.app_nil_r; reflexivity.
Qed.

Lemma cargs_split_aux : forall p D Mk gs gs1 g gs2, gs = gs1 ++ g :: gs2 ->
    cargs_ctx p D Mk gs = cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) (g :: gs2) ++ cargs_ctx p D Mk gs1.
Proof. intros * ->; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; reflexivity. Qed.

(** The arguments of a constructor before a position, over its parameters:
    the closed environment of the context of those arguments. *)
Lemma env_tele_cargs_prefix : forall p D Mk gs gs1 g gs2 ps vs, gs = gs1 ++ g :: gs2 ->
    List.length ps = im_np D Mk -> List.length vs = List.length gs1 ->
    env_tele (env_tele nil (List.rev (im_params D Mk)) ps) (List.rev (cargs_ctx p D Mk gs)) vs
    = env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ps ++ vs).
Proof.
  intros * Heq Hps Hvs.
  rewrite List.rev_app_distr, env_tele_app by (rewrite List.length_rev, length_im_params; exact Hps).
  rewrite (env_tele_firstn _ (List.rev (cargs_ctx p D Mk gs)) vs), (env_tele_firstn _ (List.rev (cargs_ctx p D Mk gs1)) vs).
  rewrite (cargs_split_aux p D Mk gs gs1 g gs2 Heq), List.rev_app_distr.
  rewrite firstn_app_exact by (rewrite List.length_rev, length_cargs_ctx; lia).
  rewrite List.firstn_all2 by (rewrite List.length_rev, length_cargs_ctx; lia).
  reflexivity.
Qed.

Lemma cargs_suffix_glu : forall p D Mk gs gs1 gs2, gs = gs1 ++ gs2 -> ⊩ cargs_ctx p D Mk gs ++ im_params D Mk ->
    exists Sb, EG cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ glu_ctx_env ↘ Sb.
Proof.
  intros * Heq [Sb HSb].
  rewrite Heq in HSb; unfold cargs_ctx in HSb; rewrite cargs_ctx_aux_app, <- List.app_assoc in HSb.
  eapply glu_ctx_env_suffix; [| exact HSb ]; apply cargs_ctx_aux_ass.
Qed.

(** The type of a domain of a recursive argument's shape, at all the
    arguments and at the non-recursive ones: related types. *)
Lemma valid_group_dom_types : forall pq G, valid_group pq G -> containers_valid G ->
    forall k Mk c gs gs1 t gs2 d B U ms vs ys, ind_member G k = Some Mk -> ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (ptyp_doms t) d = Some B ->
    List.length U = ind_nu G -> List.length ms = im_nn Mk -> List.length vs = List.length gs1 -> List.length ys = d ->
    per_tele_args (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk))
      nil nil (U ++ ms ++ vs ++ ys) (U ++ ms ++ vs ++ ys) ->
    exists (i : nat) R a a', ⟦ B[wk_pat (List.repeat false d ++ cargs_pat gs1)]ʷ ⟧
        env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk))
          (U ++ ms ++ vs ++ ys) ↘ a /\
      ⟦ B ⟧ components_env G U (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
          (ms ++ nonrec_arg_vals gs1 vs ++ ys) ↘ a' /\
      DF a ≈ a' ∈ per_univ_elem i ↘ R.
Proof.
  intros pq G Hg Hcv k Mk c gs gs1 t gs2 d B U ms vs ys HM Hcon Heq HB HlU Hlm Hlv Hly Hgp.
  pose proof (valid_group_valid _ _ Hg) as HD.
  assert (Hd : d <= List.length (ptyp_doms t)) by (assert (d < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
  destruct (valid_group_cargs_sem_all pq G Hg Hcv k Mk c gs HM Hcon gs1 (ca_rec t :: gs2) Heq) as [HW0 Hw0].
  pose proof (shape_domains_ctx_wk_gen G pq k Mk c gs HD HM Hcon gs1 t gs2 Heq Hw0 d Hd) as Hw.
  pose proof (shape_domains_ctx_sem_gen G pq k Mk c gs HD HM Hcon gs1 t gs2 Heq HW0 Hw0 d Hd) as HW.
  destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & j & HBv).
  rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
  destruct (rel_ctx_wf_per_ctx_env HW) as [RΓ HΓ].
  set (E := env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk))
              (U ++ ms ++ vs ++ ys)).
  assert (Hρ : RΓ E E).
  { apply (tele_args_env_rel _ _ _ _ _ _ HΓ HW); [| exact Hgp ].
    rewrite !List.length_app, length_shape_domains_ctx, List.length_firstn, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
  destruct (wk_type_retag_link _ _ _ _ _ _ _ Hw (rel_type_of_typ HBv) HΓ Hρ) as (i0 & Rm & m & m' & Em & Em' & HRm).
  assert (Hlf : List.length (List.firstn d (ptyp_doms t)) = d) by (rewrite List.length_firstn; lia).
  assert (HE : ctx_retag (doms_ctx (List.firstn d (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params G Mk)
                 (⟪wk_pat (List.repeat false d ++ cargs_pat gs1)⟫ E)
               = components_env G U (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn d (shape_doms_tele t))
                   (ms ++ nonrec_arg_vals gs1 vs ++ ys)).
  { unfold E; replace (List.repeat false d) with (List.repeat false (List.length (List.firstn d (ptyp_doms t)))) by (rewrite Hlf; reflexivity).
    rewrite (List.app_assoc U ms (vs ++ ys)).
    rewrite (ctx_retag_wk_cargs_doms pq G Mk gs1 (cargs_pat gs1) (List.firstn d (ptyp_doms t)) (U ++ ms) vs ys eq_refl)
      by (first [ rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | exact Hlv | lia ]).
    rewrite <- (List.app_assoc U ms), closed_env_shape_doms_components by exact HlU.
    unfold shape_doms_tele; rewrite List.firstn_map; reflexivity. }
  rewrite HE in Em'.
  rewrite !List.app_assoc in Em'.
  rewrite components_env_app_firstn_ge in Em'
    by (first [ rewrite !List.length_app, List.length_rev, length_im_nparams, length_cargs_nonrec_tele, length_nonrec_arg_vals by exact Hlv; lia
              | lia | unfold shape_doms_tele; rewrite List.length_map; lia ]).
  rewrite <- !List.app_assoc in Em'.
  exists i0, Rm, m, m'; split; [ exact Em | split; [ exact Em' | exact HRm ] ].
Qed.

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

(** ** Recursive Arguments Ending in a View

    A recursive argument whose shape ends in a view [j] is of the view's
    type, the container's member at the view's instance, glued at the
    container's type; its gluing as an element of [j] in the group is the
    coherence of the view with its container.  The element may be glued at
    any type of the container's value: an argument after some of its
    shape's domains is glued at the type its [Π]'s gluing gives. *)
Definition glu_view_end_at (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred) (j : nat) : Prop :=
  forall Mj qc kc Is vm Dq cups cs bs bs1 Δ Us Q W N v (i : universe_index) P El,
    ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups -> per_tele_args (List.rev (ind_uparams Dq)) nil nil cups cs ->
    tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs1 ->
    DG d_ind qc kc (cs ++ bs1) ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ N : W ® v ∈ El ->
    grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) j ups ups bs bs v v ->
    glu_args Δ (im_params D Mj) Id nil (Us ++ Q) (ups ++ bs) ->
    forall Δ' φ Us' Q', Δ' ⊢ᵏ φ : Δ -> List.length Us' = ind_nu D ->
      exps_eq_at Δ' (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
      ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' Q' N[φ]ʷ v.

(** A recursive argument whose shape ends in a record view [j] is of the
    record view's type, the record at the view's instance, glued at the
    record type at arguments [cs] related to the instance's values; its
    gluing as an element of [j] in the group is the coherence of the record
    view with its record.  Like [glu_view_end_at], the element may be glued
    at any type of the record's value. *)
Definition glu_rview_end_at (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred) (j : nat) : Prop :=
  forall Mj qr Is fl R cups cs Δ Us W N v (i : universe_index) P El,
    ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> record_lookup gc_deps gc_stack qr = Some R ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups -> per_tele_args (List.rev (record_params R)) nil nil cups cs ->
    DG d_record qr cs ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ N : W ® v ∈ El ->
    grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) j ups ups nil nil v v ->
    glu_args Δ (im_params D Mj) Id nil Us ups ->
    forall Δ' φ Us', Δ' ⊢ᵏ φ : Δ -> List.length Us' = ind_nu D ->
      exps_eq_at Δ' (im_params D Mj) (List.map (fun P => P[φ]ʷ) Us) Us' ->
      ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' nil N[φ]ʷ v.

(** The coherence of the member [j] the shape of a recursive argument ends
    in: with its container at a view, with its record at a record view
    (vacuous at a declared member). *)
Definition glu_end_at (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred) (j : nat) : Prop :=
  glu_view_end_at p D ups NEl AEl DP DEl j /\ glu_rview_end_at p D ups NEl AEl DP DEl j.

(** At every member. *)
Definition glu_view_end_ok (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred) : Prop :=
  forall j, glu_end_at p D ups NEl AEl DP DEl j.

(** ** A Constructor at Glued Parameters and Arguments *)

Section ConGlu.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Let HΨs := valid_group_cargs_sem p D Hg Hcv k Mk c gs HMk Hcon.
  Variables (ups : list domain) (bu : domain) (u : universe_index)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hgu : per_tele_args (List.rev (ind_uparams D)) nil nil ups ups)
    (Hbu : ⟦ ind_sort D ⟧ decl_env D ups ↘ bu)
    (Hule : universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).
  Hypothesis (Hview : glu_view_end_ok p D ups NEl AEl DP DEl).

  Let HeN := ind_fams_glu_nparams_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HNP := ind_fams_glu_nparams_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeA := ind_fams_glu_arg_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HAP := ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeD := ind_fams_glu_dom_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HDP := ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf.

  Lemma con_canon : ind_canon_props D ups.
  Proof. exact (valid_group_canon p D Hg ups Hgu Hu). Qed.

  (** The gluings of the non-uniform parameters move along their relations. *)
  Lemma nel_resp_per : forall m Mm j vs vs', ind_member D m = Some Mm -> j < im_nn Mm ->
      tele_prefix_rel (canon_nparams_rel D ups m) j vs vs' ->
      forall Γ A N n n', NEl m j vs Γ A N n -> canon_nparams_rel D ups m j vs n n' -> NEl m j vs' Γ A N n'.
  Proof.
    intros * HM Hj Hp Γ0 A0 N n n' HN Hnn.
    pose proof con_canon as Hcp.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    assert (Hk' : j < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, length_im_nparams; exact Hj).
    destruct (nparams_lt_ass D m Mm j Hass HM Hk') as (κ & S & HS).
    pose proof (nparams_prefix_rel_refl_l p D ups _ (canon_args_rel D ups) (canon_doms_rel D ups) Hass HnP HnI HaP HaI HdP HdI
                  m Mm HM j vs vs' ltac:(rewrite List.length_rev, length_im_nparams; lia) Hp) as Hd.
    pose proof (nparams_prefix_rel_refl_r p D ups _ (canon_args_rel D ups) (canon_doms_rel D ups) Hass HnP HnI HaP HaI HdP HdI
                  m Mm HM j vs vs' ltac:(rewrite List.length_rev, length_im_nparams; lia) Hp) as Hd'.
    destruct (HeN _ _ _ _ _ _ HM HS Hd) as [b Eb].
    pose proof (HNP _ _ _ _ _ _ _ HM HS Hd Eb) as Hgb.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
    assert (Hnn' : Rb n n')
      by (apply (per_head_iff Eb Eb HRb); unfold canon_nparams_rel in Hnn; rewrite (nth_ctyp_eq _ _ _ _ _ _ HM HS), (member_nparams_eq _ _ _ HM) in Hnn; exact Hnn).
    pose proof (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hgb _ HRb _ _ _ _ _ HN Hnn') as Hn2.
    destruct (canon_hn D HD Hc Hsu ups bu Hu Hbu ups Hgu _ _ _ _ _ _ _ HM HS Hp) as (a & a' & Ea & Ea' & Haa & _).
    assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct Haa as [Rh HRh].
    pose proof (per_univ_elem_cumu_universe_index _ _ _ _ HRh _ Hule) as HRh'.
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R => per_univ_elem u R b a') Rh HRh') Hgb) as Hga'.
    pose proof (HNP _ _ _ _ _ _ _ HM HS Hd' Ea') as Hgb'.
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [_ HEq].
    apply HEq; exact Hn2.
  Qed.

  (** Glued arguments of a constructor's non-recursive arguments are glued
      at the gluings of the clause. *)
  Lemma args_of_glu_args : forall Δ Us Ns ns As ws, ⊢ Δ ->
      ind_glu_components p D ups NP NEl AP AEl DP DEl Δ Us -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      glu_nparams k Mk NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
      glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) (env_tele nil (List.rev (im_params D Mk)) (ups ++ ns)) As ws ->
      tele_rel (canon_args_rel D ups k ns c) (cargs_nonrec gs) (nonrec_arg_vals gs ws) (nonrec_arg_vals gs ws) ->
      forall hs1 r B hs2 N T v, gs = hs1 ++ ca_arg r B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T ->
        List.nth_error ws (List.length hs1) = Some v ->
        Δ ⊢ N : T ® v ∈ AEl k ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws)).
  Proof.
    intros Δ Us Ns ns As ws HΔ Hc0 HUs Hnp Hns HgA Hv.
    pose proof Hc0 as [_ HCA _].
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (group_structure_uparams _ Hass) as HassU.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (HgP : glu_args Δ (im_params D Mk) Id nil (Us ++ Ns) (ups ++ ns)).
    { unfold im_params; apply glu_args_app; [ exact HassU | exact LU | exact Hu |].
      split; [ exact HUs |].
      eapply glu_args_of_nparams; eassumption. }
    enough (forall m hs1 r B hs2 N T v, List.length hs1 < m -> gs = hs1 ++ ca_arg r B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T ->
              List.nth_error ws (List.length hs1) = Some v ->
              Δ ⊢ N : T ® v ∈ AEl k ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws))) as Hm
      by (intros; eapply (Hm (S (List.length hs1))); eauto).
    induction m as [| m IH]; intros hs1 r B hs2 N T v Hlt Heq HN HT Hvv; [ lia |].
    destruct (Nat.eq_dec (List.length hs1) m) as [Hlm | Hne]; [| eapply IH; eauto; lia ].
    assert (Hh : List.length hs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
    pose proof HgA as [_ _ HA].
    destruct (HA _ _ _ _ _ _ HN HT Hvv (cargs_rev_nth_arg p D Mk _ _ _ _ _ Heq)) as [i' a1 P' El' Ha1 Hglu' HP' HM'].
    set (j := List.length (cargs_nonrec hs1)).
    assert (HBk : List.nth_error (cargs_nonrec gs) j = Some B)
      by (unfold j; rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    assert (Hpk : tele_prefix_rel (canon_args_rel D ups k ns c) j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws))
                    (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws)))
      by (eapply nonrec_prefix_pre; [ exact Hv | lia | exact Heq ]).
    destruct (HeA _ _ _ _ _ _ _ _ HMk Hns Hcon HBk Hpk) as [b Hb].
    pose proof (HAP _ _ _ _ _ _ _ _ _ HMk Hns Hcon HBk Hpk Hb) as Hgb.
    (** The two values of the argument's type. *)
    assert (Hrel : exists k0 : universe_index, Dom a1 ≈ b ∈ per_univ k0).
    { assert (HgA1 : glu_args Δ (cargs_ctx p D Mk hs1) (sb_of_list Id (Us ++ Ns)) (env_tele nil (List.rev (im_params D Mk)) (ups ++ ns))
                       (List.firstn (List.length hs1) As) (List.firstn (List.length hs1) ws)).
      { pose proof HgA as HgA'.
        rewrite (cargs_split_aux p D Mk gs hs1 (ca_arg r B) hs2 Heq), <- (List.firstn_skipn (List.length hs1) As),
          <- (List.firstn_skipn (List.length hs1) ws) in HgA'.
        apply glu_args_app in HgA'; [ exact (proj1 HgA') | apply cargs_ctx_aux_ass | |];
          rewrite List.length_firstn, length_cargs_ctx; lia. }
      assert (HgPA : glu_args Δ (cargs_ctx p D Mk hs1 ++ im_params D Mk) Id nil ((Us ++ Ns) ++ List.firstn (List.length hs1) As)
                       ((ups ++ ns) ++ List.firstn (List.length hs1) ws)).
      { destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP' LB'].
        apply glu_args_app; [ exact HassP | exact LP' | exact LB' |]; split; [ exact HgP | exact HgA1 ]. }
      pose proof (glu_args_per_tele_args _ _ _ _ _ _ ltac:(apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ])
                    HgPA) as Hgp.
      rewrite <- List.app_assoc in Hgp.
      destruct (valid_group_arg_types p D Hg Hcv k Mk c gs hs1 r B hs2 ups ns (List.firstn (List.length hs1) ws) HMk Hcon Heq Hu LNn
                  ltac:(rewrite List.length_firstn; lia) Hgp) as (i0 & R0 & a & a' & Ea & Ea' & HR0).
      rewrite (env_tele_cargs_prefix p D Mk gs hs1 (ca_arg r B) hs2 (ups ++ ns)) in Ha1
        by (first [ exact Heq | rewrite List.length_app; unfold im_np, ind_nu in *; lia | rewrite List.length_firstn; lia ]).
      rewrite <- List.app_assoc in Ha1.
      assert (a = a1) as -> by (eapply functional_eval_exp; eassumption).
      rewrite <- (cargs_nonrec_tele_firstn hs1 (ca_arg r B) hs2), <- Heq in Ea'.
      assert (Hlfw : List.length (List.firstn (List.length hs1) ws) = List.length hs1) by (rewrite List.length_firstn; lia).
      pose proof (length_nonrec_arg_vals _ _ Hlfw) as Hlnv1.
      assert (Hlk1 : List.length (cargs_nonrec hs1) <= List.length (cargs_nonrec_tele gs))
        by (rewrite length_cargs_nonrec_tele, Heq, cargs_nonrec_app, List.length_app; lia).
      rewrite components_env_app_firstn_ge in Ea';
        [| rewrite ?List.length_rev, ?length_im_nparams; lia .. ].
      assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
      exists (ul i0); eexists; exact HR0. }
    destruct Hrel as [k0 Hrel].
    assert (HTP : Δ ⊢ T ® AP k ns c j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws))).
    { eapply (HCA k Mk c gs hs1 r B hs2 Ns ns As (List.firstn (List.length hs1) ws) T HMk Hcon Heq Hnp Hns);
        [ rewrite List.length_firstn; lia | exact HT | | exact Hpk ].
      intros hs1' rB' B' hs2' N' T' v' Heq1 HN' HT' Hv'.
      assert (Hlt' : List.length hs1' < List.length hs1) by (rewrite Heq1, List.length_app; cbn; lia).
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1') (List.length hs1)); [| discriminate ].
      eapply (IH hs1' rB' B' (hs2' ++ ca_arg r B :: hs2));
        [ lia | rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ]. }
    eapply glu_univ_elem_exp_conv_universe_index; [ exact Hrel | exact Hglu' | exact Hgb | exact HM' | exact HTP ].
  Qed.

  (** The parameters of the type of a recursive argument, at an instance
      [Us ++ Ys] of the context of its shape glued to [ups ++ ns ++ nv ++ ys],
      are glued at the non-uniform parameters' telescope of the member the
      shape ends in, to their values. *)
  Lemma rec_params_args : forall Δ gs1 t gs2 Mj τ Us Ys ns nv ys SbC bsr, gs = gs1 ++ ca_rec t :: gs2 ->
      ind_member D (ptyp_mem t) = Some Mj ->
      List.length Us = ind_nu D -> List.length Ys = ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk ->
      List.length ns = im_nn Mk -> List.length nv = List.length (cargs_nonrec gs1) -> List.length ys = ptyp_depth t ->
      EG ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk ∈ glu_ctx_env ↘ SbC ->
      Δ ⊢ˢ sb_of_list τ (Us ++ Ys)
        ® components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv ++ ys) ∈ SbC ->
      ⟦ ptyp_ps t ⟧* gc_deps ⍮ gc_stack ⍮
        components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv ++ ys) ↘ bsr ->
      per_tele_args (List.rev (im_nparams Mj)) (decl_env D ups) (decl_env D ups) bsr bsr ->
      glu_args Δ (im_nparams Mj) (sb_of_list Id Us) (decl_env D ups)
        (List.map (fun P => P[sb_of_list τ (Us ++ Ys)]) (ptyp_ps t)) bsr.
  Proof.
    intros Δ gs1 t gs2 Mj τ Us Ys ns nv ys SbC bsr Heq HMj HUl HYl Hnsl Hnvl Hysl HSbC Hσ Hbsr Hgb.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (L := ptyp_depth t + K + im_nn Mk) in *.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (ρ := components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv ++ ys)) in *.
    destruct (length_rec_ps D HD k Mk HMk c gs gs1 t gs2 Hcon Heq) as (Mj' & HMj' & HPl).
    rewrite HMj in HMj'; injection HMj' as <-.
    pose proof (eval_exps_length _ _ _ Hbsr) as Hbl.
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (HwkE : ⟪wk_shiftn L⟫ ρ = decl_env D ups).
    { unfold ρ, L; replace (ptyp_depth t + K + im_nn Mk) with (List.length (ns ++ nv ++ ys)) by (rewrite !List.length_app; lia).
      apply Completeness.Inductives.Decl.eval_wk_shiftn_components_env. }
    constructor; [ rewrite List.length_map, length_im_nparams; exact HPl | rewrite length_im_nparams; lia |].
    intros m M T v κ A HM HT Hv HA.
    rewrite List.nth_error_map in HM.
    destruct (List.nth_error (ptyp_ps t) m) as [P |] eqn:HP; [ injection HM as <- | discriminate ].
    assert (Hm : m < im_nn Mj) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) (ptyp_ps t)) m) as [Tk HTk].
    { rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMj); rewrite length_im_nparams; lia. }
    pose proof (rec_tele_inst D (ptyp_mem t) Mj (ptyp_ps t) L τ Us Ys m Tk Hc HMj HUl HYl HTk) as HT'.
    fold σ in HT'; rewrite HT in HT'; injection HT' as ->.
    destruct (tele_insts_nth _ _ _ _ _ HTk) as (κ0 & A0 & HA0 & ETk).
    rewrite HA in HA0; injection HA0 as <- <-.
    destruct (glu_ind_decl_rec_field _ HG _ _ _ _ _ _ _ _ _ _ _ HMk Hcon Heq HMj HP HTk) as [SbC' HSbC' j HV].
    pose proof (functional_glu_ctx_env HSbC HSbC') as ESb.
    assert (Hσ' : Δ ⊢ˢ σ ® ρ ∈ SbC') by (apply ESb; exact Hσ).
    destruct (HV _ _ _ Hσ') as [a1 m1 P1 El1 Ha1 Hm1 Hg1 HM1].
    destruct (eval_exps_nth _ _ _ _ _ Hbsr HP) as (v' & Hv' & Ev').
    rewrite Hv in Hv'; injection Hv' as <-.
    (** The value of the type of the parameter, at the arguments' values, is
        related to the one at the parameters' before it. *)
    destruct (valid_ind_decl_nparams _ HD _ _ _ _ _ HMj HA) as (_ & j0 & HAv).
    assert (HΞ0 : ⊨ ptyp_tele t ++ nonrec_args_prefix gs K ++ im_params D Mk).
    { pose proof (valid_ind_decl_dctx _ HD _ _ _ _ _ _ _ (List.length (ptyp_doms t)) HMk Hcon Heq (le_n _)) as H.
      rewrite List.firstn_all in H; exact H. }
    destruct (rel_ctx_wf_per_ctx_env HΞ0) as [R0 HR0].
    pose proof (glu_ctx_env_per_env HSbC' HR0 Hσ') as HE.
    pose proof (rec_sub_valid D HD Hc k Mk c gs HMk Hcon gs1 t gs2 Mj Heq HMj m (Nat.lt_le_incl _ _ Hm)) as Hτ.
    (** The parameter's type is relevant, so the parameter's value is its
        evaluation. *)
    destruct (Completeness.LetCases.rel_exp_of_typ_sub_relevant HR0 Hτ HAv _ _ HE) as (a0 & Ea0 & Hk0).
    fold K L in Ea0; rewrite <- ETk in Ea0.
    assert (a0 = a1) as -> by (eapply functional_eval_exp; eassumption).
    rewrite Hk0 in Hm1; cbn [glu_term_value] in Hm1.
    assert (m1 = v) as -> by (eapply functional_eval_exp; eassumption).
    (** The values of [τ]: the parameters' environment extended by the
        parameters before, related at their telescope. *)
    set (τm := sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps t))).
    set (Eτ := components_env D ups (List.firstn m (List.rev (im_nparams Mj))) (List.firstn m bsr)).
    assert (HWm : ⊨ nparams_prefix Mj m ++ ind_uparams D).
    { pose proof (valid_ind_decl_params _ HD _ _ HMj) as HPm; unfold im_params in HPm.
      rewrite <- (List.rev_involutive (im_nparams Mj)), <- (List.firstn_skipn m (List.rev (im_nparams Mj))),
        List.rev_app_distr, <- List.app_assoc in HPm.
      exact (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HPm). }
    destruct (rel_ctx_wf_per_ctx_env HWm) as [Rm HRm].
    assert (Hlfb : List.length (List.firstn m bsr) = m) by (rewrite List.length_firstn; lia).
    assert (HEτ : Rm Eτ Eτ).
    { assert (Hgm : per_tele_args (List.rev (nparams_prefix Mj m ++ ind_uparams D)) nil nil
                      (ups ++ List.firstn m bsr) (ups ++ List.firstn m bsr)).
      { unfold nparams_prefix; rewrite List.rev_app_distr, List.rev_involutive.
        apply Decl.per_tele_args_app_intro; [ rewrite List.length_rev; exact Hu | exact Hgu |].
        assert (Hl1 : List.length (List.firstn m bsr) = List.length (List.firstn m (List.rev (im_nparams Mj))))
          by (rewrite Hlfb, List.length_firstn, List.length_rev, length_im_nparams; lia).
        pose proof Hgb as Hgb'.
        rewrite <- (List.firstn_skipn m (List.rev (im_nparams Mj))), <- (List.firstn_skipn m bsr) in Hgb'.
        destruct (Decl.per_tele_args_app (List.firstn m (List.rev (im_nparams Mj))) (List.skipn m (List.rev (im_nparams Mj)))
                    (decl_env D ups) (decl_env D ups) (List.firstn m bsr) (List.firstn m bsr) (List.skipn m bsr) (List.skipn m bsr)
                    Hl1 Hgb' Hl1) as [Hgpre _].
        exact Hgpre. }
      assert (Hlm : List.length (ups ++ List.firstn m bsr) = List.length (nparams_prefix Mj m ++ ind_uparams D))
        by (unfold nparams_prefix; rewrite !List.length_app, !List.length_rev, !List.length_firstn, !List.length_rev,
              length_im_nparams; unfold ind_nu in Hu; lia).
      pose proof (tele_args_env_rel (nparams_prefix Mj m ++ ind_uparams D) Rm (ups ++ List.firstn m bsr) (ups ++ List.firstn m bsr)
                    nil nil HRm HWm Hlm Hgm) as H.
      rewrite (Completeness.Inductives.Decl.env_tele_uparams D _ _ _ Hu) in H.
      unfold nparams_prefix in H; rewrite List.rev_involutive in H; exact H. }
    assert (Hτev : ⟦ τm : nparams_prefix Mj m ++ ind_uparams D ⟧s ρ ↘ Eτ).
    { assert (Hlτ : List.length (List.firstn m (List.rev (im_nparams Mj))) = List.length (List.firstn m (ptyp_ps t)))
        by (rewrite !List.length_firstn, List.length_rev, length_im_nparams; lia).
      assert (HX : Completeness.Inductives.Decl.env_extend_tagged (ind_uparams D) (List.firstn m (List.rev (im_nparams Mj)))
                     (ctx_retag (ind_uparams D) (⟪wk_shiftn L⟫ ρ)) (List.firstn m bsr) = Eτ).
      { rewrite HwkE; apply Completeness.Inductives.Decl.env_extend_tagged_decl_env; [ exact Hu |].
        rewrite Hlfb, List.length_firstn, List.length_rev, length_im_nparams; lia. }
      rewrite <- HX; unfold τm, nparams_prefix.
      apply Completeness.Inductives.Decl.eval_sb_of_list;
        [ apply eval_sub_of_wk, Completeness.UnitCases.wk_mono_shiftn | apply eval_exps_firstn; exact Hbsr | exact Hlτ |].
      rewrite HX; intros x Hx Hpx.
      apply (evaluated_entries_not_propositional (nparams_prefix Mj m) (ind_uparams D) Rm
               ltac:(unfold nparams_prefix; apply List.Forall_rev, Forall_firstn', List.Forall_rev;
                     exact (decl_closed_nparams_ass D Hc _ _ HMj))
               (nparams_prefix_evaluated _ HD _ _ m HMj) HRm _ _ HEτ x); [| exact Hpx ].
      unfold nparams_prefix; rewrite List.length_rev; exact Hx. }
    destruct (Completeness.LogicalRelation.Telescope.typ_inst_link _ _ _ _ _ _ _ _ _ (rel_type_of_typ HAv) HR0 Hτ HE Hτev)
      as (a & b & Ea & Eb & Hab).
    fold K L in Ea; rewrite <- ETk in Ea.
    assert (a = a1) as -> by (eapply functional_eval_exp; eassumption).
    unfold Eτ in Eb; rewrite components_env_firstn_ge in Eb by lia.
    destruct (glu_transfer_per j j0 a1 b P1 El1 Δ _ _ v Hg1 Hab ltac:(eapply glu_univ_elem_trm_typ; eassumption) HM1)
      as (k' & P' & El' & Hg' & HT' & HM').
    exact (mk_glu_arg _ _ _ _ _ _ k' b P' El' Eb Hg' HT' HM').
  Qed.

  (** Parameters related canonically read back alike. *)
  Lemma canon_params_per_top : forall j Mj bs bs', ind_member D j = Some Mj ->
      tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs' ->
      per_top_ps (List.rev (im_params D Mj)) (ups ++ bs) (ups ++ bs').
  Proof.
    intros * HMj Hbs s.
    destruct (Decl.per_tele_args_top _ _ _ _ _ Hgu ltac:(rewrite List.length_rev; exact Hu) s) as (Ms1 & Ms1' & HM1 & HM1' & HE1).
    pose proof (canon_hn D HD Hc Hsu ups bu Hu Hbu ups Hgu) as Hn.
    assert (Hassn : all_assumptions (List.rev (im_nparams Mj))) by (apply List.Forall_rev; exact (group_structure_nparams _ Hass _ _ HMj)).
    destruct (read_ps_tele (List.rev (im_nparams Mj)) (canon_nparams_rel D ups j) (decl_env D ups) (decl_env D ups) Hassn
                ltac:(intros j0 κ0 A pre pre' Hj0 Hp;
                      destruct (canon_nparams_evals _ _ _ _ Hn _ _ _ _ _ _ _ HMj Hj0 Hp) as [a a' Ea Ea' HRa];
                      exists a, a'; split; [ exact Ea | split; [ exact Ea' | intros b b' Hb; exact (per_elem_then_per_top HRa Hb) ] ])
                _ _ Hbs s) as (Ms2 & Ms2' & HM2 & HM2' & HE2).
    apply (mk_params_read_alike _ _ _ _ (Ms1 ++ Ms2)%list (Ms1' ++ Ms2')%list); rewrite ?rev_im_params_split;
      [ apply read_ps_app; assumption | apply read_ps_app; assumption | apply nfs_eq_upto_proofs_app; assumption ].
  Qed.

  (** A recursive argument ending in a declared member [j]: glued at a type
      of the value of the type of [j] at parameters glued to related values,
      an element of [j] at every weakening and every instance of the
      parameters equal to them. *)
  Lemma rec_end_decl : forall j Mj pm Δ Us Q W N v (i : universe_index) P El bs bs1, ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      ⊢ Δ -> tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs1 ->
      DG d_ind p j (ups ++ bs1) ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ N : W ® v ∈ El ->
      glu_args Δ (im_params D Mj) Id nil (Us ++ Q) (ups ++ bs) -> List.length Us = ind_nu D ->
      forall Δ' φ Us' Q', Δ' ⊢ᵏ φ : Δ -> List.length Us' = ind_nu D ->
        exps_eq_at Δ' (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
        ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' Q' N[φ]ʷ v.
  Proof.
    intros * HMj Hh HΔ Hbs Hgl0 HN0 HQp HUl Δ' φ Us' Q' Hφ HUl' HE.
    (** At a universe above the clause's. *)
    set (n := ul (Nat.max (large_level i) (large_level u))).
    assert (Hin : universe_index_le i n) by (apply universe_index_le_ul_max; unfold n; lia).
    assert (Hun : universe_index_le u n) by (apply universe_index_le_ul_max; unfold n; lia).
    destruct (glu_univ_elem_cumu_ge_universe_index Hin Hgl0) as (Pn & Eln & Hgl).
    pose proof (glu_univ_elem_typ_cumu_ge_universe_index Hin Hgl0 Hgl (glu_univ_elem_trm_typ _ _ _ _ Hgl0 _ _ _ _ HN0)) as HWP.
    pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hin Hgl0 Hgl HN0) as HNW.
    clear Hgl0 HN0.
    pose proof con_canon as Hcp.
    assert (Hlt : j < ind_ndecl D) by (eapply decl_member_lt; eassumption).
    pose proof (decl_closed_params_ass D j Mj Hc HMj) as HassP.
    pose proof (decl_closed_params D j Mj Hc HMj) as Hs.
    assert (Hbb : tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs)
      by exact (canon_nparams_rel_trans p D ups Hass Hcp _ _ _ _ _ HMj Hbs (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hbs)).
    pose proof (ind_relate D HD Hc Hsu p Hl Hass j Mj pm ups ups bs bs bu HMj Hh Hgu Hu Hbu Hbb) as HRq0.
    pose proof (per_univ_elem_cumu_universe_index _ _ _ _ HRq0 _ Hule) as HRq.
    destruct (ind_glu_of_per p D Hl u _ j Mj pm ups bs HMj Hh HRq Hu)
      as [NP2 NEl2 AP2 AEl2 DP2 DEl2 P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf2].
    assert (HT2 : Δ ⊢ im_ty_at p j Mj Us Q ® P2).
    { apply HP2; exists (Us ++ Q).
      unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
      exact (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Hass j Mj Δ (Us ++ Q) ups bs bu u NP2 NEl2 AP2 AEl2 DP2 DEl2 HMj Hlt HΔ HQp
               Hu Hbu Hule Hf2). }
    pose proof (ind_relate D HD Hc Hsu p Hl Hass j Mj pm ups ups bs1 bs bu HMj Hh Hgu Hu Hbu
                  (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hbs)) as Hab.
    (** The element's type is the member's at the parameters. *)
    assert (Hbn : universe_index_le (Completeness.Inductives.Decl.univ_idx bu) n) by (eapply universe_index_le_trans; [ exact Hule | exact Hun ]).
    pose proof (glu_typ_transfer u n _ _ _ _ _ _ _ Δ _ Hun Hbn (per_univ_sym' _ _ _ (per_univ_of_elem _ _ _ _ Hab)) Hg2 Hgl HT2) as HTn.
    pose proof (glu_univ_elem_typ_unique_upto_exp_eq' Hgl ltac:(discriminate) HWP HTn) as HWT.
    pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgl _ _ _ _ _ HNW HWT) as HN.
    pose proof (glu_univ_elem_exp_conv_universe_index (per_univ_of_elem _ _ _ _ Hab) Hgl Hg2 HN HT2) as HM2.
    apply HEl2 in HM2; destruct HM2 as [_ _ Ps2 HPs2 Hk2].
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    pose proof (glu_args_params_top _ _ _ _ _ HassP Hs (glu_args_wk _ _ _ _ _ _ _ HassP Hs Hφ HQp)) as Ht.
    destruct (proj2 HPs2 _ _ Hφ) as (HPt2 & _ & _).
    pose proof (glu_params_top_eq p D j Mj Δ' _ _ _ Hl HMj HΔ' (ind_rps_of_per _ _ _ _ _ _ _ _ HRq Hl HMj _) HPt2 Ht) as Heqq.
    assert (Heqq' : exps_eq_at Δ' (im_params D Mj) (List.map (fun P => P[φ]ʷ) Ps2) (Us' ++ Q')).
    { destruct Heqq as [HlE1 HE1]; destruct HE as [HlE2 HE2]; split; [ rewrite ?List.length_map in *; lia |].
      destruct HPt2 as [HPl2 _ _]; destruct Ht as [HQl2 _ _].
      eapply (params_eq_trans _ p D j Mj _ _ _ Hl HMj HΔ' HPl2 HQl2); [ rewrite ?List.length_map in *; lia | exact HE1 | exact HE2 ]. }
    pose proof (Hk2 Δ' φ (Us' ++ Q') Hφ Heqq') as Hgi.
    rewrite firstn_app_exact, skipn_app_exact in Hgi by exact HUl'.
    eapply (ind_glu_elem_mono p D ups NEl2 AEl2 DP2 DEl2 Hass Hcp); [ | | | exact Hgi ].
    - intros m0 Mm0 k0 vs HM0 Hk' Hp0 Γ0 A0 M0 m1 HN0.
      destruct (nparams_lt_ass D m0 Mm0 k0 Hass HM0 ltac:(rewrite List.length_rev, length_im_nparams; exact Hk')) as (κS & S & HS).
      destruct (HeN _ _ _ _ _ _ HM0 HS Hp0) as [b Eb].
      destruct (functional_glu_univ_elem _ _ _ _ _ _ (ind_fams_glu_nparams_glu _ _ _ _ _ _ _ _ _ Hf2 _ _ _ _ _ _ _ HM0 HS Hp0 Eb)
                  (HNP _ _ _ _ _ _ _ HM0 HS Hp0 Eb)) as [_ EE].
      apply EE; exact HN0.
    - intros m0 Mm0 ms c0 gs0 k0 vs HM0 Hm Hc0 Hk' Hp0 Γ0 A0 M0 m1 HN0.
      destruct (nth_error_lt_some' _ _ Hk') as [S HS].
      destruct (HeA _ _ _ _ _ _ _ _ HM0 Hm Hc0 HS Hp0) as [b Eb].
      destruct (functional_glu_univ_elem _ _ _ _ _ _ (ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf2 _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 HS Hp0 Eb)
                  (HAP _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 HS Hp0 Eb)) as [_ EE].
      apply EE; exact HN0.
    - intros m0 Mm0 ms c0 gs0 gs3 t0 gs4 ws k0 B ys0 HM0 Hm Hc0 Heq0 Hw HB Hy1 Ts.
      destruct (HeD _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 Heq0 Hw HB Hy1) as [b Eb].
      destruct (functional_glu_univ_elem _ _ _ _ _ _ (ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf2 _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 Heq0 Hw HB Hy1 Eb)
                  (HDP _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 Heq0 Hw HB Hy1 Eb)) as [EP EE].
      split; intros; [ apply EP | apply EE ]; assumption.
  Qed.

  (** A recursive argument of a constructor, after [kk] of its shape's
      domains: an element of the value of the type of the rest of the shape,
      glued at any type of it, at a glued instance [σ] of the shape's
      context on the side of the non-recursive arguments, is a recursive
      argument of the rest of the shape. *)
  Lemma con_rec_glu : forall gs1 t gs2 ns fa, gs = gs1 ++ ca_rec t :: gs2 ->
      List.length ns = im_nn Mk -> List.length fa = List.length gs1 ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa) ->
      per_tele_args (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa) ->
      glu_end_at p D ups NEl AEl DP DEl (ptyp_mem t) ->
      forall t' kk ys Δ τ Us Ys SbC W N v a (i : universe_index) P El,
        ptyp_skip kk t = t' -> kk <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns
                           (nonrec_arg_vals gs1 fa) t) kk ys ys ->
        per_tele_args (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
          (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
          (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa)) ys ys ->
        ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
        List.length Ys = kk + List.length (cargs_nonrec gs1) + im_nn Mk ->
        EG doms_ctx (List.firstn kk (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
          ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list τ (Us ++ Ys)
          ® components_env D ups
              (List.rev (doms_ctx (List.firstn kk (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mk))
              (ns ++ nonrec_arg_vals gs1 fa ++ ys) ∈ SbC ->
        ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) t' ⟧
          env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
            (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)))) ys ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ N : W ® v ∈ El ->
        glu_rec p D ups NEl AEl DP DEl k Δ Us (ns ++ nonrec_arg_vals gs1 fa ++ ys)
          (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t)) t'
          (ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) t') N v.
  Proof.
    intros gs1 t gs2 ns fa Heq Hlns Hlfa Hnsd Hp Hgall0 [Hvt Hrvt].
    pose proof con_canon as Hcp.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    destruct (valid_group_cargs_sem_all p D Hg Hcv k Mk c gs HMk Hcon gs1 (ca_rec t :: gs2) Heq) as [HC1 Hw1].
    assert (HassC1 : all_assumptions (cargs_ctx p D Mk gs1 ++ im_params D Mk))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    assert (HlC1 : List.length (ups ++ ns ++ fa) = List.length (cargs_ctx p D Mk gs1 ++ im_params D Mk))
      by (rewrite !List.length_app, length_cargs_ctx, length_im_params, Hu, Hlns, Hlfa; unfold im_np, ind_nu in *; lia).
    (** The arguments before, related at their context. *)
    assert (INV : forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
              R (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
                (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa)))
      by (intros R HR; exact (tele_args_env_rel _ _ _ _ _ _ HR HC1 HlC1 Hgall0)).
    pose proof (Completeness.Inductives.ViewArgs.view_end_rel_all VP p D HVP HPD ups ups Hgu Hu (ptyp_mem t)) as Hend.
    pose proof (Completeness.Inductives.ViewArgs.rview_end_rel_all VP p D HVP HPD ups ups Hgu Hu (ptyp_mem t)) as Hrend.
    set (nv := nonrec_arg_vals gs1 fa) in *.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (pat := cargs_pat gs1) in *.
    assert (Hlnv : List.length nv = K) by (apply length_nonrec_arg_vals; exact Hlfa).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (Hgall : forall kk ys, List.length ys = kk ->
               per_tele_args (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t))))
                 (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa)) (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa)) ys ys ->
               per_tele_args (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)) nil nil
                 (ups ++ ns ++ fa ++ ys) (ups ++ ns ++ fa ++ ys)).
    { intros kk ys Hly Hgy.
      rewrite List.rev_app_distr.
      replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      apply Decl.per_tele_args_app_intro; [| exact Hgall0 | exact Hgy ].
      rewrite List.length_rev; exact HlC1. }
    (** The environment of the arguments and the first domains, closed. *)
    assert (HEcl : forall kk ys,
               env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
                 (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys
               = env_tele nil (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
                   (ups ++ ns ++ fa ++ ys)).
    { intros kk ys.
      replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (Completeness.Inductives.Decl.env_tele_closed_app (cargs_ctx p D Mk gs1 ++ im_params D Mk) _ (ups ++ ns ++ fa) ys)
        by exact HlC1; reflexivity. }
    induction t' as [j0 Ps0 | B t'' IH];
      intros kk ys Δ τ Us Ys SbC W N v a i P El Hsk Hk Hy Hgy HΔ HUs HYl HSbC Hσ Ea Hgl HN.
    2:{ (** A domain: an element of the domain's gluing, moved to the gluing
            of the [Π]'s domain, applied to the argument gives a recursive
            argument of the rest of the shape. *)
        destruct (Tele.ptyp_skip_pi _ _ _ _ Hsk) as [HB Hs'].
        assert (Hkl : kk < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
        assert (HUl : List.length Us = ind_nu D) by (destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _]; exact LU).
        (** The rest of the shape's type is glued at the domains' gluings. *)
        pose proof (shape_typ_glu p D HG Hc Hdt Hsu ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf k Mk c gs gs1 t gs2 ns nv
                      HMk Hcon Heq Hnsd Hp Hlns Hlnv (pt_pi B t'') kk ys Δ τ Us Ys SbC Hsk Hk Hy HΔ HUl HYl HSbC Hσ) as Hsh.
        cbn [ptyp_ty ptyp_ty_at exp_sub glu_shape_typ] in Ea, Hsh |- *.
        destruct (Hsh _ _ eq_refl) as [HshD _].
        destruct (valid_group_dom_types p D Hg Hcv k Mk c gs gs1 t gs2 kk B ups ns fa ys HMk Hcon Heq HB Hu Hlns Hlfa Hly (Hgall kk ys Hly Hgy))
          as (jd & Rab & a1 & b0 & Ea1 & Eb0 & HRab).
        rewrite <- HEcl in Ea1.
        inversion Ea; subst a.
        match goal with H : ⟦ B[wk_pat _]ʷ ⟧ _ ↘ ?x |- _ => assert (x = a1) as -> by (eapply functional_eval_exp; eassumption) end.
        set (σ := sb_of_list τ (Us ++ Ys)) in *.
        set (E0 := env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa)) in *.
        set (Et := env_tele E0 (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys) in *.
        set (pat' := List.repeat false kk ++ pat) in *.
        set (Ts := List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t)) in *.
        (** The components at the first domains are those at all of them. *)
        assert (Ec_eq : components_env D ups Ts (ns ++ nv ++ ys)
                        = components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv ++ ys)).
        { unfold Ts; rewrite !List.app_assoc; apply components_env_app_firstn_ge;
            unfold shape_doms_tele; rewrite ?List.length_app, ?List.length_rev, ?length_im_nparams, ?length_cargs_nonrec_tele,
              ?List.length_map; fold K; lia. }
        (** The context of the arguments and the first domains, and its
            environment. *)
        set (Γk := shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk).
        pose proof (shape_domains_ctx_sem_gen D p k Mk c gs HD HMk Hcon gs1 t gs2 Heq HC1 Hw1 kk Hk) as HWk; fold pat Γk in HWk.
        pose proof (shape_domains_ctx_wk_gen D p k Mk c gs HD HMk Hcon gs1 t gs2 Heq Hw1 kk Hk) as Hwk; fold pat pat' Γk in Hwk.
        destruct (rel_ctx_wf_per_ctx_env HWk) as [RΓ HΓ].
        assert (HlEt : List.length (ups ++ ns ++ fa ++ ys) = List.length Γk).
        { unfold Γk; rewrite !List.length_app, length_shape_domains_ctx, List.length_firstn, length_cargs_ctx, length_im_params.
          rewrite Hu, Hlns, Hlfa; unfold im_np, ind_nu in *; lia. }
        assert (Hρ : RΓ Et Et).
        { unfold Et, E0; rewrite HEcl.
          exact (tele_args_env_rel _ _ _ _ _ _ HΓ HWk HlEt (Hgall kk ys Hly Hgy)). }
        destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HMk Hcon Heq HB) as (_ & jB & HBv).
        rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
        pose proof (rel_exp_under_ctx_wk Hwk HBv) as HBw; cbn [exp_wk] in HBw.
        pose proof (Completeness.LogicalRelation.Substitution.per_ctx_env_of_typ (κ := ak_relevant) HΓ (rel_type_of_typ HBw)) as HΓB.
        (** A level above the ones at hand. *)
        set (n := ul (Nat.max (large_level i) (Nat.max (large_level u) jd))).
        assert (Hin : universe_index_le i n) by (apply universe_index_le_ul_max; unfold n; lia).
        assert (Hun : universe_index_le u n) by (apply universe_index_le_ul_max; unfold n; lia).
        assert (Hjn : universe_index_le (ul jd) n) by (apply universe_index_le_ul_max; unfold n; cbn; lia).
        destruct (glu_univ_elem_cumu_ge_universe_index Hin Hgl) as (Pn & Eln & Hgn).
        pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hin Hgl Hgn HN) as HNn.
        pose proof (per_univ_trans _ _ _ _ _ _ HRab (per_univ_sym _ _ _ _ HRab)) as HRaa.
        pose proof (per_univ_elem_cumu_universe_index _ _ _ _ HRaa _ Hjn) as HRaan.
        destruct (glu_univ_elem_pi_clean_inversion1 HRaan ltac:(constructor) Hgn)
          as (IP & IEl & OP & OEl & elem_rel & HgI & HgO & Hper & EP & EEl).
        apply EEl in HNn.
        inversion_clear HNn as [? ? ? ? IT2 OT2 HMt Hm HAeq HITt HOTt HIP HApp].
        pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hnsd Hcon Heq Hp HB Hy Eb0) as Hgb0.
        (** An argument glued at the domain's gluing, at the [Π]'s domain. *)
        assert (Hdom : forall Δ' φ b c', Δ' ⊢ᵏ φ : Δ -> canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B c' c' ->
                  Δ' ⊢ b : B[σ][φ]ʷ ® c' ∈ DEl k (ns ++ nv ++ ys) Ts B ->
                  Rab c' c' /\ Δ' ⊢ B[σ][φ]ʷ ® IP /\ Δ' ⊢ b : B[σ][φ]ʷ ® c' ∈ IEl /\ Δ' ⊢ b : IT2[φ]ʷ ® c' ∈ IEl).
        { intros Δ' φ b c' Hφ Hc' Hb.
          unfold canon_doms_rel in Hc'; rewrite Ec_eq in Hc'.
          pose proof (dr_to_rel B _ b0 a1 c' (ul jd) Rab (ul jd) Eb0 (per_univ_of_elem _ _ _ _ HRab) HRaa Hc') as Hcc.
          pose proof (glu_typ_transfer u n (ul jd) b0 a1 _ _ IP IEl Δ' _ Hun Hjn (per_univ_sym' _ _ _ (per_univ_of_elem _ _ _ _ HRab))
                        Hgb0 HgI (HshD _ _ Hφ)) as HTyI.
          pose proof (glu_univ_elem_exp_conv_universe_index (per_univ_sym' _ _ _ (per_univ_of_elem _ _ _ _ HRab)) Hgb0 HgI Hb HTyI) as HbI.
          split; [ exact Hcc | split; [ exact HTyI | split; [ exact HbI |] ] ].
          exact (glu_elem_retype n n a1 IP IEl IP IEl Δ' _ _ b c' HgI HgI HTyI HbI (HIP _ _ Hφ)). }
        apply glu_rec_pi.
        + intros IT OT HA0 Δ' φ Hφ; injection HA0 as <- <-; exact (HshD Δ' φ Hφ).
        + intros IT OT HA0 Δ' φ b c' Hφ Hc' Hb; injection HA0 as <- <-.
          destruct (Hdom _ _ _ _ Hφ Hc' Hb) as (Hcc & _ & _ & HbI).
          destruct (HApp Δ' φ b c' Hφ HbI Hcc) as (mn & Hmn & _); exists mn; exact Hmn.
        + intros IT OT HA0 Δ' φ b c' fc Hφ Hc' Hb Hfc; injection HA0 as <- <-.
          destruct (Hdom _ _ _ _ Hφ Hc' Hb) as (Hcc & HTyI & HbI0 & HbI).
          destruct (HApp Δ' φ b c' Hφ HbI Hcc) as (mn & Hmn & Happ).
          assert (mn = fc) as <- by (eapply functional_eval_app; eassumption).
          assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
          (** The substitutions after the argument. *)
          destruct (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ (S kk) HMk Hcon Heq ltac:(lia)) as [SbC' HSbC'].
          pose proof (HshD _ _ Hφ) as HTy0.
          fold nv in Eb0; rewrite <- Ec_eq in Eb0.
          pose proof (shape_sub_step D ups u Hu k Mk c gs gs1 t gs2 kk B ns nv ys Δ τ Us Ys SbC SbC' Δ' φ b b0 c' _ _
                        HMk Hcon Heq HB
                        ltac:(rewrite !List.length_app, doms_ctx_length, List.length_firstn, length_nonrec_args_prefix,
                                length_im_nparams by exact HK; lia)
                        HSbC HSbC' Hσ Hφ
                        ltac:(erewrite shape_env_eq by (first [ exact Heq | exact Hu | exact Hlns | exact Hlnv | lia ]);
                              rewrite <- Ec_eq; exact Eb0)
                        Hgb0 HTy0 Hb) as Hσ'.
          (** The rest of the type at the argument: at the closure's
              extension and at the telescope's, related types. *)
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
          assert (Htag : per_env_extend B[wk_pat pat']ʷ B[wk_pat pat']ʷ RΓ (Et ↦ c' ⦂ entry_type_value a1)
                           (Et ↦ c' ⦂ entry_type_closure B[wk_pat pat']ʷ Et)).
          { pose proof (per_head_of Ea1 Ea1 HRaan Hcc) as Hh.
            destruct (per_head_closure_readable HΓB HΓ Hρ Hh) as [Rt _].
            pose proof (entry_readable_of_elem HRaan Hcc) as [Rv _].
            apply per_env_extend_intro'; [ exact Hρ | exact Hh | exact Rv |].
            assert (HlEt' : List.length Et = List.length Γk).
            { unfold Et, E0; rewrite HEcl, Completeness.Inductives.Decl.length_env_tele; cbn [List.length]; rewrite <- HlEt; lia. }
            unfold centry_tag in Rt; cbn [centry_type] in Rt.
            rewrite <- HlEt', Completeness.Inductives.Decl.env_upto_exact in Rt; exact Rt. }
          destruct (shape_prefix_valid p D Hg Hcv k Mk c gs HMk Hcon HΨs gs1 t gs2 Heq (S kk) ltac:(lia)) as [jT HT'].
          assert (HSk : shape_domains_ctx pat (List.firstn (S kk) (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
                        = Γk ▹{ak_relevant} B[wk_pat pat']ʷ)
            by (unfold Γk, pat'; rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia;
                reflexivity).
          fold pat in HT'; rewrite HSk, Hs' in HT'; cbn [List.repeat List.app] in HT'; fold pat' in HT'.
          destruct (rel_exp_of_typ_inversion_simple_at HΓB HT' _ _ Htag) as (b2 & b2' & Eb2 & Eb2' & Hbb').
          pose proof (HgO c' Hcc b2 Eb2) as HgOc.
          (** At a level above the type's. *)
          set (n2 := ul (Nat.max (large_level n) jT)).
          assert (Hn2 : universe_index_le n n2) by (apply universe_index_le_ul_max; unfold n2; lia).
          assert (HjT2 : universe_index_le (ul jT) n2) by (apply universe_index_le_ul_max; unfold n2; cbn; lia).
          assert (Hb2' : Dom b2' ≈ b2' ∈ per_univ n2).
          { destruct Hbb' as [Rb HRb].
            pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRb) HRb) as HRb'.
            eexists; eapply per_univ_elem_cumu_universe_index; [ exact HRb' | exact HjT2 ]. }
          destruct (per_univ_glu_univ_elem _ _ Hb2') as (P2 & El2 & Hg2).
          pose proof (glu_typ_transfer n n2 (ul jT) b2 b2' _ _ P2 El2 Δ' _ Hn2 HjT2 Hbb' HgOc Hg2
                        (glu_univ_elem_trm_typ _ _ _ _ HgOc _ _ _ _ Happ)) as HTy2.
          pose proof (glu_univ_elem_exp_conv_universe_index Hbb' HgOc Hg2 Happ HTy2) as Happ2.
          (** The telescope after one more domain. *)
          assert (Hsd : List.nth_error (shape_doms_tele t) kk = Some (ce_ass ak_relevant B))
            by (unfold shape_doms_tele; rewrite List.nth_error_map, HB; reflexivity).
          assert (HTs : Ts ++ ce_ass ak_relevant B :: nil
                        = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn (S kk) (shape_doms_tele t))
            by (unfold Ts; rewrite (firstn_S_snoc _ _ _ Hsd), <- !List.app_assoc; reflexivity).
          unfold σ; rewrite ptyp_ty_at_shape_step by assumption.
          replace ((ns ++ nv ++ ys) ++ c' :: nil) with (ns ++ nv ++ ys ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
          rewrite HTs.
          apply (IH (S kk) (ys ++ c' :: nil) Δ' (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us) (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil)
                   SbC' OT2[(ι φ),,b] (a_app N[φ]ʷ b) mn b2' n2 P2 El2);
            [ exact Hs' | lia | | | exact HΔ' | | rewrite List.length_app, List.length_map; cbn; lia | exact HSbC' | exact Hσ'
            | | exact Hg2 | exact Happ2 ].
          * apply tele_prefix_rel_snoc; [ exact Hy |].
            unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hc'.
          * rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
            cbn [List.rev].
            apply (Decl.per_tele_args_snoc _ _ _ _ _ _ _ _ _ jd Rab);
              [ rewrite List.length_rev, length_shape_domains_ctx, List.length_firstn; lia | exact Hgy | | exact Hcc ].
            fold E0 pat pat' Et.
            exact (mk_rel_mod_eval a1 a1 Ea1 Ea1 HRaa).
          * exact (glu_args_wk _ _ _ _ _ _ _ (group_structure_uparams _ Hass) (decl_closed_uparams _ Hc) Hφ HUs).
          * rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
            cbn [List.rev]; rewrite env_tele_snoc by (rewrite List.length_rev, length_shape_domains_ctx, List.length_firstn; lia).
            fold E0 pat pat' Et; cbn [List.repeat List.app]; fold pat'; exact Eb2'. }
    (** The end of the shape. *)
    destruct (ptyp_skip_self _ _ _ _ Hsk) as (HkL & <- & <-).
    assert (Hkd : kk = List.length (ptyp_doms t)) by lia.
    pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
    cbn [ptyp_ty ptyp_ty_at] in Ea |- *.
    destruct (length_rec_ps D HD k Mk HMk c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HPl).
    pose proof (Hgall kk ys Hly Hgy) as Hgall_end.
    rewrite Hkd, List.firstn_all in Hgall_end.
    pose proof Hy as Hy'; rewrite Hkd in Hy'.
    assert (HUl : List.length Us = ind_nu D) by (destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _]; exact LU).
    (** The environment of all the arguments and domains, as components. *)
    set (Z := shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk).
    assert (EZ : Z ++ ind_uparams D = shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)
      by (unfold Z, im_params; rewrite <- !List.app_assoc; reflexivity).
    assert (HZ : ⊨ Z ++ ind_uparams D).
    { rewrite EZ.
      pose proof (shape_domains_ctx_sem_gen D p k Mk c gs HD HMk Hcon gs1 t gs2 Heq HC1 Hw1 (List.length (ptyp_doms t)) (le_n _)) as H.
      rewrite List.firstn_all in H; exact H. }
    destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
    assert (HlZ : List.length (ns ++ fa ++ ys) = List.length Z)
      by (unfold Z; rewrite !List.length_app, length_shape_domains_ctx, length_cargs_ctx, length_im_nparams; lia).
    assert (EtZ : env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
                    (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys
                  = components_env D ups (List.rev Z) (ns ++ fa ++ ys)).
    { rewrite HEcl, Hkd, List.firstn_all, <- EZ.
      apply Completeness.Inductives.Con.env_tele_closed_components; exact Hu. }
    assert (HE : RZ (components_env D ups (List.rev Z) (ns ++ fa ++ ys)) (components_env D ups (List.rev Z) (ns ++ fa ++ ys))).
    { rewrite <- (Completeness.Inductives.Con.env_tele_closed_components D ups Z _ Hu).
      apply (tele_args_env_rel _ _ _ _ _ _ HRZ HZ); [ rewrite !List.length_app, <- HlZ, !List.length_app, Hu; unfold ind_nu; lia |].
      rewrite EZ; exact Hgall_end. }
    destruct (im_is_rview Mj) eqn:Hrv.
    { (** A record view: by its coherence with its record. *)
      unfold im_is_rview in Hrv; destruct (im_head Mj) as [ | | qr Is fl] eqn:Hh; try discriminate Hrv.
      pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as Hnp0.
      assert (HPs0 : ptyp_ps t = nil)
        by (destruct (ptyp_ps t); [ reflexivity | unfold im_nn in HPl; rewrite Hnp0 in HPl; discriminate HPl ]).
      destruct (valid_group_records _ _ Hg _ _ _ _ _ HMj Hh) as [R HR].
      destruct (eval_mty_inv_rview p D (ptyp_mem t) Mj qr Is fl _ _ _ _ HMj Hh Ea) as (cs & bs0 & Ecs & Ebs0 & Ea0).
      rewrite HPs0 in Ebs0; cbn [List.map] in Ebs0; inversion Ebs0; subst bs0; rewrite List.app_nil_r in Ea0; subst a.
      (** The instance's values at the group's uniform parameters. *)
      rewrite EtZ in Ecs.
      destruct (rview_pre_values p D Hg (ptyp_mem t) Mj qr Is fl R ups Z RZ (ns ++ fa ++ ys) (im_nn Mk)
                  (List.length (List.repeat false kk ++ pat)) cs HMj Hh HR Hu Hgu HZ HRZ HlZ
                  ltac:(unfold pat; rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia) HE Ecs)
        as (cups & Ecups & Hgc).
      (** The element's value is in the group's relation at the record view. *)
      destruct (glu_univ_elem_per_univ _ _ _ _ Hgl) as [Ra HRa].
      pose proof (glu_univ_elem_per_elem _ _ _ _ Hgl _ _ _ _ _ HN HRa) as Hva.
      assert (Ea' : ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ pat) (ptyp_skip kk t) ⟧
                      env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
                        (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys
                      ↘ d_record qr cs).
      { rewrite Hsk; cbn [ptyp_ty]; exact Ea. }
      pose proof (shape_char p D Hg Hcv k Mk c gs HMk Hcon HΨs gs1 t gs2 Heq ups ns fa Hu Hlns Hlfa Hgu Hnsd Hp INV Hend Hrend
                    0 kk ys _ _ _ ltac:(lia) Hy Hgy Ea' HRa) as ERa.
      apply ERa in Hva; rewrite Hsk in Hva.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hva) as (bs2 & bs3 & Ebs2 & Ebs3 & _ & _ & Hgv).
      rewrite HPs0 in Ebs2, Ebs3; inversion Ebs2; inversion Ebs3; subst bs2 bs3.
      assert (HQp : glu_args Δ (im_params D Mj) Id nil Us ups) by (unfold im_params; rewrite Hnp0; exact HUs).
      pose proof (decl_closed_params_ass D (ptyp_mem t) Mj Hc HMj) as HassPj.
      pose proof (decl_closed_params D (ptyp_mem t) Mj Hc HMj) as HsPj.
      (** The type's non-uniform parameters are none. *)
      assert (EQ : forall Q, ind_mty p D (ptyp_mem t) Us (List.map (fun P => P[sb_of_list τ (Us ++ Ys)]) (ptyp_ps t))
                             = im_ty_at p (ptyp_mem t) Mj Us Q -> Q = nil).
      { intros Q HQ; rewrite HPs0 in HQ; unfold ind_mty in HQ; rewrite HMj in HQ; unfold im_ty_at in HQ; rewrite Hh in HQ.
        apply apps_record_inj, List.app_inv_head in HQ; symmetry; exact HQ. }
      apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
      - intros bsr Q Hbsr HQ.
        rewrite HPs0 in Hbsr; inversion Hbsr; subst bsr.
        pose proof (EQ _ HQ) as ->.
        split; [ unfold im_nn; rewrite Hnp0; reflexivity | split; [ rewrite Hnp0; split; reflexivity + exact I |] ].
        intros bsr' Hb'.
        assert (bsr' = nil) as ->
          by (rewrite tele_rel_iff in Hb'; destruct Hb' as (_ & Hb' & _); rewrite Hnp0 in Hb';
              destruct bsr'; [ reflexivity | cbn in Hb'; lia ]).
        split; [ constructor; [ unfold im_nn; rewrite Hnp0; reflexivity | unfold im_nn; rewrite Hnp0; reflexivity
                              | intros [] ? ? ? _ _ Hn; discriminate Hn ] |].
        intros Δ0 φ Hφ; rewrite !List.app_nil_r.
        exact (glu_args_params_top _ _ _ _ _ HassPj HsPj (glu_args_wk _ _ _ _ _ _ _ HassPj HsPj Hφ HQp)).
      - intros bsr Q Hbsr HQ Δ' φ Us' Q' Hφ HUl' HQ'.
        pose proof (EQ _ HQ) as ->.
        rewrite List.app_nil_r in HQ'.
        assert (Q' = nil) as ->.
        { destruct HQ' as [HlQ _]; rewrite List.length_map, List.length_app in HlQ.
          destruct Q'; [ reflexivity | cbn in HlQ; lia ]. }
        rewrite List.app_nil_r in HQ'.
        exact (Hrvt Mj qr Is fl R cups cs Δ Us W N v i P El HMj Hh (valid_rview_record_lookup _ _ HR) Ecups Hgc Hgl HN Hgv HQp
                 Δ' φ Us' Hφ HUl' HQ'). }
    destruct (shape_end_params_link p D Hg k Mk c gs HMk Hcon HΨs gs1 t gs2 Heq ups ns fa ys Hu Hlns Hlfa Hgu Hnsd Hp Hgall_end Hy')
      as [bs bs1 Ebs Ebs1 Hrel].
    unfold nparams_tele_rel in Hrel; rewrite HMj in Hrel.
    destruct (eval_mty_inv p D (ptyp_mem t) Mj _ _ _ _ HMj Hrv Ea) as (cs & bs0 & Ecs & Ebs0 & ->).
    assert (Ebs1' : ⟦ List.map (fun P => P[wk_pat (List.repeat false kk ++ pat)]ʷ) (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮
                      env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
                        (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys ↘ bs1)
      by (rewrite HEcl, Hkd, List.firstn_all; exact Ebs1).
    pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs1') as ->.
    rewrite EtZ in Ecs.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (Qn := List.map (fun P => P[σ]) (ptyp_ps t)) in *.
    assert (HSbCt : EG ptyp_tele t ++ nonrec_args_prefix gs K ++ im_params D Mk ∈ glu_ctx_env ↘ SbC)
      by (rewrite Hkd, List.firstn_all in HSbC; exact HSbC).
    (** The parameters' values, related at their telescope. *)
    assert (Hly' : List.length ys = ptyp_depth t) by (unfold ptyp_depth; lia).
    pose proof (rec_prefix_tele_args D HD Hc Hsu k Mk HMk c gs gs1 t gs2 ups ups bu ns ns nv nv ys ys Hcon Heq Hgu Hu Hbu Hnsd Hp
                  (List.length (ptyp_doms t)) (le_n _) Hy') as Hgnr.
    rewrite List.firstn_all in Hgnr.
    pose proof (rec_closure D HD Hc k Mk HMk c gs gs1 t gs2 Mj Hcon Heq HMj ups ups ns ns nv nv ys ys
                  Hu Hlns Hlnv Hly' Hu Hlns Hlnv Hly' Hgnr) as Hrc; cbv zeta in Hrc.
    destruct Hrc as (bsa & bsb & Ebsa & Ebsb & Hgb & _).
    assert (bsa = bs) as -> by exact (functional_eval_exps' _ _ _ _ Ebsa Ebs).
    assert (bsb = bs) as -> by exact (functional_eval_exps' _ _ _ _ Ebsb Ebs).
    assert (HQn : glu_args Δ (im_nparams Mj) (sb_of_list Id Us) (decl_env D ups) Qn bs).
    { assert (Hσf : Δ ⊢ˢ σ ® components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                                (ns ++ nv ++ ys) ∈ SbC).
      { pose proof Hσ as Hσf; unfold K, nv in Hσf.
        erewrite shape_env_eq in Hσf;
          [ exact Hσf | first [ exact Heq | exact Hu | exact Hlns | apply length_nonrec_arg_vals; exact Hlfa | lia ] .. ]. }
      unfold Qn, σ.
      eapply rec_params_args; try eassumption; unfold ptyp_depth; lia. }
    pose proof (decl_closed_params_ass D (ptyp_mem t) Mj Hc HMj) as HassPj.
    pose proof (decl_closed_params D (ptyp_mem t) Mj Hc HMj) as HsPj.
    assert (HQp : glu_args Δ (im_params D Mj) Id nil (Us ++ Qn) (ups ++ bs)).
    { unfold im_params; apply glu_args_app; [ exact (group_structure_uparams _ Hass) | exact HUl | exact Hu |].
      split; [ exact HUs | exact HQn ]. }
    pose proof (components_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Δ Us HΔ HUs) as Hcomps.
    assert (H01 : tele_rel (canon_nparams_rel D ups (ptyp_mem t)) (List.rev (im_nparams Mj)) bs bs)
      by exact (canon_nparams_rel_trans p D ups Hass Hcp _ _ _ _ _ HMj Hrel (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hrel)).
    assert (HnQ : glu_nparams (ptyp_mem t) Mj NEl Δ Us Qn bs) by (eapply nparams_of_glu_args; eassumption).
    assert (HQl : List.length Qn = im_nn Mj) by (unfold Qn; rewrite List.length_map; exact HPl).
    assert (EQ : forall Q, ind_mty p D (ptyp_mem t) Us Qn = im_ty_at p (ptyp_mem t) Mj Us Q -> Q = Qn).
    { intros Q HQ; unfold ind_mty in HQ; rewrite HMj in HQ; unfold im_ty_at in HQ.
      unfold im_is_rview in Hrv; destruct (im_head Mj); try discriminate Hrv;
        apply apps_ind_inj, List.app_inv_head in HQ; congruence. }
    apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
    - intros bsr Q Hbsr HQ.
      rewrite (List.firstn_all2 (n := kk)) in Hbsr by (unfold shape_doms_tele; rewrite List.length_map; lia).
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      pose proof (EQ _ HQ) as ->.
      split; [ exact HQl | split; [ exact H01 |] ].
      intros bsr' Hb'.
      split; [ exact (glu_nparams_resp_per D ups NEl nel_resp_per _ _ _ _ _ _ _ HMj Hb' HnQ) |].
      intros Δ0 φ Hφ.
      pose proof (glu_args_params_top _ _ _ _ _ HassPj HsPj (glu_args_wk _ _ _ _ _ _ _ HassPj HsPj Hφ HQp)) as Ht.
      exact (glu_params_top_resp_per_top_ps _ _ _ _ _ _ (canon_params_per_top _ _ _ _ HMj Hb') Ht).
    - intros bsr Q Hbsr HQ Δ' φ Us' Q' Hφ HUl' HQ'.
      rewrite (List.firstn_all2 (n := kk)) in Hbsr by (unfold shape_doms_tele; rewrite List.length_map; lia).
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      pose proof (EQ _ HQ) as ->.
      destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh;
        [| | exfalso; exact (not_rview_record _ _ _ _ Hrv Hh) ].
      + (** A declared member: the uniform arguments are [ups]. *)
        assert (HU : ⟦ im_pre Mj (ind_uvars D (im_nn Mk) (List.length (List.repeat false kk ++ pat))) ⟧* gc_deps ⍮ gc_stack
                       ⍮ components_env D ups (List.rev Z) (ns ++ fa ++ ys) ↘ ups).
        { unfold im_pre; rewrite Hh.
          apply eval_uvars_components; [ exact Hu |].
          unfold pat; rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia. }
        pose proof (functional_eval_exps' _ _ _ _ Ecs HU) as ->.
        unfold im_ref in Hgl; rewrite Hh in Hgl; cbn [fst snd] in Hgl.
        exact (rec_end_decl (ptyp_mem t) Mj pm Δ Us Qn W N v i P El bs bs1 HMj Hh HΔ Hrel Hgl HN HQp HUl Δ' φ Us' Q' Hφ HUl' HQ').
      + (** A view: by its coherence with its container. *)
        destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & _).
        destruct (view_pre_values p D Hg Hcv (ptyp_mem t) Mj qc kc Is vm Dq ups Z RZ (ns ++ fa ++ ys) (im_nn Mk)
                    (List.length (List.repeat false kk ++ pat)) cs HMj Hh Hq Hu Hgu HZ HRZ HlZ
                    ltac:(unfold pat; rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia) HE Ecs)
          as (cups & Ecups & Hgc).
        unfold im_ref in Hgl, Ea; rewrite Hh in Hgl, Ea; cbn [fst snd] in Hgl, Ea.
        (** The element's value is in the group's relation at the view. *)
        destruct (glu_univ_elem_per_univ _ _ _ _ Hgl) as [Ra HRa].
        pose proof (glu_univ_elem_per_elem _ _ _ _ Hgl _ _ _ _ _ HN HRa) as Hva.
        assert (Ea' : ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ pat) (ptyp_skip kk t) ⟧
                        env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
                          (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys
                        ↘ d_ind qc kc (cs ++ bs1)).
        { rewrite Hsk; cbn [ptyp_ty]; exact Ea. }
        pose proof (shape_char p D Hg Hcv k Mk c gs HMk Hcon HΨs gs1 t gs2 Heq ups ns fa Hu Hlns Hlfa Hgu Hnsd Hp INV Hend Hrend
                      0 kk ys _ _ _ ltac:(lia) Hy Hgy Ea' HRa) as ERa.
        apply ERa in Hva; rewrite Hsk in Hva.
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hva) as (bs2 & bs3 & Ebs2 & Ebs3 & _ & _ & Hgv).
        rewrite (List.firstn_all2 (n := kk)) in Ebs2, Ebs3 by (unfold shape_doms_tele; rewrite List.length_map; lia).
        pose proof (functional_eval_exps' _ _ _ _ Ebs2 Ebs) as ->; pose proof (functional_eval_exps' _ _ _ _ Ebs3 Ebs) as ->.
        exact (Hvt Mj qc kc Is vm Dq cups cs bs bs1 Δ Us Qn W N v i P El HMj Hh Hq Ecups Hgc Hrel Hgl HN Hgv HQp
                 Δ' φ Us' Q' Hφ HUl' HQ').
  Qed.

  (** A recursive argument of the constructor, among arguments glued along
      its telescope, is a recursive argument of its shape, given the
      coherence of the member the shape ends in. *)
  Lemma con_rec_arg_glu : forall Δ Us Ns As ns ws, ⊢ Δ -> List.length Us = ind_nu D ->
      glu_args Δ (im_params D Mk) Id nil (Us ++ Ns) (ups ++ ns) ->
      glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) (env_tele nil (List.rev (im_params D Mk)) (ups ++ ns)) As ws ->
      glu_nparams k Mk NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
      tele_rel (canon_args_rel D ups k ns c) (cargs_nonrec gs) (nonrec_arg_vals gs ws) (nonrec_arg_vals gs ws) ->
      forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 -> glu_end_at p D ups NEl AEl DP DEl (ptyp_mem t) ->
        List.nth_error As (List.length gs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
        List.nth_error ws (List.length gs1) = Some v ->
        glu_rec p D ups NEl AEl DP DEl k Δ Us (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws))
          (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t A N v.
  Proof.
    intros Δ Us Ns As ns ws HΔ HUl HgP HgA Hnp Hnsr Hav gs1 t gs2 N A v Heq Hend HN HA Hv.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (group_structure_uparams _ Hass) as HassU.
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP LV]; rewrite length_im_params in LP, LV.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    assert (Lns : List.length ns = im_nn Mk) by (rewrite List.length_app in LV; unfold im_np in LV; lia).
    assert (LN : List.length Ns = im_nn Mk) by (rewrite List.length_app in LP; unfold im_np in LP; lia).
    pose proof HgP as HgP'; unfold im_params in HgP'.
    apply glu_args_app in HgP' as [HUs HNs]; [| exact HassU | exact HUl | exact Hu ].
    pose proof (components_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Δ Us HΔ HUs) as Hcomps.
    pose proof (args_of_glu_args Δ Us Ns ns As ws HΔ Hcomps HUs Hnp Hnsr HgA Hav) as Harg.
    set (fa := List.firstn (List.length gs1) ws).
    set (As1 := List.firstn (List.length gs1) As).
    assert (Hl1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
    assert (Hlfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn; lia).
    assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
    assert (Hpre1 : forall hs1 rB B hs2 N0 T' v0, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N0 ->
              List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
              List.nth_error fa (List.length hs1) = Some v0 ->
              Δ ⊢ N0 : T' ® v0 ∈ AEl k ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) fa))).
    { intros * Heq1 HN0 HT0 Hv0.
      assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
      unfold fa in Hv0 |- *; rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv0; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
      eapply (Harg hs1 rB B (hs2 ++ ca_rec t :: gs2)); [ rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN0 | exact HT0 | exact Hv0 ]. }
    pose proof (nonrec_prefix_pre _ gs ws gs1 (ca_rec t) gs2 Hav LW Heq) as Hp1; fold fa in Hp1.
    (** The arguments before, glued on the side of all the arguments. *)
    assert (HgA1 : glu_args Δ (cargs_ctx p D Mk gs1) (sb_of_list Id (Us ++ Ns)) (env_tele nil (List.rev (im_params D Mk)) (ups ++ ns)) As1 fa).
    { pose proof HgA as HgA''.
      rewrite (cargs_split_aux p D Mk gs gs1 (ca_rec t) gs2 Heq), <- (List.firstn_skipn (List.length gs1) As),
        <- (List.firstn_skipn (List.length gs1) ws) in HgA''.
      apply glu_args_app in HgA''; [ exact (proj1 HgA'') | apply cargs_ctx_aux_ass | |];
        rewrite List.length_firstn, length_cargs_ctx; lia. }
    assert (HassC1 : all_assumptions (cargs_ctx p D Mk gs1 ++ im_params D Mk))
      by (unfold all_assumptions; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    assert (HgPA1 : glu_args Δ (cargs_ctx p D Mk gs1 ++ im_params D Mk) Id nil ((Us ++ Ns) ++ As1) ((ups ++ ns) ++ fa)).
    { apply glu_args_app; [ exact HassP | rewrite List.length_app, length_im_params; unfold im_np in *; lia
                          | rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia |].
      split; [ exact HgP | exact HgA1 ]. }
    pose proof (glu_args_per_tele_args _ _ _ _ _ _ HassC1 HgPA1) as Hgall0; rewrite <- List.app_assoc in Hgall0.
    (** The arguments before, glued on the side of the non-recursive ones. *)
    destruct (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ 0 HMk Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
    cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0.
    pose proof (nonrec_args_prefix_glu_sub p D Hc Hass ups u NP NEl AP AEl DP DEl Hu Hf Δ Us HΔ HUs k Mk c gs gs1 (ca_rec t) gs2 Ns ns As
                  fa SbC0 HMk Hcon Heq Hnp Hnsr Hlfa ltac:(lia) Hpre1 Hp1 HSbC0) as Hσ0.
    (** The argument, glued at its type. *)
    pose proof HgA as [_ _ HgAe].
    destruct (HgAe _ _ _ _ _ _ HN HA Hv (cargs_rev_nth_rec p D Mk gs gs1 t gs2 Heq)) as [i' a1 P1 El1 Ha1 Hg1 HP1 HM1].
    fold fa in Ha1.
    rewrite (env_tele_cargs_prefix p D Mk gs gs1 (ca_rec t) gs2 (ups ++ ns) fa Heq) in Ha1
      by (first [ rewrite List.length_app; unfold im_np, ind_nu in *; lia | exact Hlfa ]).
    rewrite <- List.app_assoc in Ha1.
    pose proof (cargs_rec_type_shape p D Mk gs gs1 t gs2 (Us ++ Ns) As A Heq Hc
                  ltac:(rewrite List.length_app; unfold im_np in *; lia) HA) as ETs.
    pose proof (cargs_rec_type p D Mk gs gs1 t gs2 (sb_of_list Id (Us ++ Ns)) As A Heq HA) as ETc.
    fold As1 in ETs, ETc.
    rewrite <- sb_of_list_app in ETc.
    rewrite firstn_app_exact in ETs by exact HUl.
    rewrite <- List.app_assoc in ETs.
    assert (HlNs' : List.length (Ns ++ nonrec_exps gs1 As1) = 0 + List.length (cargs_nonrec gs1) + im_nn Mk)
      by (rewrite List.length_app, length_nonrec_exps by exact HlAs1; lia).
    assert (Hfinal : glu_rec p D ups NEl AEl DP DEl k Δ Us (ns ++ nonrec_arg_vals gs1 fa ++ nil)
                       (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn 0 (shape_doms_tele t)) t
                       (ptyp_ty_at p D Us (sb_of_list Id (Us ++ (Ns ++ nonrec_exps gs1 As1))) t) N v).
    { eapply (con_rec_glu gs1 t gs2 ns fa Heq Lns Hlfa Hnsr Hp1 Hgall0 Hend t 0 nil Δ Id Us (Ns ++ nonrec_exps gs1 As1)
                SbC0 A N v a1 i' P1 El1);
        [ reflexivity | lia | apply tele_prefix_rel_nil | constructor | exact HΔ | exact HUs | exact HlNs'
        | cbn [List.firstn doms_ctx List.map List.rev List.app]; exact HSbC0
        | cbn [List.firstn doms_ctx List.map List.rev List.app]; rewrite List.app_nil_r; rewrite <- List.app_assoc in Hσ0; exact Hσ0
        | cbn [List.repeat List.app List.firstn shape_domains_ctx List.rev]; exact Ha1
        | exact Hg1
        | exact HM1 ]. }
    cbn [List.firstn] in Hfinal; rewrite !List.app_nil_r in Hfinal; rewrite ETs; exact Hfinal.
  Qed.

  (** A constructor applied to parameters and arguments glued along its
      telescopes is an element of its member, at any stored uniform
      arguments [cs]. *)
  Lemma con_ind_glu_elem : forall Δ Us Ns As ns ws cs, im_is_rview Mk = false -> ⊢ Δ -> List.length Us = ind_nu D ->
      glu_args Δ (im_params D Mk) Id nil (Us ++ Ns) (ups ++ ns) ->
      glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) (env_tele nil (List.rev (im_params D Mk)) (ups ++ ns)) As ws ->
      List.length cs = im_unu D Mk ->
      ind_glu_elem p D ups NEl AEl DP DEl k Δ Us Ns (apps (a_con p k c) (Us ++ Ns ++ As))
        (d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c ((cs ++ ns) ++ ws)).
  Proof.
    intros Δ Us Ns As ns ws cs Hrv HΔ HUl HgP HgA Hcs.
    pose proof con_canon as Hcp.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (decl_closed_params D k Mk Hc HMk) as Hs.
    pose proof (group_structure_uparams _ Hass) as HassU.
    assert (HassCP : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP LV]; rewrite length_im_params in LP, LV.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    assert (LN : List.length Ns = im_nn Mk) by (rewrite List.length_app in LP; unfold im_np in LP; lia).
    assert (Lns : List.length ns = im_nn Mk) by (rewrite List.length_app in LV; unfold im_np in LV; lia).
    pose proof HgP as HgP'; unfold im_params in HgP'.
    apply glu_args_app in HgP' as [HUs HNs]; [| exact HassU | exact HUl | exact Hu ].
    (** The values related in the PER model. *)
    pose proof (glu_args_per_tele_args _ _ _ _ _ _ HassP HgP) as Hgp.
    assert (HgPA : glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil ((Us ++ Ns) ++ As) ((ups ++ ns) ++ ws))
      by (apply glu_args_app; [ exact HassP | rewrite List.length_app, length_im_params; unfold im_np in *; lia
                              | rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | split; assumption ]).
    pose proof (glu_args_per_tele_args _ _ _ _ _ _ HassCP HgPA) as Hgpa.
    rewrite List.rev_app_distr in Hgpa.
    destruct (Decl.per_tele_args_app (List.rev (im_params D Mk)) (List.rev (cargs_ctx p D Mk gs)) nil nil (ups ++ ns) (ups ++ ns) ws ws
                ltac:(rewrite List.length_rev, length_im_params; exact LV) Hgpa
                ltac:(rewrite List.length_rev, length_im_params; exact LV)) as [_ Hga].
    assert (Hends : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
              view_end_rel p D (List.firstn (ind_nu D) (ups ++ ns)) (List.firstn (ind_nu D) (ups ++ ns)) (ptyp_mem t) /\
              rview_end_rel p D (List.firstn (ind_nu D) (ups ++ ns)) (List.firstn (ind_nu D) (ups ++ ns)) (ptyp_mem t))
      by (intros; rewrite firstn_app_exact by exact Hu;
          split; [ exact (ViewArgs.view_end_rel_all VP p D HVP HPD ups ups Hgu Hu _)
                 | exact (ViewArgs.rview_end_rel_all VP p D HVP HPD ups ups Hgu Hu _) ]).
    pose proof (CargsRel.con_rel p D Hg Hcv k Mk c gs HMk Hcon (ups ++ ns) (ups ++ ns) ws ws Hgp
                  ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia) Hga LW Hends cs cs Hrv Hcs Hcs) as Hrel.
    rewrite firstn_app_exact, skipn_app_exact in Hrel by exact Hu.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    destruct (ind_rel_con_inv p D ups _ _ _ Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel HMk Hrv
                ltac:(rewrite List.length_app; lia)) as (gs0 & bs' & vs' & Ez & Href & _ & Hc0 & Hbl' & Hnsr & _ & Hav & Hca).
    rewrite Hcon in Hc0; injection Hc0 as <-.
    injection Ez as Ez; apply app_split_eq in Ez as [<- <-]; [| rewrite List.length_app, Hbl'; lia ].
    rewrite skipn_app_exact in Hnsr, Hav, Hca by exact Hcs.
    pose proof (components_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Δ Us HΔ HUs) as Hcomps.
    assert (Hnp : glu_nparams k Mk NEl Δ Us Ns ns) by (eapply nparams_of_glu_args; eassumption).
    pose proof (args_of_glu_args Δ Us Ns ns As ws HΔ Hcomps HUs Hnp Hnsr HgA Hav) as Harg.
    pose proof (glu_args_params_top _ _ _ _ _ HassP Hs HgP) as HPt.
    pose proof HPt as [_ HPty _].
    assert (HAty : forall j N T, List.nth_error As j = Some N ->
                     List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T -> Δ ⊢ N : T)
      by (intros; eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ]).
    assert (HMt : Δ ⊢ apps (a_con p k c) (Us ++ Ns ++ As) ≈ apps (a_con p k c) (Us ++ Ns ++ As) : im_ty_at p k Mk Us Ns).
    { pose proof (wf_exp_eq_con_apps_member Δ p D k Mk c gs (Us ++ Ns) (Us ++ Ns) As As Hl HMk Hcon HΔ
                    ltac:(rewrite List.length_app; unfold im_np in *; lia) ltac:(rewrite List.length_app; unfold im_np in *; lia)
                    ltac:(intros j0 P0 P0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl;
                          eapply HPty; eassumption)
                    LA LA
                    ltac:(intros j0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl;
                          eapply HAty; eassumption)) as H.
      rewrite firstn_app_exact, skipn_app_exact, <- List.app_assoc in H by exact HUl.
      unfold ind_mty in H; rewrite HMk in H; exact H. }
    eapply ind_glu_elem_con with (Mk := Mk) (gs := gs) (As := As);
      [ exact HMk | exact Hrv | apply surjective_pairing | exact Hcon | exact HUl | exact LN | rewrite List.length_app; lia | exact LW | exact LA
      | exact HMt | | | | exact HAty | | ].
    all: rewrite ?skipn_app_exact by exact Hcs.
    - exact Hnsr.
    - exact Hav.
    - exact Hnp.
    - exact Harg.
    - (** A recursive argument: by its shape, from its gluing at its type. *)
      intros gs1 t gs2 N A v Heq HN HA Hv.
      exact (con_rec_arg_glu Δ Us Ns As ns ws HΔ HUl HgP HgA Hnp Hnsr Hav gs1 t gs2 N A v Heq (Hview (ptyp_mem t)) HN HA Hv).
  Qed.

  (** The constructor of a record view applied to parameters and fields
      glued along its telescopes is an element of the record view, at any
      value whose projections are the fields' values, given the coherence
      of the members its recursive fields end in. *)
  Lemma con_rview_ind_glu_elem : forall qr Is fl Δ Us Ns As ns ws M m, im_head Mk = mh_record qr Is fl -> ⊢ Δ ->
      List.length Us = ind_nu D ->
      glu_args Δ (im_params D Mk) Id nil (Us ++ Ns) (ups ++ ns) ->
      glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) (env_tele nil (List.rev (im_params D Mk)) (ups ++ ns)) As ws ->
      ⟦projs fl of m ⟧ gc_deps ⍮ gc_stack ↘ ws ->
      Δ ⊢ M ≈ apps (a_con p k c) (Us ++ Ns ++ As) : im_ty_at p k Mk Us Ns ->
      (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> glu_end_at p D ups NEl AEl DP DEl (ptyp_mem t)) ->
      ind_glu_elem p D ups NEl AEl DP DEl k Δ Us Ns M m.
  Proof.
    intros qr Is fl Δ Us Ns As ns ws M m Hh HΔ HUl HgP HgA Hps HM Hends0.
    pose proof con_canon as Hcp.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (group_structure_uparams _ Hass) as HassU.
    pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMk Hh) as Hnp0.
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMk Hh) as (gs0 & Hcs0 & _).
    assert (Hcs : im_cons Mk = (c, gs) :: nil).
    { pose proof Hcon as Hc0; unfold ind_con in Hc0; rewrite Hcs0 in Hc0 |- *; cbn in Hc0.
      destruct (String.eqb c rview_con) eqn:E; [ injection Hc0 as -> | discriminate Hc0 ].
      apply String.eqb_eq in E; rewrite E; reflexivity. }
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP LV]; rewrite length_im_params in LP, LV.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    assert (LN : List.length Ns = im_nn Mk) by (rewrite List.length_app in LP; unfold im_np in LP; lia).
    assert (Lns : List.length ns = im_nn Mk) by (rewrite List.length_app in LV; unfold im_np in LV; lia).
    pose proof HgP as HgP'; unfold im_params in HgP'.
    apply glu_args_app in HgP' as [HUs HNs]; [| exact HassU | exact HUl | exact Hu ].
    (** The values related in the PER model. *)
    pose proof (glu_args_per_tele_args _ _ _ _ _ _ HassP HgP) as Hgp.
    assert (HassCP : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    assert (HgPA : glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil ((Us ++ Ns) ++ As) ((ups ++ ns) ++ ws))
      by (apply glu_args_app; [ exact HassP | rewrite List.length_app, length_im_params; unfold im_np in *; lia
                              | rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | split; assumption ]).
    pose proof (glu_args_per_tele_args _ _ _ _ _ _ HassCP HgPA) as Hgpa.
    rewrite List.rev_app_distr in Hgpa.
    destruct (Decl.per_tele_args_app (List.rev (im_params D Mk)) (List.rev (cargs_ctx p D Mk gs)) nil nil (ups ++ ns) (ups ++ ns) ws ws
                ltac:(rewrite List.length_rev, length_im_params; exact LV) Hgpa
                ltac:(rewrite List.length_rev, length_im_params; exact LV)) as [_ Hga].
    assert (Hends : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
              view_end_rel p D (List.firstn (ind_nu D) (ups ++ ns)) (List.firstn (ind_nu D) (ups ++ ns)) (ptyp_mem t) /\
              rview_end_rel p D (List.firstn (ind_nu D) (ups ++ ns)) (List.firstn (ind_nu D) (ups ++ ns)) (ptyp_mem t))
      by (intros; rewrite firstn_app_exact by exact Hu;
          split; [ exact (ViewArgs.view_end_rel_all VP p D HVP HPD ups ups Hgu Hu _)
                 | exact (ViewArgs.rview_end_rel_all VP p D HVP HPD ups ups Hgu Hu _) ]).
    destruct (CargsRel.con_args_canon p D Hg Hcv k Mk c gs HMk Hcon (ups ++ ns) (ups ++ ns) ws ws Hgp
                ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia) Hga LW Hends) as [Hav _].
    rewrite firstn_app_exact, skipn_app_exact in Hav by exact Hu.
    assert (Hnsr : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns).
    { assert (ns = nil) as -> by (destruct ns; [ reflexivity | unfold im_nn in Lns; rewrite Hnp0 in Lns; discriminate Lns ]).
      rewrite Hnp0; split; reflexivity + exact I. }
    pose proof (components_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Δ Us HΔ HUs) as Hcomps.
    assert (Hnp : glu_nparams k Mk NEl Δ Us Ns ns) by (eapply nparams_of_glu_args; eassumption).
    pose proof (args_of_glu_args Δ Us Ns ns As ws HΔ Hcomps HUs Hnp Hnsr HgA Hav) as Harg.
    assert (HAty : forall j N T, List.nth_error As j = Some N ->
                     List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T -> Δ ⊢ N : T)
      by (intros; eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ]).
    assert (ns = nil) as -> by (destruct ns; [ reflexivity | unfold im_nn in Lns; rewrite Hnp0 in Lns; discriminate Lns ]).
    eapply ind_glu_elem_record with (Mk := Mk) (gs := gs) (As := As);
      [ exact HMk | exact Hh | exact Hcs | exact HUl | exact LN | exact LA | exact Hps | exact HM | exact Hav | exact HAty
      | exact Harg |].
    intros gs1 t gs2 N A v Heq HN HA Hv.
    pose proof (con_rec_arg_glu Δ Us Ns As nil ws HΔ HUl HgP HgA Hnp Hnsr Hav gs1 t gs2 N A v Heq (Hends0 gs1 t gs2 Heq) HN HA Hv) as H.
    rewrite Hnp0 in H; cbn [List.rev List.app] in H; exact H.
  Qed.

End ConGlu.

(** The views of a group cohere with their containers in the gluing model:
    at every uniform parameters related to themselves, at the families of
    the clause. *)
Definition glu_views_ok (p : qname) (D : ind_decl) : Prop :=
  forall ups bu (u : universe_index) NP NEl AP AEl DP DEl, List.length ups = ind_nu D ->
    per_tele_args (List.rev (ind_uparams D)) nil nil ups ups -> ⟦ ind_sort D ⟧ decl_env D ups ↘ bu ->
    universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u -> ind_fams_glu D ups u NP NEl AP AEl DP DEl ->
    glu_view_end_ok p D ups NEl AEl DP DEl.

Lemma exps_eq_at_app_refl : forall Δ C1 C2 Xs Ys Zs, all_assumptions C1 -> all_assumptions C2 -> List.length Xs = List.length C1 ->
    exps_eq_at Δ C1 Xs Ys ->
    (forall k Z T, List.nth_error Zs k = Some Z -> List.nth_error (tele_insts C2 (sb_of_list Id Xs) Zs) k = Some T -> Δ ⊢ Z : T) ->
    exps_eq_at Δ (C2 ++ C1) (Xs ++ Zs) (Ys ++ Zs).
Proof.
  intros * HC1 HC2 HXl [HlXY HXY] HZ; split; [ rewrite !List.length_app; congruence |].
  intros k X Y A HX HY HA.
  rewrite tele_insts_app in HA by (try exact HC1; exact HXl).
  assert (Hl2 : List.length (tele_insts C1 Id Xs) = List.length Xs) by (rewrite length_tele_insts by exact HC1; lia).
  destruct (Nat.lt_ge_cases k (List.length Xs)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HX, HA by lia; rewrite List.nth_error_app1 in HY by lia; eauto.
  - rewrite List.nth_error_app2 in HX, HA by lia; rewrite List.nth_error_app2 in HY by lia.
    rewrite Hl2 in HA; replace (k - List.length Ys) with (k - List.length Xs) in HY by lia.
    rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; eapply HZ; eassumption.
Qed.

(** ** The Constructors of a Declared Member *)

Section ConFT.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D) (Hviews : glu_views_ok p D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (pm : qname) (c : String.string) (gs : list carg).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_decl pm) (Hcon : ind_con Mk c = Some gs)
    (HΨ : ⊩ cargs_ctx p D Mk gs ++ im_params D Mk).

  (** The universes of the sort, below a large one. *)
  Lemma sort_bound : exists n, forall ρ bu, ⟦ ind_sort D ⟧ ρ ↘ bu -> forall i, n <= i ->
      universe_index_le (Completeness.Inductives.Decl.univ_idx bu) (ul i).
  Proof.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq; [ exists i0 | exists 0 ]; intros * Hb i Hi; inversion Hb; subst; cbn; [ lia | exact I ].
  Qed.

  Lemma con_apps_eq : forall Δ Ps Ps' As vs ρ ws, ⊢ Δ -> glu_args Δ (im_params D Mk) Id nil Ps vs ->
      glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id Ps) ρ As ws -> exps_eq_at Δ (im_params D Mk) Ps Ps' ->
      Δ ⊢ apps (a_con p k c) (Ps ++ As) ≈ apps (a_con p k c) (Ps' ++ As)
        : im_ty_at p k Mk (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps).
  Proof.
    intros * HΔ HgP HgA [HlPP HPP].
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (decl_closed_params D k Mk Hc HMk) as Hs.
    destruct (glu_args_params_top _ _ _ _ _ HassP Hs HgP) as [HPl _ _].
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA _]; rewrite length_cargs_ctx in LA.
    pose proof (wf_exp_eq_con_apps_member Δ p D k Mk c gs Ps Ps' As As Hl HMk Hcon HΔ HPl ltac:(congruence) HPP LA LA
                  ltac:(intros j0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl;
                        eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ])) as H.
    unfold ind_mty in H; rewrite HMk in H; exact H.
  Qed.

  (** The type of the constructor's application, at a list of terms. *)
  Lemma con_codomain_inst : forall Ms, List.length Ms = im_np D Mk + List.length gs ->
      (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list Id Ms]
      = apps (a_ind p k) (List.firstn (im_np D Mk) Ms).
  Proof.
    intros Ms HMl.
    unfold ind_mty; rewrite HMk; unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
    rewrite apps_exp_sub; cbn [exp_sub]; f_equal.
    unfold ind_uvars; rewrite vars_from_app.
    pose proof (vars_from_sb_of_list_app (List.firstn (im_np D Mk) Ms) (List.skipn (im_np D Mk) Ms) Id) as H.
    rewrite List.firstn_skipn, List.length_skipn, List.length_firstn in H.
    replace (List.length Ms - im_np D Mk) with (List.length gs) in H by lia.
    replace (Nat.min (im_np D Mk) (List.length Ms)) with (ind_nu D + im_nn Mk) in H by (unfold im_np in *; lia).
    exact H.
  Qed.

  (** The constructor applied to glued parameters and arguments is glued at
      the type at the parameters. *)
  Lemma con_base : forall Δ Ms vs w (i : nat) b P El, ⊢ Δ ->
      (forall ρ bu, ⟦ ind_sort D ⟧ ρ ↘ bu -> universe_index_le (Completeness.Inductives.Decl.univ_idx bu) (ul i)) ->
      glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil Ms vs ->
      Completeness.Inductives.Con.con_value p D k Mk c vs w ->
      ⟦ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) ⟧
        env_tele nil (List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)) vs ↘ b ->
      DG b ∈ glu_univ_elem i ↘ P ↘ El ->
      (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w w) ->
      Δ ⊢ apps (a_con p k c) Ms
        : (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list Id Ms]
        ® w ∈ El.
  Proof.
    intros * HΔ Hbnd Hgall Hw Hb Hglu HPER.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (decl_closed_params D k Mk Hc HMk) as Hs.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (HassC : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk Hin (eq_sym (List.app_nil_r gs))) as HsC.
    destruct (glu_args_length _ _ _ _ _ _ Hgall) as [LM LV]; rewrite List.length_app, length_cargs_ctx, length_im_params in LM, LV.
    set (Ps := List.firstn (im_np D Mk) Ms); set (As := List.skipn (im_np D Mk) Ms).
    set (ps := List.firstn (im_np D Mk) vs); set (ws := List.skipn (im_np D Mk) vs).
    assert (EM : Ms = Ps ++ As) by (symmetry; apply List.firstn_skipn).
    assert (EV : vs = ps ++ ws) by (symmetry; apply List.firstn_skipn).
    assert (LPs : List.length Ps = im_np D Mk) by (unfold Ps; rewrite List.length_firstn; lia).
    assert (Lps : List.length ps = im_np D Mk) by (unfold ps; rewrite List.length_firstn; lia).
    assert (LAs : List.length As = List.length gs) by (unfold As; rewrite List.length_skipn; lia).
    assert (Lws : List.length ws = List.length gs) by (unfold ws; rewrite List.length_skipn; lia).
    pose proof Hgall as Hg0.
    rewrite EM, EV in Hg0; apply glu_args_app in Hg0; [| exact HassP | rewrite length_im_params; exact LPs | rewrite length_im_params; exact Lps ].
    destruct Hg0 as [HgP HgA].
    rewrite (con_codomain_inst Ms ltac:(lia)); fold Ps.
    assert (Eb : ⟦ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) ⟧
                   env_tele nil (List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)) vs ↘ d_ind p k ps).
    { unfold ind_mty; rewrite HMk; unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
      apply Modules.eval_apps_exp; exists (d_ind p k nil); split; [ constructor |].
      apply Modules.eval_app_args_ind; exists ps; split.
      - unfold ind_uvars; rewrite vars_from_app, EV.
        rewrite List.rev_app_distr; unfold env_tele.
        rewrite tele_entries_app by (rewrite List.length_rev, length_im_params; exact Lps).
        pose proof (Decl.eval_vars_from_args (tele_entries nil (List.rev (im_params D Mk)) ps) nil
                      (tele_entries (env_tele nil (List.rev (im_params D Mk)) ps) (List.rev (cargs_ctx p D Mk gs)) ws)) as H.
        rewrite tele_entries_values, !Completeness.Inductives.Decl.tele_entries_length in H.
        replace (List.length gs) with (List.length ws) by exact Lws.
        replace (ind_nu D + im_nn Mk) with (List.length ps) by (unfold im_np in *; lia).
        exact H.
      - change (d_ind p k ps) with (d_ind p k (nil ++ ps)); apply (eval_apps_indty p D k Mk ps nil Hl HMk); cbn; lia. }
    assert (b = d_ind p k ps) as -> by (eapply functional_eval_exp; eassumption).
    set (ups := List.firstn (ind_nu D) ps) in *; set (ns := List.skipn (ind_nu D) ps) in *.
    assert (Eps : ps = ups ++ ns) by (symmetry; apply List.firstn_skipn).
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; unfold im_np in *; lia).
    assert (Hrv : im_is_rview Mk = false) by (unfold im_is_rview; rewrite Hh; reflexivity).
    destruct (Completeness.Inductives.Con.con_value_full p D k Mk c gs vs w Hrv ltac:(lia) Hw) as (cs & Hcs & ->).
    unfold im_ref in *; rewrite Hh in *; cbn [fst snd] in *.
    assert (Esk : List.skipn (ind_nu D) vs = ns ++ ws)
      by (rewrite EV, Eps, <- List.app_assoc, skipn_app_exact by exact Hu; reflexivity).
    rewrite Esk in *.
    clearbody ups ns.
    rewrite Eps in Hglu, HPER, HgP, HgA.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
    destruct (ind_glu_of_per p D Hl i Rb k Mk pm ups ns HMk Hh HRb Hu) as [NP NEl AP AEl DP DEl P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf].
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hg2) as [_ EEl].
    apply EEl, HEl2.
    pose proof (HPER _ HRb) as Hrb.
    pose proof (Completeness.Inductives.Decl.per_univ_elem_univ) as _.
    assert (Hlt : k < ind_ndecl D) by (eapply decl_member_lt; [ exact HΔ | exact Hl | exact HMk | exact Hh ]).
    assert (HgPd : per_tele_args (List.rev (im_params D Mk)) nil nil (ups ++ ns) (ups ++ ns)).
    { exact (glu_args_per_tele_args _ _ _ _ _ _ HassP HgP). }
    rewrite rev_im_params in HgPd.
    destruct (Decl.per_tele_args_app (List.rev (ind_uparams D)) (List.rev (im_nparams Mk)) nil nil ups ups ns ns
                ltac:(rewrite List.length_rev; exact Hu) HgPd ltac:(rewrite List.length_rev; exact Hu)) as [Hgu _].
    assert (HUs : glu_args Δ (ind_uparams D) Id nil (List.firstn (ind_nu D) Ps) ups).
    { pose proof (glu_args_uparams_of_params D Hass Mk _ _ _ HgP) as H; rewrite firstn_app_exact in H by exact Hu; exact H. }
    destruct (Completeness.Inductives.Model.sort_value D HD ups Hgu Hu) as [bu Hbu].
    pose proof (Hbnd _ _ Hbu) as Hule.
    pose proof (Hviews ups bu (ul i) NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf) as Hview.
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ps _ _); [ | apply HR2; exact Hrb | |].
    { rewrite EM; pose proof (con_apps_eq Δ Ps Ps As _ _ ws HΔ HgP HgA (glu_params_top_refl _ _ _ _ _
                                (glu_args_params_top _ _ _ _ _ HassP Hs HgP))) as H.
      unfold im_ty_at, im_ref, im_pre in H; rewrite Hh in H; cbn [fst snd] in H; rewrite List.firstn_skipn in H.
      gen_presups; assumption. }
    { exact (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Hass k Mk Δ Ps ups ns bu (ul i) NP NEl AP AEl DP DEl HMk Hlt HΔ HgP Hu Hbu Hule Hf). }
    intros Δ' φ Ps' Hφ HPs'.
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    pose proof (glu_args_resp_eq Δ' _ nil _ Ps' _ HassP (member_params_wf _ _ _ _ _ Hdt HMk) HΔ' HPs'
                  (glu_args_wk _ _ _ _ _ _ _ HassP Hs Hφ HgP)) as HgP'.
    pose proof (glu_args_wk _ _ _ _ _ _ _ HassC HsC Hφ Hgall) as Hgw.
    rewrite EM, List.map_app, EV, Eps in Hgw.
    assert (LPw : List.length (List.map (fun M => M[φ]ʷ) Ps) = List.length (im_params D Mk))
      by (rewrite List.length_map, length_im_params; exact LPs).
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [_ Lupn].
    pose proof Hgw as Hgw'; apply glu_args_app in Hgw'; [| exact HassP | exact LPw | exact Lupn ].
    destruct Hgw' as [_ HgAw].
    pose proof (exps_eq_at_app_refl Δ' (im_params D Mk) (cargs_ctx p D Mk gs) _ Ps' (List.map (fun M => M[φ]ʷ) As)
                  HassP (cargs_ctx_aux_ass _ _ _ _ _) LPw HPs'
                  ltac:(intros; eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgAw | eassumption | eassumption ])) as Heq2.
    destruct (cargs_ctx_wf _ _ p D k Mk c gs (ctx_wf_gctx _ _ _ HΔ') (decls_of_ctx _ _ _ HΔ') Hl HMk Hin gs nil
                (eq_sym (List.app_nil_r gs))) as (HwfC & _ & _).
    pose proof (glu_args_resp_eq Δ' _ nil _ _ _ HassC HwfC HΔ' Heq2 Hgw) as Hg'.
    destruct HPs' as [HlPP HPP].
    apply glu_args_app in Hg'; [| exact HassP | rewrite <- HlPP; exact LPw | exact Lupn ].
    destruct Hg' as [_ HgA'].
    assert (HlPs' : List.length Ps' = im_np D Mk) by (rewrite <- HlPP, List.length_map; exact LPs).
    rewrite <- (List.firstn_skipn (ind_nu D) Ps') in HgP', HgA'.
    pose proof (con_ind_glu_elem VP p D HVP HPD HG k Mk c gs HMk Hcon ups bu (ul i) NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf
                  Hview Δ' (List.firstn (ind_nu D) Ps') (List.skipn (ind_nu D) Ps') (List.map (fun M => M[φ]ʷ) As) ns ws cs Hrv HΔ'
                  ltac:(rewrite List.length_firstn; unfold im_np in *; lia) HgP' HgA' Hcs) as Hgi.
    unfold im_ref in Hgi; rewrite Hh in Hgi; cbn [fst snd] in Hgi.
    rewrite List.app_assoc.
    eapply ind_glu_elem_resp_exp_eq; [ exact Hgi | exact HMk |].
    rewrite List.app_assoc, List.firstn_skipn.
    rewrite EM, apps_wk, List.map_app; cbn [exp_wk].
    rewrite List.firstn_skipn in HgP', HgA'.
    eapply con_apps_eq; [ exact HΔ' | exact HgP' | exact HgA' |].
    split; [ rewrite List.length_map; congruence |].
    eapply (params_eq_sym _ p D k Mk); [ exact Hl | exact HMk | exact HΔ' | | | exact HPP ]; rewrite ?List.length_map; lia.
  Qed.

  (** The constructor is glued at its type. *)
  Lemma glu_rel_exp_con0 : forall (j0 : nat), ⋅ ⊢ con_ty p D k Mk gs : Typeω@j0 -> ⋅ ⊢ a_con p k c : con_ty p D k Mk gs ->
      ⋅ ⊩ a_con p k c : con_ty p D k Mk gs.
  Proof.
    intros j0 Hj Hcty.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (HassC : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk Hin (eq_sym (List.app_nil_r gs))) as HsC.
    destruct sort_bound as [n0 Hn0].
    pose proof HΨ as [SbC HSbC].
    assert (HSbC0 : EG (cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅ ∈ glu_ctx_env ↘ SbC) by (rewrite List.app_nil_r; exact HSbC).
    destruct (glu_ctx_env_entries_valid _ _ _ HassC HSbC0 (Nat.max j0 n0)) as (i & Hji & HAents).
    assert (Hi : ⋅ ⊢ con_ty p D k Mk gs : Typeω@i) by (eapply lift_exp_ge; [| exact Hj ]; lia).
    assert (Hg0 : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact (glu_ctx_env_wf_ctx HSbC)).
    eapply (glu_closed_const_by _ _ i (fun m0 => m0 = d_con p k c nil));
      [ reflexivity | intros; eapply con_ty_sub; eassumption | exact Hi
      | intros ρ; exists (d_con p k c nil); split; [| reflexivity ];
        eapply eval_exp_con; [ exact Hl | exact HMk | unfold im_starts, im_is_decl; rewrite Hh; reflexivity ] |].
    intros Δ σ m0 Hσ -> a P El Ha Hglu.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
    pose proof Hi as Hi'; unfold con_ty in Hi'; rewrite <- ctx_pi_app in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ HassC Hi') as [HCs _].
    replace (con_ty p D k Mk gs) with ((con_ty p D k Mk gs)[σ]) by (eapply con_ty_sub; eassumption).
    unfold con_ty in Ha |- *; rewrite <- ctx_pi_app in Ha |- *.
    change (a_con p k c) with (apps (a_con p k c) nil).
    eapply (ctx_pi_glu_elem_by (Completeness.Inductives.Con.con_value p D k Mk c) (a_con p k c)
              ((cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅))
      with (Γb := ⋅) (Sb_b := nil_glu_sub_pred) (Sb := SbC) (xs := nil);
      [ reflexivity | | exact HassC | eapply glu_ctx_env_nil; [ reflexivity | exact Hg0 ] | exact HSbC0
      | exists nil; reflexivity
      | intros; eapply HAents; eassumption
      | intros; eapply HCs; eassumption
      | exact Hσ | reflexivity | exact (Completeness.Inductives.Con.con_value_decl p D k Mk c pm nil Hh) | | | | exact Ha | exact Hglu ].
    - intros Δ1 Γ' Sb' Δ' σ' xs x w HT _ _ HlΓ Hw.
      apply (Completeness.Inductives.Con.con_value_step VP p D HVP HPD k Mk c gs HMk Hcon xs x w);
        [ | intros * Hh'; rewrite Hh in Hh'; discriminate | exact Hw ].
      assert (List.length Γ' <= List.length ((cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅)) by (rewrite HT, List.length_app; lia).
      rewrite List.app_nil_r, List.length_app, length_cargs_ctx, length_im_params in *; lia.
    - cbn [apps_exp]; rewrite ctx_pi_app.
      change (ctx_pi (im_params D Mk) (ctx_pi (cargs_ctx p D Mk gs)
                (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))))
        with (con_ty p D k Mk gs).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hcty Hσ) as Hcσ; cbn [exp_sub] in Hcσ; exact Hcσ.
    - intros R a' Ha' HR.
      destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Hcty)) as (env_rel & Henv & j' & Hsimp).
      assert (Hnil : env_rel nil nil) by (inversion Henv; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
      destruct (Completeness.ContextCases.rel_type_kind_of_typ (completeness_fundamental_exp _ _ _ Hj) _ Henv _ _ Hnil)
        as (a0 & Ea0 & Hk0).
      destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & [Hp | (m1 & m2 & Hm1 & Hm2 & Hmm)]).
      { (* the type of a constructor is relevant *)
        assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption); congruence. }
      unfold con_ty in Ha1; rewrite <- ctx_pi_app in Ha1.
      assert (a1 = a') as -> by (eapply functional_eval_exp; eassumption).
      assert (Em : ⟦ a_con p k c ⟧ nil ↘ d_con p k c nil)
        by (eapply eval_exp_con; [ exact Hl | exact HMk | unfold im_starts, im_is_decl; rewrite Hh; reflexivity ]).
      assert (m1 = d_con p k c nil) as -> by (eapply functional_eval_exp; eassumption).
      assert (m2 = d_con p k c nil) as -> by (eapply functional_eval_exp; eassumption).
      assert (Ha2' : ⟦ ctx_pi (cargs_ctx p D Mk gs ++ im_params D Mk)
                       (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk))) ⟧ nil ↘ a2)
        by (unfold con_ty in Ha2; rewrite <- ctx_pi_app in Ha2; exact Ha2).
      assert (a2 = a') as -> by (eapply functional_eval_exp; eassumption).
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR); exact Hmm.
    - intros Δ' φ Ms vs w' Hφ Hga Hw' b P' El' Hb Hglub HPb; cbn [List.map List.app] in *.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      apply (glu_args_closed_base _ _ _ Id _ _ _ HassC HsC) in Hga.
      destruct (glu_args_length _ _ _ _ _ _ Hga) as [HMl _].
      rewrite (sb_of_list_scoped_base _ _ _ Id).
      2:{ rewrite HMl, List.length_app, length_cargs_ctx; unfold ind_mty; rewrite HMk; unfold im_ty_at, im_ref, im_pre; rewrite Hh.
          apply exp_scoped_apps; split; [ cbn; exact I |].
          unfold ind_uvars; apply List.Forall_app; split; apply vars_from_scoped; rewrite length_im_params; unfold im_np; lia. }
      rewrite List.app_nil_r in Hb.
      eapply con_base; [ exact HΔ' | | exact Hga | exact Hw' | exact Hb | exact Hglub | exact HPb ].
      intros; eapply Hn0; [ eassumption | lia ].
  Qed.

End ConFT.

End Fixed_GCtx.
