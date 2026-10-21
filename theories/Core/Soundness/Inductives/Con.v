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
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
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

Lemma per_univ_of_elem : forall (i : uidx) R a b, DF a ≈ b ∈ per_univ_elem i ↘ R -> Dom a ≈ b ∈ per_univ i.
Proof. intros * H; exists R; exact H. Qed.

(** ** Glued Arguments Relate in the PER Model *)

Lemma glu_args_per_gargs : forall C Δ Ms vs Sb, tele_ass C -> ⊨ C -> ⊢ Δ -> EG C ∈ glu_ctx_env ↘ Sb ->
    glu_args Δ C Id nil Ms vs -> per_gargs (List.rev C) nil nil vs vs.
Proof.
  intros * Hass HC HΔ HSb Hg.
  assert (Hσ : Δ ⊢ˢ sb_of_list Id Ms ® env_args nil vs ∈ Sb).
  { eapply glu_sub_of_list with (C := C) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ exact Hass | rewrite List.app_nil_r; exact HSb | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
      | cbn; apply wf_sub_nil'; exact HΔ | exact Hg ]. }
  destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
  pose proof (glu_ctx_env_per_env HSb HR Hσ) as HE.
  destruct (glu_args_length _ _ _ _ _ _ Hg) as [_ Hl].
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  assert (HR' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ R)
    by (rewrite List.rev_involutive, List.app_nil_r; exact HR).
  exact (proj2 (Decl.rel_gargs _ _ _ _ Args.per_ctx_env_nil_true HC' (List.Forall_rev Hass) HR' nil nil vs vs
                  ltac:(rewrite List.length_rev; exact Hl) ltac:(rewrite List.length_rev; exact Hl) HE)).
Qed.

Lemma cargs_rev_nth_arg : forall p D Mk gs gs1 B gs2, gs = gs1 ++ ca_arg B :: gs2 ->
    List.nth_error (List.rev (cargs_ctx p D Mk gs)) (List.length gs1) = Some (ce_ass B[wk_pat (cargs_pat gs1)]ʷ).
Proof.
  intros * ->.
  unfold cargs_ctx; rewrite cargs_ctx_aux_app; cbn [cargs_ctx_aux].
  rewrite !List.rev_app_distr; cbn [List.rev List.app].
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag, List.app_nil_r; reflexivity.
Qed.

Lemma cargs_rev_nth_rec : forall p D Mk gs gs1 Pr gs2, gs = gs1 ++ ca_rec Pr :: gs2 ->
    List.nth_error (List.rev (cargs_ctx p D Mk gs)) (List.length gs1)
      = Some (ce_ass (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) Pr)).
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

Lemma cargs_suffix_glu : forall p D Mk gs gs1 gs2, gs = gs1 ++ gs2 -> ⊩ cargs_ctx p D Mk gs ++ im_params D Mk ->
    exists Sb, EG cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ glu_ctx_env ↘ Sb.
Proof.
  intros * Heq [Sb HSb].
  rewrite Heq in HSb; unfold cargs_ctx in HSb; rewrite cargs_ctx_aux_app, <- List.app_assoc in HSb.
  eapply glu_ctx_env_suffix; [| exact HSb ]; apply cargs_ctx_aux_ass.
Qed.

(** The type of a domain of a recursive argument's shape, at all the
    arguments and at the non-recursive ones: related types. *)
Lemma vg_dom_types : forall pq G, valid_group pq G -> containers_valid G ->
    forall k Mk c gs gs1 t gs2 d B U ms vs ys, ind_member G k = Some Mk -> ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (ptyp_doms t) d = Some B ->
    List.length U = ind_nu G -> List.length ms = im_nn Mk -> List.length vs = List.length gs1 -> List.length ys = d ->
    per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk)) nil nil
      (U ++ ms ++ vs ++ ys) (U ++ ms ++ vs ++ ys) ->
    exists (i : nat) R a a', ⟦ B[wk_pat (List.repeat false d ++ cargs_pat gs1)]ʷ ⟧ env_args nil (U ++ ms ++ vs ++ ys) ↘ a /\
      ⟦ B ⟧ env_args nil (U ++ ms ++ nonrec_arg_vals gs1 vs ++ ys) ↘ a' /\ DF a ≈ a' ∈ per_univ_elem i ↘ R.
Proof.
  intros pq G Hg Hcv k Mk c gs gs1 t gs2 d B U ms vs ys HM Hcon Heq HB HlU Hlm Hlv Hly Hgp.
  pose proof (vgr_valid _ _ Hg) as HD.
  assert (Hd : d <= List.length (ptyp_doms t)) by (assert (d < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
  destruct (vg_cargs_sem_all pq G Hg Hcv k Mk c gs HM Hcon gs1 (ca_rec t :: gs2) Heq) as [HW0 Hw0].
  pose proof (sh_wk_gen G pq k Mk c gs HD HM Hcon gs1 t gs2 Heq Hw0 d Hd) as Hw.
  pose proof (sh_sem_gen G pq k Mk c gs HD HM Hcon gs1 t gs2 Heq HW0 Hw0 d Hd) as HW.
  destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & j & HBv).
  rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
  destruct (rel_exp_under_ctx_wk_simple Hw HBv) as (RΓ & HΓ & i0 & Hwk).
  assert (Hρ : RΓ (env_args nil (U ++ ms ++ vs ++ ys)) (env_args nil (U ++ ms ++ vs ++ ys))).
  { apply (gargs_env_rel _ _ _ _ _ _ HΓ HW); [| exact Hgp ].
    rewrite !List.length_app, length_sh_ctx, List.length_firstn, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
  destruct (Hwk _ _ Hρ) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
  assert (Hy1 : y = d_univ j) by (cbn in Ey; inversion Ey; reflexivity).
  rewrite Hy1 in HRy; clear Hy1 Ey Ey'.
  destruct (Decl.per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
  apply ERy in Hmm; destruct Hmm as [Rm HRm].
  assert (HwE : ⟪wk_pat (List.repeat false d ++ cargs_pat gs1)⟫ (env_args nil (U ++ ms ++ vs ++ ys))
                = env_args nil (U ++ ms ++ nonrec_arg_vals gs1 vs ++ ys)).
  { replace (U ++ ms ++ vs ++ ys) with ((U ++ ms ++ vs) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
    rewrite env_args_app, eval_wk_pat_falses by exact Hly.
    replace (U ++ ms ++ vs) with ((U ++ ms) ++ vs) by (rewrite <- List.app_assoc; reflexivity).
    rewrite env_args_app, Decl.eval_wk_pat_args by exact Hlv.
    rewrite <- !env_args_app, <- !List.app_assoc; reflexivity. }
  rewrite HwE in Em'.
  exists j, Rm, m, m'; split; [ exact Em | split; [ exact Em' | exact HRm ] ].
Qed.

(** ** The Parameters of a Recursive Argument's Type *)

Section RecParams.
  Variable (D : ind_decl).
  Hypothesis (HD : valid_ind_decl D) (Hc : decl_closed D) (Hass : grp_tele_ass D).
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
    { pose proof (vid_dctx _ HD _ _ _ _ _ _ _ (List.length (ptyp_doms t)) HM Hcon Heq (le_n _)) as H.
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
      destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
      pose proof (vid_rec _ HD _ _ _ _ _ _ _ _ _ _ _ HM Hcon Heq HMj HP HT) as HPv.
      destruct (vid_npar _ HD _ _ _ _ HMj HA) as (_ & j & HAv).
      rewrite (firstn_S_snoc _ _ _ HP), sb_of_list_app, (nparams_prefix_S _ _ _ HA); cbn [sb_of_list List.app].
      eapply Completeness.LogicalRelation.Substitution.rel_sub_under_ctx_extend; [ exact Hτ | exact HAv | exact HPv ].
  Qed.
End RecParams.

(** ** Recursive Arguments Ending in a View

    A recursive argument whose shape ends in a view [j] is of the view's
    type, the container's member at the view's instance, glued at the
    container's type; its gluing as an element of [j] in the group is the
    coherence of the view with its container. *)
Definition glu_view_end_ok (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred) : Prop :=
  forall j Mj qc kc Is vm Dq cups cs bs bs1 Δ Us Q N v (i : uidx) P El,
    ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups -> per_gargs (List.rev (ind_uparams Dq)) nil nil cups cs ->
    tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs1 ->
    DG d_ind qc kc (cs ++ bs1) ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ im_ty_at p j Mj Us Q ® P -> Δ ⊢ N : im_ty_at p j Mj Us Q ® v ∈ El ->
    grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) j ups ups bs bs v v ->
    glu_args Δ (im_params D Mj) Id nil (Us ++ Q) (ups ++ bs) ->
    forall Δ' φ Us' Q', Δ' ⊢ᵏ φ : Δ -> List.length Us' = ind_nu D ->
      exps_eq_at Δ' (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
      ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' Q' N[φ]ʷ v.

(** ** A Constructor at Glued Parameters and Arguments *)

Section ConGlu.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := vgr_lookup _ _ Hg.
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hsu := vgr_sort _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Let Hdt := vgr_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs)
    (HΨ : ⊩ cargs_ctx p D Mk gs ++ im_params D Mk).
  Let HΨs := vg_cargs_sem p D Hg Hcv k Mk c gs HMk Hcon.
  Variables (ups : list domain) (bu : domain) (u : uidx)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups)
    (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).
  (** The types of the rests of a recursive argument's shape are types, in
      the context of the arguments before it and the shape's domains before
      the rest. *)
  Hypothesis (HshV : forall gs1 t gs2 kk, gs = gs1 ++ ca_rec t :: gs2 -> kk <= List.length (ptyp_doms t) ->
       exists j : nat, sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
         ⊩ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t) : Typeω@j).
  Hypothesis (Hview : glu_view_end_ok p D ups NEl AEl DP DEl).

  Let HeN := ifg_npar_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HNP := ifg_npar_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeA := ifg_arg_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HAP := ifg_arg_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeD := ifg_dom_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HDP := ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf.

  Lemma con_canon : ind_canon_props D ups.
  Proof. exact (vg_canon p D Hg ups Hgu Hu). Qed.

  (** The gluings of the non-uniform parameters move along their relations. *)
  Lemma nel_resp_per : forall m Mm j vs vs', ind_member D m = Some Mm -> j < im_nn Mm ->
      tele_prefix_rel (canon_nparams_rel D ups m) j vs vs' ->
      forall Γ A N n n', NEl m j vs Γ A N n -> canon_nparams_rel D ups m j vs n n' -> NEl m j vs' Γ A N n'.
  Proof.
    intros * HM Hj Hp Γ0 A0 N n n' HN Hnn.
    pose proof con_canon as Hcp.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    assert (Hk' : j < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, length_im_nparams; exact Hj).
    destruct (nparams_lt_ass D m Mm j Hass HM Hk') as [S HS].
    pose proof (nparams_prefix_rel_refl_l p D ups _ (canon_args_rel D ups) (canon_doms_rel ups) Hass HnP HnI HaP HaI HdP HdI
                  m Mm HM j vs vs' ltac:(rewrite List.length_rev, length_im_nparams; lia) Hp) as Hd.
    pose proof (nparams_prefix_rel_refl_r p D ups _ (canon_args_rel D ups) (canon_doms_rel ups) Hass HnP HnI HaP HaI HdP HdI
                  m Mm HM j vs vs' ltac:(rewrite List.length_rev, length_im_nparams; lia) Hp) as Hd'.
    destruct (HeN _ _ _ _ _ HM HS Hd) as [b Eb].
    pose proof (HNP _ _ _ _ _ _ HM HS Hd Eb) as Hgb.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
    assert (Hnn' : Rb n n')
      by (apply (per_head_iff Eb Eb HRb); unfold canon_nparams_rel in Hnn; rewrite (nth_ctyp_eq _ _ _ _ _ HM HS) in Hnn; exact Hnn).
    pose proof (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hgb _ HRb _ _ _ _ _ HN Hnn') as Hn2.
    destruct (canon_hn D HD Hc Hsu ups bu Hu Hbu ups Hgu _ _ _ _ _ _ HM HS Hp) as (a & a' & Ea & Ea' & Haa).
    assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct Haa as [Rh HRh].
    pose proof (per_univ_elem_cumu_uidx _ _ _ _ HRh _ Hule) as HRh'.
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R => per_univ_elem u R b a') Rh HRh') Hgb) as Hga'.
    pose proof (HNP _ _ _ _ _ _ HM HS Hd' Ea') as Hgb'.
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [_ HEq].
    apply HEq; exact Hn2.
  Qed.

  (** Glued arguments of a constructor's non-recursive arguments are glued
      at the gluings of the clause. *)
  Lemma args_of_glu_args : forall Δ Us Ns ns As ws, ⊢ Δ ->
      ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      glu_nparams k Mk NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
      glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns)) As ws ->
      tele_rel (canon_args_rel D ups k ns c) (cargs_nonrec gs) (nonrec_arg_vals gs ws) (nonrec_arg_vals gs ws) ->
      forall hs1 B hs2 N T v, gs = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T ->
        List.nth_error ws (List.length hs1) = Some v ->
        Δ ⊢ N : T ® v ∈ AEl k ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws)).
  Proof.
    intros Δ Us Ns ns As ws HΔ Hc0 HUs Hnp Hns HgA Hv.
    pose proof Hc0 as [_ HCA _].
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (dc_ass _ Hc) as HassU.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (HgP : glu_args Δ (im_params D Mk) Id nil (Us ++ Ns) (ups ++ ns)).
    { unfold im_params; apply glu_args_app; [ exact HassU | exact LU | exact Hu |].
      split; [ exact HUs |].
      eapply glu_args_of_nparams; eassumption. }
    enough (forall m hs1 B hs2 N T v, List.length hs1 < m -> gs = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T ->
              List.nth_error ws (List.length hs1) = Some v ->
              Δ ⊢ N : T ® v ∈ AEl k ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws))) as Hm
      by (intros; eapply (Hm (S (List.length hs1))); eauto).
    induction m as [| m IH]; intros hs1 B hs2 N T v Hlt Heq HN HT Hvv; [ lia |].
    destruct (Nat.eq_dec (List.length hs1) m) as [Hlm | Hne]; [| eapply IH; eauto; lia ].
    assert (Hh : List.length hs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
    pose proof HgA as [_ _ HA].
    destruct (HA _ _ _ _ _ HN HT Hvv (cargs_rev_nth_arg p D Mk _ _ _ _ Heq)) as [i' a1 P' El' Ha1 Hglu' HP' HM'].
    set (j := List.length (cargs_nonrec hs1)).
    assert (HBk : List.nth_error (cargs_nonrec gs) j = Some B)
      by (unfold j; rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    assert (Hpk : tele_prefix_rel (canon_args_rel D ups k ns c) j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws))
                    (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws)))
      by (eapply nonrec_prefix_pre; [ exact Hv | lia | exact Heq ]).
    destruct (HeA _ _ _ _ _ _ _ _ HMk Hns Hcon HBk Hpk) as [b Hb].
    pose proof (HAP _ _ _ _ _ _ _ _ _ HMk Hns Hcon HBk Hpk Hb) as Hgb.
    (** The two values of the argument's type. *)
    assert (Hrel : exists k0 : uidx, Dom a1 ≈ b ∈ per_univ k0).
    { destruct (vg_cargs_sem_all p D Hg Hcv k Mk c gs HMk Hcon hs1 (ca_arg B :: hs2) Heq) as [HC1 _].
      destruct (cargs_suffix_glu p D Mk gs hs1 (ca_arg B :: hs2) Heq HΨ) as [Sb1 HSb1].
      assert (HgA1 : glu_args Δ (cargs_ctx p D Mk hs1) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns))
                       (List.firstn (List.length hs1) As) (List.firstn (List.length hs1) ws)).
      { pose proof HgA as HgA'.
        rewrite (cargs_split_aux p D Mk gs hs1 (ca_arg B) hs2 Heq), <- (List.firstn_skipn (List.length hs1) As),
          <- (List.firstn_skipn (List.length hs1) ws) in HgA'.
        apply glu_args_app in HgA'; [ exact (proj1 HgA') | apply cargs_ctx_aux_ass | |];
          rewrite List.length_firstn, length_cargs_ctx; lia. }
      assert (HgPA : glu_args Δ (cargs_ctx p D Mk hs1 ++ im_params D Mk) Id nil ((Us ++ Ns) ++ List.firstn (List.length hs1) As)
                       ((ups ++ ns) ++ List.firstn (List.length hs1) ws)).
      { destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP' LB'].
        apply glu_args_app; [ exact HassP | exact LP' | exact LB' |]; split; [ exact HgP | exact HgA1 ]. }
      pose proof (glu_args_per_gargs _ _ _ _ _ ltac:(apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ])
                    HC1 HΔ HSb1 HgPA) as Hgp.
      rewrite <- List.app_assoc in Hgp.
      destruct (vg_arg_types p D Hg Hcv k Mk c gs hs1 B hs2 ups ns (List.firstn (List.length hs1) ws) HMk Hcon Heq Hu LNn
                  ltac:(rewrite List.length_firstn; lia) Hgp) as (i0 & R0 & a & a' & Ea & Ea' & HR0).
      rewrite <- env_args_app in Ha1.
      assert (a = a1) as -> by (rewrite List.app_assoc in Ea; eapply functional_eval_exp; eassumption).
      assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
      exists (ul i0); eexists; exact HR0. }
    destruct Hrel as [k0 Hrel].
    assert (HTP : Δ ⊢ T ® AP k ns c j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) ws))).
    { eapply (HCA k Mk c gs hs1 B hs2 Ns ns As (List.firstn (List.length hs1) ws) T HMk Hcon Heq Hnp Hns);
        [ rewrite List.length_firstn; lia | exact HT | | exact Hpk ].
      intros hs1' B' hs2' N' T' v' Heq1 HN' HT' Hv'.
      assert (Hlt' : List.length hs1' < List.length hs1) by (rewrite Heq1, List.length_app; cbn; lia).
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1') (List.length hs1)); [| discriminate ].
      eapply (IH hs1' B' (hs2' ++ ca_arg B :: hs2)); [ lia | rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ]. }
    eapply glu_univ_elem_exp_conv_uidx; [ exact Hrel | exact Hglu' | exact Hgb | exact HM' | exact HTP ].
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
      Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nv ++ ys) ∈ SbC ->
      ⟦ ptyp_ps t ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nv ++ ys) ↘ bsr ->
      glu_args Δ (im_nparams Mj) (sb_of_list Id Us) (env_args nil ups)
        (List.map (fun P => P[sb_of_list τ (Us ++ Ys)]) (ptyp_ps t)) bsr.
  Proof.
    intros Δ gs1 t gs2 Mj τ Us Ys ns nv ys SbC bsr Heq HMj HUl HYl Hnsl Hnvl Hysl HSbC Hσ Hbsr.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (L := ptyp_depth t + K + im_nn Mk) in *.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (ρ := env_args nil (ups ++ ns ++ nv ++ ys)) in *.
    destruct (length_rec_ps D HD k Mk HMk c gs gs1 t gs2 Hcon Heq) as (Mj' & HMj' & HPl).
    rewrite HMj in HMj'; injection HMj' as <-.
    pose proof (eval_exps_length _ _ _ Hbsr) as Hbl.
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    constructor; [ rewrite List.length_map, length_im_nparams; exact HPl | rewrite length_im_nparams; lia |].
    intros m M T v A HM HT Hv HA.
    rewrite List.nth_error_map in HM.
    destruct (List.nth_error (ptyp_ps t) m) as [P |] eqn:HP; [ injection HM as <- | discriminate ].
    assert (Hm : m < im_nn Mj) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) (ptyp_ps t)) m) as [Tk HTk].
    { rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMj); rewrite length_im_nparams; lia. }
    pose proof (rec_tele_inst D (ptyp_mem t) Mj (ptyp_ps t) L τ Us Ys m Tk Hc HMj HUl HYl HTk) as HT'.
    fold σ in HT'; rewrite HT in HT'; injection HT' as ->.
    destruct (tele_insts_nth _ _ _ _ _ HTk) as (A0 & HA0 & ETk).
    rewrite HA in HA0; injection HA0 as <-.
    destruct (gid_rec _ HG _ _ _ _ _ _ _ _ _ _ _ HMk Hcon Heq HMj HP HTk) as [SbC' HSbC' j HV].
    pose proof (functional_glu_ctx_env HSbC HSbC') as ESb.
    assert (Hσ' : Δ ⊢ˢ σ ® ρ ∈ SbC') by (apply ESb; exact Hσ).
    destruct (HV _ _ _ Hσ') as [a1 m1 P1 El1 Ha1 Hm1 Hg1 HM1].
    destruct (eval_exps_nth _ _ _ _ _ Hbsr HP) as (v' & Hv' & Ev').
    rewrite Hv in Hv'; injection Hv' as <-.
    assert (m1 = v) as -> by (eapply functional_eval_exp; eassumption).
    (** The value of the type of the parameter, at the arguments' values, is
        related to the one at the parameters' before it. *)
    destruct (vid_npar _ HD _ _ _ _ HMj HA) as (_ & j0 & HAv).
    assert (HΞ0 : ⊨ ptyp_tele t ++ nonrec_args_prefix gs K ++ im_params D Mk).
    { pose proof (vid_dctx _ HD _ _ _ _ _ _ _ (List.length (ptyp_doms t)) HMk Hcon Heq (le_n _)) as H.
      rewrite List.firstn_all in H; exact H. }
    destruct (rel_ctx_wf_per_ctx_env HΞ0) as [R0 HR0].
    pose proof (glu_ctx_env_per_env HSbC' HR0 Hσ') as HE.
    pose proof (rec_sub_valid D HD Hc k Mk c gs HMk Hcon gs1 t gs2 Mj Heq HMj m (Nat.lt_le_incl _ _ Hm)) as Hτ.
    assert (Hτev : ⟦ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps t)) ⟧s ρ ↘ env_args (env_args nil ups) (List.firstn m bsr)).
    { apply Decl.eval_sb_of_list; [| apply eval_exps_firstn; exact Hbsr ].
      replace (env_args nil ups) with (⟪wk_shiftn L⟫ ρ); [ apply eval_sub_of_wk; apply Completeness.UnitCases.wk_mono_shiftn |].
      unfold ρ, L; rewrite env_args_app.
      replace (ptyp_depth t + K + im_nn Mk) with (List.length (ns ++ nv ++ ys)) by (rewrite !List.length_app; unfold ptyp_depth in *; lia).
      apply Completeness.UnitCases.eval_wk_shiftn_args. }
    destruct (Completeness.LogicalRelation.Telescope.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HR0 Hτ HE Hτev) as (a & b & Ea & Eb & Hab).
    fold K L in Ea; rewrite <- ETk in Ea.
    assert (a = a1) as -> by (eapply functional_eval_exp; eassumption).
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
    destruct (Decl.per_gargs_top _ _ _ _ _ Hgu ltac:(rewrite List.length_rev; exact Hu) s) as (Ms1 & HM1 & HM1').
    pose proof (canon_hn D HD Hc Hsu ups bu Hu Hbu ups Hgu) as Hn.
    assert (Hassn : tele_ass (List.rev (im_nparams Mj))) by (apply List.Forall_rev; exact (gta_nparams _ Hass _ _ HMj)).
    destruct (read_ps_tele (List.rev (im_nparams Mj)) (canon_nparams_rel D ups j) (env_args nil ups) (env_args nil ups) Hassn
                ltac:(intros j0 A pre pre' Hj0 Hp; rewrite <- !env_args_app;
                      destruct (canon_nparams_evals _ _ _ _ Hn _ _ _ _ _ _ HMj Hj0 Hp) as [a a' Ea Ea' HRa];
                      exists a, a'; split; [ exact Ea | split; [ exact Ea' | intros b b' Hb; exact (per_elem_then_per_top HRa Hb) ] ])
                _ _ Hbs s) as (Ms2 & HM2 & HM2').
    exists (nfs_app Ms1 Ms2); rewrite rev_im_params_split; split; apply read_ps_app; assumption.
  Qed.

  (** A recursive argument ending in a declared member [j]: of the type of
      [j] at parameters glued to related values, an element of [j] at
      every weakening and every instance of the parameters equal to them. *)
  Lemma rec_end_decl : forall j Mj pm Δ Us Q N v (i : uidx) P El bs bs1, ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      ⊢ Δ -> tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs1 ->
      DG d_ind p j (ups ++ bs1) ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ N : im_ty_at p j Mj Us Q ® v ∈ El ->
      glu_args Δ (im_params D Mj) Id nil (Us ++ Q) (ups ++ bs) -> List.length Us = ind_nu D ->
      forall Δ' φ Us' Q', Δ' ⊢ᵏ φ : Δ -> List.length Us' = ind_nu D ->
        exps_eq_at Δ' (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
        ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' Q' N[φ]ʷ v.
  Proof.
    intros * HMj Hh HΔ Hbs Hgl HN HQp HUl Δ' φ Us' Q' Hφ HUl' HE.
    pose proof con_canon as Hcp.
    assert (Hlt : j < ind_ndecl D) by (eapply decl_member_lt; eassumption).
    pose proof (decl_closed_params_ass D j Mj Hc HMj) as HassP.
    pose proof (decl_closed_params D j Mj Hc HMj) as Hs.
    assert (Hbb : tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs)
      by exact (canon_nparams_rel_trans p D ups Hass Hcp _ _ _ _ _ HMj Hbs (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hbs)).
    pose proof (ind_relate D HD Hc Hsu p Hl Hass j Mj pm ups ups bs bs bu HMj Hh Hgu Hu Hbu Hbb) as HRq0.
    pose proof (per_univ_elem_cumu_uidx _ _ _ _ HRq0 _ Hule) as HRq.
    destruct (ind_glu_of_per p D Hl u _ j Mj pm ups bs HMj Hh HRq Hu)
      as [NP2 NEl2 AP2 AEl2 DP2 DEl2 P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf2].
    assert (HT2 : Δ ⊢ im_ty_at p j Mj Us Q ® P2).
    { apply HP2; exists (Us ++ Q).
      unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
      exact (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Hass j Mj Δ (Us ++ Q) ups bs bu u NP2 NEl2 AP2 AEl2 DP2 DEl2 HMj Hlt HΔ HQp
               Hu Hbu Hule Hf2). }
    pose proof (ind_relate D HD Hc Hsu p Hl Hass j Mj pm ups ups bs1 bs bu HMj Hh Hgu Hu Hbu
                  (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hbs)) as Hab.
    pose proof (glu_univ_elem_exp_conv_uidx (per_univ_of_elem _ _ _ _ Hab) Hgl Hg2 HN HT2) as HM2.
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
      destruct (nparams_lt_ass D m0 Mm0 k0 Hass HM0 ltac:(rewrite List.length_rev, length_im_nparams; exact Hk')) as [S HS].
      destruct (HeN _ _ _ _ _ HM0 HS Hp0) as [b Eb].
      destruct (functional_glu_univ_elem _ _ _ _ _ _ (ifg_npar_glu _ _ _ _ _ _ _ _ _ Hf2 _ _ _ _ _ _ HM0 HS Hp0 Eb)
                  (HNP _ _ _ _ _ _ HM0 HS Hp0 Eb)) as [_ EE].
      apply EE; exact HN0.
    - intros m0 Mm0 ms c0 gs0 k0 vs HM0 Hm Hc0 Hk' Hp0 Γ0 A0 M0 m1 HN0.
      destruct (nth_error_lt_some' _ _ Hk') as [S HS].
      destruct (HeA _ _ _ _ _ _ _ _ HM0 Hm Hc0 HS Hp0) as [b Eb].
      destruct (functional_glu_univ_elem _ _ _ _ _ _ (ifg_arg_glu _ _ _ _ _ _ _ _ _ Hf2 _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 HS Hp0 Eb)
                  (HAP _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 HS Hp0 Eb)) as [_ EE].
      apply EE; exact HN0.
    - intros m0 Mm0 ms c0 gs0 gs3 t0 gs4 ws k0 B ys0 HM0 Hm Hc0 Heq0 Hw HB Hy1.
      destruct (HeD _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 Heq0 Hw HB Hy1) as [b Eb].
      destruct (functional_glu_univ_elem _ _ _ _ _ _ (ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf2 _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 Heq0 Hw HB Hy1 Eb)
                  (HDP _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc0 Heq0 Hw HB Hy1 Eb)) as [EP EE].
      split; intros; [ apply EP | apply EE ]; assumption.
  Qed.

End ConGlu.

End Fixed_GCtx.
