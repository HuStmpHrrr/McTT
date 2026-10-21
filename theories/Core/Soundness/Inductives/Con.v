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

  (** A recursive argument of a constructor, after [kk] of its shape's
      domains: an element of the type of the rest of the shape, at a glued
      instance of the shape's context (on the side of the non-recursive
      arguments, [σ], and on the one of all the arguments, [σc]), is a
      recursive argument of the rest of the shape. *)
  Lemma con_rec_glu : forall gs1 t gs2 ns fa, gs = gs1 ++ ca_rec t :: gs2 ->
      List.length ns = im_nn Mk -> List.length fa = List.length gs1 ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa) ->
      (forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
         R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
      forall t' kk ys Δ τ Us Ys SbC σc Sbc N v a (i : uidx) P El,
        ptyp_skip kk t = t' -> kk <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel ups k) ns (nonrec_arg_vals gs1 fa) (ptyp_doms t)) kk ys ys ->
        per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
          (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
        ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
        List.length Ys = kk + List.length (cargs_nonrec gs1) + im_nn Mk ->
        EG doms_ctx (List.firstn kk (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
          ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nonrec_arg_vals gs1 fa ++ ys) ∈ SbC ->
        EG sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ glu_ctx_env ↘ Sbc ->
        Δ ⊢ˢ σc ® env_args nil (ups ++ ns ++ fa ++ ys) ∈ Sbc ->
        ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) t' = (ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) t')[σc] ->
        ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) t' ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) t' ® P ->
        Δ ⊢ N : ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) t' ® v ∈ El ->
        glu_rec p D ups NEl AEl DP DEl k Δ Us (ns ++ nonrec_arg_vals gs1 fa ++ ys) t' (ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) t') N v.
  Proof.
    intros gs1 t gs2 ns fa Heq Hlns Hlfa Hnsd Hp INV.
    pose proof con_canon as Hcp.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    destruct (vg_cargs_sem_all p D Hg Hcv k Mk c gs HMk Hcon gs1 (ca_rec t :: gs2) Heq) as [HC1 Hw1].
    assert (HassC1 : tele_ass (cargs_ctx p D Mk gs1 ++ im_params D Mk))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    (** The arguments before, related. *)
    assert (Hgall0 : per_gargs (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
    { destruct (rel_ctx_wf_per_ctx_env HC1) as [R1 HR1].
      assert (HC' : ⊨ List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HC1).
      assert (HR' : EF List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅
                      ≈ List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅ ∈ per_ctx_env ↘ R1)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HR1).
      assert (Hl0 : List.length (ups ++ ns ++ fa) = List.length (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)))
        by (rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx, length_im_params, Hu, Hlns, Hlfa;
            unfold im_np, ind_nu in *; lia).
      exact (proj2 (Decl.rel_gargs _ _ _ _ Args.per_ctx_env_nil_true HC' (List.Forall_rev HassC1) HR' nil nil _ _ Hl0 Hl0 (INV _ HR1))). }
    pose proof (Completeness.Inductives.Con.view_end_rel_all VP p D HVP HPD ups ups Hgu Hu (ptyp_mem t)) as Hend.
    set (nv := nonrec_arg_vals gs1 fa) in *.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (pat := cargs_pat gs1) in *.
    assert (Hlnv : List.length nv = K) by (apply length_nonrec_arg_vals; exact Hlfa).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (Hgall : forall kk ys, List.length ys = kk ->
               per_gargs (List.rev (sh_ctx pat (List.firstn kk (ptyp_doms t))))
                 (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
               per_gargs (List.rev (sh_ctx pat (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)) nil nil
                 (ups ++ ns ++ fa ++ ys) (ups ++ ns ++ fa ++ ys)).
    { intros kk ys Hly Hgy.
      rewrite List.rev_app_distr.
      replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      apply Decl.per_gargs_app_intro; [| exact Hgall0 | exact Hgy ].
      rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx, length_im_params, Hu, Hlns, Hlfa;
        unfold im_np, ind_nu in *; lia. }
    induction t' as [j0 Ps0 | B t'' IH];
      intros kk ys Δ τ Us Ys SbC σc Sbc N v a i P El Hsk Hk Hy Hgy HΔ HUs HYl HSbC Hσ HSbc Hσc HTeq Ea Hgl HTP HN.
    2:{ (** A domain: an element of the domain's gluing, moved to the gluing
            of the [Π]'s domain, applied to the argument gives a recursive
            argument of the rest of the shape. *)
        destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hs'].
        assert (Hkl : kk < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
        assert (HUl : List.length Us = ind_nu D) by (destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _]; exact LU).
        (** The rest of the shape's type is glued at the domains' gluings. *)
        pose proof (shape_typ_glu p D HG Hc Hdt Hsu ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf k Mk c gs gs1 t gs2 ns nv
                      HMk Hcon Heq Hnsd Hp Hlns Hlnv (pt_pi B t'') kk ys Δ τ Us Ys SbC Hsk Hk Hy HΔ HUl HYl HSbC Hσ) as Hsh.
        cbn [ptyp_ty ptyp_ty_at exp_sub glu_shape_typ] in Ea, HTeq, HTP, HN, Hsh |- *.
        destruct (Hsh _ _ eq_refl) as [HshD _].
        injection HTeq as HITeq HOTeq.
        destruct (vg_dom_types p D Hg Hcv k Mk c gs gs1 t gs2 kk B ups ns fa ys HMk Hcon Heq HB Hu Hlns Hlfa Hly (Hgall kk ys Hly Hgy))
          as (jd & Rab & a1 & b0 & Ea1 & Eb0 & HRab).
        inversion Ea; subst a.
        match goal with H : ⟦ B[wk_pat _]ʷ ⟧ _ ↘ ?x |- _ => assert (x = a1) as -> by (eapply functional_eval_exp; eassumption) end.
        set (σ := sb_of_list τ (Us ++ Ys)) in *.
        set (E := env_args nil (ups ++ ns ++ fa ++ ys)) in *.
        (** A level above the ones at hand. *)
        set (n := ul (Nat.max (ulvl i) (Nat.max (ulvl u) jd))).
        assert (Hin : uidx_le i n) by (apply uidx_le_ul_max; unfold n; lia).
        assert (Hun : uidx_le u n) by (apply uidx_le_ul_max; unfold n; lia).
        assert (Hjn : uidx_le (ul jd) n) by (apply uidx_le_ul_max; unfold n; cbn; lia).
        destruct (glu_univ_elem_cumu_ge_uidx Hin Hgl) as (Pn & Eln & Hgn).
        pose proof (glu_univ_elem_typ_cumu_ge_uidx Hin Hgl Hgn HTP) as HTPn.
        pose proof (glu_univ_elem_exp_cumu_ge_uidx Hin Hgl Hgn HN) as HNn.
        pose proof (per_univ_trans _ _ _ _ _ _ HRab (per_univ_sym _ _ _ _ HRab)) as HRaa.
        pose proof (per_univ_elem_cumu_uidx _ _ _ _ HRaa _ Hjn) as HRaan.
        destruct (glu_univ_elem_pi_clean_inversion1 HRaan Hgn) as (IP & IEl & OP & OEl & elem_rel & HgI & HgO & Hper & EP & EEl).
        apply EEl in HNn.
        inversion_clear HNn as [? ? ? ? IT2 OT2 HMt Hm HAeq HITt HOTt HIP HApp].
        pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hnsd Hcon Heq Hp HB Hy Eb0) as Hgb0.
        (** An argument glued at the domain's gluing, at the [Π]'s domain. *)
        assert (Hdom : forall Δ' φ b c', Δ' ⊢ᵏ φ : Δ -> canon_doms_rel ups k (ns ++ nv ++ ys) B c' c' ->
                  Δ' ⊢ b : B[σ][φ]ʷ ® c' ∈ DEl k (ns ++ nv ++ ys) B ->
                  Rab c' c' /\ Δ' ⊢ B[σ][φ]ʷ ® IP /\ Δ' ⊢ b : B[σ][φ]ʷ ® c' ∈ IEl /\ Δ' ⊢ b : IT2[φ]ʷ ® c' ∈ IEl).
        { intros Δ' φ b c' Hφ Hc' Hb.
          pose proof (dr_to_rel B _ b0 a1 c' (ul jd) Rab (ul jd) Eb0 (per_univ_of_elem _ _ _ _ HRab) HRaa Hc') as Hcc.
          pose proof (glu_typ_transfer u n (ul jd) b0 a1 _ _ IP IEl Δ' _ Hun Hjn (per_univ_sym' _ _ _ (per_univ_of_elem _ _ _ _ HRab))
                        Hgb0 HgI (HshD _ _ Hφ)) as HTyI.
          pose proof (glu_univ_elem_exp_conv_uidx (per_univ_sym' _ _ _ (per_univ_of_elem _ _ _ _ HRab)) Hgb0 HgI Hb HTyI) as HbI.
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
          destruct (gid_dctx _ HG _ _ _ _ _ _ _ (S kk) HMk Hcon Heq ltac:(lia)) as [SbC' HSbC'].
          pose proof (HshD _ _ Hφ) as HTy0.
          pose proof (shape_sub_step D ups u DP DEl k Mk c gs gs1 t gs2 kk B ns nv ys Δ τ Us Ys SbC SbC' Δ' φ b b0 c'
                        HMk Hcon Heq HB HSbC HSbC' Hσ Hφ Eb0 Hgb0 HTy0 Hb) as Hσ'.
          destruct (HshV gs1 t gs2 (S kk) Heq ltac:(lia)) as [jv HVv].
          pose proof HVv as [Sbc' HSbc' _ _].
          pose proof HSbc' as HSbc''.
          rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l in HSbc'' by lia.
          cbn [List.app] in HSbc''.
          assert (Hσc' : Δ' ⊢ˢ (sb_wk σc φ),,b ® E ↦ c' ∈ Sbc').
          { eapply glu_sub_snoc; [ exact HSbc | exact HSbc'' | eapply glu_ctx_env_sub_monotone; eassumption |].
            fold pat; rewrite <- exp_wk_sub, <- HITeq.
            exact (mk_glu_arg _ _ _ _ _ _ n a1 IP IEl Ea1 HgI HTyI HbI0). }
          (** The type of the rest, and its value. *)
          assert (HTeq' : ptyp_ty_at p D (List.map (fun U => U[φ]ʷ) Us)
                            (sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))) t''
                          = (ptyp_ty p D (im_nn Mk) (List.repeat false (S kk) ++ pat) t'')[(sb_wk σc φ),,b]).
          { rewrite <- ptyp_ty_at_shape_step by assumption; fold σ; rewrite HOTeq, exp_sub_sub.
            apply exp_sub_sb_eq, sb_q_extend_wk. }
          destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbc' HVv Hσc') as (_ & a2 & Ea2 & Hpa2 & HXP).
          rewrite Hs' in Ea2, HXP; fold pat in Ea2, HXP.
          destruct (per_univ_glu_univ_elem _ _ Hpa2) as (P2 & El2 & Hga2).
          pose proof (HXP _ _ Hga2) as HXP2.
          pose proof (HgO c' Hcc a2 Ea2) as HgOc.
          pose proof (glu_univ_elem_trm_typ _ _ _ _ HgOc _ _ _ _ Happ) as HOT2P.
          pose proof (glu_elem_retype n jv a2 _ _ P2 El2 Δ' _ _ _ _ HgOc Hga2 HOT2P Happ HXP2) as Happ'.
          rewrite <- HTeq' in HXP2, Happ'.
          unfold σ; rewrite ptyp_ty_at_shape_step by assumption.
          replace ((ns ++ nv ++ ys) ++ c' :: nil) with (ns ++ nv ++ ys ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
          apply (IH (S kk) (ys ++ c' :: nil) Δ' (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us) (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil)
                   SbC' ((sb_wk σc φ),,b) Sbc' (a_app N[φ]ʷ b) mn a2 jv P2 El2);
            [ exact Hs' | lia | | | exact HΔ' | | rewrite List.length_app, List.length_map; cbn; lia | exact HSbC' | exact Hσ'
            | exact HSbc' | | exact HTeq' | | exact Hga2 | exact HXP2 | exact Happ' ].
          * apply tele_prefix_rel_snoc; [ exact Hy |].
            unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hc'.
          * rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
            cbn [List.rev].
            apply (Decl.per_gargs_snoc _ _ _ _ _ _ _ _ jd Rab);
              [ rewrite List.length_rev, length_sh_ctx, List.length_firstn; lia | exact Hgy | | exact Hcc ].
            rewrite <- !env_args_app, <- !List.app_assoc.
            exact (mk_rel_mod_eval a1 a1 Ea1 Ea1 HRaa).
          * exact (glu_args_wk _ _ _ _ _ _ _ (dc_ass _ Hc) (dc_uparams _ Hc) Hφ HUs).
          * replace (ups ++ ns ++ fa ++ ys ++ c' :: nil) with ((ups ++ ns ++ fa ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc; exact Hσc'.
          * replace (ups ++ ns ++ fa ++ ys ++ c' :: nil) with ((ups ++ ns ++ fa ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc; exact Ea2. }
    (** The end of the shape. *)
    destruct (ptyp_skip_self _ _ _ _ Hsk) as (HkL & <- & <-).
    assert (Hkd : kk = List.length (ptyp_doms t)) by lia.
    pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
    cbn [ptyp_ty ptyp_ty_at] in Ea, HTP, HN |- *.
    destruct (length_rec_ps D HD k Mk HMk c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HPl).
    pose proof (Hgall kk ys Hly Hgy) as Hgall_end.
    rewrite Hkd, List.firstn_all in Hgall_end.
    pose proof Hy as Hy'; rewrite Hkd in Hy'.
    destruct (shape_end_params_link p D Hg k Mk c gs HMk Hcon HΨs gs1 t gs2 Heq ups ns fa ys Hu Hlns Hlfa Hgu Hnsd Hp Hgall_end Hy')
      as [bs bs1 Ebs Ebs1 Hrel].
    unfold ntele_rel in Hrel; rewrite HMj in Hrel.
    rewrite <- Hkd in Ebs1.
    destruct (eval_mty_inv p D (ptyp_mem t) Mj _ _ _ _ HMj Ea) as (cs & bs0 & Ecs & Ebs0 & ->).
    pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs1) as ->.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (Qn := List.map (fun P => P[σ]) (ptyp_ps t)) in *.
    assert (HUl : List.length Us = ind_nu D) by (destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _]; exact LU).
    assert (HSbCt : EG ptyp_tele t ++ nonrec_args_prefix gs K ++ im_params D Mk ∈ glu_ctx_env ↘ SbC)
      by (rewrite Hkd, List.firstn_all in HSbC; exact HSbC).
    assert (HQn : glu_args Δ (im_nparams Mj) (sb_of_list Id Us) (env_args nil ups) Qn bs).
    { unfold Qn, σ.
      eapply rec_params_args; try eassumption; unfold ptyp_depth; lia. }
    pose proof (decl_closed_params_ass D (ptyp_mem t) Mj Hc HMj) as HassPj.
    pose proof (decl_closed_params D (ptyp_mem t) Mj Hc HMj) as HsPj.
    assert (HQp : glu_args Δ (im_params D Mj) Id nil (Us ++ Qn) (ups ++ bs)).
    { unfold im_params; apply glu_args_app; [ exact (dc_ass _ Hc) | exact HUl | exact Hu |].
      split; [ exact HUs | exact HQn ]. }
    pose proof (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Δ Us HΔ HUs) as Hcomps.
    assert (H01 : tele_rel (canon_nparams_rel D ups (ptyp_mem t)) (List.rev (im_nparams Mj)) bs bs)
      by exact (canon_nparams_rel_trans p D ups Hass Hcp _ _ _ _ _ HMj Hrel (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hrel)).
    pose proof (nparams_of_glu_args p D Hass ups u NP NEl AP AEl DP DEl Hu Hf _ _ Δ Us Qn bs HMj Hcomps HQn H01) as HnQ.
    assert (HQl : List.length Qn = im_nn Mj) by (unfold Qn; rewrite List.length_map; exact HPl).
    assert (EQ : forall Q, ind_mty p D (ptyp_mem t) Us Qn = im_ty_at p (ptyp_mem t) Mj Us Q -> Q = Qn).
    { intros Q HQ; unfold ind_mty in HQ; rewrite HMj in HQ; unfold im_ty_at in HQ.
      apply apps_ind_inj, List.app_inv_head in HQ; congruence. }
    assert (HN' : Δ ⊢ N : im_ty_at p (ptyp_mem t) Mj Us Qn ® v ∈ El) by (unfold ind_mty in HN; rewrite HMj in HN; exact HN).
    assert (HTP' : Δ ⊢ im_ty_at p (ptyp_mem t) Mj Us Qn ® P) by (unfold ind_mty in HTP; rewrite HMj in HTP; exact HTP).
    apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
    - intros bsr Q Hbsr HQ.
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      pose proof (EQ _ HQ) as ->.
      split; [ exact HQl | split; [ exact H01 |] ].
      intros bsr' Hb'.
      split; [ exact (glu_nparams_resp_per D ups NEl nel_resp_per _ _ _ _ _ _ _ HMj Hb' HnQ) |].
      intros Δ0 φ Hφ.
      pose proof (glu_args_params_top _ _ _ _ _ HassPj HsPj (glu_args_wk _ _ _ _ _ _ _ HassPj HsPj Hφ HQp)) as Ht.
      exact (glu_params_top_resp_per_top_ps _ _ _ _ _ _ (canon_params_per_top _ _ _ _ HMj Hb') Ht).
    - intros bsr Q Hbsr HQ Δ' φ Us' Q' Hφ HUl' HQ'.
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      pose proof (EQ _ HQ) as ->.
      destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh.
      + (** A declared member: the uniform arguments are [ups]. *)
        assert (HU : ⟦ im_pre Mj (ind_uvars D (im_nn Mk) (List.length (List.repeat false kk ++ pat))) ⟧* gc_deps ⍮ gc_stack
                       ⍮ env_args nil (ups ++ ns ++ fa ++ ys) ↘ ups).
        { unfold im_pre, ind_uvars; rewrite Hh.
          replace (List.length (List.repeat false kk ++ pat) + im_nn Mk) with (List.length (ns ++ fa ++ ys))
            by (unfold pat; rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia).
          rewrite <- Hu; apply Decl.eval_vars_from_args. }
        pose proof (functional_eval_exps' _ _ _ _ Ecs HU) as ->.
        unfold im_ref in Hgl; rewrite Hh in Hgl; cbn [fst snd] in Hgl.
        exact (rec_end_decl (ptyp_mem t) Mj pm Δ Us Qn N v i P El bs bs1 HMj Hh HΔ Hrel Hgl HN' HQp HUl Δ' φ Us' Q' Hφ HUl' HQ').
      + (** A view: by its coherence with its container. *)
        destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & _).
        set (Z := sh_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk).
        assert (EZ : Z ++ ind_uparams D = sh_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)
          by (unfold Z, im_params; rewrite <- !List.app_assoc; reflexivity).
        assert (HZ : ⊨ Z ++ ind_uparams D).
        { rewrite EZ.
          pose proof (sh_sem_gen D p k Mk c gs HD HMk Hcon gs1 t gs2 Heq HC1 Hw1 (List.length (ptyp_doms t)) (le_n _)) as H.
          rewrite List.firstn_all in H; exact H. }
        destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
        assert (HlZ : List.length (ns ++ fa ++ ys) = List.length Z)
          by (unfold Z; rewrite !List.length_app, length_sh_ctx, length_cargs_ctx, length_im_nparams; lia).
        assert (HE : RZ (env_args nil (ups ++ ns ++ fa ++ ys)) (env_args nil (ups ++ ns ++ fa ++ ys))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRZ HZ); [ rewrite !List.length_app, <- HlZ, !List.length_app, Hu; unfold ind_nu; lia |].
          rewrite EZ; exact Hgall_end. }
        destruct (view_pre_values p D Hg Hcv (ptyp_mem t) Mj qc kc Is vm Dq ups Z RZ (ns ++ fa ++ ys) (im_nn Mk)
                    (List.length (List.repeat false kk ++ pat)) cs HMj Hh Hq Hu Hgu HZ HRZ HlZ
                    ltac:(unfold pat; rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia) HE Ecs)
          as (cups & Ecups & Hgc).
        unfold im_ref in Hgl, Ea; rewrite Hh in Hgl, Ea; cbn [fst snd] in Hgl, Ea.
        (** The element's value is in the group's relation at the view. *)
        destruct (glu_univ_elem_per_univ _ _ _ _ Hgl) as [Ra HRa].
        pose proof (glu_univ_elem_per_elem _ _ _ _ Hgl _ _ _ _ _ HN' HRa) as Hva.
        assert (Ea' : ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ pat) (ptyp_skip kk t) ⟧ env_args nil (ups ++ ns ++ fa ++ ys)
                        ↘ d_ind qc kc (cs ++ bs1)).
        { rewrite Hsk; cbn [ptyp_ty]; exact Ea. }
        pose proof (shape_char p D Hg Hcv k Mk c gs HMk Hcon HΨs gs1 t gs2 Heq ups ns fa Hu Hlns Hlfa Hgu Hnsd Hp INV Hend
                      0 kk ys _ _ _ ltac:(lia) Hy Hgy Ea' HRa) as ERa.
        apply ERa in Hva; rewrite Hsk in Hva.
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hva) as (bs2 & bs3 & Ebs2 & Ebs3 & _ & _ & Hgv).
        pose proof (functional_eval_exps' _ _ _ _ Ebs2 Ebs) as ->; pose proof (functional_eval_exps' _ _ _ _ Ebs3 Ebs) as ->.
        exact (Hview (ptyp_mem t) Mj qc kc Is vm Dq cups cs bs bs1 Δ Us Qn N v i P El HMj Hh Hq Ecups Hgc Hrel Hgl HTP' HN' Hgv HQp
                 Δ' φ Us' Q' Hφ HUl' HQ').
  Qed.

  (** A constructor applied to parameters and arguments glued along its
      telescopes is an element of its member, at any stored uniform
      arguments [cs]. *)
  Lemma con_ind_glu_elem : forall Δ Us Ns As ns ws cs, ⊢ Δ -> List.length Us = ind_nu D ->
      glu_args Δ (im_params D Mk) Id nil (Us ++ Ns) (ups ++ ns) ->
      glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns)) As ws ->
      List.length cs = im_unu D Mk ->
      ind_glu_elem p D ups NEl AEl DP DEl k Δ Us Ns (apps (a_con p k c) (Us ++ Ns ++ As))
        (d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c ((cs ++ ns) ++ ws)).
  Proof.
    intros Δ Us Ns As ns ws cs HΔ HUl HgP HgA Hcs.
    pose proof con_canon as Hcp.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (decl_closed_params D k Mk Hc HMk) as Hs.
    pose proof (dc_ass _ Hc) as HassU.
    assert (HassCP : tele_ass (cargs_ctx p D Mk gs ++ im_params D Mk))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP LV]; rewrite length_im_params in LP, LV.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    assert (LN : List.length Ns = im_nn Mk) by (rewrite List.length_app in LP; unfold im_np in LP; lia).
    assert (Lns : List.length ns = im_nn Mk) by (rewrite List.length_app in LV; unfold im_np in LV; lia).
    pose proof HgP as HgP'; unfold im_params in HgP'.
    apply glu_args_app in HgP' as [HUs HNs]; [| exact HassU | exact HUl | exact Hu ].
    (** The values related in the PER model. *)
    pose proof (gid_params _ HG _ _ HMk) as [SbP HSbP].
    pose proof (glu_args_per_gargs _ _ _ _ _ HassP (vid_params _ HD _ _ HMk) HΔ HSbP HgP) as Hgp.
    assert (HgPA : glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil ((Us ++ Ns) ++ As) ((ups ++ ns) ++ ws))
      by (apply glu_args_app; [ exact HassP | rewrite List.length_app, length_im_params; unfold im_np in *; lia
                              | rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | split; assumption ]).
    destruct HΨ as [SbCP HSbCP].
    pose proof (glu_args_per_gargs _ _ _ _ _ HassCP HΨs HΔ HSbCP HgPA) as Hgpa.
    rewrite List.rev_app_distr in Hgpa.
    destruct (Decl.per_gargs_app (List.rev (im_params D Mk)) (List.rev (cargs_ctx p D Mk gs)) nil nil (ups ++ ns) (ups ++ ns) ws ws
                ltac:(rewrite List.length_rev, length_im_params; exact LV) Hgpa
                ltac:(rewrite List.length_rev, length_im_params; exact LV)) as [_ Hga].
    pose proof (Completeness.Inductives.Con.con_rel VP p D HVP HPD k Mk c gs HMk Hcon (ups ++ ns) (ups ++ ns) ws ws Hgp
                  ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia) Hga LW cs cs Hcs Hcs) as Hrel.
    rewrite firstn_app_exact, skipn_app_exact in Hrel by exact Hu.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    destruct (ind_rel_con_inv p D ups _ _ _ Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel HMk
                ltac:(rewrite List.length_app; lia)) as (gs0 & bs' & vs' & Ez & Href & _ & Hc0 & Hbl' & Hnsr & _ & Hav & Hca).
    rewrite Hcon in Hc0; injection Hc0 as <-.
    injection Ez as Ez; apply app_split_eq in Ez as [<- <-]; [| rewrite List.length_app, Hbl'; lia ].
    rewrite skipn_app_exact in Hnsr, Hav, Hca by exact Hcs.
    pose proof (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Δ Us HΔ HUs) as Hcomps.
    pose proof (nparams_of_glu_args p D Hass ups u NP NEl AP AEl DP DEl Hu Hf k Mk Δ Us Ns ns HMk Hcomps HNs Hnsr) as Hnp.
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
      [ exact HMk | apply surjective_pairing | exact Hcon | exact HUl | exact LN | rewrite List.length_app; lia | exact LW | exact LA
      | exact HMt | | | | exact HAty | | ].
    all: rewrite ?skipn_app_exact by exact Hcs.
    - exact Hnsr.
    - exact Hav.
    - exact Hnp.
    - exact Harg.
    - (** A recursive argument: by its shape, from its gluing at its type. *)
      intros gs1 t gs2 N A v Heq HN HA Hv.
      set (fa := List.firstn (List.length gs1) ws).
      set (As1 := List.firstn (List.length gs1) As).
      assert (Hl1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      assert (Hlfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn; lia).
      assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      assert (Hpre1 : forall hs1 B hs2 N0 T' v0, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N0 ->
                List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
                List.nth_error fa (List.length hs1) = Some v0 ->
                Δ ⊢ N0 : T' ® v0 ∈ AEl k ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) fa))).
      { intros * Heq1 HN0 HT0 Hv0.
        assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
        unfold fa in Hv0 |- *; rewrite List.firstn_firstn, Nat.min_l by lia.
        rewrite List.nth_error_firstn in Hv0; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
        eapply (Harg hs1 B (hs2 ++ ca_rec t :: gs2)); [ rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN0 | exact HT0 | exact Hv0 ]. }
      pose proof (nonrec_prefix_pre _ gs ws gs1 (ca_rec t) gs2 Hav LW Heq) as Hp1; fold fa in Hp1.
      (** The arguments before, glued on the side of all the arguments. *)
      destruct (cargs_suffix_glu p D Mk gs gs1 (ca_rec t :: gs2) Heq (ex_intro _ SbCP HSbCP)) as [Sb1 HSb1].
      assert (HgA1 : glu_args Δ (cargs_ctx p D Mk gs1) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns)) As1 fa).
      { pose proof HgA as HgA''.
        rewrite (cargs_split_aux p D Mk gs gs1 (ca_rec t) gs2 Heq), <- (List.firstn_skipn (List.length gs1) As),
          <- (List.firstn_skipn (List.length gs1) ws) in HgA''.
        apply glu_args_app in HgA''; [ exact (proj1 HgA'') | apply cargs_ctx_aux_ass | |];
          rewrite List.length_firstn, length_cargs_ctx; lia. }
      assert (Hσc0 : Δ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ As1) ® env_args nil ((ups ++ ns) ++ fa) ∈ Sb1).
      { eapply glu_sub_of_list with (C := cargs_ctx p D Mk gs1 ++ im_params D Mk) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
          [ unfold tele_ass; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]
          | rewrite List.app_nil_r; exact HSb1 | eapply glu_ctx_env_nil; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
          | cbn; apply wf_sub_nil'; exact HΔ |].
        apply glu_args_app; [ exact HassP | rewrite List.length_app, length_im_params; unfold im_np in *; lia
                            | rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia |].
        split; [ exact HgP | exact HgA1 ]. }
      assert (INV : forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
                R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))).
      { intros R HR.
        pose proof (glu_ctx_env_per_env HSb1 HR Hσc0) as H.
        rewrite <- List.app_assoc in H; exact H. }
      (** The arguments before, glued on the side of the non-recursive ones. *)
      destruct (gid_dctx _ HG _ _ _ _ _ _ _ 0 HMk Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
      cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0.
      pose proof (nonrec_args_prefix_glu_sub p D Hc ups u NP NEl AP AEl DP DEl Hu Hf Δ Us HΔ HUs k Mk c gs gs1 (ca_rec t) gs2 Ns ns As
                    fa SbC0 HMk Hcon Heq Hnp Hnsr Hlfa ltac:(lia) Hpre1 Hp1 HSbC0) as Hσ0.
      (** The argument, glued at its type. *)
      pose proof HgA as [_ _ HgAe].
      destruct (HgAe _ _ _ _ _ HN HA Hv (cargs_rev_nth_rec p D Mk gs gs1 t gs2 Heq)) as [i' a1 P1 El1 Ha1 Hg1 HP1 HM1].
      fold fa in Ha1.
      pose proof (cargs_rec_type_sh p D Mk gs gs1 t gs2 (Us ++ Ns) As A Heq Hc
                    ltac:(rewrite List.length_app; unfold im_np in *; lia) HA) as ETs.
      pose proof (cargs_rec_type p D Mk gs gs1 t gs2 (sb_of_list Id (Us ++ Ns)) As A Heq HA) as ETc.
      fold As1 in ETs, ETc.
      rewrite <- sb_of_list_app in ETc.
      rewrite firstn_app_exact in ETs by exact HUl.
      rewrite <- List.app_assoc in ETs.
      assert (HlNs' : List.length (Ns ++ nonrec_exps gs1 As1) = 0 + List.length (cargs_nonrec gs1) + im_nn Mk)
        by (rewrite List.length_app, length_nonrec_exps by exact HlAs1; lia).
      assert (Hfinal : glu_rec p D ups NEl AEl DP DEl k Δ Us (ns ++ nonrec_arg_vals gs1 fa ++ nil) t
                         (ptyp_ty_at p D Us (sb_of_list Id (Us ++ (Ns ++ nonrec_exps gs1 As1))) t) N v).
      { eapply (con_rec_glu gs1 t gs2 ns fa Heq Lns Hlfa Hnsr Hp1 INV t 0 nil Δ Id Us (Ns ++ nonrec_exps gs1 As1)
                  SbC0 (sb_of_list Id ((Us ++ Ns) ++ As1)) Sb1 N v a1 i' P1 El1);
          [ reflexivity | lia | apply tele_prefix_rel_nil | constructor | exact HΔ | exact HUs | exact HlNs'
          | cbn [List.firstn doms_ctx List.map List.rev List.app]; exact HSbC0
          | rewrite !List.app_nil_r; rewrite <- !List.app_assoc in Hσ0; exact Hσ0
          | cbn [List.firstn sh_ctx List.app]; exact HSb1
          | rewrite !List.app_nil_r; replace (ups ++ ns ++ fa) with ((ups ++ ns) ++ fa) by (rewrite <- List.app_assoc; reflexivity); exact Hσc0
          | cbn [List.repeat List.app]; rewrite <- ETs, <- ETc; reflexivity
          | cbn [List.repeat List.app]; rewrite List.app_nil_r; rewrite <- env_args_app, <- List.app_assoc in Ha1; exact Ha1
          | exact Hg1
          | rewrite <- ETs; exact HP1
          | rewrite <- ETs; exact HM1 ]. }
      rewrite List.app_nil_r in Hfinal; rewrite ETs; exact Hfinal.
  Qed.

End ConGlu.

(** The views of a group cohere with their containers in the gluing model:
    at every uniform parameters related to themselves, at the families of
    the clause. *)
Definition glu_views_ok (p : qname) (D : ind_decl) : Prop :=
  forall ups bu (u : uidx) NP NEl AP AEl DP DEl, List.length ups = ind_nu D ->
    per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> ⟦ ind_sort D ⟧ env_args nil ups ↘ bu ->
    uidx_le (Completeness.Inductives.Decl.univ_idx bu) u -> ind_fams_glu D ups u NP NEl AP AEl DP DEl ->
    glu_view_end_ok p D ups NEl AEl DP DEl.

Lemma exps_eq_at_app_refl : forall Δ C1 C2 Xs Ys Zs, tele_ass C1 -> tele_ass C2 -> List.length Xs = List.length C1 ->
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
  Let Hl := vgr_lookup _ _ Hg.
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hsu := vgr_sort _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Let Hdt := vgr_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (pm : qname) (c : String.string) (gs : list carg).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_decl pm) (Hcon : ind_con Mk c = Some gs)
    (HΨ : ⊩ cargs_ctx p D Mk gs ++ im_params D Mk).
  Hypothesis (HshV : forall gs1 t gs2 kk, gs = gs1 ++ ca_rec t :: gs2 -> kk <= List.length (ptyp_doms t) ->
       exists j : nat, sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
         ⊩ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t) : Typeω@j).

  (** The universes of the sort, below a large one. *)
  Lemma sort_bound : exists n, forall ρ bu, ⟦ ind_sort D ⟧ ρ ↘ bu -> forall i, n <= i ->
      uidx_le (Completeness.Inductives.Decl.univ_idx bu) (ul i).
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
      (forall ρ bu, ⟦ ind_sort D ⟧ ρ ↘ bu -> uidx_le (Completeness.Inductives.Decl.univ_idx bu) (ul i)) ->
      glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil Ms vs ->
      Completeness.Inductives.Con.con_value p D k Mk c vs w ->
      ⟦ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) ⟧ env_args nil vs ↘ b ->
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
    assert (HassC : tele_ass (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
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
    assert (Eb : ⟦ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) ⟧ env_args nil vs
                   ↘ d_ind p k ps).
    { unfold ind_mty; rewrite HMk; unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
      apply Modules.eval_apps_exp; exists (d_ind p k nil), ps; split; [ constructor | split ].
      - unfold ind_uvars; rewrite vars_from_app, EV.
        replace (List.length gs) with (List.length ws) by exact Lws.
        replace (ind_nu D + im_nn Mk) with (List.length ps) by (unfold im_np in *; lia).
        apply Decl.eval_vars_from_args.
      - change (d_ind p k ps) with (d_ind p k (nil ++ ps)); apply (eval_apps_indty p D k Mk ps nil Hl HMk); cbn; lia. }
    assert (b = d_ind p k ps) as -> by (eapply functional_eval_exp; eassumption).
    set (ups := List.firstn (ind_nu D) ps) in *; set (ns := List.skipn (ind_nu D) ps) in *.
    assert (Eps : ps = ups ++ ns) by (symmetry; apply List.firstn_skipn).
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; unfold im_np in *; lia).
    destruct (Completeness.Inductives.Con.con_value_full p D k Mk c gs vs w ltac:(lia) Hw) as (cs & Hcs & ->).
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
    assert (HgPd : per_gargs (List.rev (im_params D Mk)) nil nil (ups ++ ns) (ups ++ ns)).
    { pose proof (gid_params _ HG _ _ HMk) as [SbP HSbP].
      exact (glu_args_per_gargs _ _ _ _ _ HassP (vid_params _ HD _ _ HMk) HΔ HSbP HgP). }
    rewrite rev_im_params in HgPd.
    destruct (Decl.per_gargs_app (List.rev (ind_uparams D)) (List.rev (im_nparams Mk)) nil nil ups ups ns ns
                ltac:(rewrite List.length_rev; exact Hu) HgPd ltac:(rewrite List.length_rev; exact Hu)) as [Hgu _].
    assert (HUs : glu_args Δ (ind_uparams D) Id nil (List.firstn (ind_nu D) Ps) ups).
    { pose proof (glu_args_uparams_of_params D Hc Mk _ _ _ HgP) as H; rewrite firstn_app_exact in H by exact Hu; exact H. }
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
    pose proof HΨ as [SbCP HSbCP].
    pose proof (glu_ctx_env_wf_ctx HSbCP) as HwfC.
    pose proof (glu_args_resp_eq Δ' _ nil _ _ _ HassC HwfC HΔ' Heq2 Hgw) as Hg'.
    destruct HPs' as [HlPP HPP].
    apply glu_args_app in Hg'; [| exact HassP | rewrite <- HlPP; exact LPw | exact Lupn ].
    destruct Hg' as [_ HgA'].
    assert (HlPs' : List.length Ps' = im_np D Mk) by (rewrite <- HlPP, List.length_map; exact LPs).
    rewrite <- (List.firstn_skipn (ind_nu D) Ps') in HgP', HgA'.
    pose proof (con_ind_glu_elem VP p D HVP HPD HG k Mk c gs HMk Hcon HΨ ups bu (ul i) NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf
                  HshV Hview Δ' (List.firstn (ind_nu D) Ps') (List.skipn (ind_nu D) Ps') (List.map (fun M => M[φ]ʷ) As) ns ws cs HΔ'
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
    assert (HassC : tele_ass (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
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
      destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m1 & m2 & Hm1 & Hm2 & Hmm).
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
      eapply con_base; [ exact HΔ' | | exact Hga | exact Hw' | exact Hb | exact Hglub | exact HPb ].
      intros; eapply Hn0; [ eassumption | lia ].
  Qed.

End ConFT.

End Fixed_GCtx.
