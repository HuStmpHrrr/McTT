(** * The Clusters of the Views, and the Nesting Order Below Them

    The cluster of a typed view [(qx, kx, Cs)] is its siblings, the
    members of the group at [qx] at [Cs].  An instance the cluster's
    constructors meet is found in the normal form of an argument type of
    a member of that group at [Cs] (directly, or, for a view sibling,
    through the view equations: [view_sib_link]):
    - at a recursive argument, it is a sibling ([rec_meet_in_sibs]);
    - at a non-recursive one, it is one nesting step ([NestAcc.grp_step])
      below the group at [Cs], at the initial environment of the
      declaration's context ([nonrec_meet_below]), which the order
      [view_lt] records ([view_below]).
    A typed view's type is one of the PER model, so [view_lt] is well
    founded below it ([view_inv_acc]). *)

From Stdlib Require Import Lia List PeanoNat String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Completeness Soundness Consequences.NormalFormWeakening.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Semantic.Inductives Require Import NestAcc IndCanon.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Algorithmic Require Import Strengthening.
From Mctt.Extraction Require Import ViewsSearch ViewsReach IndDecl.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope Instance Substitution.
From Mctt.Core.Completeness.Consequences Require Import Types Rules.
From Mctt.Core.Completeness.Inductives Require Import Decl Model ArgTypes Elim ElimView ViewReadback.
From Mctt.Core.Completeness Require Import LogicalRelation UnitCases UniverseCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Inductives Require Import UniformParams Views.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** The Type of a Recursive Argument, Moved *)

(** The type of a recursive argument moved along [q^n τ] past its
    context: a chain of [Π]s ending in the member its shape ends in. *)
Lemma ptyp_ty_sub_pis : forall pq D nn t pat τ, exists Bs Ps,
    (ptyp_ty pq D nn pat t)[sb_qn (List.length pat + nn) τ]
    = pis Bs (ind_mty pq D (ptyp_mem t) (ind_uvars D nn (List.length pat + List.length Bs)) Ps)[sb_qn (List.length pat + List.length Bs + nn) τ].
Proof.
  intros pq D nn t; induction t as [j Ps | B t IH]; intros pat τ.
  - exists nil, (List.map (fun P => P[wk_pat pat]ʷ) Ps); cbn [ptyp_ty pis List.length ptyp_mem]; rewrite !Nat.add_0_r; reflexivity.
  - cbn [ptyp_ty ptyp_mem]; destruct (IH (false :: pat) τ) as (Bs & Ps & E).
    exists (B[wk_pat pat]ʷ[sb_qn (List.length pat + nn) τ] :: Bs), Ps; cbn [exp_sub pis List.length] in E |- *.
    f_equal.
    change (sb_q (sb_qn (List.length pat + nn) τ)) with (sb_qn (S (List.length pat + nn)) τ).
    replace (S (List.length pat + nn)) with (S (List.length pat) + nn) by lia; rewrite E.
    replace (S (List.length pat) + List.length Bs) with (List.length pat + S (List.length Bs)) by lia; reflexivity.
Qed.

(** The uniform parameters as variables, moved along [q^k] of an
    instance: the instance weakened. *)
Lemma vars_sub_qn : forall k Cs,
    List.map (fun M => M[sb_qn k (sb_of_list Id Cs)]) (vars_from k (List.length Cs)) = List.map (fun C => C[wk_shiftn k]ʷ) Cs.
Proof.
  intros k Cs.
  replace (vars_from k (List.length Cs)) with (List.map (fun M => M[wk_shiftn k]ʷ) (vars_from 0 (List.length Cs)))
    by (rewrite vars_from_wk_shiftn; reflexivity).
  rewrite List.map_map, (List.map_ext _ (fun M => M[sb_of_list Id Cs][wk_shiftn k]ʷ)) by (intros; apply exp_shiftn_sub_qn0).
  rewrite <- (List.map_map (fun M => M[sb_of_list Id Cs]) (fun M => M[wk_shiftn k]ʷ)), vars_from_sb_of_list; reflexivity.
Qed.

(** Chains of [Π]s with ends that are no [Π]s are equal exactly when
    their domains and their ends are. *)
Lemma pis_inj : forall Bs1 Bs2 E1 E2, (forall B C, E1 <> a_pi B C) -> (forall B C, E2 <> a_pi B C) ->
    pis Bs1 E1 = pis Bs2 E2 -> Bs1 = Bs2 /\ E1 = E2.
Proof.
  induction Bs1 as [| B1 Bs1 IH]; intros [| B2 Bs2] * H1 H2 H; cbn in H.
  - split; [ reflexivity | exact H ].
  - exfalso; exact (H1 _ _ H).
  - exfalso; exact (H2 _ _ (eq_sym H)).
  - injection H as -> H; destruct (IH _ _ _ H1 H2 H) as [-> ->]; split; reflexivity.
Qed.

(** Weakening by a pattern of recursive arguments only is injective. *)
Lemma exp_wk_pat_inj : forall L M N, M[wk_pat (List.repeat true L)]ʷ = N[wk_pat (List.repeat true L)]ʷ -> M = N.
Proof.
  intros * H; apply (f_equal (fun X => X[unwk_pat (List.repeat true L)]ʷ)) in H.
  rewrite !(exp_wk_wk_ext _ _ _ wk_id (unwk_wk_pat _)), !exp_wk_id in H; exact H.
Qed.

(** The type of the argument [g] of a constructor of a member with [nn]
    non-uniform parameters, in the context of those before it, [pat]
    telling which of those are recursive. *)
Definition carg_ty (pq : qname) (D : ind_decl) (nn : nat) (pat : list bool) (g : carg) : typ :=
  match g with
  | ca_arg A => A[wk_pat pat]ʷ
  | ca_rec t => ptyp_ty pq D nn pat t
  end.

(** The arguments of a constructor, split at an argument: those after
    it, its type, and those before it. *)
Lemma cargs_ctx_split : forall pq D M gs1 g gs2,
    cargs_ctx pq D M (gs1 ++ g :: gs2)
    = cargs_ctx_aux pq D (im_nn M) (match g with ca_rec _ => true | ca_arg _ => false end :: cargs_pat gs1) gs2
        ++ ce_ass (carg_ty pq D (im_nn M) (cargs_pat gs1) g) :: cargs_ctx pq D M gs1.
Proof.
  intros; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r.
  destruct g as [A | t]; cbn [cargs_ctx_aux carg_ty]; rewrite <- List.app_assoc; reflexivity.
Qed.

(** ** Where the Classification Meets an Instance *)

(** An instance the classified arguments meet is met by one of them,
    classified in the context of those before it. *)
Lemma cls_args_in_site : forall Θ Ξ Γp nu np n pat args1 args gs,
    cls_args_in Θ Ξ Γp nu np n pat args1 args gs -> List.length pat = List.length args1 ->
    forall z, In z (List.concat (List.map rcarg_view gs)) ->
    exists pre y T post pat' g, args = pre ++ (y, T) :: post /\ cls_arg_in Θ Ξ (rtele (args1 ++ pre) ++ Γp) nu np n pat' T g /\
      In z (rcarg_view g) /\ List.length pat' = List.length args1 + List.length pre.
Proof.
  induction 1 as [| pat args1 y T args g gs Hg Hgs IH]; intros Hl z Hz; cbn in Hz; [ destruct Hz |].
  apply List.in_app_or in Hz as [Hz | Hz].
  - exists nil, y, T, args, pat, g; rewrite List.app_nil_r; cbn; split; [ reflexivity | split; [ exact Hg | split; [ exact Hz | lia ] ] ].
  - destruct (IH ltac:(rewrite List.length_app; cbn; lia) _ Hz) as (pre & y' & T' & post & pat' & g' & -> & Hg' & Hin & Hl').
    exists ((y, T) :: pre), y', T', post, pat', g'; rewrite <- List.app_assoc in Hg'; cbn [List.app] in Hg' |- *.
    split; [ reflexivity | split; [ exact Hg' | split; [ exact Hin |] ] ].
    rewrite List.length_app in Hl'; cbn in Hl' |- *; lia.
Qed.

(** An instance the classified constructors meet. *)
Lemma cls_cons_in_site : forall Θ Ξ Γp nu np n rcs cs, cls_cons_in Θ Ξ Γp nu np n rcs cs ->
    forall z, In z (rcons_views cs) ->
    exists rc pre y T post pat g, In rc rcs /\ snd rc = pre ++ (y, T) :: post /\
      cls_arg_in Θ Ξ (rtele pre ++ Γp) nu np n pat T g /\ In z (rcarg_view g) /\ List.length pat = List.length pre.
Proof.
  unfold cls_cons_in, rcons_views; induction 1 as [| rc c rcs cs [_ Hc] _ IH]; intros z Hz; cbn in Hz; [ destruct Hz |].
  apply List.in_app_or in Hz as [Hz | Hz].
  - destruct (cls_args_in_site _ _ _ _ _ _ _ _ _ _ Hc eq_refl _ Hz) as (pre & y & T & post & pat & g & Heq & Hg & Hin & Hl).
    exists rc, pre, y, T, post, pat, g; cbn [List.app List.length] in *.
    split; [ left; reflexivity | split; [ exact Heq | split; [ exact Hg | split; [ exact Hin | lia ] ] ] ].
  - destruct (IH _ Hz) as (rc' & pre & y & T & post & pat & g & Hrc & Hrest).
    exists rc', pre, y, T, post, pat, g; split; [ right; exact Hrc | exact Hrest ].
Qed.

Lemma ctx_args_app : forall Δ1 Δ2, ctx_args (Δ1 ++ Δ2) = ctx_args Δ2 ++ ctx_args Δ1.
Proof. intros; unfold ctx_args; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma rtele_ctx_args : forall Δ, tele_ass Δ -> rtele (ctx_args Δ) = Δ.
Proof.
  intros Δ Hass; unfold rtele, ctx_args; rewrite List.map_rev, List.rev_involutive, List.map_map.
  induction Hass as [| e Δ [A ->] _ IH]; cbn [List.map]; [ reflexivity | cbn; f_equal; exact IH ].
Qed.

(** The arguments of a constructor, moved along [q^nn σ], split at an
    argument met: the arguments before it, and its type. *)
Lemma cargs_sub_split : forall pq D M gs σ pre y T post,
    ctx_args (tele_sub (cargs_ctx pq D M gs) (sb_qn (im_nn M) σ)) = pre ++ (y, T) :: post ->
    exists gs1 g gs2, gs = gs1 ++ g :: gs2 /\ List.length gs1 = List.length pre /\
      rtele pre = tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ) /\
      T = (carg_ty pq D (im_nn M) (cargs_pat gs1) g)[sb_qn (List.length gs1 + im_nn M) σ].
Proof.
  intros * H.
  assert (Hl : List.length pre < List.length gs).
  { apply (f_equal (@List.length _)) in H.
    unfold ctx_args in H; rewrite List.length_rev, List.length_map, length_tele_sub, length_cargs_ctx, List.length_app in H; cbn in H.
    lia. }
  destruct (nth_error_lt_some' gs _ Hl) as [g Hg].
  destruct (List.nth_error_split _ _ Hg) as (gs1 & gs2 & -> & Hl1).
  exists gs1, g, gs2; split; [ reflexivity | split; [ exact Hl1 |] ].
  rewrite cargs_ctx_split, !tele_sub_app in H; cbn [tele_sub List.length] in H.
  rewrite ctx_args_app, length_cargs_ctx in H.
  assert (Hcons : forall e Y, ctx_args (e :: Y) = ctx_args Y ++ ((""%string, centry_ty e) :: nil)) by (intros; reflexivity).
  rewrite Hcons in H; cbn [centry_sub centry_ty] in H.
  rewrite <- List.app_assoc in H; cbn [List.app] in H.
  assert (Hass : tele_ass (tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ))) by (apply tele_ass_sub, cargs_ctx_aux_ass).
  assert (Hla : List.length (ctx_args (tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ))) = List.length pre)
    by (unfold ctx_args; rewrite List.length_rev, List.length_map, length_tele_sub, length_cargs_ctx; exact Hl1).
  destruct (app_split_eq _ _ _ _ H Hla) as [Hpre Hrest].
  injection Hrest as _ HT _.
  split; [ rewrite <- Hpre; apply rtele_ctx_args, Hass |].
  rewrite <- HT, sb_qn_plus; reflexivity.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** ** Normal Forms of Chains of [Π]s and of Inductive Types *)

  Lemma nbe_ty_pis_inv : forall Bs Γ E W, nbe_ty_f Γ (pis Bs E) W ->
      exists WBs WE, nf_to_exp W = pis (List.map nf_to_exp WBs) (nf_to_exp WE) /\ List.length WBs = List.length Bs /\
        nbe_ty_f (doms_ctx Bs ++ Γ) E WE.
  Proof.
    induction Bs as [| B Bs IH]; intros Γ E W HW; cbn [pis] in HW.
    - exists nil, W; split; [ reflexivity | split; [ reflexivity | exact HW ] ].
    - destruct (nbe_ty_pi_inv _ _ _ _ _ _ HW) as (WB & WC & -> & _ & HC).
      destruct (IH _ _ _ HC) as (WBs & WE & HWC & Hl & HE).
      exists (WB :: WBs), WE; cbn [nf_to_exp List.map pis List.length]; rewrite HWC; split; [ reflexivity | split; [ lia |] ].
      unfold doms_ctx in *; cbn [List.map List.rev]; rewrite <- List.app_assoc; exact HE.
  Qed.

  Lemma apps_ind_not_pi : forall qi k Ms B C, apps (a_ind qi k) Ms <> a_pi B C.
  Proof. intros * H; apply (f_equal app_head) in H; rewrite app_head_apps in H; discriminate. Qed.

  Lemma nbe_ty_True_inv : forall Γ W, nbe_ty_f Γ a_True W -> W = nf_True.
  Proof. intros * [ρ m Hinit Ea Hr]; inversion Ea; subst; inversion Hr; reflexivity. Qed.

  Lemma nbe_ty_ind_inv : forall Γ qi k Ms W, nbe_ty_f Γ (apps (a_ind qi k) Ms) W -> exists Rs, W = nf_indty qi k Rs.
  Proof.
    intros * [ρ m Hinit Ea Hr].
    apply Modules.eval_apps_exp in Ea as (f & ms & Ef & Ems & Eap).
    inversion Ef; subst.
    apply eval_apps_ind_inv in Eap; cbn in Eap; subst.
    inversion Hr; subst; eauto.
  Qed.

  (** The sibling a member [jm] of the group at [qx] gives at normal
      uniform arguments [Cs]: the member its type former is, at the
      normal forms of its uniform arguments at [Cs]. *)
  Lemma sib_of_member : forall Γu qx D Cs Ws ss jm Mjm, ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack qx = Some D ->
      nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws -> Cs = List.map nf_to_exp Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss -> ind_member D jm = Some Mjm ->
      exists Dq WQ, ind_lookup gc_deps gc_stack (fst (im_ref qx jm Mjm)) = Some Dq /\
        nbes gc_deps gc_stack Γu (im_pre Mjm Cs) (tele_insts (ind_uparams Dq) Id (im_pre Mjm Cs)) WQ /\
        In (fst (im_ref qx jm Mjm), snd (im_ref qx jm Mjm), List.map nf_to_exp WQ) ss.
  Proof.
    intros * Hg Hl Hn HCs Hss HM.
    destruct (sibs_from_nth _ _ _ _ _ _ _ _ Hss) as [_ Hssn].
    destruct (Hssn _ _ HM) as (e & He & Hse); cbn [Nat.add] in Hse.
    inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv]; subst; unfold im_ref, im_pre; rewrite Hh; cbn [fst snd].
    - exists D, Ws; split; [ exact Hl | split; [ exact Hn |] ].
      exact (List.nth_error_In _ _ He).
    - destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [_ Hcv].
      rewrite (tele_insts_sub (ind_uparams Dv) 0 Id Id (sb_of_list sb_id (List.map nf_to_exp Ws)) Iv (dc_ass _ Hcv) (dc_uparams _ Hcv)
                 ltac:(intros; lia)) in Hnv.
      exists Dv, Wv; split; [ exact Hlv | split; [ exact Hnv | exact (List.nth_error_In _ _ He) ] ].
  Qed.

  (** A member's uniform arguments at [Cs] are as many as the uniform
      parameters of the group its type former is in. *)
  Lemma length_im_pre : forall qx D Cs jm Mjm Dq, ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack qx = Some D ->
      List.length Cs = ind_nu D -> ind_member D jm = Some Mjm -> ind_lookup gc_deps gc_stack (fst (im_ref qx jm Mjm)) = Some Dq ->
      List.length (im_pre Mjm Cs) = ind_nu Dq.
  Proof.
    intros * Hg Hl HCl HM HlQ; unfold im_ref, im_pre in *.
    destruct (im_head Mjm) as [pm | qv kv Iv vm] eqn:Hh; cbn [fst] in HlQ.
    - rewrite Hl in HlQ; injection HlQ as <-; exact HCl.
    - destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
      destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dv & Mk' & Hlv & _ & _ & HIl & _).
      rewrite HlQ in Hlv; injection Hlv as <-; rewrite List.length_map; exact HIl.
  Qed.

  (** ** A Meet Off a Recursive Argument Is a Sibling

      A nested occurrence the classification finds in the normal form of
      a recursive argument of a constructor of a member of the group at
      [qx] at normal [Cs] is the sibling, at [Cs], of the member the
      argument's shape ends in. *)
  Theorem rec_meet_in_sibs : forall Γu qx D Cs Ws ss m Mi c gs gs1 t gs2 (i : nat) W nu np n pat gz z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws -> Cs = List.map nf_to_exp Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu
        ⊢ (ptyp_ty qx D (im_nn Mi) (cargs_pat gs1) t)[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu)
        (ptyp_ty qx D (im_nn Mi) (cargs_pat gs1) t)[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] W ->
      cls_arg (grp_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some gz -> In z (rcarg_view gz) ->
      List.length pat = List.length gs1 -> np - nu = im_nn Mi ->
      In z ss.
  Proof.
    intros * Hg Hl HCl Hn HCs Hss HM Hcon Heq HT HW Hcls Hin Hlp Hnn.
    destruct z as [[qz kz] Csz].
    destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & mz & HWe2 & HE2 & Hh2 & Hg2 & Hm2 & HC2).
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
    set (σ := sb_of_list Id Cs) in *.
    set (Γ := tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) σ ++ Γu) in *.
    (** the type: [Π]s ending in the member the shape ends in, at [Cs]
        weakened past the [Π]s' domains and the arguments before *)
    destruct (ptyp_ty_sub_pis qx D (im_nn Mi) t (cargs_pat gs1) σ) as (Bs & Ps & ET).
    rewrite length_cargs_pat in ET; rewrite ET in HT, HW.
    rewrite ind_mty_sub in HT, HW by (try exact Hc; apply length_ind_uvars).
    unfold ind_uvars in HT, HW; rewrite <- HCl in HT, HW; unfold σ in HT, HW; rewrite vars_sub_qn in HT, HW.
    set (K := List.length gs1 + List.length Bs + im_nn Mi) in *.
    destruct (nbe_ty_pis_inv _ _ _ _ HW) as (WBs & WE & HWe & HlWB & HWE).
    unfold ind_mty in HT, HWE; destruct (ind_member D (ptyp_mem t)) as [Mjm |] eqn:HMjm.
    2:{ rewrite (nbe_ty_True_inv _ _ HWE) in HWe; rewrite HWe2 in HWe; cbn [nf_to_exp] in HWe.
        assert (HT0 : forall B C, a_True <> a_pi B C) by (intros B C H0; discriminate H0).
        destruct (pis_inj _ _ _ _ HE2 HT0 HWe) as [_ ->]; discriminate. }
    unfold im_ty_at in HT, HWE.
    rewrite <- (im_pre_wk D (ptyp_mem t) Mjm Cs (wk_shiftn K) Hc HMjm HCl) in HT, HWE.
    (** its normal form ends in the member's at the normal forms of its
        arguments: that is where the occurrence is found *)
    destruct (nbe_ty_ind_inv _ _ _ _ _ HWE) as [Rs ->].
    cbn [nf_to_exp] in HWe; rewrite HWe2 in HWe.
    destruct (pis_inj _ _ _ _ HE2 (apps_ind_not_pi _ _ _) HWe) as [-> ->].
    rewrite app_head_apps in Hh2; cbn in Hh2; injection Hh2 as Hqz Hkz.
    rewrite app_args_apps in Hm2, HC2; cbn [app_args List.app] in Hm2, HC2.
    rewrite List.length_map, HlWB, Hlp, Hnn in HC2.
    replace (List.length Bs + List.length gs1 + im_nn Mi) with K in HC2 by (unfold K; lia).
    destruct (sib_of_member _ _ _ _ _ _ _ _ Hg Hl Hn HCs Hss HMjm) as (Dq & WQ & HlQ & HnQ & HinQ).
    pose proof (length_im_pre _ _ _ _ _ _ Hg Hl HCl HMjm HlQ) as HlQu.
    subst qz kz.
    set (qr := fst (im_ref qx (ptyp_mem t) Mjm)) in *; set (kr := snd (im_ref qx (ptyp_mem t) Mjm)) in *.
    set (Q := im_pre Mjm Cs) in *.
    unfold grp_info in Hg2; rewrite HlQ in Hg2.
    destruct (kr <? ind_ndecl Dq) eqn:Hkr; [ injection Hg2 as <- | discriminate ].
    apply Nat.ltb_lt in Hkr.
    destruct (List.nth_error (ind_members Dq) kr) as [Mkr |] eqn:HMkr;
      [| apply List.nth_error_None in HMkr; pose proof (ind_ndecl_le Dq); lia ].
    change (ind_member Dq kr = Some Mkr) in HMkr.
    destruct (decl_of_glookup _ _ _ _ Hg HlQ) as [Hdtq Hcq].
    pose proof (pis_typed_inv _ _ _ _ HT) as HEt.
    pose proof (ind_type_length _ _ _ _ _ _ _ HlQ HMkr HEt) as HRl.
    pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ HlQ HMkr HEt HRl) as HRt.
    destruct (nbes_nth _ _ _ _ _ _ HnQ) as (HlWQ & HlTQ & HnthQ).
    set (Ψ := doms_ctx Bs ++ tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) σ).
    assert (HlΨ : List.length Ψ = K)
      by (unfold Ψ, K, doms_ctx; rewrite List.length_app, length_tele_sub, List.length_rev, List.length_map, List.length_app,
            length_cargs_ctx; unfold im_nn; lia).
    assert (HΨa : tele_ass Ψ).
    { unfold Ψ; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass |].
      apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ Hdt _ _ HM) ]. }
    assert (HΨΓ : ⊢ Ψ ++ Γu) by (unfold Ψ; rewrite <- List.app_assoc; gen_presups; assumption).
    assert (HCszl : List.length Csz = ind_nu Dq)
      by (apply (f_equal (@List.length _)) in HC2; rewrite List.length_firstn, List.length_map in HC2; lia).
    set (args := List.map (fun N => N[wk_shiftn K]ʷ) Q ++ List.map (fun N => N[sb_qn K (sb_of_list Id Cs)]) Ps) in *.
    assert (Hfa : List.firstn (ind_nu Dq) args = List.map (fun N => N[wk_shiftn K]ʷ) Q)
      by (unfold args; rewrite List.firstn_app, List.length_map, HlQu, Nat.sub_diag, List.firstn_all2 by (rewrite List.length_map; lia);
          cbn; apply List.app_nil_r).
    (** each found argument, strengthened, is the normal form of the
        sibling's argument there *)
    assert (Heqc : Csz = List.map nf_to_exp WQ).
    { apply List.nth_error_ext; intros j.
      destruct (Nat.lt_ge_cases j (ind_nu Dq)) as [Hj | Hj];
        [| rewrite !(proj2 (List.nth_error_None _ _)) by (rewrite ?List.length_map; lia); reflexivity ].
      destruct (nth_error_lt_some' Csz j ltac:(lia)) as [C HCj].
      destruct (nth_error_lt_some' Q j ltac:(lia)) as [Qj HQj].
      destruct (nth_error_lt_some' (tele_insts (ind_uparams Dq) Id Q) j ltac:(lia)) as [T0 HT0].
      destruct (HnthQ _ _ _ HQj HT0) as (W0 & HW0 & HQt & HnQj).
      destruct (nbe_wk_tele Ψ Γu Qj T0 W0 HΨa HΨΓ HQt HnQj) as (W' & HW' & HW'e).
      rewrite HlΨ in HW', HW'e.
      pose proof (tele_insts_params_uniform_wk Dq Mkr Q args (wk_shiftn K) j T0 (dc_ass _ Hcq) (dc_uparams _ Hcq) HlQu Hfa HT0) as HT0w.
      assert (HPj : List.nth_error args j = Some Qj[wk_shiftn K]ʷ)
        by (unfold args; rewrite List.nth_error_app1 by (rewrite List.length_map; lia); rewrite List.nth_error_map, HQj; reflexivity).
      destruct (nbe_ind_args _ _ _ _ _ _ _ HlQ HMkr HRl HRt HWE j _ _ HPj HT0w) as (R & HR & HnR).
      assert (Hctx : doms_ctx Bs ++ Γ = Ψ ++ Γu) by (unfold Ψ, Γ; rewrite List.app_assoc; reflexivity).
      rewrite Hctx in HnR.
      pose proof (functional_nbe _ _ _ _ _ HnR HW') as ->.
      assert (HCw : List.nth_error (List.map (fun C => C[wk_pat (List.repeat true K)]ʷ) Csz) j = Some C[wk_pat (List.repeat true K)]ʷ)
        by (rewrite List.nth_error_map, HCj; reflexivity).
      rewrite <- HC2, List.nth_error_firstn in HCw.
      destruct (j <? ind_nu Dq) eqn:Ejn; [| apply Nat.ltb_ge in Ejn; lia ].
      rewrite <- nfs_list_exps, List.nth_error_map, HR in HCw; cbn in HCw; injection HCw as HCw.
      rewrite HW'e, <- (exp_wk_wk_eq _ _ _ (wk_pat_trues K)) in HCw.
      apply exp_wk_pat_inj in HCw.
      rewrite HCj, List.nth_error_map, HW0; cbn; rewrite HCw; reflexivity. }
    rewrite Heqc; exact HinQ.
  Qed.

  (** ** Instances at the Initial Environment *)

  (** The values, at the initial environment of [Γ], of an instance over
      [Γ] of a closed telescope are related at the telescope. *)
  Lemma inst_gargs : forall Γ U Ms ρ, tele_ass U -> ⊨ U -> ⊢ Γ -> List.length Ms = List.length U ->
      (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts U Id Ms) j = Some T -> Γ ⊢ N : T) ->
      initial_env_f Γ ρ ->
      exists us, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ us /\ per_gargs (List.rev U) nil nil us us /\ List.length us = List.length U.
  Proof.
    intros * HUa HU HΓ Hl HMs Hρ.
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    pose proof (gsub_closed_inst U Γ Ms HUa HU HΓs Hl
                  (fun j N T HN HT => completeness_fundamental_exp _ _ _ (HMs j N T HN HT))) as Hg.
    pose proof (gsub_valid Hg) as Hτ.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    destruct (per_ctx_then_per_env_initial_env HRΓ) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hρ) as ->.
    pose proof (functional_initial_env _ _ Hib _ Hρ) as ->.
    destruct (rel_sub_under_ctx_simple Hτ) as (RΓ' & HRΓ' & RUΓ & HRUΓ & Hσ).
    assert (E : RΓ <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hσ _ _ (proj1 (E _ _) Hab)) as (ρσ & ρσ' & Eσ & _ & _).
    destruct (eval_sb_of_list_inv _ _ _ _ _ Eσ (eval_sub_id _)) as (us & Eus & Heq).
    pose proof (eval_exps_length _ _ _ Eus) as Hlus.
    assert (Eσ' : ⟦ sb_of_list Id Ms ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ env_args ρ us)
      by (apply eval_sb_of_list; [ apply eval_sub_id | exact Eus ]).
    destruct (closed_app_sem U Γ HUa HU HΓs) as [HUΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HU) as [RU HRU].
    pose proof (rel_sub_under_ctx_at' Hτ HRΓ HRUΓ _ _ _ _ Hab Eσ' Eσ') as HUU.
    pose proof (Hres _ _ HRU HRUΓ _ _ HUU) as HUU'.
    assert (HlU : List.length us = List.length U) by lia.
    pose proof (closed_env_base U RU _ _ ρ ρ nil nil HUa HU HRU HlU HlU HUU') as H0.
    assert (HU' : ⊨ List.rev (List.rev U) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HU).
    assert (HRU' : EF List.rev (List.rev U) ++ ⋅ ≈ List.rev (List.rev U) ++ ⋅ ∈ per_ctx_env ↘ RU)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
    destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HU' (List.Forall_rev HUa) HRU' nil nil us us
                ltac:(rewrite List.length_rev; exact HlU) ltac:(rewrite List.length_rev; exact HlU) H0) as [_ Hg0].
    exists us; auto.
  Qed.

  (** ** Elements of a Telescope

      A telescope of assumptions over a context has elements over any
      environment of the context: its variables, read as fresh
      neutrals. *)
  Lemma gargs_exist : forall Δ Γ RΓ ρ, tele_ass Δ -> ⊨ Δ ++ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
      exists xs, per_gargs (List.rev Δ) ρ ρ xs xs /\ List.length xs = List.length Δ.
  Proof.
    induction Δ as [| e Δ IH]; intros * HΔa HΔ HRΓ Hρ; [ exists nil; split; constructor |].
    assert (He : exists A, e = ce_ass A) by (inversion HΔa as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (HΔa' : tele_ass Δ) by (inversion HΔa; assumption).
    destruct (rel_ctx_wf_ass_inv HΔ) as [i HA].
    pose proof (rel_ctx_wf_tail HΔ) as HΔ'.
    destruct (IH _ _ _ HΔa' HΔ' HRΓ Hρ) as (xs & Hxs & Hl).
    destruct (rel_ctx_wf_per_ctx_env HΔ') as [RΔ HRΔ].
    pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRΔ HΔ' Hρ Hl Hxs) as HE.
    destruct (rel_exp_of_typ_inversion_simple_at HRΔ HA _ _ HE) as (a & a' & Ea & Ea' & [R HR]).
    pose proof (functional_eval_exp _ _ _ _ Ea Ea') as <-.
    exists (xs ++ ⇑! a 0 :: nil); split; [| rewrite List.length_app; cbn; lia ].
    cbn [List.rev]; apply per_gargs_snoc with (i := i) (R := R);
      [ rewrite List.length_rev; exact Hl | exact Hxs | econstructor; eassumption | exact (var_per_elem 0 HR) ].
  Qed.

  (** ** The End of a Chain of [Π]s

      The value of a chain of [Π]s at an environment of its context has, as
      shape end, the value of its end at the environment extended by fresh
      variables of its domains, which is one of the context extended by the
      domains. *)
  Lemma shape_end_at : forall Bs Γ E (i : nat) RΓ ρ w, Γ ⊢ pis Bs E : Typeω@i -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
      ⟦ pis Bs E ⟧ ρ ↘ w ->
      exists ws e RE, EF doms_ctx Bs ++ Γ ≈ doms_ctx Bs ++ Γ ∈ per_ctx_env ↘ RE /\ RE (env_args ρ ws) (env_args ρ ws) /\
        List.length ws = List.length Bs /\ shape_end e w /\ ⟦ E ⟧ env_args ρ ws ↘ e.
  Proof.
    induction Bs as [| B Bs IH]; intros * HT HRΓ Hρ Ew; cbn [pis] in HT, Ew.
    - exists nil, w, RΓ; cbn; repeat split; [ exact HRΓ | exact Hρ | apply se_here | exact Ew ].
    - destruct (wf_pi_inversion' HT) as [HB HC].
      inversion Ew; subst.
      pose proof (completeness_fundamental_exp _ _ _ HB) as HBs.
      pose proof (per_ctx_env_of_typ HRΓ HBs) as HRB.
      match goal with Ha : ⟦ B ⟧ ρ ↘ ?a0 |- _ => rename Ha into EB end.
      destruct (rel_exp_of_typ_inversion_simple_at HRΓ HBs _ _ Hρ) as (a1 & a2 & Ea1 & Ea2 & [Ra HRa]).
      pose proof (functional_eval_exp _ _ _ _ Ea1 EB) as ->; pose proof (functional_eval_exp _ _ _ _ Ea2 EB) as ->.
      (** the fresh variable of the domain *)
      assert (Hρ' : per_env_extend B B RΓ (ρ ↦ ⇑! a 0) (ρ ↦ ⇑! a 0)).
      { split; [ exact Hρ | cbn; eapply per_head_of; [ exact EB | exact EB | exact HRa | exact (var_per_elem 0 HRa) ] ]. }
      destruct (rel_exp_of_typ_inversion_simple_at HRB (completeness_fundamental_exp _ _ _ HC) _ _ Hρ') as (b & _ & Eb & _ & _).
      destruct (IH _ _ _ _ _ _ HC HRB Hρ' Eb) as (ws & e & RE & HRE & HE & Hl & Hse & Ee).
      exists (⇑! a 0 :: ws), e, RE.
      assert (Hd : doms_ctx (B :: Bs) ++ Γ = doms_ctx Bs ++ (Γ ▹ B))
        by (unfold doms_ctx; cbn [List.map List.rev]; rewrite <- List.app_assoc; reflexivity).
      rewrite Hd; cbn [List.length]; repeat split; try assumption; [ lia |].
      econstructor; eassumption.
  Qed.

  (** Arguments related to themselves at a telescope over the values
      [base] and the elements before are, appended, elements of it. *)
  Lemma per_gargs_tele_elems : forall ts base pre T xs,
      per_gargs ts (env_args nil (base ++ pre)) (env_args nil (base ++ pre)) xs xs -> List.length xs = List.length ts ->
      tele_elems base T pre -> tele_elems base (T ++ ts) (pre ++ xs).
  Proof.
    induction ts as [| e ts IH]; intros * H Hl HT.
    - destruct xs; cbn in Hl; [| discriminate ]; rewrite !List.app_nil_r; exact HT.
    - destruct xs as [| x xs]; cbn in Hl; [ discriminate |].
      inversion H as [| i A ? ? ? ? ? ? ? R HA Hx Hg]; subst.
      destruct HA as [a a' Ea Ea' HR].
      pose proof (functional_eval_exp _ _ _ _ Ea Ea') as <-.
      assert (Henv : env_args nil (base ++ pre) ↦ x = env_args nil (base ++ pre ++ x :: nil))
        by (rewrite List.app_assoc, env_args_snoc; reflexivity).
      rewrite Henv in Hg.
      replace (T ++ ce_ass A :: ts) with ((T ++ ce_ass A :: nil) ++ ts) by (rewrite <- List.app_assoc; reflexivity).
      replace (pre ++ x :: xs) with ((pre ++ x :: nil) ++ xs) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ exact Hg | lia |].
      econstructor; [ exact HT | exact Ea | exact HR | exact Hx ].
  Qed.

  (** Arguments related to themselves at a constructor's arguments: their
      non-recursive ones are elements of the non-recursive arguments'
      types, each at the non-recursive ones before it. *)
  Lemma nonrec_elems : forall p D m Mi c gs, valid_group p D -> containers_valid D -> ind_member D m = Some Mi ->
      ind_con Mi c = Some gs ->
      forall gs1 gs2 us ms vs, gs = gs1 ++ gs2 -> List.length us = ind_nu D -> List.length ms = im_nn Mi ->
      List.length vs = List.length gs1 ->
      per_gargs (List.rev (cargs_ctx p D Mi gs1 ++ im_params D Mi)) nil nil (us ++ ms ++ vs) (us ++ ms ++ vs) ->
      tele_elems (us ++ ms) (List.map ce_ass (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs).
  Proof.
    intros p D m Mi c gs Hvg Hcv HM Hcon gs1; induction gs1 as [| g gs1 IH] using List.rev_ind;
      intros gs2 us ms vs Heq Hlu Hlm Hlv Hg.
    - destruct vs; cbn in Hlv; [| discriminate ]; constructor.
    - rewrite List.length_app in Hlv; cbn in Hlv.
      destruct (List.exists_last (l := vs) ltac:(intros ->; cbn in Hlv; lia)) as (vs' & v & ->).
      rewrite List.length_app in Hlv; cbn in Hlv.
      rewrite cargs_ctx_snoc, <- List.app_assoc, List.rev_app_distr, List.rev_app_distr, List.app_assoc,
        <- List.rev_app_distr in Hg.
      replace ((us ++ ms) ++ vs' ++ v :: nil) with ((us ++ ms ++ vs') ++ v :: nil) in Hg
        by (rewrite <- !List.app_assoc; reflexivity).
      assert (Hl0 : List.length (us ++ ms ++ vs') = List.length (List.rev (cargs_ctx p D Mi gs1 ++ im_params D Mi))).
      { rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
      destruct (per_gargs_app _ _ _ _ _ _ _ _ Hl0 Hg Hl0) as [Hpre Hlast].
      pose proof (IH (g :: gs2) us ms vs' ltac:(rewrite Heq, <- List.app_assoc; reflexivity) Hlu Hlm ltac:(lia) Hpre) as IHg.
      rewrite cargs_nonrec_app, nonrec_arg_vals_app by lia.
      destruct g as [A | t]; cbn [cargs_nonrec nonrec_arg_vals]; [| rewrite !List.app_nil_r; exact IHg ].
      rewrite List.map_app; cbn [List.map].
      destruct (vg_arg_types p D Hvg Hcv m Mi c gs gs1 A gs2 us ms vs' HM Hcon
                  ltac:(rewrite Heq, <- List.app_assoc; reflexivity) Hlu Hlm ltac:(lia) Hpre) as (i & R & a & a' & Ea & Ea' & HR).
      cbn [cargs_ctx_aux List.app List.rev] in Hlast.
      inversion Hlast as [| i0 A0 ? ? ? ? ? ? ? R0 HA0 Hv _]; subst.
      destruct HA0 as [a0 a0' E0 E0' H0].
      pose proof (functional_eval_exp _ _ _ _ E0 Ea) as ->; pose proof (functional_eval_exp _ _ _ _ E0' Ea) as ->.
      assert (Hv' : R v v) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ H0 HR); exact Hv).
      rewrite List.app_assoc in Ea'.
      econstructor; [ exact IHg | exact Ea' | exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR) HR) | exact Hv' ].
  Qed.

  (** A list substitution weakened, evaluated: the values of its terms
      weakened after its base's weakened. *)
  Lemma eval_sb_wk_of_list_inv : forall Ms σ φ ρ E E0, ⟦ sb_wk (sb_of_list σ Ms) φ ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ E ->
      ⟦ sb_wk σ φ ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ E0 ->
      exists ms, ⟦ List.map (fun M => M[φ]ʷ) Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ env_eq E (env_args E0 ms).
  Proof.
    induction Ms as [| M Ms IH]; intros σ φ ρ E E0 H H0; cbn [sb_of_list] in H.
    - exists nil; split; [ constructor | cbn; eapply functional_eval_sub; eassumption ].
    - pose proof (H (List.length Ms + 0)) as Hx; cbn [sb_wk] in Hx; rewrite sb_of_list_ge in Hx; cbn in Hx.
      destruct Hx as (m & Hme & Hm).
      destruct (IH _ _ _ _ (E0 ↦ m) H (eval_sub_wk_extend _ _ _ _ _ _ H0 Hm)) as (ms & Hms & HE).
      exists (m :: ms); split; [ cbn [List.map]; econstructor; eassumption | exact HE ].
  Qed.

  (** The values of an instance over [Γu] of a closed telescope, weakened
      past a telescope [Ψ], at an environment of [Ψ ++ Γu] over the
      initial one of [Γu], are related to the values of the instance at
      the initial environment. *)
  Lemma wk_inst_gargs : forall Ψ Γu U Ms ρ0 xs RΨ, tele_ass U -> ⊨ U -> ⊢ Γu -> List.length Ms = List.length U ->
      (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts U Id Ms) j = Some T -> Γu ⊢ N : T) ->
      initial_env_f Γu ρ0 -> EF Ψ ++ Γu ≈ Ψ ++ Γu ∈ per_ctx_env ↘ RΨ -> RΨ (env_args ρ0 xs) (env_args ρ0 xs) ->
      List.length xs = List.length Ψ ->
      exists us us', ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us /\
        ⟦ List.map (fun M => M[wk_shiftn (List.length Ψ)]ʷ) Ms ⟧* gc_deps ⍮ gc_stack ⍮ env_args ρ0 xs ↘ us' /\
        per_gargs (List.rev U) nil nil us' us.
  Proof.
    intros * HUa HU HΓ Hl HMs Hρ0 HRΨ Hρ Hlx.
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    pose proof (gsub_closed_inst U Γu Ms HUa HU HΓs Hl
                  (fun j N T HN HT => completeness_fundamental_exp _ _ _ (HMs j N T HN HT))) as Hg.
    destruct (gsub_valid Hg) as [R1 HR1 R2 HR2 Hbody].
    pose proof (rel_wk_shiftn _ _ _ _ HRΨ HR1) as Hwk.
    destruct (Hbody _ _ HRΨ _ Hwk _ _ Hρ) as [E1 E2 E3 E4 Ev1 Ev2 _ _ Hch].
    rewrite <- Hlx, eval_wk_shiftn_args in Ev2.
    destruct (eval_sb_of_list_inv _ _ _ _ _ Ev2 (eval_sub_id _)) as (us & Eus & Heq2).
    assert (E0 : ⟦ sb_wk Id (wk_shiftn (List.length Ψ)) ⟧s gc_deps ⍮ gc_stack ⍮ env_args ρ0 xs ↘ ρ0).
    { pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length xs)) (env_args ρ0 xs) _) as H0.
      rewrite eval_wk_shiftn_args in H0; rewrite <- Hlx; exact H0. }
    destruct (eval_sb_wk_of_list_inv _ _ _ _ _ _ Ev1 E0) as (us' & Eus' & Heq1).
    destruct Hch as (H12 & _).
    pose proof (per_ctx_env_resp_env_eq HR2 _ _ _ _ Heq1 Heq2 H12) as HUU.
    destruct (closed_app_sem U Γu HUa HU HΓs) as [HUΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HU) as [RU HRU].
    pose proof (Hres _ _ HRU HR2 _ _ HUU) as HUU'.
    pose proof (eval_exps_length _ _ _ Eus) as Hl1; pose proof (eval_exps_length _ _ _ Eus') as Hl2.
    rewrite List.length_map in Hl2.
    assert (HlU : List.length us = List.length U) by lia; assert (HlU' : List.length us' = List.length U) by lia.
    pose proof (closed_env_base U RU _ _ ρ0 ρ0 nil nil HUa HU HRU HlU' HlU HUU') as H0.
    assert (HU' : ⊨ List.rev (List.rev U) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HU).
    assert (HRU' : EF List.rev (List.rev U) ++ ⋅ ≈ List.rev (List.rev U) ++ ⋅ ∈ per_ctx_env ↘ RU)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
    destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HU' (List.Forall_rev HUa) HRU' nil nil us' us
                ltac:(rewrite List.length_rev; exact HlU') ltac:(rewrite List.length_rev; exact HlU) H0) as [_ Hg0].
    exists us, us'; auto.
  Qed.

  (** A group filed in a well-formed global context is a valid group,
      whose views' containers are. *)
  Lemma valid_group_gc : forall p D, ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack p = Some D ->
      valid_group p D /\ containers_valid D.
  Proof.
    intros p D Hg Hl; destruct GC as [Θ Ξ]; cbn in *.
    pose proof (valid_groups_of_emb _ _ _ _ (valid_emb_refl _ _ Hg)) as HV.
    split; [ exact (valid_groups_valid _ HV _ _ Hl) | exact (containers_valid_of_groups _ HV _ _ Hl) ].
  Qed.

  (** A declared member at uniform arguments related to themselves, and
      some non-uniform ones, is a type of the model. *)
  Lemma decl_member_type : forall p D k Mk ups, ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack p = Some D ->
      ind_member D k = Some Mk -> k < ind_ndecl D ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      exists ns (i : uidx) R, DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ R.
  Proof.
    intros * Hg Hl HM Hk Hgu Hu.
    destruct (valid_group_gc _ _ Hg Hl) as [Hvg _].
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    assert (Hd : im_is_decl Mk = true) by (apply (dt_order _ _ _ Hdt _ _ HM); exact Hk).
    unfold im_is_decl in Hd; destruct (im_head Mk) as [pm | ? ? ? ?] eqn:Hh; [| discriminate ].
    destruct (sort_value D (vgr_valid _ _ Hvg) ups Hgu Hu) as [a Ea].
    destruct (fresh_nparams_exist _ _ Hvg ups Hgu Hu k Mk 0 HM) as (ns & _ & Hns).
    exists ns, (univ_idx a); eexists.
    exact (ind_relate D (vgr_valid _ _ Hvg) (vgr_closed _ _ Hvg) (vgr_sort _ _ Hvg) p Hl (vgr_ass _ _ Hvg)
             k Mk pm ups ups ns ns a HM Hh Hgu Hu Ea Hns).
  Qed.

  (** ** A Meet Off a Non-Recursive Argument Is a Nesting Step

      A nested occurrence the classification finds in the normal form of
      a non-recursive argument of a constructor of a member of the group
      at [p] at [Cs] is one nesting step out of every member of the group
      at [Cs], at the initial environment of [Γu]. *)
  Theorem nonrec_meet_below : forall Γu p D k Cs ρ0 us m Mi c gs gs1 A gs2 (i : nat) W Bs qz kz Rs Dz Csz,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_arg A :: gs2 ->
      tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu
        ⊢ A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu)
        A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] W ->
      nf_to_exp W = pis Bs (apps (a_ind qz kz) (nfs_to_exps Rs)) ->
      ind_lookup gc_deps gc_stack qz = Some Dz -> kz < ind_ndecl Dz -> List.length Csz = ind_nu Dz ->
      (forall j C T, List.nth_error Csz j = Some C -> List.nth_error (tele_insts (ind_uparams Dz) Id Csz) j = Some T ->
         Γu ⊢ C : T) ->
      List.firstn (ind_nu Dz) (nfs_to_exps Rs)
        = List.map (fun C => C[wk_pat (List.repeat true (List.length Bs + List.length gs1 + im_nn Mi))]ʷ) Csz ->
      exists usz nsz, ⟦ Csz ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ usz /\ List.length usz = ind_nu Dz /\
        grp_step (d_ind qz kz (usz ++ nsz)) (d_ind p k us).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe Hlz Hkz HCzl HCzt HCz.
    set (σ := sb_of_list Id Cs) in *.
    set (Δ := cargs_ctx p D Mi gs1 ++ im_nparams Mi) in *.
    destruct (valid_group_gc _ _ Hg Hl) as [Hvg Hcv].
    destruct (valid_group_gc _ _ Hg Hlz) as [Hvgz _].
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
    destruct (decl_of_glookup _ _ _ _ Hg Hlz) as [Hdtz Hcz].
    assert (HlΔ : List.length Δ = List.length gs1 + im_nn Mi)
      by (unfold Δ; rewrite List.length_app, length_cargs_ctx; reflexivity).
    rewrite <- HlΔ in HT, HW.
    (** the values of [Cs], related at the uniform telescope *)
    pose proof (vid_uparams _ (vgr_valid _ _ Hvg)) as HUs.
    destruct (inst_gargs Γu (ind_uparams D) Cs ρ0 (dc_ass _ Hc) HUs HΓu ltac:(rewrite HCl; reflexivity) HCt Hρ0)
      as (us' & Eus' & Hgu & Hlu).
    pose proof (functional_eval_exps' _ _ _ _ Eus' Eus) as ->.
    (** the argument's type is one of the closed telescope of the
        arguments before and the member's parameters *)
    assert (HXs : exists j : nat, Δ ++ ind_uparams D ⊨ A[wk_pat (cargs_pat gs1)]ʷ : Typeω@j).
    { destruct (vg_cargs_sem_all p D Hvg Hcv m Mi c gs HM Hcon (gs1 ++ ca_arg A :: nil) gs2
                  ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as [HW1 _].
      rewrite cargs_ctx_snoc in HW1; cbn [cargs_ctx_aux List.app] in HW1.
      unfold Δ, im_params in *; rewrite <- List.app_assoc.
      exact (rel_ctx_wf_ass_inv HW1). }
    destruct HXs as [jX HXs].
    assert (HΔU : ⊨ Δ ++ ind_uparams D).
    { destruct (vg_cargs_sem_all p D Hvg Hcv m Mi c gs HM Hcon gs1 (ca_arg A :: gs2) Heq) as [HW1 _].
      unfold Δ, im_params in *; rewrite <- List.app_assoc; exact HW1. }
    assert (HΔa : tele_ass (Δ ++ ind_uparams D)).
    { unfold Δ; rewrite <- List.app_assoc; change (im_nparams Mi ++ ind_uparams D) with (im_params D Mi).
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_params_ass _ _ _ Hc HM) ]. }
    pose proof (dc_ass _ Hc) as HUa.
    destruct (rel_ctx_wf_per_ctx_env HUs) as [RU HRU].
    assert (HUU : RU (env_args nil us) (env_args nil us)).
    { assert (HRU0 : EF ind_uparams D ++ ⋅ ≈ ind_uparams D ++ ⋅ ∈ per_ctx_env ↘ RU) by (rewrite List.app_nil_r; exact HRU).
      apply (gargs_env_rel_gen _ _ _ _ _ _ _ _ per_ctx_env_nil_true HRU0 ltac:(rewrite List.app_nil_r; exact HUs) I Hlu Hgu). }
    assert (HΔa' : tele_ass Δ) by (apply List.Forall_app in HΔa as [H _]; exact H).
    (** fresh elements of the arguments before and the parameters *)
    destruct (gargs_exist Δ (ind_uparams D) RU (env_args nil us) HΔa' HΔU HRU HUU) as (xs & Hxs & Hlx).
    assert (HU0 : RU (env_args nil us) (env_args ρ0 us)) by exact (closed_env_base _ _ _ _ nil nil nil ρ0 HUa HUs HRU Hlu Hlu HUU).
    pose proof (per_gargs_base (List.rev Δ) (ind_uparams D) RU HRU ltac:(rewrite List.rev_involutive; exact HΔU) (List.Forall_rev HΔa')
                  _ _ (env_args ρ0 us) (env_args ρ0 us) xs xs HUU HU0 HU0 Hxs) as Hxsσ.
    (** the instance along [Cs] over [Γu] *)
    pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
    pose proof (gsub_valid (gsub_closed_inst (ind_uparams D) Γu Cs HUa HUs HΓs ltac:(rewrite HCl; reflexivity)
                  (fun j N T HN HT0 => completeness_fundamental_exp _ _ _ (HCt j N T HN HT0)))) as Hτ.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
    destruct (per_ctx_then_per_env_initial_env HRΓu) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hρ0) as ->; pose proof (functional_initial_env _ _ Hib _ Hρ0) as ->.
    assert (Eσ : ⟦ σ ⟧s gc_deps ⍮ gc_stack ⍮ ρ0 ↘ env_args ρ0 us) by (apply eval_sb_of_list; [ apply eval_sub_id | exact Eus ]).
    assert (HΔUΓ : ⊨ Δ ++ ind_uparams D ++ Γu)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HΔa HΔU HΓs))).
    destruct (outer_base Δ (ind_uparams D ++ Γu) Γu RΓu σ ρ0 (env_args ρ0 us) HΔa' HΔUΓ HRΓu Hτ Hab Eσ xs Hxsσ Hlx)
      as (RS & RΔ & Y & HRS & HSS & HRΔ & _ & _ & _).
    set (X := A[wk_pat (cargs_pat gs1)]ʷ) in *.
    assert (HXΓ : Δ ++ ind_uparams D ++ Γu ⊨ X : Typeω@jX)
      by (rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ HΔa HΔU HΓs HXs)).
    destruct (outer_typ_link Δ (ind_uparams D ++ Γu) Γu RΓu σ ρ0 (env_args ρ0 us) X X jX HΔa' HΔUΓ HXΓ HRΓu Hτ Hab Eσ xs Hxsσ Hlx)
      as (t & b & Et & Eb & Htb).
    (** the normal form's value, related to the type's *)
    pose proof (soundness_ty' HT HW) as HTW.
    destruct (rel_exp_of_typ_inversion_simple_at HRS (completeness_fundamental_exp_eq _ _ _ _ HTW) _ _ HSS)
      as (t' & w & Et' & Ew & Htw).
    pose proof (functional_eval_exp _ _ _ _ Et' Et) as ->.
    (** the type at the elements, as the model reads the argument *)
    assert (Hall : per_gargs (List.rev (Δ ++ ind_uparams D)) nil nil (us ++ xs) (us ++ xs))
      by (rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlu | exact Hgu | exact Hxs ]).
    set (ms := List.firstn (im_nn Mi) xs); set (vs := List.skipn (im_nn Mi) xs).
    assert (Hxs_eq : xs = ms ++ vs) by (symmetry; apply List.firstn_skipn).
    assert (Hlms : List.length ms = im_nn Mi)
      by (unfold ms; rewrite List.length_firstn; unfold Δ, im_nn in *; rewrite List.length_app in Hlx; lia).
    assert (Hlvs : List.length vs = List.length gs1)
      by (unfold vs; rewrite List.length_skipn; unfold Δ, im_nn in *; rewrite List.length_app, length_cargs_ctx in Hlx; lia).
    assert (Hall' : per_gargs (List.rev (cargs_ctx p D Mi gs1 ++ im_params D Mi)) nil nil (us ++ ms ++ vs) (us ++ ms ++ vs))
      by (unfold im_params; rewrite List.app_assoc, <- Hxs_eq; exact Hall).
    destruct (vg_arg_types p D Hvg Hcv m Mi c gs gs1 A gs2 us ms vs HM Hcon Heq ltac:(rewrite Hlu; reflexivity) Hlms Hlvs Hall')
      as (iA & RA & a & a' & Ea & Ea' & HRA).
    rewrite <- Hxs_eq in Ea.
    destruct (rel_ctx_wf_per_ctx_env HΔU) as [RC HRC].
    assert (Hlen0 : List.length (us ++ xs) = List.length (Δ ++ ind_uparams D)) by (rewrite !List.length_app; lia).
    assert (HCC : RC (env_args nil (us ++ xs)) (env_args nil (us ++ xs))).
    { assert (HRC0 : EF (Δ ++ ind_uparams D) ++ ⋅ ≈ (Δ ++ ind_uparams D) ++ ⋅ ∈ per_ctx_env ↘ RC) by (rewrite List.app_nil_r; exact HRC).
      assert (HC0 : ⊨ (Δ ++ ind_uparams D) ++ ⋅) by (rewrite List.app_nil_r; exact HΔU).
      exact (gargs_env_rel_gen (Δ ++ ind_uparams D) nil (fun _ _ => True) RC nil nil (us ++ xs) (us ++ xs)
               per_ctx_env_nil_true HRC0 HC0 I Hlen0 Hall). }
    pose proof (closed_env_base _ _ _ _ nil nil ρ0 nil HΔa HΔU HRC Hlen0 Hlen0 HCC) as HCC'.
    destruct (rel_exp_of_typ_inversion_simple_at HRC HXs _ _ HCC') as (b' & a2 & Eb' & Ea2 & Hba).
    rewrite <- env_args_app in Eb.
    pose proof (functional_eval_exp _ _ _ _ Eb' Eb) as ->; pose proof (functional_eval_exp _ _ _ _ Ea2 Ea) as ->.
    assert (Hwa : per_univ i w a').
    { eapply per_univ_trans'; [ apply per_univ_sym'; exact Htw |].
      eapply per_univ_trans'; [ exact Htb |].
      eapply per_univ_trans'; [ exact Hba | exists RA; exact HRA ]. }
    destruct Hwa as [R0 HR0].
    (** the shape end of the normal form's value: the member at [qz] at
        the values of the end's arguments *)
    assert (HWt : tele_sub Δ σ ++ Γu ⊢ pis Bs (apps (a_ind qz kz) (nfs_to_exps Rs)) : Typeω@i)
      by (rewrite <- HWe; gen_presups; assumption).
    rewrite HWe in Ew.
    destruct (shape_end_at Bs _ _ i RS (env_args ρ0 xs) w HWt HRS HSS Ew) as (ws & e & RE & HRE & HEE & Hlw & Hse & Ee).
    pose proof (pis_typed_inv _ _ _ _ HWt) as HEt.
    destruct (rel_exp_of_typ_inversion_simple_at HRE (completeness_fundamental_exp _ _ _ HEt) _ _ HEE)
      as (e1 & e2 & Ee1 & Ee2 & [Re HRe]).
    pose proof (functional_eval_exp _ _ _ _ Ee1 Ee) as ->; pose proof (functional_eval_exp _ _ _ _ Ee2 Ee) as ->.
    pose proof Ee as Ee0.
    apply Modules.eval_apps_exp in Ee0 as (f & msE & Ef & EmsE & Eap).
    inversion Ef; match goal with H : _ = f |- _ => subst f | H : f = _ |- _ => subst f end.
    apply eval_apps_ind_inv in Eap; cbn in Eap.
    subst e; clear Ef.
    (** the end's uniform arguments: the values of [Csz] weakened past the
        domains and the arguments before, related to those of [Csz] at the
        initial environment *)
    set (Ψ := doms_ctx Bs ++ tele_sub Δ σ).
    assert (HlΨ : List.length Ψ = List.length Bs + List.length gs1 + im_nn Mi)
      by (unfold Ψ, doms_ctx; rewrite List.length_app, length_tele_sub, List.length_rev, List.length_map; lia).
    assert (HRE' : EF Ψ ++ Γu ≈ Ψ ++ Γu ∈ per_ctx_env ↘ RE) by (unfold Ψ; rewrite <- List.app_assoc; exact HRE).
    rewrite <- env_args_app in HEE, EmsE.
    destruct (wk_inst_gargs Ψ Γu (ind_uparams Dz) Csz ρ0 (xs ++ ws) RE (dc_ass _ Hcz) (vid_uparams _ (vgr_valid _ _ Hvgz)) HΓu
                ltac:(rewrite HCzl; reflexivity) HCzt Hρ0 HRE' HEE ltac:(rewrite List.length_app, HlΨ, Hlw, Hlx, HlΔ; lia))
      as (usz & usE & Eusz & EusE & HgE).
    assert (Hfm : forall n Ms0 ms0 ρe, ⟦ Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρe ↘ ms0 ->
              ⟦ List.firstn n Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρe ↘ List.firstn n ms0).
    { induction n as [| n IHn]; intros Ms0 ms0 ρe Hev; [ cbn; constructor |].
      destruct Hev; cbn; constructor; auto. }
    pose proof (Hfm (ind_nu Dz) _ _ _ EmsE) as EfE.
    rewrite HCz in EfE; rewrite HlΨ in EusE.
    rewrite (List.map_ext _ (fun C => C[wk_shiftn (List.length Bs + List.length gs1 + im_nn Mi)]ʷ)) in EfE
      by (intros C; apply exp_wk_wk_eq, wk_pat_trues).
    pose proof (functional_eval_exps' _ _ _ _ EfE EusE) as HfE.
    assert (HlE : List.length usE = ind_nu Dz)
      by (pose proof (eval_exps_length _ _ _ EusE) as H; rewrite List.length_map in H; lia).
    assert (HlZ : List.length usz = ind_nu Dz) by (pose proof (eval_exps_length _ _ _ Eusz); lia).
    set (nsE := List.skipn (ind_nu Dz) msE).
    assert (HmsE : msE = usE ++ nsE) by (rewrite <- HfE; symmetry; apply List.firstn_skipn).
    rewrite HmsE in HRe, Hse.
    (** the member at [Csz] is related to the end *)
    destruct (List.nth_error (ind_members Dz) kz) as [Mkz |] eqn:HMkz;
      [| apply List.nth_error_None in HMkz; pose proof (ind_ndecl_le Dz); lia ].
    change (ind_member Dz kz = Some Mkz) in HMkz.
    assert (Hdz : im_is_decl Mkz = true) by (apply (dt_order _ _ _ Hdtz _ _ HMkz); exact Hkz).
    unfold im_is_decl in Hdz; destruct (im_head Mkz) as [pmz | ? ? ? ?] eqn:Hhz; [| discriminate ].
    pose proof (icc_ns _ _ _ _ _ _ _ _ (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HRe Hlz HlE HlE)) as HnsE.
    unfold member_nparams in HnsE; rewrite HMkz in HnsE.
    pose proof (uparams_refl_l Dz (vgr_valid _ _ Hvgz) Hcz _ _ HgE) as HgEE.
    destruct (sort_value Dz (vgr_valid _ _ Hvgz) usE HgEE HlE) as [aE EaE].
    pose proof (ind_relate Dz (vgr_valid _ _ Hvgz) Hcz (vgr_sort _ _ Hvgz) qz Hlz (vgr_ass _ _ Hvgz) kz Mkz pmz usE usz nsE nsE aE
                  HMkz Hhz HgE HlE EaE HnsE) as HEZ.
    (** the step *)
    exists usz, nsE; split; [ exact Eusz | split; [ exact HlZ |] ].
    rewrite <- (List.app_nil_r us).
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    assert (Hfirst : List.firstn (List.length (cargs_nonrec gs1)) (cargs_nonrec gs) = cargs_nonrec gs1)
      by (rewrite Heq, cargs_nonrec_app, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
    assert (Hlr : List.length ms = List.length (List.rev (im_nparams Mi))) by (rewrite List.length_rev; exact Hlms).
    unfold Δ in Hxs; rewrite List.rev_app_distr, Hxs_eq in Hxs.
    destruct (per_gargs_app _ _ _ _ _ _ _ _ Hlr Hxs Hlr) as [Hms0 _].
    rewrite <- (List.app_nil_r us) in Hms0.
    pose proof (per_gargs_tele_elems _ us nil nil ms Hms0 Hlr (te_nil _)) as Hms; cbn [List.app] in Hms.
    pose proof (nonrec_elems p D m Mi c gs Hvg Hcv HM Hcon gs1 (ca_arg A :: gs2) us ms vs Heq ltac:(rewrite Hlu; reflexivity)
                  Hlms Hlvs Hall') as Hvs.
    rewrite <- Hfirst in Hvs.
    exact (gs_intro _ p k D us nil m Mi c gs _ A ms _ a' i R0 w _ _ _ Hl ltac:(rewrite Hlu; reflexivity) HM Hcon HA Hms Hvs Ea'
             HR0 Hse (per_univ_sym _ _ _ _ HEZ)).
  Qed.
End Fixed_GCtx.

(** ** The Order the Meets Leaving a Cluster Descend *)

(** [view_below Θ Ξ Γu qz kz Csz qx kx Csx]: at the initial environment of
    [Γu], a type of the member [kz] of the group at [qz] at [Csz] is one
    nesting step ([grp_step]) out of the member [kx] of the group at [qx]
    at [Csx]. *)
#[warnings="-cannot-define-projection"]
Record view_below (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (qz : qname) (kz : nat) (Csz : list exp)
    (qx : qname) (kx : nat) (Csx : list exp) : Prop := mk_view_below
  { (** An environment of [Γu] *)
    below_env : env
    (** It is [Γu]'s initial environment *)
  ; below_env_initial : initial_env Θ Ξ Γu below_env
    (** The values of the upper view's uniform arguments [Csx] *)
  ; below_uparams : list domain
    (** They are those of [Csx] at the environment *)
  ; below_uparams_eval : ⟦ Csx ⟧* Θ ⍮ Ξ ⍮ below_env ↘ below_uparams
    (** The values of the lower view's uniform arguments [Csz] *)
  ; below_meet_uparams : list domain
    (** They are those of [Csz] at the environment *)
  ; below_meet_uparams_eval : ⟦ Csz ⟧* Θ ⍮ Ξ ⍮ below_env ↘ below_meet_uparams
    (** The values of the non-uniform parameters of the lower type *)
  ; below_meet_nparams : list domain
    (** The lower view's group *)
  ; below_meet_group : ind_decl
    (** It is filed at [qz] *)
  ; below_meet_lookup : ind_lookup Θ Ξ qz = Some below_meet_group
    (** As many uniform values as it has uniform parameters *)
  ; below_meet_length : List.length below_meet_uparams = ind_nu below_meet_group
    (** The lower type is one nesting step out of the upper one *)
  ; below_step : @grp_step (gc_mk Θ Ξ) (d_ind qz kz (below_meet_uparams ++ below_meet_nparams)) (d_ind qx kx below_uparams) }.

(** The order on views. *)
Definition view_lt (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (z x : rview) : Prop :=
  let '(qz, kz, Csz) := z in let '(qx, kx, Csx) := x in view_below Θ Ξ Γu qz kz Csz qx kx Csx.

(** A view whose type is accessible for the nesting steps is accessible
    for [view_lt]. *)
Lemma view_below_acc : forall Θ Ξ Γu a, @nest_acc (gc_mk Θ Ξ) a ->
    forall qx kx Csx ρ usx nsx Dx, initial_env Θ Ξ Γu ρ -> ⟦ Csx ⟧* Θ ⍮ Ξ ⍮ ρ ↘ usx ->
    ind_lookup Θ Ξ qx = Some Dx -> List.length usx = ind_nu Dx -> a = d_ind qx kx (usx ++ nsx) ->
    Acc (view_lt Θ Ξ Γu) (qx, kx, Csx).
Proof.
  intros Θ Ξ Γu a H; induction H as [a _ IH]; intros * Hi Eus Hl Hlen ->.
  constructor; intros [[qz kz] Csz] [ρ' Hi' us' Eus' usz Eusz nsz Dz Hlz Hlenz Hstep].
  pose proof (functional_initial_env _ _ Hi' _ Hi) as ->.
  pose proof (@functional_eval_exps' (gc_mk Θ Ξ) _ _ _ _ Eus' Eus) as ->.
  rewrite <- (List.app_nil_r usx) in Hstep.
  pose proof (@grp_step_member_irrel (gc_mk Θ Ξ) _ qx kx kx Dx usx nil nsx Hl Hlen Hstep) as Hstep'.
  exact (IH _ Hstep' qz kz Csz ρ usz nsz Dz Hi' Eusz Hlz Hlenz eq_refl).
Qed.

(** A typed view is accessible for [view_lt]: its type is one of the
    model. *)
Theorem view_inv_acc : forall Θ Ξ Γu qx kx Csx, ⊢ᵍ Θ ⍮ Ξ -> view_inv Θ Ξ Γu qx kx Csx -> Acc (view_lt Θ Ξ Γu) (qx, kx, Csx).
Proof.
  intros * Hg [[Dx Hl Hk Hlen Hty HΓu] _ _ _].
  destruct (List.nth_error (ind_members Dx) kx) as [Mk |] eqn:HM;
    [| apply List.nth_error_None in HM; pose proof (ind_ndecl_le Dx); lia ].
  change (ind_member Dx kx = Some Mk) in HM.
  destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
  pose proof (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ HΓu) as HΓs.
  destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
  destruct (per_ctx_then_per_env_initial_env HRΓ) as (ρ & _ & Hρ & _ & _).
  destruct (@inst_gargs (gc_mk Θ Ξ) Γu (ind_uparams Dx) Csx ρ (dc_ass _ Hc)
              (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ (dt_uparams _ _ _ Hdt)) HΓu
              ltac:(rewrite Hlen; reflexivity) Hty Hρ) as (us & Eus & Hgu & Hlu).
  destruct (@decl_member_type (gc_mk Θ Ξ) qx Dx kx Mk us Hg Hl HM Hk Hgu Hlu) as (ns & i & R & HR).
  eapply (view_below_acc Θ Ξ Γu _ (@per_univ_nest_acc_rel (gc_mk Θ Ξ) _ _ _ _ _ _ _ HR HR) qx kx Csx ρ us ns Dx Hρ Eus Hl Hlu eq_refl).
Qed.

Section MeetsOffMembers.
  Context {GC : GCtx}.

  (** ** A View Sibling Is Its Member

      The terms of a closed telescope's instance are equal to their normal
      forms, as a substitution. *)
  Lemma nbes_sub_eq : forall Γ U Ms Ws, tele_ass U -> ⊢ U -> ⊢ Γ -> List.length Ms = List.length U ->
      nbes gc_deps gc_stack Γ Ms (tele_insts U Id Ms) Ws -> Γ ⊢ˢ sb_of_list Id Ms ≈ sb_of_list Id (List.map nf_to_exp Ws) : U.
  Proof.
    intros * HUa HU HΓ HlM Hn.
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlW & HlT & Hnth).
    rewrite <- (List.app_nil_r U).
    eapply wf_sub_eq_of_list; [ exact HUa | rewrite List.app_nil_r; exact HU | exact (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HΓ))
                              | exact HlM | rewrite List.length_map, HlW; exact HlM |].
    intros j N N' T HN HN' HT.
    destruct (Hnth _ _ _ HN HT) as (W & HW & HNt & HNW).
    rewrite List.nth_error_map, HW in HN'; cbn in HN'; injection HN' as <-.
    exact (soundness' HNt HNW).
  Qed.

  (** The view equations of the member [i] of the group at [qx], a view of
      the member [kv] of the group at [qv], at [Cs]: its sibling's
      parameters and constructors' arguments are the member's at [Cs]. *)
  Theorem view_sib_link : forall Γu qx D Cs i Mi qv kv Iv vm Dqv Wv My,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      ind_member D i = Some Mi -> im_head Mi = mh_view qv kv Iv vm -> ind_lookup gc_deps gc_stack qv = Some Dqv ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list Id Cs]) Iv)
        (List.map (fun T => T[sb_of_list Id Cs]) (tele_insts (ind_uparams Dqv) Id Iv)) Wv ->
      ind_member Dqv kv = Some My ->
      im_nn Mi = im_nn My /\
      gc_deps ⍮ gc_stack ⍮ Γu ⊢ˣ tele_sub (im_nparams Mi) (sb_of_list Id Cs)
        ≈ tele_sub (im_nparams My) (sb_of_list Id (List.map nf_to_exp Wv)) /\
      (forall c gs', ind_con My c = Some gs' -> exists gs, ind_con Mi c = Some gs /\
         gc_deps ⍮ gc_stack ⍮ tele_sub (im_nparams Mi) (sb_of_list Id Cs) ++ Γu
           ⊢ˣ tele_sub (cargs_ctx qx D Mi gs) (sb_qn (im_nn Mi) (sb_of_list Id Cs))
           ≈ tele_sub (cargs_ctx qv Dqv My gs') (sb_qn (im_nn My) (sb_of_list Id (List.map nf_to_exp Wv)))).
  Proof.
    intros * Hg HΓu Hl HCl HCt HMi Hh Hlv Hn HMy.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
    destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [Hdtv Hcv].
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMi Hh) as (Dqv' & My' & Hlv' & HMy' & Hkv & HIl & Hvml & Hvmk & Hnames & _).
    rewrite Hlv in Hlv'; injection Hlv' as <-; rewrite HMy in HMy'; injection HMy' as <-.
    set (σC := sb_of_list Id Cs) in *.
    set (σY := sb_of_list Id (List.map nf_to_exp Wv)) in *.
    set (σIv := sb_of_list Id (List.map (fun I => I[σC]) Iv)).
    pose proof (wf_uparams_sub _ _ _ _ _ Hdt HΓu HCl HCt) as HσC.
    (** the view's instance at [Cs] is equal to its normal form *)
    rewrite (tele_insts_sub (ind_uparams Dqv) 0 Id Id σC Iv (dc_ass _ Hcv) (dc_uparams _ Hcv) ltac:(intros; lia)) in Hn.
    assert (HσIY : Γu ⊢ˢ σIv ≈ σY : ind_uparams Dqv)
      by (apply nbes_sub_eq; [ exact (dc_ass _ Hcv) | exact (dt_uparams _ _ _ Hdtv) | exact HΓu | rewrite List.length_map; exact HIl
                             | exact Hn ]).
    (** the non-uniform parameters: the view equation at [Cs], then the
        instance replaced by its normal form *)
    pose proof (dt_view_nparams _ _ _ _ Hg Hdt Hl i Mi qv kv Iv vm Dqv kv My i Mi HMi Hh Hlv HMy Hvmk HMi) as H1.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ H1 HσC) as H1'.
    pose proof (tele_list_grp_sb 0 Iv σC (im_nparams My) ltac:(rewrite HIl; exact (decl_closed_nparams_scoped _ Hcv _ _ HMy))) as E0.
    fold σC in H1'; change (sb_qn 0 (sb_of_list Id Iv)) with (sb_of_list Id Iv) in E0; change (sb_qn 0 σC) with σC in E0.
    change (sb_qn 0 (sb_of_list Id (List.map (fun M => M[σC]) Iv))) with σIv in E0; rewrite E0 in H1'.
    pose proof (member_params_wf _ _ _ _ _ Hdtv HMy) as HPy.
    pose proof (tele_sub_eq_ext (im_nparams My) (ind_uparams Dqv) Γu σIv σY (dt_nparams_ass _ _ _ Hdtv _ _ HMy) HPy HσIY) as H2.
    pose proof (ext_eq_trans_ass _ _ _ _ (tele_ass_sub _ _ (dt_nparams_ass _ _ _ Hdt _ _ HMi))
                  (tele_ass_sub _ _ (dt_nparams_ass _ _ _ Hdtv _ _ HMy)) H1' H2) as HNP.
    assert (Hnn : im_nn Mi = im_nn My)
      by (pose proof (ext_eq_length _ _ _ _ _ HNP) as E; rewrite !length_tele_sub in E; exact E).
    split; [ exact Hnn | split; [ exact HNP |] ].
    (** the constructors' arguments: the same *)
    intros c gs' Hc'.
    pose proof (cons_lookup_in _ _ _ Hc') as HIn'.
    assert (Hcn : In c (List.map fst (im_cons Mi))) by (rewrite Hnames; apply (List.in_map fst _ _ HIn')).
    apply List.in_map_iff in Hcn as ([c0 gs] & Hc0 & HIn); cbn in Hc0; subst c0.
    pose proof (cons_lookup_nodup _ _ _ (dt_nodup _ _ _ Hdt _ _ HMi) HIn) as Hcon.
    exists gs; split; [ exact Hcon |].
    pose proof (dt_view_args _ _ _ _ Hg Hdt Hl i Mi qv kv Iv vm Dqv kv My i Mi c gs' gs HMi Hh Hlv HMy Hvmk HMi Hc' Hcon) as H3.
    pose proof (wf_sub_ext _ _ (im_nparams Mi) (ind_uparams D) Γu σC HσC (ext_eq_ctx_left _ _ _ _ _ HNP)
                  (member_params_wf _ _ _ _ _ Hdt HMi)) as Hτ.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ H3 Hτ) as H3'.
    change (List.length (im_nparams Mi)) with (im_nn Mi) in H3'.
    rewrite (tele_list_grp_sb (im_nn Mi) Iv σC (cargs_ctx qv Dqv My gs')) in H3'
      by (rewrite HIl, Hnn; exact (decl_closed_cargs_scoped _ Hcv _ _ _ _ _ HMy HIn')).
    fold σIv in H3'; rewrite Hnn in H3'.
    pose proof (sb_qn_eq_ext (im_nparams My) (ind_uparams Dqv) Γu σIv σY (dt_nparams_ass _ _ _ Hdtv _ _ HMy) HPy HσIY) as HqY.
    pose proof (ctxsub_ext_rev _ _ _ _ _ H1' (tele_ass_sub _ _ (dt_nparams_ass _ _ _ Hdt _ _ HMi))) as Hid.
    pose proof (ctxsub_sub_eq _ _ _ _ _ _ _ Hid HqY) as HqY'.
    change (List.length (im_nparams My)) with (im_nn My) in HqY'.
    destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg (fun pq D0 Hl0 => proj1 (decl_of_glookup _ _ _ _ Hg Hl0)) Hlv HMy HIn' gs' nil
                ltac:(rewrite List.app_nil_r; reflexivity)) as (HWc & _).
    pose proof (tele_sub_eq_ext (cargs_ctx qv Dqv My gs') (im_params Dqv My) _ _ _ (cargs_ctx_aux_ass _ _ _ _ _) HWc HqY') as H4.
    eapply ext_eq_trans_ass; [ apply tele_ass_sub, cargs_ctx_aux_ass | apply tele_ass_sub, cargs_ctx_aux_ass | | exact H4 ].
    rewrite Hnn; apply ext_eq_sym_ass; [ apply tele_ass_sub, cargs_ctx_aux_ass | exact H3' ].
  Qed.

  (** ** Where the Meets Off a Member of the Cluster Land

      A nested occurrence the classification finds in the normal form of
      an argument of a constructor of a member of the group at [qx], at
      normal uniform arguments [Cs] over [Γu], is a sibling at [Cs] when
      the argument is recursive, and below every view of the group at [Cs]
      otherwise. *)
  Theorem meet_off_member : forall Γu qx D kx Cs Ws ss m Mi c gs gs1 g gs2 (i : nat) W nu n pat gz z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws -> Cs = List.map nf_to_exp Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ g :: gs2 ->
      tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu
        ⊢ (carg_ty qx D (im_nn Mi) (cargs_pat gs1) g)[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu)
        (carg_ty qx D (im_nn Mi) (cargs_pat gs1) g)[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] W ->
      cls_arg (grp_info gc_deps gc_stack) nu (im_nn Mi + nu) n pat (nf_to_exp W) = Some gz -> In z (rcarg_view gz) ->
      List.length pat = List.length gs1 ->
      In z ss \/ view_lt gc_deps gc_stack Γu z (qx, kx, Cs).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hn HCs Hss HM Hcon Heq HT HW Hcls Hin Hlp.
    destruct g as [A | t]; cbn [carg_ty] in HT, HW.
    - (** a non-recursive argument: a nesting step *)
      right; destruct z as [[qz kz] Csz].
      set (Δ := tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) in *.
      destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
      assert (HΔa : tele_ass Δ)
        by (apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ Hdt _ _ HM) ]).
      assert (HlΔ : List.length Δ = List.length pat + (im_nn Mi + nu - nu))
        by (unfold Δ; rewrite length_tele_sub, List.length_app, length_cargs_ctx; unfold im_nn; lia).
      destruct (nest_view_inv _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hcls Hin) as [[Dz Hlz Hkz HCzl HCzt _] _ _ _].
      destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs & E & mz & HWe & HE & Hh & Hg2 & Hm & HC).
      pose proof HW as [ρw mw _ _ Hrw]; pose proof (read_typ_type_nf _ _ _ Hrw) as HWn.
      destruct (nf_pis_end _ _ _ HWn HWe) as (WE & HWE & HWEe).
      rewrite <- HWEe in Hh; destruct (nf_ind_view _ _ _ HWE Hh) as [Rs ->].
      cbn [nf_to_exp] in HWEe; subst E.
      rewrite app_args_apps in HC; cbn [app_args List.app] in HC.
      unfold grp_info in Hg2; rewrite Hlz in Hg2.
      destruct (kz <? ind_ndecl Dz); [ injection Hg2 as <- | discriminate ].
      replace (List.length Bs + List.length pat + (im_nn Mi + nu - nu)) with (List.length Bs + List.length gs1 + im_nn Mi) in HC
        by lia.
      pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
      destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
      destruct (per_ctx_then_per_env_initial_env HRΓu) as (ρ0 & _ & Hρ0 & _ & _).
      destruct (decl_of_glookup _ _ _ _ Hg Hl) as [_ Hc].
      destruct (inst_gargs Γu (ind_uparams D) Cs ρ0 (dc_ass _ Hc) (completeness_fundamental_ctx _ (dt_uparams _ _ _ Hdt)) HΓu
                  ltac:(rewrite HCl; reflexivity) HCt Hρ0) as (us & Eus & _ & _).
      destruct (nonrec_meet_below Γu qx D kx Cs ρ0 us m Mi c gs gs1 A gs2 i W Bs qz kz Rs Dz Csz Hg HΓu Hl HCl HCt Hρ0 Eus
                  HM Hcon Heq HT HW HWe Hlz Hkz HCzl HCzt HC) as (usz & nsz & Eusz & Hlusz & Hstep).
      clear - Hρ0 Eus Eusz Hlz Hlusz Hstep; destruct GC as [Θ0 Ξ0].
      exact (mk_view_below _ _ _ _ _ _ _ _ _ ρ0 Hρ0 us Eus usz Eusz nsz Dz Hlz Hlusz Hstep).
    - (** a recursive argument: a sibling *)
      left; eapply rec_meet_in_sibs; try eassumption; lia.
  Qed.

  (** The context of the arguments of a constructor before one, over the
      member's parameters at [Cs]. *)
  Lemma cargs_pre_ctx : forall pq D M gs1 σ Γu,
      tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ) ++ tele_sub (im_nparams M) σ ++ Γu
      = tele_sub (cargs_ctx pq D M gs1 ++ im_nparams M) σ ++ Γu.
  Proof. intros; rewrite tele_sub_app, <- List.app_assoc; reflexivity. Qed.

  (** The arguments of a constructor, moved along [q^nn σ], at an
      argument: those after it, its type, those before it. *)
  Lemma cargs_sub_at : forall pq D M gs1 g gs2 σ, exists X,
      tele_sub (cargs_ctx pq D M (gs1 ++ g :: gs2)) (sb_qn (im_nn M) σ)
      = X ++ ce_ass (carg_ty pq D (im_nn M) (cargs_pat gs1) g)[sb_qn (List.length gs1 + im_nn M) σ]
          :: tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ) /\ List.length X = List.length gs2.
  Proof.
    intros; rewrite cargs_ctx_split, !tele_sub_app; cbn [tele_sub List.length centry_sub].
    eexists; split; [ rewrite length_cargs_ctx, (sb_qn_plus (List.length gs1) (im_nn M) σ); reflexivity |].
    rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity.
  Qed.

  (** The instances the constructors of the member [j] of the group at
      [qx] at normal [Cs] meet, classified as a view's are, are siblings
      at [Cs] or below every view of the group at [Cs]. *)
  Theorem member_meets : forall Γu qx D kx Cs Ws ss j Mj cs nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws -> Cs = List.map nf_to_exp Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss ->
      ind_member D j = Some Mj ->
      cls_cons_in gc_deps gc_stack (tele_sub (im_nparams Mj) (sb_of_list sb_id Cs) ++ Γu) nu (im_nn Mj + nu) n
        (List.map (fun cg => (fst cg, ctx_args (tele_sub (cargs_ctx qx D Mj (snd cg)) (sb_qn (im_nn Mj) (sb_of_list sb_id Cs)))))
           (im_cons Mj)) cs ->
      In z (rcons_views cs) ->
      In z ss \/ view_lt gc_deps gc_stack Γu z (qx, kx, Cs).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hn HCs Hss HMj Hcls Hz.
    destruct (cls_cons_in_site _ _ _ _ _ _ _ _ Hcls _ Hz) as (rc & pre & y & T & post & pat & g & Hrc & Hsnd & Hgc & Hin & Hlp).
    apply List.in_map_iff in Hrc as ([c gs] & <- & HIn); cbn [fst snd] in Hsnd.
    destruct (cargs_sub_split _ _ _ _ _ _ _ _ _ Hsnd) as (gs1 & g' & gs2 & Heq & Hl1 & Hpre & ->).
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    pose proof (cons_lookup_nodup _ _ _ (dt_nodup _ _ _ Hdt _ _ HMj) HIn) as Hcon.
    rewrite Hpre, cargs_pre_ctx in Hgc.
    inversion Hgc as [g0 Hsyn | i W g0 Hnone HTt HW Hcl]; subst.
    - rewrite (cls_arg_none_view _ _ _ _ _ _ Hsyn) in Hin; destruct Hin.
    - exact (meet_off_member Γu qx D kx _ Ws ss j Mj c _ gs1 g' gs2 i W nu n pat g z Hg HΓu Hl HCl HCt Hn eq_refl Hss HMj Hcon
               eq_refl HTt HW Hcl Hin ltac:(lia)).
  Qed.

  (** The instances a view sibling's constructors meet: those of the
      member of the group at [qx] it is, at [Cs], by the view
      equations. *)
  Theorem view_sib_meets : forall Γu qx D kx Cs Ws ss i Mi qv kv Iv vm Dqv Wv My cs nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws -> Cs = List.map nf_to_exp Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss ->
      ind_member D i = Some Mi -> im_head Mi = mh_view qv kv Iv vm -> ind_lookup gc_deps gc_stack qv = Some Dqv ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list Id Cs]) Iv)
        (List.map (fun T => T[sb_of_list Id Cs]) (tele_insts (ind_uparams Dqv) Id Iv)) Wv ->
      ind_member Dqv kv = Some My ->
      cls_cons_in gc_deps gc_stack (tele_sub (im_nparams My) (sb_of_list sb_id (List.map nf_to_exp Wv)) ++ Γu) nu (im_nn My + nu) n
        (List.map (fun cg => (fst cg, ctx_args (tele_sub (cargs_ctx qv Dqv My (snd cg))
                                                  (sb_qn (im_nn My) (sb_of_list sb_id (List.map nf_to_exp Wv))))))
           (im_cons My)) cs ->
      In z (rcons_views cs) ->
      In z ss \/ view_lt gc_deps gc_stack Γu z (qx, kx, Cs).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hn HCs Hss HMi Hh Hlv Hnv HMy Hcls Hz.
    destruct (cls_cons_in_site _ _ _ _ _ _ _ _ Hcls _ Hz) as (rc & pre & y & T & post & pat & g & Hrc & Hsnd & Hgc & Hin & Hlp).
    apply List.in_map_iff in Hrc as ([c gs'] & <- & HIn'); cbn [fst snd] in Hsnd.
    destruct (cargs_sub_split _ _ _ _ _ _ _ _ _ Hsnd) as (gs1y & gy & gs2y & Heqy & Hl1y & Hpre & ->).
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [Hdtv _].
    pose proof (cons_lookup_nodup _ _ _ (dt_nodup _ _ _ Hdtv _ _ HMy) HIn') as Hc'.
    destruct (view_sib_link Γu qx D Cs i Mi qv kv Iv vm Dqv Wv My Hg HΓu Hl HCl HCt HMi Hh Hlv Hnv HMy) as (Hnn & HNP & Hcons).
    destruct (Hcons c gs' Hc') as (gs & Hcon & HE2).
    rewrite Hpre in Hgc.
    destruct Hgc as [g0 Hsyn | iy W g0 Hnone HTy HWy Hcl].
    { rewrite (cls_arg_none_view _ _ _ _ _ _ Hsyn) in Hin; destruct Hin. }
    subst gs'.
    set (σC := sb_of_list Id Cs) in *; set (σY := sb_of_list Id (List.map nf_to_exp Wv)) in *.
    (** the member's arguments, split at the same position *)
    assert (Hlg : List.length gs = List.length (gs1y ++ gy :: gs2y))
      by (pose proof (ext_eq_length _ _ _ _ _ HE2) as E; rewrite !length_tele_sub, !length_cargs_ctx in E; exact E).
    assert (Hj : List.length gs1y < List.length gs) by (rewrite Hlg, List.length_app; cbn; lia).
    destruct (nth_error_lt_some' gs _ Hj) as [g' Hg'].
    destruct (List.nth_error_split _ _ Hg') as (gs1 & gs2 & -> & Hl1).
    destruct (cargs_sub_at qx D Mi gs1 g' gs2 σC) as (X & EX & HlX).
    destruct (cargs_sub_at qv Dqv My gs1y gy gs2y σY) as (Xy & EXy & HlXy).
    rewrite EX, EXy in HE2.
    assert (HaD : tele_ass (tele_sub (cargs_ctx qx D Mi (gs1 ++ g' :: gs2)) (sb_qn (im_nn Mi) σC)))
      by (apply tele_ass_sub, cargs_ctx_aux_ass).
    rewrite EX in HaD.
    (** the parameters and the arguments before, and the argument's
        types, equal *)
    pose proof (ext_eq_app _ _ _ _ _ _ _ (tele_ass_sub _ _ (dt_nparams_ass _ _ _ Hdt _ _ HMi)) HaD HNP HE2) as HEall.
    rewrite <- !List.app_assoc in HEall; cbn [List.app] in HEall.
    apply ext_eq_app_inv in HEall; [| rewrite HlX, HlXy; rewrite !List.length_app in Hlg; cbn in Hlg; lia ].
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ HEall) as (i0 & HE1 & HT' & HTT & HTy').
    assert (HaY : tele_ass (tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC) ++ tele_sub (im_nparams Mi) σC))
      by (apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ Hdt _ _ HMi) ]).
    (** so the same normal form, in the member's context *)
    pose proof (rxu_eq _ _ _ (proj1 completeness_fundamental_modules _ _ _ (ext_eq_sym_ass _ _ _ _ _ HaY HE1))) as HY2D.
    rewrite List.app_assoc in HTy, HWy.
    pose proof (ctxeq_nbe_ty_eq' _ _ _ _ _ HTy HY2D HWy) as HWD.
    destruct (completeness_ty HTT) as (W0 & HW0D & HW0Y).
    pose proof (functional_nbe_ty _ _ _ _ HW0Y HWD) as ->.
    rewrite <- List.app_assoc, cargs_pre_ctx in HT', HW0D.
    rewrite <- Hnn in Hcl.
    exact (meet_off_member Γu qx D kx Cs Ws ss i Mi c _ gs1 g' gs2 i0 W nu n pat g0 z Hg HΓu Hl HCl HCt Hn HCs Hss HMi Hcon
             eq_refl HT' HW0D Hcl Hin ltac:(lia)).
  Qed.

  (** ** Siblings in an Ill-Formed Context

      Nothing is typed in an ill-formed context, so every instance of a
      sibling there is empty. *)
  Lemma nbes_ill : forall Γ Ms As Ws, nbes gc_deps gc_stack Γ Ms As Ws -> ~ ⊢ Γ -> Ms = nil /\ Ws = nil.
  Proof.
    intros * Hn HΓ; destruct Hn as [| M Ms A As W Ws HM _ _]; [ split; reflexivity |].
    exfalso; exact (HΓ (presup_exp_ctx HM)).
  Qed.

  (** The siblings of a view sibling of [(qx, k, Cs)] in an ill-formed
      context are siblings of [(qx, k, Cs)]. *)
  Lemma view_entry_sibs_ill : forall Γu qx D Cs m Mm qv kv Iv vm Wv Dqv ss ssy,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ~ ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D ->
      ind_member D m = Some Mm -> im_head Mm = mh_view qv kv Iv vm -> ind_lookup gc_deps gc_stack qv = Some Dqv ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list sb_id Cs]) Iv)
        (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (ind_uparams Dqv) sb_id Iv)) Wv ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss ->
      sibs_from gc_deps gc_stack Γu qv (List.map nf_to_exp Wv) 0 (ind_members Dqv) ssy ->
      incl ssy ss.
  Proof.
    intros * Hg HΓu Hl HMm Hh Hlv Hn Hss Hssy e He.
    destruct (nbes_ill _ _ _ _ Hn HΓu) as [HIv ->].
    apply List.map_eq_nil in HIv; subst Iv.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMm Hh) as (Dqv' & Mkv & Hlv' & _ & _ & _ & Hvml & _).
    rewrite Hlv in Hlv'; injection Hlv' as <-.
    destruct (sibs_from_in _ _ _ _ _ _ _ _ Hssy _ He) as (i' & Mi' & HMi' & Hei' & Hse); cbn [Nat.add] in Hse.
    assert (Hi'l : i' < List.length vm) by (rewrite Hvml; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' vm i' Hi'l) as [v Hv].
    destruct (sibs_from_nth _ _ _ _ _ _ _ _ Hss) as [_ Hssn].
    inversion Hse as [? ? pm' Hhd | ? ? q'' k'' Is'' vm'' D'' We Hhd Hl'' Hne]; subst.
    - destruct (dt_view_decl _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMm Hh Hlv HMi' Hhd Hv) as (Mv & vm' & HMv & HhMv).
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? qv0 kv0 Iv0 vm0 Dv0 Ws0 Hh0 Hl0 Hn0]; subst; rewrite HhMv in Hh0; [ discriminate |].
      injection Hh0 as <- <- <- <-.
      destruct (nbes_ill _ _ _ _ Hn0 HΓu) as [_ ->].
      exact (List.nth_error_In _ _ He0).
    - destruct (nbes_ill _ _ _ _ Hne HΓu) as [HIs ->].
      apply List.map_eq_nil in HIs; subst Is''.
      destruct (dt_view_view _ _ _ Hdt m Mm qv kv nil vm Dqv i' Mi' v q'' k'' nil vm'' HMm Hh Hlv HMi' Hhd Hv)
        as (Mv & X & vm' & HMv & HhMv & HXl).
      destruct X; [| discriminate ].
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? qv0 kv0 Iv0 vm0 Dv0 Ws0 Hh0 Hl0 Hn0]; subst; rewrite HhMv in Hh0; [ discriminate |].
      injection Hh0 as <- <- <- <-.
      destruct (nbes_ill _ _ _ _ Hn0 HΓu) as [_ ->].
      exact (List.nth_error_In _ _ He0).
  Qed.
End MeetsOffMembers.
