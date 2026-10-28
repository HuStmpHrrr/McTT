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
    founded below it ([view_inv_acc]).

    A record view [(qr, Is)] is its own cluster: every instance its
    constructor's fields meet, at a field's normal form at [Is], is one
    nesting step ([NestAcc.grp_step_record]) below the record type at
    [Is] ([record_view_meets_below]).  A record view sibling of an
    inductive view is its container's record member at [Cs]: its meets are
    the member's, by the record view equations ([record_sib_link],
    [record_sib_meets]).  The steps share the semantics of an argument's
    normal form's shape end ([arg_shape_end], [ind_end_rel],
    [record_end_rel]). *)

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
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
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

(** A record's fields, at a field: those after it, its type, those before
    it. *)
Lemma record_fctx_at : forall R k f A, List.nth_error (record_fields R) k = Some (f, A) ->
    record_fctx R (List.length (record_fields R))
    = List.rev (List.map (fun fT => ce_ass (snd fT)) (List.skipn (S k) (record_fields R))) ++ ce_ass A :: record_fctx R k.
Proof.
  intros * HfA; unfold record_fctx; rewrite List.firstn_all.
  rewrite <- (List.firstn_skipn (S k) (record_fields R)) at 1.
  rewrite (firstn_S_nth_error _ _ _ HfA), !List.map_app, !List.rev_app_distr; reflexivity.
Qed.

Lemma length_record_fctx_le : forall R k, k <= List.length (record_fields R) -> List.length (record_fctx R k) = k.
Proof. intros R k Hk; unfold record_fctx; rewrite List.length_rev, List.length_map, List.length_firstn; lia. Qed.

(** A record's fields, moved along [σ], split at a field met: the fields
    before it, and its type. *)
Lemma fctx_sub_split : forall R σ pre y T post,
    ctx_args (tele_sub (record_fctx R (List.length (record_fields R))) σ) = pre ++ (y, T) :: post ->
    exists f A, List.nth_error (record_fields R) (List.length pre) = Some (f, A) /\
      rtele pre = tele_sub (record_fctx R (List.length pre)) σ /\ T = A[sb_qn (List.length pre) σ].
Proof.
  intros * H.
  assert (HlF : forall k, k <= List.length (record_fields R) -> List.length (record_fctx R k) = k)
    by (intros k Hk; unfold record_fctx; rewrite List.length_rev, List.length_map, List.length_firstn; lia).
  assert (Hl : List.length pre < List.length (record_fields R)).
  { apply (f_equal (@List.length _)) in H.
    unfold ctx_args in H; rewrite List.length_rev, List.length_map, length_tele_sub, HlF, List.length_app in H by lia; cbn in H.
    lia. }
  destruct (nth_error_lt_some' (record_fields R) _ Hl) as [[f A] HfA].
  exists f, A; split; [ exact HfA |].
  set (k := List.length pre) in *.
  rewrite (record_fctx_at _ _ _ _ HfA), tele_sub_app, ctx_args_app in H; cbn [tele_sub centry_sub] in H.
  assert (Hcons : forall e Y, ctx_args (e :: Y) = ctx_args Y ++ ((""%string, centry_ty e) :: nil)) by (intros; reflexivity).
  rewrite Hcons in H; cbn [centry_ty] in H.
  rewrite <- List.app_assoc in H; cbn [List.app] in H.
  assert (Hass : tele_ass (tele_sub (record_fctx R k) σ))
    by (apply tele_ass_sub; unfold record_fctx, tele_ass; apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; eexists; reflexivity).
  assert (Hla : List.length (ctx_args (tele_sub (record_fctx R k) σ)) = List.length pre)
    by (unfold ctx_args; rewrite List.length_rev, List.length_map, length_tele_sub, HlF by lia; reflexivity).
  destruct (app_split_eq _ _ _ _ H Hla) as [Hpre Hrest].
  injection Hrest as _ HT _.
  split; [ rewrite <- Hpre; apply rtele_ctx_args, Hass |].
  rewrite <- HT, HlF by lia; reflexivity.
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

  Lemma apps_record_not_pi : forall qr Ms B C, apps (a_record qr) Ms <> a_pi B C.
  Proof. intros * H; apply (f_equal app_head) in H; rewrite app_head_apps in H; discriminate. Qed.

  Lemma nbe_ty_record_inv : forall Γ qr Ms W, nbe_ty_f Γ (apps (a_record qr) Ms) W -> exists Rs, W = nf_record qr Rs.
  Proof.
    intros * [ρ m Hinit Ea Hr].
    apply Modules.eval_apps_exp in Ea as (f & ms & Ef & Ems & Eap).
    inversion Ef; subst.
    apply eval_apps_record_inv in Eap; cbn in Eap; subst.
    inversion Hr; subst; eauto.
  Qed.

  (** A member's type, other than a record view's, is its type former's at
      its uniform arguments. *)
  Lemma im_ty_at_not_rview : forall pq k (M : imember) Us Ns, im_is_rview M = false ->
      im_ty_at pq k M Us Ns = apps_exp (a_ind (fst (im_ref pq k M)) (snd (im_ref pq k M))) (im_pre M Us ++ Ns).
  Proof. intros * H; unfold im_ty_at, im_is_rview in *; destruct (im_head M); [ reflexivity | reflexivity | discriminate ]. Qed.

  (** The sibling a member [jm] of the group at [qx] gives at normal
      uniform arguments [Cs]: the member its type former is, at the
      normal forms of its uniform arguments at [Cs]. *)
  Lemma sib_of_member : forall Γu qx D Cs Ws ss jm Mjm, ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack qx = Some D ->
      nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws -> Cs = List.map nf_to_exp Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss -> ind_member D jm = Some Mjm -> im_is_rview Mjm = false ->
      exists Dq WQ, ind_lookup gc_deps gc_stack (fst (im_ref qx jm Mjm)) = Some Dq /\
        nbes gc_deps gc_stack Γu (im_pre Mjm Cs) (tele_insts (ind_uparams Dq) Id (im_pre Mjm Cs)) WQ /\
        In (vk_ind (fst (im_ref qx jm Mjm)) (snd (im_ref qx jm Mjm)) (List.map nf_to_exp WQ)) ss.
  Proof.
    intros * Hg Hl Hn HCs Hss HM Hnr.
    destruct (sibs_from_nth _ _ _ _ _ _ _ _ Hss) as [_ Hssn].
    destruct (Hssn _ _ HM) as (e & He & Hse); cbn [Nat.add] in Hse.
    inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr']; subst;
      unfold im_ref, im_pre; rewrite Hh; cbn [fst snd].
    3:{ exfalso; unfold im_is_rview in Hnr; rewrite Hh in Hnr; discriminate Hnr. }
    - exists D, Ws; split; [ exact Hl | split; [ exact Hn |] ].
      exact (List.nth_error_In _ _ He).
    - destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [_ Hcv].
      rewrite (tele_insts_sub (ind_uparams Dv) 0 Id Id (sb_of_list sb_id (List.map nf_to_exp Ws)) Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv)
                 ltac:(intros; lia)) in Hnv.
      exists Dv, Wv; split; [ exact Hlv | split; [ exact Hnv | exact (List.nth_error_In _ _ He) ] ].
  Qed.

  (** The sibling a record view member [jm] of the group at [qx] gives at
      [Cs]: the record at the normal forms of its instance at [Cs]. *)
  Lemma sib_of_record_member : forall Γu qx D Cs ss jm Mjm qr Ir fl,
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss -> ind_member D jm = Some Mjm ->
      im_head Mjm = mh_record qr Ir fl ->
      exists Rr WQ, record_lookup gc_deps gc_stack qr = Some Rr /\
        nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list sb_id Cs]) Ir)
          (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (record_params Rr) sb_id Ir)) WQ /\
        In (vk_record qr (List.map nf_to_exp WQ)) ss.
  Proof.
    intros * Hss HM Hh.
    destruct (sibs_from_nth _ _ _ _ _ _ _ _ Hss) as [_ Hssn].
    destruct (Hssn _ _ HM) as (e & He & Hse); cbn [Nat.add] in Hse.
    inversion Hse as [? ? pm Hh' | ? ? qv kv Iv vmv Dv Wv Hh' Hlv Hnv | ? ? qr' Ir' fl' Rr Wr Hh' Hlr Hnr']; subst;
      rewrite Hh in Hh'; try discriminate.
    injection Hh' as <- <- <-.
    exists Rr, Wr; split; [ exact Hlr | split; [ exact Hnr' | exact (List.nth_error_In _ _ He) ] ].
  Qed.

  (** A member's uniform arguments at [Cs] are as many as the uniform
      parameters of the group its type former is in.  A record view's
      type former is its record's, whose parameters are not a group's. *)
  Lemma length_im_pre : forall qx D Cs jm Mjm Dq, ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack qx = Some D ->
      List.length Cs = ind_nu D -> ind_member D jm = Some Mjm -> im_is_rview Mjm = false ->
      ind_lookup gc_deps gc_stack (fst (im_ref qx jm Mjm)) = Some Dq ->
      List.length (im_pre Mjm Cs) = ind_nu Dq.
  Proof.
    intros * Hg Hl HCl HM Hnr HlQ; unfold im_ref, im_pre in *.
    destruct (im_head Mjm) as [pm | qv kv Iv vm | qr Ir fl] eqn:Hh; cbn [fst] in HlQ.
    3: { exfalso; unfold im_is_rview in Hnr; rewrite Hh in Hnr; discriminate Hnr. }
    - rewrite Hl in HlQ; injection HlQ as <-; exact HCl.
    - destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dv & Mk' & Hlv & _ & _ & HIl & _).
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
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some gz ->
      In z (rcarg_view gz) ->
      List.length pat = List.length gs1 -> np - nu = im_nn Mi ->
      In z ss.
  Proof.
    intros * Hg Hl HCl Hn HCs Hss HM Hcon Heq HT HW Hcls Hin Hlp Hnn.
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
    2:{ rewrite (nbe_ty_True_inv _ _ HWE) in HWe; cbn [nf_to_exp] in HWe.
        assert (HT0 : forall B C, a_True <> a_pi B C) by (intros B C H0; discriminate H0).
        destruct z as [qz kz Csz | qz Isz].
        - destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & mz & HWe2 & HE2 & Hh2 & _).
          rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 HT0 HWe) as [_ ->]; discriminate.
        - destruct (cls_arg_record_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & HWe2 & HE2 & Hh2 & _).
          rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 HT0 HWe) as [_ ->]; discriminate. }
    pose proof (pis_typed_inv _ _ _ _ HT) as HEt.
    set (Ψ := doms_ctx Bs ++ tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) σ).
    assert (HlΨ : List.length Ψ = K)
      by (unfold Ψ, K, doms_ctx; rewrite List.length_app, length_tele_sub, List.length_rev, List.length_map, List.length_app,
            length_cargs_ctx; unfold im_nn; lia).
    assert (HΨa : tele_ass Ψ).
    { unfold Ψ; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass |].
      apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ Hdt _ _ HM) ]. }
    assert (HΨΓ : ⊢ Ψ ++ Γu) by (unfold Ψ; rewrite <- List.app_assoc; gen_presups; assumption).
    assert (Hctx : doms_ctx Bs ++ Γ = Ψ ++ Γu) by (unfold Ψ, Γ; rewrite List.app_assoc; reflexivity).
    destruct (im_is_rview Mjm) eqn:Hnr.
    { (** a record view member: the end is the record type at the member's
          instance, whose normal form is the sibling's *)
      unfold im_is_rview in Hnr; destruct (im_head Mjm) as [| | qr Ir fl] eqn:Hh; try discriminate Hnr.
      unfold im_ty_at in HT, HWE, HEt; rewrite Hh in HT, HWE, HEt.
      rewrite <- (im_pre_wk D (ptyp_mem t) Mjm Cs (wk_shiftn K) Hc HMjm HCl) in HT, HWE, HEt.
      destruct (nbe_ty_record_inv _ _ _ _ HWE) as [Rs ->].
      cbn [nf_to_exp] in HWe.
      destruct z as [qz kz Csz | qz Isz].
      - exfalso; destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & mz & HWe2 & HE2 & Hh2 & _).
        rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 (apps_record_not_pi _ _) HWe) as [_ ->].
        rewrite app_head_apps in Hh2; discriminate.
      - destruct (cls_arg_record_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & HWe2 & HE2 & Hh2 & _ & _ & HC2).
        rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 (apps_record_not_pi _ _) HWe) as [-> ->].
        rewrite app_head_apps in Hh2; cbn in Hh2; injection Hh2 as <-.
        rewrite app_args_apps in HC2; cbn [app_args List.app] in HC2.
        rewrite List.length_map, HlWB, Hlp, Hnn in HC2.
        replace (List.length Bs + List.length gs1 + im_nn Mi) with K in HC2 by (unfold K; lia).
        destruct (sib_of_record_member _ _ _ _ _ _ _ _ _ _ Hss HMjm Hh) as (Rr & WQ & HlR & HnQ & HinQ).
        destruct (rview_struct_record _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMjm Hh) as [Rr' HRf].
        pose proof (rview_record_lookup _ _ _ _ _ _ HRf) as HlR'; rewrite HlR in HlR'; injection HlR' as <-.
        pose proof (rview_record_count _ _ _ _ _ _ HRf) as HIl.
        pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) HlR) as HcR.
        pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR) as HRt.
        assert (HRa : tele_ass (record_params Rr)) by exact (typed_params_ass _ _ _ HRt).
        set (Q := im_pre Mjm Cs) in *.
        assert (EQ : Q = List.map (fun I => I[sb_of_list sb_id Cs]) Ir) by (unfold Q, im_pre; rewrite Hh; reflexivity).
        pose proof (wf_record_apps_len _ _ _ _ _ HlR HEt) as HRl.
        (** no argument past the instance *)
        assert (HPs : Ps = nil).
        { rewrite List.length_app, !List.length_map, EQ, List.length_map, HIl in HRl.
          destruct Ps; [ reflexivity | cbn in HRl; lia ]. }
        subst Ps; cbn [List.map] in HT, HEt, HWE; rewrite List.app_nil_r in HT, HEt, HWE.
        rewrite <- EQ, (record_params_insts_sub Rr Ir (sb_of_list sb_id Cs) HcR), <- EQ in HnQ.
        destruct (nbes_nth _ _ _ _ _ _ HnQ) as (HlWQ & HlTQ & HnthQ).
        assert (HlQ : List.length Q = List.length (record_params Rr)) by (rewrite EQ, List.length_map; exact HIl).
        assert (HlI : List.length Isz = List.length Q)
          by (pose proof (soundness_ty' HEt HWE) as HTW'; cbn [nf_to_exp] in HTW';
              assert (HWt' : doms_ctx Bs ++ Γ ⊢ apps (a_record qr) (List.map nf_to_exp Rs) : Typeω@i) by (gen_presups; assumption);
              pose proof (wf_record_apps_len _ _ _ _ _ HlR HWt') as HRl';
              apply (f_equal (@List.length _)) in HC2; rewrite List.length_map in HRl'; rewrite !List.length_map in HC2; lia).
        (** each found argument, strengthened, is the normal form of the
            sibling's argument there *)
        assert (Heqc : Isz = List.map nf_to_exp WQ).
        { apply List.nth_error_ext; intros j.
          destruct (Nat.lt_ge_cases j (List.length Q)) as [Hj | Hj];
            [| rewrite !(proj2 (List.nth_error_None _ _)) by (rewrite ?List.length_map; lia); reflexivity ].
          destruct (nth_error_lt_some' Isz j ltac:(lia)) as [C HCj].
          destruct (nth_error_lt_some' Q j Hj) as [Qj HQj].
          destruct (nth_error_lt_some' (tele_insts (record_params Rr) Id Q) j
                      ltac:(rewrite length_tele_insts by exact HRa; lia)) as [T0 HT0].
          destruct (HnthQ _ _ _ HQj HT0) as (W0 & HW0 & HQt & HnQj).
          destruct (nbe_wk_tele Ψ Γu Qj T0 W0 HΨa HΨΓ HQt HnQj) as (W' & HW' & HW'e).
          rewrite HlΨ in HW', HW'e.
          assert (HT0w : List.nth_error (tele_insts (record_params Rr) Id (List.map (fun N => N[wk_shiftn K]ʷ) Q)) j
                         = Some T0[wk_shiftn K]ʷ).
          { rewrite (List.map_ext (fun N => N[wk_shiftn K]ʷ) (fun M => M[ι (wk_shiftn K)]) (fun M => eq_sym (exp_sub_of_wk M _))).
            rewrite (tele_insts_closed_sub _ _ _ _ _ HRa (closed_params _ HcR) HT0), exp_sub_of_wk; reflexivity. }
          assert (HPj : List.nth_error (List.map (fun N => N[wk_shiftn K]ʷ) Q) j = Some Qj[wk_shiftn K]ʷ)
            by (rewrite List.nth_error_map, HQj; reflexivity).
          destruct (nbe_record_args _ _ _ _ _ _ HlR HEt HWE j _ _ HPj HT0w) as (R & HR & HnR).
          rewrite Hctx in HnR.
          pose proof (functional_nbe _ _ _ _ _ HnR HW') as ->.
          assert (HCw : List.nth_error (List.map (fun C => C[wk_pat (List.repeat true K)]ʷ) Isz) j
                        = Some C[wk_pat (List.repeat true K)]ʷ)
            by (rewrite List.nth_error_map, HCj; reflexivity).
          rewrite <- HC2, List.nth_error_map, HR in HCw; cbn in HCw; injection HCw as HCw.
          rewrite HW'e, <- (exp_wk_wk_eq _ _ _ (wk_pat_trues K)) in HCw.
          apply exp_wk_pat_inj in HCw.
          rewrite HCj, List.nth_error_map, HW0; cbn; rewrite HCw; reflexivity. }
        rewrite Heqc; exact HinQ. }
    destruct z as [qz kz Csz | qz Isz].
    2:{ exfalso; rewrite (im_ty_at_not_rview _ _ _ _ _ Hnr) in HWE; destruct (nbe_ty_ind_inv _ _ _ _ _ HWE) as [Rs ->].
        cbn [nf_to_exp] in HWe; destruct (cls_arg_record_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & HWe2 & HE2 & Hh2 & _).
        rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 (apps_ind_not_pi _ _ _) HWe) as [_ ->].
        rewrite app_head_apps in Hh2; discriminate. }
    destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & mz & HWe2 & HE2 & Hh2 & Hg2 & Hm2 & HC2).
    rewrite (im_ty_at_not_rview _ _ _ _ _ Hnr) in HT, HWE, HEt.
    rewrite <- (im_pre_wk D (ptyp_mem t) Mjm Cs (wk_shiftn K) Hc HMjm HCl) in HT, HWE, HEt.
    (** its normal form ends in the member's at the normal forms of its
        arguments: that is where the occurrence is found *)
    destruct (nbe_ty_ind_inv _ _ _ _ _ HWE) as [Rs ->].
    cbn [nf_to_exp] in HWe; rewrite HWe2 in HWe.
    destruct (pis_inj _ _ _ _ HE2 (apps_ind_not_pi _ _ _) HWe) as [-> ->].
    rewrite app_head_apps in Hh2; cbn in Hh2; injection Hh2 as Hqz Hkz.
    rewrite app_args_apps in Hm2, HC2; cbn [app_args List.app] in Hm2, HC2.
    rewrite List.length_map, HlWB, Hlp, Hnn in HC2.
    replace (List.length Bs + List.length gs1 + im_nn Mi) with K in HC2 by (unfold K; lia).
    destruct (sib_of_member _ _ _ _ _ _ _ _ Hg Hl Hn HCs Hss HMjm Hnr) as (Dq & WQ & HlQ & HnQ & HinQ).
    pose proof (length_im_pre _ _ _ _ _ _ Hg Hl HCl HMjm Hnr HlQ) as HlQu.
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
    pose proof (ind_type_length _ _ _ _ _ _ _ HlQ HMkr HEt) as HRl.
    pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ HlQ HMkr HEt HRl) as HRt.
    destruct (nbes_nth _ _ _ _ _ _ HnQ) as (HlWQ & HlTQ & HnthQ).
    assert (HCszl : List.length Csz = ind_nu Dq)
      by (apply (f_equal (@List.length _)) in HC2; rewrite List.length_firstn, !List.length_map in HC2; rewrite ?List.length_map in Hm2; lia).
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
      pose proof (tele_insts_params_uniform_wk Dq Mkr Q args (wk_shiftn K) j T0 (decl_closed_ass _ Hcq) (decl_closed_uparams _ Hcq) HlQu Hfa HT0) as HT0w.
      assert (HPj : List.nth_error args j = Some Qj[wk_shiftn K]ʷ)
        by (unfold args; rewrite List.nth_error_app1 by (rewrite List.length_map; lia); rewrite List.nth_error_map, HQj; reflexivity).
      destruct (nbe_ind_args _ _ _ _ _ _ _ HlQ HMkr HRl HRt HWE j _ _ HPj HT0w) as (R & HR & HnR).
      rewrite Hctx in HnR.
      pose proof (functional_nbe _ _ _ _ _ HnR HW') as ->.
      assert (HCw : List.nth_error (List.map (fun C => C[wk_pat (List.repeat true K)]ʷ) Csz) j = Some C[wk_pat (List.repeat true K)]ʷ)
        by (rewrite List.nth_error_map, HCj; reflexivity).
      rewrite <- HC2, List.nth_error_firstn in HCw.
      destruct (j <? ind_nu Dq) eqn:Ejn; [| apply Nat.ltb_ge in Ejn; lia ].
      rewrite List.nth_error_map, HR in HCw; cbn in HCw; injection HCw as HCw.
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
    pose proof (valid_groups_of_embedding _ _ _ _ (valid_gctx_embedding_refl _ _ Hg)) as HV.
    split; [ exact (valid_groups_valid _ HV _ _ Hl) | exact (containers_valid_of_groups _ HV _ _ Hl) ].
  Qed.

  (** A record filed in a well-formed global context is a valid record. *)
  Lemma valid_rview_record_gc : forall qr R, ⊢ᵍ gc_deps ⍮ gc_stack -> record_lookup gc_deps gc_stack qr = Some R ->
      valid_rview_record qr R.
  Proof.
    intros qr R Hg Hl; destruct GC as [Θ Ξ]; cbn in *.
    exact (@mk_valid_rview_record (gc_mk Θ Ξ) _ _ Hl (valid_gctx_embedding_record _ _ _ _ (valid_gctx_embedding_refl _ _ Hg) _ _ Hl)
             (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl)).
  Qed.

  (** A declared member at uniform arguments related to themselves, and
      some non-uniform ones, is a type of the model. *)
  Lemma decl_member_type : forall p D k Mk ups, ⊢ᵍ gc_deps ⍮ gc_stack -> ind_lookup gc_deps gc_stack p = Some D ->
      ind_member D k = Some Mk -> k < ind_ndecl D ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      exists ns (i : universe_index) R, DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ R.
  Proof.
    intros * Hg Hl HM Hk Hgu Hu.
    destruct (valid_group_gc _ _ Hg Hl) as [Hvg _].
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    assert (Hd : im_is_decl Mk = true) by (apply (decl_typed_order _ _ _ Hdt _ _ HM); exact Hk).
    unfold im_is_decl in Hd; destruct (im_head Mk) as [pm | ? ? ? ? | ? ? ?] eqn:Hh; [| discriminate .. ].
    destruct (sort_value D (valid_group_valid _ _ Hvg) ups Hgu Hu) as [a Ea].
    destruct (fresh_nparams_exist _ _ Hvg ups Hgu Hu k Mk 0 HM) as (ns & _ & Hns).
    exists ns, (univ_idx a); eexists.
    exact (ind_relate D (valid_group_valid _ _ Hvg) (valid_group_closed _ _ Hvg) (valid_group_sort _ _ Hvg) p Hl (valid_group_ass _ _ Hvg)
             k Mk pm ups ups ns ns a HM Hh Hgu Hu Ea Hns).
  Qed.

  (** ** The Shape End of an Argument's Normal Form, Semantically

      A type [X] over a closed telescope [Δ] of a closed telescope [U],
      at an instance [Cs] of [U] over [Γu]: at elements [xs] of [Δ] at the
      values [us] of [Cs], the value of the normal form of [X] at [Cs] is
      related to [X]'s at [us] and [xs], and the end of its [Π]s at fresh
      variables [ws] is the value of the normal form's end. *)
  Lemma arg_shape_end : forall Γu U Δ X (jX : nat) Cs ρ0 us (i : nat) W Bs E,
      ⊢ Γu -> tele_ass U -> ⊨ U -> tele_ass Δ -> ⊨ Δ ++ U -> Δ ++ U ⊨ X : Typeω@jX ->
      List.length Cs = List.length U ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts U Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      tele_sub Δ (sb_of_list Id Cs) ++ Γu ⊢ X[sb_qn (List.length Δ) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub Δ (sb_of_list Id Cs) ++ Γu) X[sb_qn (List.length Δ) (sb_of_list Id Cs)] W ->
      nf_to_exp W = pis Bs E ->
      exists xs a w ws e RE, per_gargs (List.rev U) nil nil us us /\ List.length us = List.length U /\
        per_gargs (List.rev Δ) (env_args nil us) (env_args nil us) xs xs /\ List.length xs = List.length Δ /\
        ⟦ X ⟧ env_args nil (us ++ xs) ↘ a /\ per_univ i w a /\ shape_end e w /\
        EF (doms_ctx Bs ++ tele_sub Δ (sb_of_list Id Cs)) ++ Γu ≈ (doms_ctx Bs ++ tele_sub Δ (sb_of_list Id Cs)) ++ Γu
          ∈ per_ctx_env ↘ RE /\
        RE (env_args ρ0 (xs ++ ws)) (env_args ρ0 (xs ++ ws)) /\ List.length ws = List.length Bs /\
        ⟦ E ⟧ env_args ρ0 (xs ++ ws) ↘ e.
  Proof.
    intros * HΓu HUa HUs HΔa' HΔU HXs HCl HCt Hρ0 Eus HT HW HWe.
    set (σ := sb_of_list Id Cs) in *.
    destruct (inst_gargs Γu U Cs ρ0 HUa HUs HΓu HCl HCt Hρ0) as (us' & Eus' & Hgu & Hlu).
    pose proof (functional_eval_exps' _ _ _ _ Eus' Eus) as ->.
    assert (HΔa : tele_ass (Δ ++ U)) by (apply List.Forall_app; split; assumption).
    destruct (rel_ctx_wf_per_ctx_env HUs) as [RU HRU].
    assert (HUU : RU (env_args nil us) (env_args nil us)).
    { assert (HRU0 : EF U ++ ⋅ ≈ U ++ ⋅ ∈ per_ctx_env ↘ RU) by (rewrite List.app_nil_r; exact HRU).
      apply (gargs_env_rel_gen _ _ _ _ _ _ _ _ per_ctx_env_nil_true HRU0 ltac:(rewrite List.app_nil_r; exact HUs) I Hlu Hgu). }
    (** fresh elements of the telescope *)
    destruct (gargs_exist Δ U RU (env_args nil us) HΔa' HΔU HRU HUU) as (xs & Hxs & Hlx).
    assert (HU0 : RU (env_args nil us) (env_args ρ0 us)) by exact (closed_env_base _ _ _ _ nil nil nil ρ0 HUa HUs HRU Hlu Hlu HUU).
    pose proof (per_gargs_base (List.rev Δ) U RU HRU ltac:(rewrite List.rev_involutive; exact HΔU) (List.Forall_rev HΔa')
                  _ _ (env_args ρ0 us) (env_args ρ0 us) xs xs HUU HU0 HU0 Hxs) as Hxsσ.
    (** the instance along [Cs] over [Γu] *)
    pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
    pose proof (gsub_valid (gsub_closed_inst U Γu Cs HUa HUs HΓs HCl
                  (fun j N T HN HT0 => completeness_fundamental_exp _ _ _ (HCt j N T HN HT0)))) as Hτ.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
    destruct (per_ctx_then_per_env_initial_env HRΓu) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hρ0) as ->; pose proof (functional_initial_env _ _ Hib _ Hρ0) as ->.
    assert (Eσ : ⟦ σ ⟧s gc_deps ⍮ gc_stack ⍮ ρ0 ↘ env_args ρ0 us) by (apply eval_sb_of_list; [ apply eval_sub_id | exact Eus ]).
    assert (HΔUΓ : ⊨ Δ ++ U ++ Γu)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HΔa HΔU HΓs))).
    destruct (outer_base Δ (U ++ Γu) Γu RΓu σ ρ0 (env_args ρ0 us) HΔa' HΔUΓ HRΓu Hτ Hab Eσ xs Hxsσ Hlx)
      as (RS & RΔ & Y & HRS & HSS & HRΔ & _ & _ & _).
    assert (HXΓ : Δ ++ U ++ Γu ⊨ X : Typeω@jX)
      by (rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ HΔa HΔU HΓs HXs)).
    destruct (outer_typ_link Δ (U ++ Γu) Γu RΓu σ ρ0 (env_args ρ0 us) X X jX HΔa' HΔUΓ HXΓ HRΓu Hτ Hab Eσ xs Hxsσ Hlx)
      as (t & b & Et & Eb & Htb).
    (** the normal form's value, related to the type's *)
    pose proof (soundness_ty' HT HW) as HTW.
    destruct (rel_exp_of_typ_inversion_simple_at HRS (completeness_fundamental_exp_eq _ _ _ _ HTW) _ _ HSS)
      as (t' & w & Et' & Ew & Htw).
    pose proof (functional_eval_exp _ _ _ _ Et' Et) as ->.
    (** the type at the elements, over the closed telescope *)
    assert (Hall : per_gargs (List.rev (Δ ++ U)) nil nil (us ++ xs) (us ++ xs))
      by (rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlu | exact Hgu | exact Hxs ]).
    destruct (rel_ctx_wf_per_ctx_env HΔU) as [RC HRC].
    assert (Hlen0 : List.length (us ++ xs) = List.length (Δ ++ U)) by (rewrite !List.length_app; lia).
    assert (HCC : RC (env_args nil (us ++ xs)) (env_args nil (us ++ xs))).
    { assert (HRC0 : EF (Δ ++ U) ++ ⋅ ≈ (Δ ++ U) ++ ⋅ ∈ per_ctx_env ↘ RC) by (rewrite List.app_nil_r; exact HRC).
      assert (HC0 : ⊨ (Δ ++ U) ++ ⋅) by (rewrite List.app_nil_r; exact HΔU).
      exact (gargs_env_rel_gen (Δ ++ U) nil (fun _ _ => True) RC nil nil (us ++ xs) (us ++ xs)
               per_ctx_env_nil_true HRC0 HC0 I Hlen0 Hall). }
    pose proof (closed_env_base _ _ _ _ nil nil ρ0 nil HΔa HΔU HRC Hlen0 Hlen0 HCC) as HCC'.
    destruct (rel_exp_of_typ_inversion_simple_at HRC HXs _ _ HCC') as (b' & a2 & Eb' & Ea2 & Hba).
    rewrite <- env_args_app in Eb.
    pose proof (functional_eval_exp _ _ _ _ Eb' Eb) as ->.
    assert (Hwa : per_univ i w a2).
    { eapply per_univ_trans'; [ apply per_univ_sym'; exact Htw |].
      eapply per_univ_trans'; [ exact Htb | exact Hba ]. }
    (** the end of the normal form's [Π]s *)
    assert (HWt : tele_sub Δ σ ++ Γu ⊢ pis Bs E : Typeω@i) by (rewrite <- HWe; gen_presups; assumption).
    rewrite HWe in Ew.
    destruct (shape_end_at Bs _ _ i RS (env_args ρ0 xs) w HWt HRS HSS Ew) as (ws & e & RE & HRE & HEE & Hlw & Hse & Ee).
    rewrite <- env_args_app in HEE, Ee.
    exists xs, a2, w, ws, e, RE; repeat split; try assumption.
    rewrite <- List.app_assoc; exact HRE.
  Qed.

  (** A member of a filed group at uniform arguments [Csz] over [Γu]
      whose weakenings are the first arguments of the end [apps (a_ind qz
      kz) Rs] of a normal form, evaluated at an extension [zs] of the
      initial environment: the member at the values of [Csz] is related to
      the end's value. *)
  Lemma ind_end_rel : forall Γu Ψ ρ0 zs RE (i : nat) qz kz Rs Dz Csz e,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> initial_env_f Γu ρ0 ->
      EF Ψ ++ Γu ≈ Ψ ++ Γu ∈ per_ctx_env ↘ RE -> RE (env_args ρ0 zs) (env_args ρ0 zs) -> List.length zs = List.length Ψ ->
      Ψ ++ Γu ⊢ apps (a_ind qz kz) (List.map nf_to_exp Rs) : Typeω@i ->
      ⟦ apps (a_ind qz kz) (List.map nf_to_exp Rs) ⟧ env_args ρ0 zs ↘ e ->
      ind_lookup gc_deps gc_stack qz = Some Dz -> kz < ind_ndecl Dz -> List.length Csz = ind_nu Dz ->
      (forall j C T, List.nth_error Csz j = Some C -> List.nth_error (tele_insts (ind_uparams Dz) Id Csz) j = Some T ->
         Γu ⊢ C : T) ->
      List.firstn (ind_nu Dz) (List.map nf_to_exp Rs) = List.map (fun C => C[wk_pat (List.repeat true (List.length Ψ))]ʷ) Csz ->
      exists usz nsz, ⟦ Csz ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ usz /\ List.length usz = ind_nu Dz /\
        exists j : universe_index, per_univ j (d_ind qz kz (usz ++ nsz)) e.
  Proof.
    intros * Hg HΓu Hρ0 HRE HEE Hlz HEt Ee Hlz' Hkz HCzl HCzt HCz.
    destruct (valid_group_gc _ _ Hg Hlz') as [Hvgz _].
    destruct (decl_of_glookup _ _ _ _ Hg Hlz') as [Hdtz Hcz].
    destruct (rel_exp_of_typ_inversion_simple_at HRE (completeness_fundamental_exp _ _ _ HEt) _ _ HEE)
      as (e1 & e2 & Ee1 & Ee2 & [Re HRe]).
    pose proof (functional_eval_exp _ _ _ _ Ee1 Ee) as ->; pose proof (functional_eval_exp _ _ _ _ Ee2 Ee) as ->.
    pose proof Ee as Ee0.
    apply Modules.eval_apps_exp in Ee0 as (f & msE & Ef & EmsE & Eap).
    inversion Ef; match goal with H : _ = f |- _ => subst f | H : f = _ |- _ => subst f end.
    apply eval_apps_ind_inv in Eap; cbn in Eap.
    subst e; clear Ef.
    (** the end's uniform arguments: the values of [Csz] weakened past the
        extension, related to those of [Csz] at the initial environment *)
    destruct (wk_inst_gargs Ψ Γu (ind_uparams Dz) Csz ρ0 zs RE (decl_closed_ass _ Hcz) (valid_ind_decl_uparams _ (valid_group_valid _ _ Hvgz)) HΓu
                ltac:(rewrite HCzl; reflexivity) HCzt Hρ0 HRE HEE Hlz)
      as (usz & usE & Eusz & EusE & HgE).
    assert (Hfm : forall n Ms0 ms0 ρe, ⟦ Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρe ↘ ms0 ->
              ⟦ List.firstn n Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρe ↘ List.firstn n ms0).
    { induction n as [| n IHn]; intros Ms0 ms0 ρe Hev; [ cbn; constructor |].
      destruct Hev; cbn; constructor; auto. }
    pose proof (Hfm (ind_nu Dz) _ _ _ EmsE) as EfE.
    rewrite HCz in EfE.
    rewrite (List.map_ext _ (fun C => C[wk_shiftn (List.length Ψ)]ʷ)) in EfE by (intros C; apply exp_wk_wk_eq, wk_pat_trues).
    pose proof (functional_eval_exps' _ _ _ _ EfE EusE) as HfE.
    assert (HlE : List.length usE = ind_nu Dz)
      by (pose proof (eval_exps_length _ _ _ EusE) as H; rewrite List.length_map in H; lia).
    assert (HlZ : List.length usz = ind_nu Dz) by (pose proof (eval_exps_length _ _ _ Eusz); lia).
    set (nsE := List.skipn (ind_nu Dz) msE).
    assert (HmsE : msE = usE ++ nsE) by (rewrite <- HfE; symmetry; apply List.firstn_skipn).
    rewrite HmsE in HRe |- *.
    (** the member at [Csz] is related to the end *)
    destruct (List.nth_error (ind_members Dz) kz) as [Mkz |] eqn:HMkz;
      [| apply List.nth_error_None in HMkz; pose proof (ind_ndecl_le Dz); lia ].
    change (ind_member Dz kz = Some Mkz) in HMkz.
    assert (Hdz : im_is_decl Mkz = true) by (apply (decl_typed_order _ _ _ Hdtz _ _ HMkz); exact Hkz).
    unfold im_is_decl in Hdz; destruct (im_head Mkz) as [pmz | ? ? ? ? | ? ? ?] eqn:Hhz; [| discriminate .. ].
    pose proof (ind_canon_clause_ns _ _ _ _ _ _ _ _ (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HRe Hlz' HlE HlE)) as HnsE.
    unfold member_nparams in HnsE; rewrite HMkz in HnsE.
    pose proof (uparams_refl_l Dz (valid_group_valid _ _ Hvgz) Hcz _ _ HgE) as HgEE.
    destruct (sort_value Dz (valid_group_valid _ _ Hvgz) usE HgEE HlE) as [aE EaE].
    pose proof (ind_relate Dz (valid_group_valid _ _ Hvgz) Hcz (valid_group_sort _ _ Hvgz) qz Hlz' (valid_group_ass _ _ Hvgz) kz Mkz pmz usE usz nsE nsE aE
                  HMkz Hhz HgE HlE EaE HnsE) as HEZ.
    exists usz, nsE; split; [ exact Eusz | split; [ exact HlZ |] ].
    exists (univ_idx aE); eapply per_univ_trans'; [ eexists; apply per_univ_sym; exact HEZ | eexists; exact HRe ].
  Qed.

  (** Likewise a record type at an instance [Isz] over [Γu] whose
      weakenings are the arguments of the end [apps (a_record qz) Rs]. *)
  Lemma record_end_rel : forall Γu Ψ ρ0 zs RE qz Rs Rz Isz e,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> initial_env_f Γu ρ0 ->
      EF Ψ ++ Γu ≈ Ψ ++ Γu ∈ per_ctx_env ↘ RE -> RE (env_args ρ0 zs) (env_args ρ0 zs) -> List.length zs = List.length Ψ ->
      ⟦ apps (a_record qz) (List.map nf_to_exp Rs) ⟧ env_args ρ0 zs ↘ e ->
      record_lookup gc_deps gc_stack qz = Some Rz -> List.length Isz = List.length (record_params Rz) ->
      (forall j C T, List.nth_error Isz j = Some C -> List.nth_error (tele_insts (record_params Rz) Id Isz) j = Some T ->
         Γu ⊢ C : T) ->
      List.map nf_to_exp Rs = List.map (fun C => C[wk_pat (List.repeat true (List.length Ψ))]ʷ) Isz ->
      exists usz, ⟦ Isz ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ usz /\ List.length usz = List.length (record_params Rz) /\
        exists j : universe_index, exists R, DF d_record qz usz ≈ e ∈ per_univ_elem j ↘ R.
  Proof.
    intros * Hg HΓu Hρ0 HRE HEE Hlz Ee Hlr HIzl HIzt HCz.
    pose proof Ee as Ee0.
    apply Modules.eval_apps_exp in Ee0 as (f & msE & Ef & EmsE & Eap).
    inversion Ef; match goal with H : _ = f |- _ => subst f | H : f = _ |- _ => subst f end.
    apply eval_apps_record_inv in Eap; cbn in Eap.
    subst e; clear Ef.
    pose proof (valid_rview_record_gc _ _ Hg Hlr) as HvR.
    destruct (wk_inst_gargs Ψ Γu (record_params Rz) Isz ρ0 zs RE (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HvR))
                (params_valid _ (valid_rview_record_valid _ _ HvR)) HΓu HIzl HIzt Hρ0 HRE HEE Hlz)
      as (usz & usE & Eusz & EusE & HgE).
    rewrite HCz in EmsE.
    rewrite (List.map_ext _ (fun C => C[wk_shiftn (List.length Ψ)]ʷ)) in EmsE by (intros C; apply exp_wk_wk_eq, wk_pat_trues).
    pose proof (functional_eval_exps' _ _ _ _ EmsE EusE) as ->.
    assert (HlE : List.length usE = List.length (record_params Rz))
      by (pose proof (eval_exps_length _ _ _ EusE) as H; rewrite List.length_map in H; lia).
    assert (HlZ : List.length usz = List.length (record_params Rz)) by (pose proof (eval_exps_length _ _ _ Eusz); lia).
    destruct (vrr_type_rel qz Rz usE usz HvR HgE HlE) as [iz HEZ].
    exists usz; split; [ exact Eusz | split; [ exact HlZ |] ].
    exists iz; eexists; apply per_univ_sym; exact HEZ.
  Qed.

  (** The end of the normal form of a non-recursive argument of a
      constructor of a member of the group at [p] at [Cs], at fresh
      variables [zs] of the arguments before, the member's non-uniform
      parameters and the normal form's domains: every type related to it
      is one nesting step out of every member of the group at [Cs]. *)
  Lemma nonrec_step : forall Γu p D k Cs ρ0 us m Mi c gs gs1 A gs2 (i : nat) W Bs E,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_arg A :: gs2 ->
      tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu
        ⊢ A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu)
        A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] W ->
      nf_to_exp W = pis Bs E ->
      exists zs e RE,
        EF (doms_ctx Bs ++ tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) ++ Γu
          ≈ (doms_ctx Bs ++ tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) ++ Γu ∈ per_ctx_env ↘ RE /\
        RE (env_args ρ0 zs) (env_args ρ0 zs) /\ List.length zs = List.length Bs + List.length gs1 + im_nn Mi /\
        ⟦ E ⟧ env_args ρ0 zs ↘ e /\
        forall b (j : universe_index) R, DF b ≈ e ∈ per_univ_elem j ↘ R -> grp_step b (d_ind p k us).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe.
    set (Δ := cargs_ctx p D Mi gs1 ++ im_nparams Mi) in *.
    destruct (valid_group_gc _ _ Hg Hl) as [Hvg Hcv].
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
    assert (HlΔ : List.length Δ = List.length gs1 + im_nn Mi)
      by (unfold Δ; rewrite List.length_app, length_cargs_ctx; reflexivity).
    rewrite <- HlΔ in HT, HW.
    pose proof (valid_ind_decl_uparams _ (valid_group_valid _ _ Hvg)) as HUs.
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
    assert (HΔa' : tele_ass Δ) by (apply List.Forall_app in HΔa as [H _]; exact H).
    destruct (arg_shape_end Γu (ind_uparams D) Δ (A[wk_pat (cargs_pat gs1)]ʷ) jX Cs ρ0 us i W Bs E HΓu (decl_closed_ass _ Hc) HUs
                HΔa' HΔU HXs ltac:(rewrite HCl; reflexivity) HCt Hρ0 Eus HT HW HWe)
      as (xs & a & w & ws & e & RE & Hgu & Hlu & Hxs & Hlx & Ea & Hwa & Hse & HRE & HEE & Hlw & Ee).
    exists (xs ++ ws), e, RE; split; [ exact HRE | split; [ exact HEE | split; [ rewrite List.length_app, Hlx, Hlw, HlΔ; lia | split; [ exact Ee |] ] ] ].
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
      as (iA & RA & a0 & a' & Ea0 & Ea' & HRA).
    rewrite <- Hxs_eq in Ea0; pose proof (functional_eval_exp _ _ _ _ Ea0 Ea) as ->.
    assert (Hwa' : per_univ i w a') by (eapply per_univ_trans'; [ exact Hwa | exists RA; exact HRA ]).
    destruct Hwa' as [R0 HR0].
    intros b j R Hb.
    rewrite <- (List.app_nil_r us).
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    assert (Hfirst : List.firstn (List.length (cargs_nonrec gs1)) (cargs_nonrec gs) = cargs_nonrec gs1)
      by (rewrite Heq, cargs_nonrec_app, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
    assert (Hlr : List.length ms = List.length (List.rev (im_nparams Mi))) by (rewrite List.length_rev; exact Hlms).
    unfold Δ in Hxs; rewrite List.rev_app_distr, Hxs_eq in Hxs.
    destruct (per_gargs_app _ _ _ _ _ _ _ _ Hlr Hxs Hlr) as [Hms0 _].
    rewrite <- (List.app_nil_r us) in Hms0.
    pose proof (per_gargs_tele_elems _ us nil nil ms Hms0 Hlr (tele_elems_nil _)) as Hms; cbn [List.app] in Hms.
    pose proof (nonrec_elems p D m Mi c gs Hvg Hcv HM Hcon gs1 (ca_arg A :: gs2) us ms vs Heq ltac:(rewrite Hlu; reflexivity)
                  Hlms Hlvs Hall') as Hvs.
    rewrite <- Hfirst in Hvs.
    exact (grp_step_intro b p k D us nil m Mi c gs _ A ms _ a' i R0 w e j R Hl ltac:(rewrite Hlu; reflexivity) HM Hcon HA Hms Hvs Ea'
             HR0 Hse Hb).
  Qed.

  (** The end of the normal form of a field of the record at [qx] at an
      instance [Isx], at fresh variables [zs] of the fields before and
      the normal form's domains: every type related to it is one nesting
      step out of the record type at the instance. *)
  Lemma field_step : forall Γu qx Rx Isx ρ0 usx j f A (i : nat) W Bs E,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> record_lookup gc_deps gc_stack qx = Some Rx ->
      List.length Isx = List.length (record_params Rx) ->
      (forall j C T, List.nth_error Isx j = Some C -> List.nth_error (tele_insts (record_params Rx) Id Isx) j = Some T ->
         Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Isx ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ usx ->
      List.nth_error (record_fields Rx) j = Some (f, A) ->
      tele_sub (record_fctx Rx j) (sb_of_list Id Isx) ++ Γu ⊢ A[sb_qn j (sb_of_list Id Isx)] : Typeω@i ->
      nbe_ty_f (tele_sub (record_fctx Rx j) (sb_of_list Id Isx) ++ Γu) A[sb_qn j (sb_of_list Id Isx)] W ->
      nf_to_exp W = pis Bs E ->
      exists zs e RE,
        EF (doms_ctx Bs ++ tele_sub (record_fctx Rx j) (sb_of_list Id Isx)) ++ Γu
          ≈ (doms_ctx Bs ++ tele_sub (record_fctx Rx j) (sb_of_list Id Isx)) ++ Γu ∈ per_ctx_env ↘ RE /\
        RE (env_args ρ0 zs) (env_args ρ0 zs) /\ List.length zs = List.length Bs + j /\
        ⟦ E ⟧ env_args ρ0 zs ↘ e /\
        forall b (j' : universe_index) R, DF b ≈ e ∈ per_univ_elem j' ↘ R -> grp_step b (d_record qx usx).
  Proof.
    intros * Hg HΓu Hl HIl HIt Hρ0 Eus HfA HT HW HWe.
    pose proof (valid_rview_record_gc _ _ Hg Hl) as HvR.
    pose proof (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HvR)) as HUa.
    pose proof (params_valid _ (valid_rview_record_valid _ _ HvR)) as HUs.
    pose proof (field_ctx_valid _ (valid_rview_record_valid _ _ HvR)) as HFs.
    assert (Hjl : j < List.length (record_fields Rx)) by (apply List.nth_error_Some; congruence).
    assert (HlΔ : List.length (record_fctx Rx j) = j) by (apply length_record_fctx_le; lia).
    (** the fields before, and the field's type over them *)
    rewrite (record_fctx_at _ _ _ _ HfA), <- List.app_assoc in HFs.
    pose proof (rel_ctx_wf_app_r _ _ HFs) as HAF; cbn [List.app] in HAF.
    destruct (rel_ctx_wf_ass_inv HAF) as [jX HXs].
    pose proof (rel_ctx_wf_tail HAF) as HΔU.
    assert (HΔa : tele_ass (record_fctx Rx j)) by apply record_fctx_ass.
    destruct (arg_shape_end Γu (record_params Rx) (record_fctx Rx j) A jX Isx ρ0 usx i W Bs E HΓu HUa HUs HΔa HΔU HXs HIl HIt
                Hρ0 Eus ltac:(rewrite HlΔ; exact HT) ltac:(rewrite HlΔ; exact HW) HWe)
      as (xs & a & w & ws & e & RE & Hgu & Hlu & Hxs & Hlx & Ea & Hwa & Hse & HRE & HEE & Hlw & Ee).
    exists (xs ++ ws), e, RE; split; [ exact HRE | split; [ exact HEE | split; [ rewrite List.length_app, Hlx, Hlw, HlΔ; lia | split; [ exact Ee |] ] ] ].
    destruct Hwa as [R0 HR0].
    intros b j' R Hb.
    (** the elements of the fields before, as the record clause reads them *)
    assert (Hrev : List.rev (record_fctx Rx j) = List.map (fun fT => ce_ass (snd fT)) (List.firstn j (record_fields Rx)))
      by (unfold record_fctx; apply List.rev_involutive).
    rewrite Hrev in Hxs.
    rewrite <- (List.app_nil_r usx) in Hxs.
    pose proof (per_gargs_tele_elems _ usx nil nil xs Hxs ltac:(rewrite List.length_map, List.length_firstn; lia) (tele_elems_nil _))
      as Hvs; cbn [List.app] in Hvs.
    exact (grp_step_record b qx Rx usx j f A xs a i R0 w e j' R Hl HfA Hvs Ea HR0 Hse Hb).
  Qed.

  (** The end of a normal form of a type, over [Δ ++ Γu], is a type over
      its domains. *)
  Lemma nf_end_typed : forall Δ Γu T W (i : nat) Bs E, Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W ->
      nf_to_exp W = pis Bs E -> (doms_ctx Bs ++ Δ) ++ Γu ⊢ E : Typeω@i.
  Proof.
    intros * HT HW HWe; pose proof (soundness_ty' HT HW) as HTW.
    assert (HWt : Δ ++ Γu ⊢ nf_to_exp W : Typeω@i) by (gen_presups; assumption).
    rewrite HWe in HWt; rewrite <- List.app_assoc; exact (pis_typed_inv _ _ _ _ HWt).
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
      nf_to_exp W = pis Bs (apps (a_ind qz kz) (List.map nf_to_exp Rs)) ->
      ind_lookup gc_deps gc_stack qz = Some Dz -> kz < ind_ndecl Dz -> List.length Csz = ind_nu Dz ->
      (forall j C T, List.nth_error Csz j = Some C -> List.nth_error (tele_insts (ind_uparams Dz) Id Csz) j = Some T ->
         Γu ⊢ C : T) ->
      List.firstn (ind_nu Dz) (List.map nf_to_exp Rs)
        = List.map (fun C => C[wk_pat (List.repeat true (List.length Bs + List.length gs1 + im_nn Mi))]ʷ) Csz ->
      exists usz nsz, ⟦ Csz ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ usz /\ List.length usz = ind_nu Dz /\
        grp_step (d_ind qz kz (usz ++ nsz)) (d_ind p k us).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe Hlz Hkz HCzl HCzt HCz.
    destruct (nonrec_step Γu p D k Cs ρ0 us m Mi c gs gs1 A gs2 i W Bs _ Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe)
      as (zs & e & RE & HRE & HEE & Hlzs & Ee & Hstep).
    pose proof (nf_end_typed _ _ _ _ _ _ _ HT HW HWe) as HEt.
    set (Ψ := doms_ctx Bs ++ tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) in *.
    assert (HlΨ : List.length Ψ = List.length Bs + List.length gs1 + im_nn Mi)
      by (unfold Ψ, doms_ctx; rewrite List.length_app, length_tele_sub, List.length_rev, List.length_map, List.length_app,
            length_cargs_ctx; unfold im_nn; lia).
    rewrite <- HlΨ in HCz.
    destruct (ind_end_rel Γu Ψ ρ0 zs RE i qz kz Rs Dz Csz e Hg HΓu Hρ0 HRE HEE ltac:(lia) HEt Ee Hlz Hkz HCzl HCzt HCz)
      as (usz & nsz & Eusz & HlZ & jz & [R2 HEZ]).
    exists usz, nsz; split; [ exact Eusz | split; [ exact HlZ | exact (Hstep _ _ _ HEZ) ] ].
  Qed.

  (** Likewise for a record view the classification finds there: the
      record type at its instance is one nesting step out of every member
      of the group at [Cs]. *)
  Theorem nonrec_meet_below_record : forall Γu p D k Cs ρ0 us m Mi c gs gs1 A gs2 (i : nat) W Bs qz Rs Rz Isz,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_arg A :: gs2 ->
      tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu
        ⊢ A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu)
        A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] W ->
      nf_to_exp W = pis Bs (apps (a_record qz) (List.map nf_to_exp Rs)) ->
      record_lookup gc_deps gc_stack qz = Some Rz -> List.length Isz = List.length (record_params Rz) ->
      (forall j C T, List.nth_error Isz j = Some C -> List.nth_error (tele_insts (record_params Rz) Id Isz) j = Some T ->
         Γu ⊢ C : T) ->
      List.map nf_to_exp Rs = List.map (fun C => C[wk_pat (List.repeat true (List.length Bs + List.length gs1 + im_nn Mi))]ʷ) Isz ->
      exists usz, ⟦ Isz ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ usz /\ List.length usz = List.length (record_params Rz) /\
        grp_step (d_record qz usz) (d_ind p k us).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe Hlz HCzl HCzt HCz.
    destruct (nonrec_step Γu p D k Cs ρ0 us m Mi c gs gs1 A gs2 i W Bs _ Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe)
      as (zs & e & RE & HRE & HEE & Hlzs & Ee & Hstep).
    set (Ψ := doms_ctx Bs ++ tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) in *.
    assert (HlΨ : List.length Ψ = List.length Bs + List.length gs1 + im_nn Mi)
      by (unfold Ψ, doms_ctx; rewrite List.length_app, length_tele_sub, List.length_rev, List.length_map, List.length_app,
            length_cargs_ctx; unfold im_nn; lia).
    rewrite <- HlΨ in HCz.
    destruct (record_end_rel Γu Ψ ρ0 zs RE qz Rs Rz Isz e Hg HΓu Hρ0 HRE HEE ltac:(lia) Ee Hlz HCzl HCzt HCz)
      as (usz & Eusz & HlZ & jz & R2 & HEZ).
    exists usz; split; [ exact Eusz | split; [ exact HlZ | exact (Hstep _ _ _ HEZ) ] ].
  Qed.
End Fixed_GCtx.

(** ** The Order the Meets Leaving a Cluster Descend *)

(** The type value of a view at the values [us] of the arguments its key
    fixes and the values [ns] of its non-uniform parameters: the
    container's member, or the record type (which has none). *)
Definition key_type (x : view_key) (us ns : list domain) : domain :=
  match x with
  | vk_ind qc k _ => d_ind qc k (us ++ ns)
  | vk_record qr _ => d_record qr us
  end.

(** The values [us] are as many as the arguments the key's container or
    record takes. *)
Definition key_arity (Θ : gdeps) (Ξ : gstack) (x : view_key) (us : list domain) : Prop :=
  match x with
  | vk_ind qc _ _ => exists D, ind_lookup Θ Ξ qc = Some D /\ List.length us = ind_nu D
  | vk_record qr _ => exists R, record_lookup Θ Ξ qr = Some R /\ List.length us = List.length (record_params R)
  end.

(** [view_below Θ Ξ Γu z x]: at the initial environment of [Γu], a type
    of the view [z] is one nesting step ([grp_step]) out of the view [x],
    a member of a group or a record type. *)
#[warnings="-cannot-define-projection"]
Record view_below (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (z x : view_key) : Prop := mk_view_below
  { (** An environment of [Γu] *)
    below_env : env
    (** It is [Γu]'s initial environment *)
  ; below_env_initial : initial_env Θ Ξ Γu below_env
    (** The values of the arguments the upper view's key fixes *)
  ; below_uparams : list domain
    (** They are those of its arguments at the environment *)
  ; below_uparams_eval : ⟦ view_key_args x ⟧* Θ ⍮ Ξ ⍮ below_env ↘ below_uparams
    (** The values of the arguments the lower view's key fixes *)
  ; below_meet_uparams : list domain
    (** They are those of its arguments at the environment *)
  ; below_meet_uparams_eval : ⟦ view_key_args z ⟧* Θ ⍮ Ξ ⍮ below_env ↘ below_meet_uparams
    (** The values of the non-uniform parameters of the lower type *)
  ; below_meet_nparams : list domain
    (** As many as the lower view's container or record takes *)
  ; below_meet_arity : key_arity Θ Ξ z below_meet_uparams
    (** The lower type is one nesting step out of the upper one *)
  ; below_step : @grp_step (gc_mk Θ Ξ) (key_type z below_meet_uparams below_meet_nparams) (key_type x below_uparams nil) }.

(** The order on views. *)
Definition view_lt (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (z x : view_key) : Prop := view_below Θ Ξ Γu z x.

(** A view whose type is accessible for the nesting steps is accessible
    for [view_lt]. *)
Lemma view_below_acc : forall Θ Ξ Γu a, @nest_acc (gc_mk Θ Ξ) a ->
    forall x ρ usx nsx, initial_env Θ Ξ Γu ρ -> ⟦ view_key_args x ⟧* Θ ⍮ Ξ ⍮ ρ ↘ usx ->
    key_arity Θ Ξ x usx -> a = key_type x usx nsx -> Acc (view_lt Θ Ξ Γu) x.
Proof.
  intros Θ Ξ Γu a H; induction H as [a _ IH]; intros * Hi Eus Har ->.
  constructor; intros z [ρ' Hi' us' Eus' usz Eusz nsz Harz Hstep].
  pose proof (functional_initial_env _ _ Hi' _ Hi) as ->.
  pose proof (@functional_eval_exps' (gc_mk Θ Ξ) _ _ _ _ Eus' Eus) as ->.
  assert (Hstep' : @grp_step (gc_mk Θ Ξ) (key_type z usz nsz) (key_type x usx nsx)).
  { destruct x as [qx kx Csx | qx Isx]; cbn [key_type key_arity] in Hstep, Har |- *; [| exact Hstep ].
    destruct Har as (Dx & Hl & Hlen).
    rewrite List.app_nil_r in Hstep; rewrite <- (List.app_nil_r usx) in Hstep.
    exact (@grp_step_member_irrel (gc_mk Θ Ξ) _ qx kx kx Dx usx nil nsx Hl Hlen Hstep). }
  exact (IH _ Hstep' z ρ usz nsz Hi' Eusz Harz eq_refl).
Qed.

(** A typed record view is accessible for [view_lt]: its type is one of
    the model. *)
Theorem record_view_inv_acc : forall Θ Ξ Γu qx Isx, ⊢ᵍ Θ ⍮ Ξ -> record_view_inv Θ Ξ Γu qx Isx ->
    Acc (view_lt Θ Ξ Γu) (vk_record qx Isx).
Proof.
  intros * Hg [[Rx Hl Hlen Hty HΓu] _ _ _].
  pose proof (@valid_rview_record_gc (gc_mk Θ Ξ) _ _ Hg Hl) as HvR.
  pose proof (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ HΓu) as HΓs.
  destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
  destruct (per_ctx_then_per_env_initial_env HRΓ) as (ρ & _ & Hρ & _ & _).
  destruct (@inst_gargs (gc_mk Θ Ξ) Γu (record_params Rx) Isx ρ (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HvR))
              (params_valid _ (valid_rview_record_valid _ _ HvR)) HΓu Hlen Hty Hρ) as (us & Eus & Hgu & Hlu).
  destruct (@vrr_type_rel (gc_mk Θ Ξ) qx Rx us us HvR Hgu Hlu) as [i HR].
  exact (view_below_acc Θ Ξ Γu _ (@per_univ_nest_acc_rel (gc_mk Θ Ξ) _ _ _ _ _ _ _ HR HR) (vk_record qx Isx) ρ us nil Hρ Eus
           (ex_intro _ Rx (conj Hl Hlu)) eq_refl).
Qed.

(** A typed view is accessible for [view_lt]: its type is one of the
    model. *)
Theorem view_inv_acc : forall Θ Ξ Γu qx kx Csx, ⊢ᵍ Θ ⍮ Ξ -> view_inv Θ Ξ Γu qx kx Csx -> Acc (view_lt Θ Ξ Γu) (vk_ind qx kx Csx).
Proof.
  intros * Hg [[Dx Hl Hk Hlen Hty HΓu] _ _ _].
  destruct (List.nth_error (ind_members Dx) kx) as [Mk |] eqn:HM;
    [| apply List.nth_error_None in HM; pose proof (ind_ndecl_le Dx); lia ].
  change (ind_member Dx kx = Some Mk) in HM.
  destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
  pose proof (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ HΓu) as HΓs.
  destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
  destruct (per_ctx_then_per_env_initial_env HRΓ) as (ρ & _ & Hρ & _ & _).
  destruct (@inst_gargs (gc_mk Θ Ξ) Γu (ind_uparams Dx) Csx ρ (decl_closed_ass _ Hc)
              (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ (decl_typed_uparams_field _ _ _ Hdt)) HΓu
              ltac:(rewrite Hlen; reflexivity) Hty Hρ) as (us & Eus & Hgu & Hlu).
  destruct (@decl_member_type (gc_mk Θ Ξ) qx Dx kx Mk us Hg Hl HM Hk Hgu Hlu) as (ns & i & R & HR).
  exact (view_below_acc Θ Ξ Γu _ (@per_univ_nest_acc_rel (gc_mk Θ Ξ) _ _ _ _ _ _ _ HR HR) (vk_ind qx kx Csx) ρ us ns Hρ Eus
           (ex_intro _ Dx (conj Hl Hlu)) eq_refl).
Qed.

(** A view of the invariant is accessible for [view_lt]. *)
Corollary key_inv_acc : forall Θ Ξ Γu x, ⊢ᵍ Θ ⍮ Ξ -> key_inv Θ Ξ Γu x -> Acc (view_lt Θ Ξ Γu) x.
Proof. intros * Hg Hx; destruct x; [ exact (view_inv_acc _ _ _ _ _ _ Hg Hx) | exact (record_view_inv_acc _ _ _ _ _ Hg Hx) ]. Qed.

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
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMi Hh) as (Dqv' & My' & Hlv' & HMy' & Hkv & HIl & Hvml & Hvmk & Hnames & _).
    rewrite Hlv in Hlv'; injection Hlv' as <-; rewrite HMy in HMy'; injection HMy' as <-.
    set (σC := sb_of_list Id Cs) in *.
    set (σY := sb_of_list Id (List.map nf_to_exp Wv)) in *.
    set (σIv := sb_of_list Id (List.map (fun I => I[σC]) Iv)).
    pose proof (wf_uparams_sub _ _ _ _ _ Hdt HΓu HCl HCt) as HσC.
    (** the view's instance at [Cs] is equal to its normal form *)
    rewrite (tele_insts_sub (ind_uparams Dqv) 0 Id Id σC Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv) ltac:(intros; lia)) in Hn.
    assert (HσIY : Γu ⊢ˢ σIv ≈ σY : ind_uparams Dqv)
      by (apply nbes_sub_eq; [ exact (decl_closed_ass _ Hcv) | exact (decl_typed_uparams_field _ _ _ Hdtv) | exact HΓu | rewrite List.length_map; exact HIl
                             | exact Hn ]).
    (** the non-uniform parameters: the view equation at [Cs], then the
        instance replaced by its normal form *)
    pose proof (decl_typed_view_nparams _ _ _ _ Hg Hdt Hl i Mi qv kv Iv vm Dqv kv My i Mi HMi Hh Hlv HMy Hvmk HMi) as H1.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ H1 HσC) as H1'.
    pose proof (tele_list_grp_sb 0 Iv σC (im_nparams My) ltac:(rewrite HIl; exact (decl_closed_nparams_scoped _ Hcv _ _ HMy))) as E0.
    fold σC in H1'; change (sb_qn 0 (sb_of_list Id Iv)) with (sb_of_list Id Iv) in E0; change (sb_qn 0 σC) with σC in E0.
    change (sb_qn 0 (sb_of_list Id (List.map (fun M => M[σC]) Iv))) with σIv in E0; rewrite E0 in H1'.
    pose proof (member_params_wf _ _ _ _ _ Hdtv HMy) as HPy.
    pose proof (tele_sub_eq_ext (im_nparams My) (ind_uparams Dqv) Γu σIv σY (decl_typed_nparams_ass _ _ _ Hdtv _ _ HMy) HPy HσIY) as H2.
    pose proof (ext_eq_trans_ass _ _ _ _ (tele_ass_sub _ _ (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi))
                  (tele_ass_sub _ _ (decl_typed_nparams_ass _ _ _ Hdtv _ _ HMy)) H1' H2) as HNP.
    assert (Hnn : im_nn Mi = im_nn My)
      by (pose proof (ext_eq_length _ _ _ _ _ HNP) as E; rewrite !length_tele_sub in E; exact E).
    split; [ exact Hnn | split; [ exact HNP |] ].
    (** the constructors' arguments: the same *)
    intros c gs' Hc'.
    pose proof (cons_lookup_in _ _ _ Hc') as HIn'.
    assert (Hcn : In c (List.map fst (im_cons Mi))) by (rewrite Hnames; apply (List.in_map fst _ _ HIn')).
    apply List.in_map_iff in Hcn as ([c0 gs] & Hc0 & HIn); cbn in Hc0; subst c0.
    pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ Hdt _ _ HMi) HIn) as Hcon.
    exists gs; split; [ exact Hcon |].
    pose proof (decl_typed_view_args _ _ _ _ Hg Hdt Hl i Mi qv kv Iv vm Dqv kv My i Mi c gs' gs HMi Hh Hlv HMy Hvmk HMi Hc' Hcon) as H3.
    pose proof (wf_sub_ext _ _ (im_nparams Mi) (ind_uparams D) Γu σC HσC (ext_eq_ctx_left _ _ _ _ _ HNP)
                  (member_params_wf _ _ _ _ _ Hdt HMi)) as Hτ.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ H3 Hτ) as H3'.
    change (List.length (im_nparams Mi)) with (im_nn Mi) in H3'.
    rewrite (tele_list_grp_sb (im_nn Mi) Iv σC (cargs_ctx qv Dqv My gs')) in H3'
      by (rewrite HIl, Hnn; exact (decl_closed_cargs_scoped _ Hcv _ _ _ _ _ HMy HIn')).
    fold σIv in H3'; rewrite Hnn in H3'.
    pose proof (sb_qn_eq_ext (im_nparams My) (ind_uparams Dqv) Γu σIv σY (decl_typed_nparams_ass _ _ _ Hdtv _ _ HMy) HPy HσIY) as HqY.
    pose proof (ctxsub_ext_rev _ _ _ _ _ H1' (tele_ass_sub _ _ (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi))) as Hid.
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
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu (im_nn Mi + nu) n pat (nf_to_exp W) = Some gz ->
      In z (rcarg_view gz) ->
      List.length pat = List.length gs1 ->
      In z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Cs).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hn HCs Hss HM Hcon Heq HT HW Hcls Hin Hlp.
    destruct g as [A | t]; cbn [carg_ty] in HT, HW.
    - (** a non-recursive argument: a nesting step *)
      right.
      set (Δ := tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) in *.
      destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
      assert (HΔa : tele_ass Δ)
        by (apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ Hdt _ _ HM) ]).
      assert (HlΔ : List.length Δ = List.length pat + (im_nn Mi + nu - nu))
        by (unfold Δ; rewrite length_tele_sub, List.length_app, length_cargs_ctx; unfold im_nn; lia).
      pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
      destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
      destruct (per_ctx_then_per_env_initial_env HRΓu) as (ρ0 & _ & Hρ0 & _ & _).
      destruct (inst_gargs Γu (ind_uparams D) Cs ρ0 (decl_closed_ass _ Hc) (completeness_fundamental_ctx _ (decl_typed_uparams_field _ _ _ Hdt)) HΓu
                  ltac:(rewrite HCl; reflexivity) HCt Hρ0) as (us & Eus & _ & _).
      destruct z as [qz kz Csz | qz Isz].
      2:{ (** a record view: a step into the record type *)
          destruct (nest_record_view_inv _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hcls Hin) as [[Rz Hlz HIzl HIzt _] _ _ _].
          destruct (nest_record_end _ _ _ _ _ _ _ _ _ _ _ _ HT HW Hcls Hin) as (Bs & Rz' & Rs & HWe & Hlz' & _ & _ & _ & _ & HC).
          rewrite Hlz in Hlz'; injection Hlz' as <-.
          replace (List.length Bs + List.length pat + (im_nn Mi + nu - nu)) with (List.length Bs + List.length gs1 + im_nn Mi) in HC
            by lia.
          destruct (nonrec_meet_below_record Γu qx D kx Cs ρ0 us m Mi c gs gs1 A gs2 i W Bs qz Rs Rz Isz Hg HΓu Hl HCl HCt Hρ0 Eus
                      HM Hcon Heq HT HW HWe Hlz HIzl HIzt HC) as (usz & Eusz & Hlusz & Hstep).
          clear - Hρ0 Eus Eusz Hlz Hlusz Hstep; destruct GC as [Θ0 Ξ0].
          refine (mk_view_below _ _ _ (vk_record qz Isz) (vk_ind qx kx Cs) ρ0 Hρ0 us Eus usz Eusz nil
                    (ex_intro _ Rz (conj Hlz Hlusz)) _).
          cbn [key_type]; rewrite List.app_nil_r; exact Hstep. }
      destruct (nest_view_inv _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hcls Hin) as [[Dz Hlz Hkz HCzl HCzt _] _ _ _].
      destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs & E & mz & HWe & HE & Hh & Hg2 & Hm & HC).
      pose proof HW as [ρw mw _ _ Hrw]; pose proof (read_typ_type_nf _ _ _ Hrw) as HWn.
      destruct (nf_pis_end _ _ _ HWn HWe) as (WE & HWE & HWEe).
      rewrite <- HWEe in Hh; destruct (nf_ind_view _ _ _ HWE Hh) as [Rs ->].
      cbn [nf_to_exp] in HWEe; subst E.
      rewrite app_args_apps in HC; cbn [app_args List.app] in HC.
      unfold grp_info in Hg2; rewrite Hlz in Hg2.
      destruct (kz <? ind_ndecl Dz); [ injection Hg2 as <- | discriminate ].
      replace (List.length Bs + List.length pat + (im_nn Mi + nu - nu)) with (List.length Bs + List.length gs1 + im_nn Mi) in HC
        by lia.
      destruct (nonrec_meet_below Γu qx D kx Cs ρ0 us m Mi c gs gs1 A gs2 i W Bs qz kz Rs Dz Csz Hg HΓu Hl HCl HCt Hρ0 Eus
                  HM Hcon Heq HT HW HWe Hlz Hkz HCzl HCzt HC) as (usz & nsz & Eusz & Hlusz & Hstep).
      clear - Hρ0 Eus Eusz Hlz Hlusz Hstep; destruct GC as [Θ0 Ξ0].
      refine (mk_view_below _ _ _ (vk_ind qz kz Csz) (vk_ind qx kx Cs) ρ0 Hρ0 us Eus usz Eusz nsz
                (ex_intro _ Dz (conj Hlz Hlusz)) _).
      cbn [key_type]; rewrite List.app_nil_r; exact Hstep.
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
      In z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Cs).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hn HCs Hss HMj Hcls Hz.
    destruct (cls_cons_in_site _ _ _ _ _ _ _ _ Hcls _ Hz) as (rc & pre & y & T & post & pat & g & Hrc & Hsnd & Hgc & Hin & Hlp).
    apply List.in_map_iff in Hrc as ([c gs] & <- & HIn); cbn [fst snd] in Hsnd.
    destruct (cargs_sub_split _ _ _ _ _ _ _ _ _ Hsnd) as (gs1 & g' & gs2 & Heq & Hl1 & Hpre & ->).
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ Hdt _ _ HMj) HIn) as Hcon.
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
      In z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Cs).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hn HCs Hss HMi Hh Hlv Hnv HMy Hcls Hz.
    destruct (cls_cons_in_site _ _ _ _ _ _ _ _ Hcls _ Hz) as (rc & pre & y & T & post & pat & g & Hrc & Hsnd & Hgc & Hin & Hlp).
    apply List.in_map_iff in Hrc as ([c gs'] & <- & HIn'); cbn [fst snd] in Hsnd.
    destruct (cargs_sub_split _ _ _ _ _ _ _ _ _ Hsnd) as (gs1y & gy & gs2y & Heqy & Hl1y & Hpre & ->).
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [Hdtv _].
    pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ Hdtv _ _ HMy) HIn') as Hc'.
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
    pose proof (ext_eq_app _ _ _ _ _ _ _ (tele_ass_sub _ _ (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi)) HaD HNP HE2) as HEall.
    rewrite <- !List.app_assoc in HEall; cbn [List.app] in HEall.
    apply ext_eq_app_inv in HEall; [| rewrite HlX, HlXy; rewrite !List.length_app in Hlg; cbn in Hlg; lia ].
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ HEall) as (i0 & HE1 & HT' & HTT & HTy').
    assert (HaY : tele_ass (tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC) ++ tele_sub (im_nparams Mi) σC))
      by (apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi) ]).
    (** so the same normal form, in the member's context *)
    pose proof (rel_ext_under_ctx_eq _ _ _ (proj1 completeness_fundamental_modules _ _ _ (ext_eq_sym_ass _ _ _ _ _ HaY HE1))) as HY2D.
    rewrite List.app_assoc in HTy, HWy.
    pose proof (ctxeq_nbe_ty_eq' _ _ _ _ _ HTy HY2D HWy) as HWD.
    destruct (completeness_ty HTT) as (W0 & HW0D & HW0Y).
    pose proof (functional_nbe_ty _ _ _ _ HW0Y HWD) as ->.
    rewrite <- List.app_assoc, cargs_pre_ctx in HT', HW0D.
    rewrite <- Hnn in Hcl.
    exact (meet_off_member Γu qx D kx Cs Ws ss i Mi c _ gs1 g' gs2 i0 W nu n pat g0 z Hg HΓu Hl HCl HCt Hn HCs Hss HMi Hcon
             eq_refl HT' HW0D Hcl Hin ltac:(lia)).
  Qed.

  (** The record view equations of the member [i] of the group at [qx], a
      record view of the record at [qr], at [Cs]: the record's fields at
      the normal forms of its instance there are the member's
      constructor's arguments at [Cs]. *)
  Theorem record_sib_link : forall Γu qx D Cs i Mi qr Ir fl Rr Wr c gs,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      ind_member D i = Some Mi -> im_head Mi = mh_record qr Ir fl -> record_lookup gc_deps gc_stack qr = Some Rr ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list Id Cs]) Ir)
        (List.map (fun T => T[sb_of_list Id Cs]) (tele_insts (record_params Rr) Id Ir)) Wr ->
      im_cons Mi = (c, gs) :: nil ->
      gc_deps ⍮ gc_stack ⍮ Γu ⊢ˣ tele_sub (record_fctx Rr (List.length (record_fields Rr))) (sb_of_list Id (List.map nf_to_exp Wr))
        ≈ tele_sub (cargs_ctx qx D Mi gs) (sb_qn (im_nn Mi) (sb_of_list Id Cs)).
  Proof.
    intros * Hg HΓu Hl HCl HCt HMi Hh Hlr Hn Hcs.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
    destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMi Hh) as [_ Hnn]; rewrite Hnn; change (sb_qn 0 ?σ) with σ.
    destruct (rview_struct_record _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMi Hh) as [Rr' HRf].
    pose proof (rview_record_lookup _ _ _ _ _ _ HRf) as Hlr'; rewrite Hlr in Hlr'; injection Hlr' as <-.
    pose proof (rview_record_count _ _ _ _ _ _ HRf) as HIl.
    pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) Hlr) as HcR.
    pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hlr) as HRt.
    assert (HRa : tele_ass (record_params Rr)) by exact (typed_params_ass _ _ _ HRt).
    set (σC := sb_of_list Id Cs) in *.
    set (σY := sb_of_list Id (List.map nf_to_exp Wr)) in *.
    set (F := record_fctx Rr (List.length (record_fields Rr))) in *.
    pose proof (wf_uparams_sub _ _ _ _ _ Hdt HΓu HCl HCt) as HσC.
    (** the record view equation at the group's uniform parameters, moved
        to [Γu] along [Cs] *)
    pose proof (decl_typed_rview_fields _ _ _ _ Hg Hdt Hl _ _ _ _ _ _ _ _ HMi Hh Hlr Hcs) as HE.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HE HσC) as H1.
    assert (HFs : ctx_scoped (0 + List.length Ir) F).
    { rewrite HIl; pose proof (record_fctx_scoped Rr _ (le_n _) (fun k f T Hk _ => closed_fields _ HcR _ _ _ Hk)
                              (closed_params _ HcR)) as Hs.
      apply ctx_scoped_app in Hs as [Hs _]; rewrite Nat.add_0_r in Hs; exact Hs. }
    pose proof (tele_list_grp_sb 0 Ir σC F HFs) as E0.
    change (sb_qn 0 ?x) with x in E0; fold F σC in H1; rewrite E0 in H1.
    (** the instance at [Cs] is equal to its normal form *)
    rewrite (record_params_insts_sub Rr Ir σC HcR) in Hn.
    pose proof (record_typed_fctx_wf _ _ _ HRt 0 ltac:(lia)) as HP0; cbn [record_fctx List.firstn List.map List.rev List.app] in HP0.
    assert (HσIY : Γu ⊢ˢ sb_of_list Id (List.map (fun I => I[σC]) Ir) ≈ σY : record_params Rr)
      by (apply nbes_sub_eq; [ exact HRa | exact HP0 | exact HΓu | rewrite List.length_map; exact HIl | exact Hn ]).
    assert (HFa : tele_ass F) by apply record_fctx_ass.
    pose proof (tele_sub_eq_ext F (record_params Rr) Γu _ _ HFa (record_typed_fctx_wf _ _ _ HRt _ (le_n _)) HσIY) as H2.
    eapply ext_eq_trans_ass; [ apply tele_ass_sub, HFa | apply tele_ass_sub, HFa | apply ext_eq_sym_ass; [ apply tele_ass_sub, HFa | exact H2 ] |].
    exact H1.
  Qed.

  (** The instances a record view sibling's constructor meets: those of
      the member of the group at [qx] it is, at [Cs], by the record view
      equations. *)
  Theorem record_sib_meets : forall Γu qx D kx Cs Ws ss i Mi qr Ir fl Rr Wr cs nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws -> Cs = List.map nf_to_exp Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss ->
      ind_member D i = Some Mi -> im_head Mi = mh_record qr Ir fl -> record_lookup gc_deps gc_stack qr = Some Rr ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list Id Cs]) Ir)
        (List.map (fun T => T[sb_of_list Id Cs]) (tele_insts (record_params Rr) Id Ir)) Wr ->
      cls_cons_in gc_deps gc_stack Γu nu nu n
        ((rview_con, ctx_args (tele_sub (record_fctx Rr (List.length (record_fields Rr))) (sb_of_list sb_id (List.map nf_to_exp Wr))))
           :: nil) cs ->
      In z (rcons_views cs) ->
      In z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Cs).
  Proof.
    intros * Hg HΓu Hl HCl HCt Hn HCs Hss HMi Hh Hlr Hnr Hcls Hz.
    destruct (cls_cons_in_site _ _ _ _ _ _ _ _ Hcls _ Hz) as (rc & pre & y & T & post & pat & g & Hrc & Hsnd & Hgc & Hin & Hlp).
    destruct Hrc as [<- | []]; cbn [snd] in Hsnd.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMi Hh) as (gs & Hcs & _).
    destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMi Hh) as [_ Hnn].
    pose proof (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMi Hh) as HnP.
    pose proof (record_sib_link Γu qx D Cs i Mi qr Ir fl Rr Wr rview_con gs Hg HΓu Hl HCl HCt HMi Hh Hlr Hnr Hcs) as HE2.
    set (σC := sb_of_list Id Cs) in *; set (σY := sb_of_list Id (List.map nf_to_exp Wr)) in *.
    set (ΔY := tele_sub (record_fctx Rr (List.length (record_fields Rr))) σY) in *.
    assert (HaY : tele_ass ΔY) by (apply tele_ass_sub, record_fctx_ass).
    (** the fields, split at the one met *)
    assert (EY : ΔY = rtele post ++ ce_ass T :: rtele pre).
    { rewrite <- (rtele_ctx_args ΔY HaY), Hsnd; unfold rtele; rewrite List.map_app, List.rev_app_distr; cbn [List.map List.rev].
      rewrite <- List.app_assoc; reflexivity. }
    destruct Hgc as [g0 Hsyn | iy W g0 Hnone HTy HWy Hcl].
    { rewrite (cls_arg_none_view _ _ _ _ _ _ Hsyn) in Hin; destruct Hin. }
    (** the member's arguments, split at the same position *)
    assert (Hlg : List.length gs = List.length pre + S (List.length post)).
    { pose proof (ext_eq_length _ _ _ _ _ HE2) as E; rewrite EY, length_tele_sub, length_cargs_ctx in E.
      unfold rtele in E; rewrite List.length_app, List.length_rev, List.length_map in E; cbn in E.
      rewrite List.length_rev, List.length_map in E; lia. }
    assert (Hj : List.length pre < List.length gs) by lia.
    destruct (nth_error_lt_some' gs _ Hj) as [g' Hg'].
    destruct (List.nth_error_split _ _ Hg') as (gs1 & gs2 & -> & Hl1).
    destruct (cargs_sub_at qx D Mi gs1 g' gs2 σC) as (X & EX & HlX).
    rewrite EY, EX in HE2.
    apply ext_eq_app_inv in HE2;
      [| unfold rtele; rewrite List.length_rev, List.length_map, HlX; rewrite List.length_app in Hlg; cbn in Hlg; lia ].
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ HE2) as (i0 & HE1 & HT' & HTT & HTy').
    (** so the same normal form, in the member's context *)
    assert (HaP : tele_ass (rtele pre))
      by (unfold rtele, tele_ass; apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; eexists; reflexivity).
    pose proof (rel_ext_under_ctx_eq _ _ _ (proj1 completeness_fundamental_modules _ _ _ HE1)) as HY2D.
    destruct (completeness_ty HTT) as (W0 & HW0D & HW0Y).
    pose proof (functional_nbe_ty _ _ _ _ HW0D HWy) as ->.
    assert (HT'r : rtele pre ++ Γu ⊢ (carg_ty qx D (im_nn Mi) (cargs_pat gs1) g')[sb_qn (List.length gs1 + im_nn Mi) σC] : Typeω@i0)
      by (gen_presups; assumption).
    pose proof (ctxeq_nbe_ty_eq' _ _ _ _ _ HT'r HY2D HW0Y) as HWD.
    clear HW0Y; rename HWD into HW0Y.
    assert (EΓ : tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC) ++ Γu
                 = tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) σC ++ Γu)
      by (rewrite HnP, List.app_nil_r, Hnn; reflexivity).
    rewrite EΓ in HTy', HW0Y.
    assert (Hcon : ind_con Mi rview_con = Some (gs1 ++ g' :: gs2))
      by (unfold ind_con; rewrite Hcs; cbn; reflexivity).
    assert (Hcl' : cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu (im_nn Mi + nu) n pat (nf_to_exp W) = Some g0)
      by (rewrite Hnn; exact Hcl).
    exact (meet_off_member Γu qx D kx Cs Ws ss i Mi rview_con _ gs1 g' gs2 i0 W nu n pat g0 z Hg HΓu Hl HCl HCt Hn HCs Hss HMi Hcon
             eq_refl HTy' HW0Y Hcl' Hin ltac:(lia)).
  Qed.

  (** ** The Meets of a Record View Are Below It

      A record view is its own cluster: an instance its constructor's
      classified fields meet, at a field's normal form at the instance, is
      one nesting step out of the record type at the instance. *)
  Theorem record_view_meets_below : forall Γu qx Isx Rx cs nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> record_view_typed gc_deps gc_stack Γu qx Isx -> record_lookup gc_deps gc_stack qx = Some Rx ->
      cls_cons_in gc_deps gc_stack Γu nu nu n
        ((rview_con, ctx_args (tele_sub (record_fctx Rx (List.length (record_fields Rx))) (sb_of_list sb_id Isx))) :: nil) cs ->
      In z (rcons_views cs) -> view_lt gc_deps gc_stack Γu z (vk_record qx Isx).
  Proof.
    intros * Hg [Rx' Hl' HIl HIt HΓu] Hl Hcls Hz.
    rewrite Hl in Hl'; injection Hl' as <-.
    destruct (cls_cons_in_site _ _ _ _ _ _ _ _ Hcls _ Hz) as (rc & pre & y & T & post & pat & g & Hrc & Hsnd & Hgc & Hin & Hlp).
    destruct Hrc as [<- | []]; cbn [snd] in Hsnd.
    destruct (fctx_sub_split _ _ _ _ _ _ Hsnd) as (f & A & HfA & Hpre & ->).
    set (j := List.length pre) in *.
    destruct Hgc as [g0 Hsyn | i W g0 Hnone HT HW Hcl].
    { rewrite (cls_arg_none_view _ _ _ _ _ _ Hsyn) in Hin; destruct Hin. }
    rewrite Hpre in HT, HW.
    set (Δ := tele_sub (record_fctx Rx j) (sb_of_list Id Isx)) in *.
    assert (Hjl : j < List.length (record_fields Rx)) by (apply List.nth_error_Some; congruence).
    assert (HΔa : tele_ass Δ) by (apply tele_ass_sub, record_fctx_ass).
    assert (HlΔ : List.length Δ = List.length pat + (nu - nu))
      by (unfold Δ; rewrite length_tele_sub, length_record_fctx_le by lia; lia).
    pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
    destruct (per_ctx_then_per_env_initial_env HRΓu) as (ρ0 & _ & Hρ0 & _ & _).
    pose proof (valid_rview_record_gc _ _ Hg Hl) as HvR.
    destruct (inst_gargs Γu (record_params Rx) Isx ρ0 (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HvR))
                (params_valid _ (valid_rview_record_valid _ _ HvR)) HΓu HIl HIt Hρ0) as (usx & Eusx & _ & _).
    assert (HlΨ : forall Bs, List.length (doms_ctx Bs ++ Δ) = List.length Bs + j)
      by (intros Bs; unfold doms_ctx, Δ; rewrite List.length_app, List.length_rev, List.length_map, length_tele_sub,
            length_record_fctx_le by lia; reflexivity).
    destruct z as [qz kz Csz | qz Isz].
    - (** a nested occurrence: the member at its instance *)
      destruct (nest_view_inv _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hcl Hin) as [[Dz Hlz Hkz HCzl HCzt _] _ _ _].
      destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcl Hin) as (Bs & E & mz & HWe & HE & Hh & Hg2 & Hm & HC).
      pose proof HW as [ρw mw _ _ Hrw]; pose proof (read_typ_type_nf _ _ _ Hrw) as HWn.
      destruct (nf_pis_end _ _ _ HWn HWe) as (WE & HWE & HWEe).
      rewrite <- HWEe in Hh; destruct (nf_ind_view _ _ _ HWE Hh) as [Rs ->].
      cbn [nf_to_exp] in HWEe; subst E.
      rewrite app_args_apps in HC; cbn [app_args List.app] in HC.
      unfold grp_info in Hg2; rewrite Hlz in Hg2.
      destruct (kz <? ind_ndecl Dz); [ injection Hg2 as <- | discriminate ].
      destruct (field_step Γu qx Rx Isx ρ0 usx j f A i W Bs _ Hg HΓu Hl HIl HIt Hρ0 Eusx HfA HT HW HWe)
        as (zs & e & RE & HRE & HEE & Hlzs & Ee & Hstep).
      pose proof (nf_end_typed _ _ _ _ _ _ _ HT HW HWe) as HEt.
      rewrite <- (HlΨ Bs) in Hlzs.
      replace (List.length Bs + List.length pat + (nu - nu)) with (List.length (doms_ctx Bs ++ Δ)) in HC by (rewrite HlΨ; lia).
      destruct (ind_end_rel Γu (doms_ctx Bs ++ Δ) ρ0 zs RE i qz kz Rs Dz Csz e Hg HΓu Hρ0 HRE HEE Hlzs HEt Ee Hlz Hkz HCzl HCzt HC)
        as (usz & nsz & Eusz & HlZ & jz & [R2 HEZ]).
      clear - Hρ0 Eusx Eusz Hlz HlZ Hstep HEZ; destruct GC as [Θ0 Ξ0].
      exact (mk_view_below _ _ _ (vk_ind qz kz Csz) (vk_record qx Isx) ρ0 Hρ0 usx Eusx usz Eusz nsz
               (ex_intro _ Dz (conj Hlz HlZ)) (Hstep _ _ _ HEZ)).
    - (** a record view: the record at its instance *)
      destruct (nest_record_view_inv _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hcl Hin) as [[Rz Hlz HIzl HIzt _] _ _ _].
      destruct (nest_record_end _ _ _ _ _ _ _ _ _ _ _ _ HT HW Hcl Hin) as (Bs & Rz' & Rs & HWe & Hlz' & _ & _ & _ & _ & HC).
      rewrite Hlz in Hlz'; injection Hlz' as <-.
      destruct (field_step Γu qx Rx Isx ρ0 usx j f A i W Bs _ Hg HΓu Hl HIl HIt Hρ0 Eusx HfA HT HW HWe)
        as (zs & e & RE & HRE & HEE & Hlzs & Ee & Hstep).
      rewrite <- (HlΨ Bs) in Hlzs.
      replace (List.length Bs + List.length pat + (nu - nu)) with (List.length (doms_ctx Bs ++ Δ)) in HC by (rewrite HlΨ; lia).
      destruct (record_end_rel Γu (doms_ctx Bs ++ Δ) ρ0 zs RE qz Rs Rz Isz e Hg HΓu Hρ0 HRE HEE Hlzs Ee Hlz HIzl HIzt HC)
        as (usz & Eusz & HlZ & jz & R2 & HEZ).
      clear - Hρ0 Eusx Eusz Hlz HlZ Hstep HEZ; destruct GC as [Θ0 Ξ0].
      exact (mk_view_below _ _ _ (vk_record qz Isz) (vk_record qx Isx) ρ0 Hρ0 usx Eusx usz Eusz nil
               (ex_intro _ Rz (conj Hlz HlZ)) (Hstep _ _ _ HEZ)).
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
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMm Hh) as (Dqv' & Mkv & Hlv' & _ & _ & _ & Hvml & _).
    rewrite Hlv in Hlv'; injection Hlv' as <-.
    destruct (sibs_from_in _ _ _ _ _ _ _ _ Hssy _ He) as (i' & Mi' & HMi' & Hei' & Hse); cbn [Nat.add] in Hse.
    assert (Hi'l : i' < List.length vm) by (rewrite Hvml; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' vm i' Hi'l) as [v Hv].
    destruct (sibs_from_nth _ _ _ _ _ _ _ _ Hss) as [_ Hssn].
    inversion Hse as [? ? pm' Hhd | ? ? q'' k'' Is'' vm'' D'' We Hhd Hl'' Hne | ? ? q'' Is'' fl'' R'' We Hhd Hl'' Hne]; subst.
    - destruct (decl_typed_view_decl _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMm Hh Hlv HMi' Hhd Hv) as (Mv & vm' & HMv & HhMv).
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? qv0 kv0 Iv0 vm0 Dv0 Ws0 Hh0 Hl0 Hn0 | ? ? ? ? ? ? ? Hh0 ? ?]; subst; rewrite HhMv in Hh0;
        try discriminate.
      injection Hh0 as <- <- <- <-.
      destruct (nbes_ill _ _ _ _ Hn0 HΓu) as [_ ->].
      exact (List.nth_error_In _ _ He0).
    - destruct (nbes_ill _ _ _ _ Hne HΓu) as [HIs ->].
      apply List.map_eq_nil in HIs; subst Is''.
      destruct (decl_typed_view_view _ _ _ Hdt m Mm qv kv nil vm Dqv i' Mi' v q'' k'' nil vm'' HMm Hh Hlv HMi' Hhd Hv)
        as (Mv & X & vm' & HMv & HhMv & HXl).
      destruct X; [| discriminate ].
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? qv0 kv0 Iv0 vm0 Dv0 Ws0 Hh0 Hl0 Hn0 | ? ? ? ? ? ? ? Hh0 ? ?]; subst; rewrite HhMv in Hh0;
        try discriminate.
      injection Hh0 as <- <- <- <-.
      destruct (nbes_ill _ _ _ _ Hn0 HΓu) as [_ ->].
      exact (List.nth_error_In _ _ He0).
    - destruct (nbes_ill _ _ _ _ Hne HΓu) as [HIs ->].
      apply List.map_eq_nil in HIs; subst Is''.
      destruct (decl_typed_view_rview _ _ _ Hdt m Mm qv kv nil vm Dqv i' Mi' v q'' nil fl'' HMm Hh Hlv HMi' Hhd Hv)
        as (Mv & X & HMv & HhMv & HXl).
      destruct X; [| discriminate ].
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? ? ? ? ? ? ? Hh0 ? ? | ? ? qr0 Ir0 fl0 R0 Ws0 Hh0 Hl0 Hn0]; subst; rewrite HhMv in Hh0;
        try discriminate.
      injection Hh0 as <- <- <-.
      destruct (nbes_ill _ _ _ _ Hn0 HΓu) as [_ ->].
      exact (List.nth_error_In _ _ He0).
  Qed.
End MeetsOffMembers.
