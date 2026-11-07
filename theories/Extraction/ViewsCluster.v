(** * The Clusters of the Views, and the Nesting Order Below Them

    The cluster of a typed view [(qx, kx, Cs)] is its siblings, the
    members of the group at [qx] at [Cs].  An instance the cluster's
    constructors meet is found in the normal form of an argument type of
    a member of that group at [Cs] (directly, or, for a view sibling,
    through the view equations: [view_sibling_link]):
    - at a recursive argument, it is a sibling ([rec_meet_in_siblings]);
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
    the member's, by the record view equations ([record_sibling_link],
    [record_sibling_meets]).  The steps share the semantics of an argument's
    normal form's shape end ([arg_shape_end], [ind_end_rel],
    [record_end_rel]). *)

From Stdlib Require Import Lia List PeanoNat String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Completeness Soundness Consequences.NormalFormWeakening.
From Mctt.Core Require Import Consequences.Consistency Consequences.FiledConstructorTypes Semantic.Realizability.
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
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic Require Import Fresh.
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
Lemma pis_inj : forall Bs1 Bs2 E1 E2, (forall B C, E1 <> a_pi ak_relevant ak_relevant B C) -> (forall B C, E2 <> a_pi ak_relevant ak_relevant B C) ->
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
  | ca_arg _ A => A[wk_pat pat]ʷ
  | ca_rec t => ptyp_ty pq D nn pat t
  end.

(** The kind of the argument [g]: a recursive one is relevant. *)
Definition carg_kind (g : carg) : abs_kind :=
  match g with
  | ca_arg κ _ => κ
  | ca_rec _ => ak_relevant
  end.

(** The arguments of a constructor, split at an argument: those after
    it, its type, and those before it. *)
Lemma cargs_ctx_split : forall pq D M gs1 g gs2,
    cargs_ctx pq D M (gs1 ++ g :: gs2)
    = cargs_ctx_aux pq D (im_nn M) (match g with ca_rec _ => true | ca_arg _ _ => false end :: cargs_pat gs1) gs2
        ++ ce_ass (carg_kind g) (carg_ty pq D (im_nn M) (cargs_pat gs1) g) :: cargs_ctx pq D M gs1.
Proof.
  intros; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r.
  destruct g as [r A | t]; cbn [cargs_ctx_aux carg_ty]; rewrite <- List.app_assoc; reflexivity.
Qed.

(** ** Where the Classification Meets an Instance *)

(** An instance the classified arguments meet is met by one of them,
    classified in the context of those before it. *)
Lemma classify_args_in_site : forall Θ Ξ Γp nu np n pat args1 args gs,
    classify_args_in Θ Ξ Γp nu np n pat args1 args gs -> List.length pat = List.length args1 ->
    forall z, In z (List.concat (List.map classified_carg_view gs)) ->
    exists pre y κ T post pat' g, args = pre ++ (y, κ, T) :: post /\ classify_arg_in Θ Ξ (raw_args_tele (args1 ++ pre) ++ Γp) nu np n pat' T g /\
      In z (classified_carg_view g) /\ List.length pat' = List.length args1 + List.length pre.
Proof.
  induction 1 as [| pat args1 y κ T args g gs Hg _ Hgs IH]; intros Hl z Hz; cbn in Hz; [ destruct Hz |].
  apply List.in_app_or in Hz as [Hz | Hz].
  - assert (Ev : classified_carg_view (classified_carg_tag κ g) = classified_carg_view g) by (destruct g; reflexivity).
    rewrite Ev in Hz.
    exists nil, y, κ, T, args, pat, g; rewrite List.app_nil_r; cbn; split; [ reflexivity | split; [ exact Hg | split; [ exact Hz | lia ] ] ].
  - destruct (IH ltac:(rewrite List.length_app; cbn; lia) _ Hz) as (pre & y' & κ' & T' & post & pat' & g' & -> & Hg' & Hin & Hl').
    exists ((y, κ, T) :: pre), y', κ', T', post, pat', g'; rewrite <- List.app_assoc in Hg'; cbn [List.app] in Hg' |- *.
    split; [ reflexivity | split; [ exact Hg' | split; [ exact Hin |] ] ].
    rewrite List.length_app in Hl'; cbn in Hl' |- *; lia.
Qed.

(** An instance the classified constructors meet. *)
Lemma classify_cons_in_site : forall Θ Ξ Γp nu np n rcs cs, classify_cons_in Θ Ξ Γp nu np n rcs cs ->
    forall z, In z (classified_cons_views cs) ->
    exists rc pre y κ T post pat g, In rc rcs /\ snd rc = pre ++ (y, κ, T) :: post /\
      classify_arg_in Θ Ξ (raw_args_tele pre ++ Γp) nu np n pat T g /\ In z (classified_carg_view g) /\ List.length pat = List.length pre.
Proof.
  unfold classify_cons_in, classified_cons_views; induction 1 as [| rc c rcs cs [_ Hc] _ IH]; intros z Hz; cbn in Hz; [ destruct Hz |].
  apply List.in_app_or in Hz as [Hz | Hz].
  - destruct (classify_args_in_site _ _ _ _ _ _ _ _ _ _ Hc eq_refl _ Hz) as (pre & y & κ & T & post & pat & g & Heq & Hg & Hin & Hl).
    exists rc, pre, y, κ, T, post, pat, g; cbn [List.app List.length] in *.
    split; [ left; reflexivity | split; [ exact Heq | split; [ exact Hg | split; [ exact Hin | lia ] ] ] ].
  - destruct (IH _ Hz) as (rc' & pre & y & κ & T & post & pat & g & Hrc & Hrest).
    exists rc', pre, y, κ, T, post, pat, g; split; [ right; exact Hrc | exact Hrest ].
Qed.

Lemma ctx_args_app : forall Δ1 Δ2, ctx_args (Δ1 ++ Δ2) = ctx_args Δ2 ++ ctx_args Δ1.
Proof. intros; unfold ctx_args; rewrite List.flat_map_app, List.rev_app_distr; reflexivity. Qed.

Lemma raw_args_tele_ctx_args : forall Δ, all_assumptions Δ -> raw_args_tele (ctx_args Δ) = Δ.
Proof.
  intros Δ Hass; unfold raw_args_tele, ctx_args; rewrite List.map_rev, List.rev_involutive.
  induction Hass as [| e Δ (κ & A & ->) _ IH]; cbn [List.flat_map List.map centry_arg List.app]; [ reflexivity | cbn; f_equal; exact IH ].
Qed.

(** The arguments of a telescope of assumptions are as many as its
    entries. *)
Lemma length_ctx_args : forall Δ, all_assumptions Δ -> List.length (ctx_args Δ) = List.length Δ.
Proof.
  intros Δ Hass; unfold ctx_args; rewrite List.length_rev.
  induction Hass as [| e Δ (κ & A & ->) _ IH]; cbn; [ reflexivity | lia ].
Qed.

(** The arguments of a constructor, moved along [q^nn σ], split at an
    argument met: the arguments before it, and its type. *)
Lemma ctx_args_cons_ass : forall κ A Y, ctx_args (ce_ass κ A :: Y) = ctx_args Y ++ ((""%string, κ, A) :: nil).
Proof. intros; reflexivity. Qed.

Lemma cargs_sub_split : forall pq D M gs σ pre y κ T post,
    ctx_args (tele_sub (cargs_ctx pq D M gs) (sb_qn (im_nn M) σ)) = pre ++ (y, κ, T) :: post ->
    exists gs1 g gs2, gs = gs1 ++ g :: gs2 /\ List.length gs1 = List.length pre /\
      raw_args_tele pre = tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ) /\ κ = carg_kind g /\
      T = (carg_ty pq D (im_nn M) (cargs_pat gs1) g)[sb_qn (List.length gs1 + im_nn M) σ].
Proof.
  intros * H.
  assert (Hassg : forall gs0, all_assumptions (tele_sub (cargs_ctx pq D M gs0) (sb_qn (im_nn M) σ)))
    by (intros; apply all_assumptions_sub, cargs_ctx_aux_ass).
  assert (Hl : List.length pre < List.length gs).
  { apply (f_equal (@List.length _)) in H.
    rewrite length_ctx_args, length_tele_sub, length_cargs_ctx, List.length_app in H by apply Hassg; cbn in H.
    lia. }
  destruct (nth_error_lt_some' gs _ Hl) as [g Hg].
  destruct (List.nth_error_split _ _ Hg) as (gs1 & gs2 & -> & Hl1).
  exists gs1, g, gs2; split; [ reflexivity | split; [ exact Hl1 |] ].
  rewrite cargs_ctx_split, !tele_sub_app in H; cbn [tele_sub List.length] in H.
  rewrite ctx_args_app, length_cargs_ctx in H.
  cbn [centry_sub] in H; rewrite ctx_args_cons_ass in H.
  rewrite <- List.app_assoc in H; cbn [List.app] in H.
  assert (Hla : List.length (ctx_args (tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ))) = List.length pre)
    by (rewrite length_ctx_args, length_tele_sub, length_cargs_ctx by apply Hassg; exact Hl1).
  destruct (app_split_eq _ _ _ _ H Hla) as [Hpre Hrest].
  injection Hrest as _ Hκ HT _.
  split; [ rewrite <- Hpre; apply raw_args_tele_ctx_args, Hassg |].
  split; [ symmetry; exact Hκ |].
  rewrite <- HT, sb_qn_plus; reflexivity.
Qed.

(** A record's fields, at a field: those after it, its type, those before
    it. *)
(** The fields' context is of assumptions. *)
Lemma fields_tele_ass : forall fs κs, all_assumptions (fields_tele fs κs).
Proof.
  induction fs as [| fT fs IH]; intros κs; cbn [fields_tele]; [ constructor |].
  apply List.Forall_app; split; [ apply IH | constructor; [ do 2 eexists; reflexivity | constructor ] ].
Qed.

Lemma record_fctx_ass : forall R k, all_assumptions (record_fctx R k).
Proof. intros; apply fields_tele_ass. Qed.

(** A record's fields, at a field: those after it, its type at its kind,
    those before it. *)
Lemma record_fctx_at : forall R k f A, List.nth_error (record_fields R) k = Some (f, A) ->
    record_fctx R (List.length (record_fields R))
    = fields_tele (List.skipn (S k) (record_fields R)) (List.skipn (S k) (record_field_kinds R))
        ++ ce_ass (record_field_kind R k) A :: record_fctx R k.
Proof.
  intros * HfA; unfold record_fctx at 1; rewrite List.firstn_all.
  assert (Hk : S k <= List.length (record_fields R)) by (assert (Hk : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence); lia).
  rewrite <- (List.firstn_skipn (S k) (record_fields R)) at 1.
  rewrite fields_tele_app, List.length_firstn, Nat.min_l by exact Hk.
  change (fields_tele (List.firstn (S k) (record_fields R)) (record_field_kinds R)) with (record_fctx R (S k)).
  rewrite (record_fctx_succ _ _ _ _ HfA); reflexivity.
Qed.

Lemma length_record_fctx_le : forall R k, k <= List.length (record_fields R) -> List.length (record_fctx R k) = k.
Proof. exact length_record_fctx. Qed.

(** A record's fields, moved along [σ], split at a field met: the fields
    before it, and its type at its kind. *)
Lemma fctx_sub_split : forall R σ pre y κ T post,
    ctx_args (tele_sub (record_fctx R (List.length (record_fields R))) σ) = pre ++ (y, κ, T) :: post ->
    exists f A, List.nth_error (record_fields R) (List.length pre) = Some (f, A) /\
      raw_args_tele pre = tele_sub (record_fctx R (List.length pre)) σ /\ κ = record_field_kind R (List.length pre) /\
      T = A[sb_qn (List.length pre) σ].
Proof.
  intros * H.
  assert (HlF : forall k, k <= List.length (record_fields R) -> List.length (record_fctx R k) = k) by exact (length_record_fctx R).
  assert (Hass : forall k, all_assumptions (tele_sub (record_fctx R k) σ)) by (intros; apply all_assumptions_sub, record_fctx_ass).
  assert (Hl : List.length pre < List.length (record_fields R)).
  { apply (f_equal (@List.length _)) in H.
    rewrite length_ctx_args, length_tele_sub, HlF, List.length_app in H by (try apply Hass; lia); cbn in H.
    lia. }
  destruct (nth_error_lt_some' (record_fields R) _ Hl) as [[f A] HfA].
  exists f, A; split; [ exact HfA |].
  set (k := List.length pre) in *.
  rewrite (record_fctx_at _ _ _ _ HfA), tele_sub_app, ctx_args_app in H; cbn [tele_sub centry_sub] in H.
  rewrite ctx_args_cons_ass in H.
  rewrite <- List.app_assoc in H; cbn [List.app] in H.
  assert (Hla : List.length (ctx_args (tele_sub (record_fctx R k) σ)) = List.length pre)
    by (rewrite length_ctx_args, length_tele_sub, HlF by (try apply Hass; lia); reflexivity).
  destruct (app_split_eq _ _ _ _ H Hla) as [Hpre Hrest].
  injection Hrest as _ Hκ HT _.
  split; [ rewrite <- Hpre; apply raw_args_tele_ctx_args, Hass |].
  split; [ symmetry; exact Hκ |].
  rewrite <- HT, HlF by lia; reflexivity.
Qed.

(** ** Normal Keys and the Instances Normal Forms Meet *)

(** A key is normal over [Γu] when it is the key there of an instance:
    its arguments are the normal forms of the instance's
    ([view_inst_key]).  Every key the view search makes is one. *)
Definition key_normal (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (x : view_key) : Prop :=
  exists v, view_inst_key Θ Ξ Γu v x.

(** [z] is an instance the classification of [T] as its normal form meets
    in [Γ], whether [T] classifies as written or not: [classify_in_nf]
    without its first premise. *)
#[warnings="-cannot-define-projection"]
Record nf_meet_at (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (nu np n : nat) (pat : list bool) (T : exp) (z : view_key) : Prop :=
  mk_nf_meet_at
  { (** The universe [T] is a type of *)
    nfm_index : nat
    (** [T] is a type of it *)
  ; nfm_typed : Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@nfm_index
    (** The normal form of [T] *)
  ; nfm_nf : nf
    (** It is [T]'s *)
  ; nfm_nbe : nbe_ty Θ Ξ Γ T nfm_nf
    (** It holds no proof *)
  ; nfm_proof_free : nf_proof_free nfm_nf
    (** Its classification, its instances as written *)
  ; nfm_written : written_carg
    (** It classifies so *)
  ; nfm_classify : classify_arg (grp_info Θ Ξ) (rec_info Θ Ξ) nu np n pat (nf_to_exp nfm_nf) = Some nfm_written
    (** The classification, its instances keyed *)
  ; nfm_keyed : classified_carg
    (** They are keyed so, past the arguments before and the non-uniform
        parameters *)
  ; nfm_key : written_carg_key Θ Ξ (List.skipn (List.length pat + (np - nu)) Γ) nfm_written nfm_keyed
    (** [z] is one of them *)
  ; nfm_in : In z (classified_carg_view nfm_keyed) }.

(** [z] is an instance the classification as its normal form of an
    argument of one of the constructors [rcs] meets, in the context of the
    arguments before it over [Γp], at some bits [pat] for those. *)
#[warnings="-cannot-define-projection"]
Record nf_meet_in (Θ : gdeps) (Ξ : gstack) (Γp : ctx) (nu np n : nat) (rcs : list (string * list (string * abs_kind * exp)))
    (z : view_key) : Prop := mk_nf_meet_in
  { (** The constructor *)
    nmi_con : (string * list (string * abs_kind * exp))%type
    (** It is one of [rcs] *)
  ; nmi_con_in : In nmi_con rcs
    (** The arguments before the argument *)
  ; nmi_pre : list (string * abs_kind * exp)
    (** The argument's name *)
  ; nmi_name : string
    (** Its kind *)
  ; nmi_kind : abs_kind
    (** Its type *)
  ; nmi_ty : exp
    (** The arguments after it *)
  ; nmi_post : list (string * abs_kind * exp)
    (** The constructor's arguments, split at it *)
  ; nmi_split : snd nmi_con = nmi_pre ++ (nmi_name, nmi_kind, nmi_ty) :: nmi_post
    (** The bits of the arguments before *)
  ; nmi_pat : list bool
    (** One per argument before *)
  ; nmi_pat_length : List.length nmi_pat = List.length nmi_pre
    (** [z] is met there *)
  ; nmi_meet : nf_meet_at Θ Ξ (raw_args_tele nmi_pre ++ Γp) nu np n nmi_pat nmi_ty z }.

(** An instance a classified argument meets is met by its normal form:
    the classification as written meets none. *)
Lemma classify_arg_in_nf_meet : forall Θ Ξ Γ nu np n pat T g z, classify_arg_in Θ Ξ Γ nu np n pat T g ->
    In z (classified_carg_view g) -> nf_meet_at Θ Ξ Γ nu np n pat T z.
Proof.
  intros * Hg Hz; inversion Hg as [gw g' Hsyn Hk | i W gw g' _ HT HW Hpf Hcl Hk]; subst.
  - destruct (@written_carg_key_view (gc_mk Θ Ξ) _ _ _ _ Hk Hz) as (x & Hx & _).
    rewrite (classify_arg_none_view _ _ _ _ _ _ Hsyn) in Hx; destruct Hx.
  - exact (mk_nf_meet_at _ _ _ _ _ _ _ _ _ i HT W HW Hpf gw Hcl g Hk Hz).
Qed.

(** An instance classified constructors meet is met by the normal form of
    one of their arguments. *)
Lemma classify_cons_in_nf_meet : forall Θ Ξ Γp nu np n rcs cs z, classify_cons_in Θ Ξ Γp nu np n rcs cs ->
    In z (classified_cons_views cs) -> nf_meet_in Θ Ξ Γp nu np n rcs z.
Proof.
  intros * Hc Hz.
  destruct (classify_cons_in_site _ _ _ _ _ _ _ _ Hc _ Hz) as (rc & pre & y & κ & T & post & pat & g & Hrc & Hs & Hg & Hin & Hl).
  exact (mk_nf_meet_in _ _ _ _ _ _ _ _ rc Hrc pre y κ T post Hs pat Hl (classify_arg_in_nf_meet _ _ _ _ _ _ _ _ _ _ Hg Hin)).
Qed.

(** Past a telescope, its context. *)
Lemma skipn_ctx_app : forall (Δ Γ : ctx) m, m = List.length Δ -> List.skipn m (Δ ++ Γ) = Γ.
Proof. intros Δ Γ m ->; rewrite List.skipn_app, List.skipn_all, Nat.sub_diag; reflexivity. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** ** Normal Forms of Chains of [Π]s and of Inductive Types *)

  (** The normal form of a chain of relevant [Π]s ends in the normal form
      of its end, under its domains; it holds no proof if the whole does
      not. *)
  Lemma nbe_ty_pis_inv : forall Bs Γ E W, nbe_ty_f Γ (pis Bs E) W ->
      exists WBs WE, nf_to_exp W = pis (List.map nf_to_exp WBs) (nf_to_exp WE) /\ List.length WBs = List.length Bs /\
        nbe_ty_f (doms_ctx Bs ++ Γ) E WE /\ (nf_proof_free W -> nf_proof_free WE).
  Proof.
    induction Bs as [| B Bs IH]; intros Γ E W HW; cbn [pis] in HW.
    - exists nil, W; split; [ reflexivity | split; [ reflexivity | split; [ exact HW | exact (fun H => H) ] ] ].
    - destruct (nbe_ty_pi_inv _ _ _ _ _ _ _ _ HW) as (WB & WC & -> & _ & HC).
      destruct (IH _ _ _ HC) as (WBs & WE & HWC & Hl & HE & Hpf).
      exists (WB :: WBs), WE; cbn [nf_to_exp List.map pis List.length]; rewrite HWC; split; [ reflexivity | split; [ lia |] ].
      split; [ unfold doms_ctx in *; cbn [List.map List.rev]; rewrite <- List.app_assoc; exact HE |].
      intros [_ HpfC]; exact (Hpf HpfC).
  Qed.

  Lemma apps_ind_not_pi : forall qi k Ms B C, apps (a_ind qi k) Ms <> a_pi ak_relevant ak_relevant B C.
  Proof. intros * H; apply (f_equal app_head) in H; rewrite app_head_apps in H; discriminate. Qed.

  Lemma nbe_ty_placeholder_type_inv : forall Γ W, nbe_ty_f Γ a_prop W -> W = nf_prop.
  Proof. intros * [ρ m Hinit Ea Hr]; inversion Ea; subst; inversion Hr; reflexivity. Qed.

  Lemma nbe_ty_ind_inv : forall Γ qi k Ms W, nbe_ty_f Γ (apps (a_ind qi k) Ms) W -> exists Rs, W = nf_indty qi k Rs.
  Proof.
    intros * [ρ m Hinit Ea Hr].
    apply eval_apps_ind_exp in Ea as (f & ms & Ef & Ems & Eap).
    inversion Ef; subst.
    apply eval_apps_ind_inv in Eap; cbn in Eap; subst.
    inversion Hr; subst; eauto.
  Qed.

  Lemma apps_record_not_pi : forall qr Ms B C, apps (a_record qr) Ms <> a_pi ak_relevant ak_relevant B C.
  Proof. intros * H; apply (f_equal app_head) in H; rewrite app_head_apps in H; discriminate. Qed.

  Lemma nbe_ty_record_inv : forall Γ qr Ms W, nbe_ty_f Γ (apps (a_record qr) Ms) W -> exists Rs, W = nf_record qr Rs.
  Proof.
    intros * [ρ m Hinit Ea Hr].
    apply eval_apps_record_exp in Ea as (f & ms & Ef & Ems & Eap).
    inversion Ef; subst.
    apply eval_apps_record_inv in Eap; cbn in Eap; subst.
    inversion Hr; subst; eauto.
  Qed.

  (** A member's type, other than a record view's, is its type former's at
      its uniform arguments. *)
  Lemma im_ty_at_not_rview : forall pq k (M : imember) Us Ns, im_is_rview M = false ->
      im_ty_at pq k M Us Ns = apps_exp (a_ind (fst (im_ref pq k M)) (snd (im_ref pq k M))) (im_pre M Us ++ Ns).
  Proof. intros * H; unfold im_ty_at, im_is_rview in *; destruct (im_head M); [ reflexivity | reflexivity | discriminate ]. Qed.

  (** ** Meets along Equal Telescopes *)

  (** The left side of a telescope equation whose right side's head is a
      type of a universe has a head of a universe: the heads are of sorts
      of one kind ([sort_kind_of_typed]). *)
  Lemma ext_head_large : forall Γ Ψ Ψ' κ A A' (i : nat), ext_eq_ass_head gc_deps gc_stack Γ Ψ Ψ' κ A A' ->
      Ψ' ++ Γ ⊢ A' : Typeω@i -> exists k : nat, Ψ ++ Γ ⊢ A : Typeω@k.
  Proof.
    intros * [S1 HS1 S2 HS2 _ HA HA' _ _] HA'i.
    pose proof (sort_kind_of_typed _ _ _ _ _ HA'i (sort_kind_universe i) HA' (sort_kind_type_sort _ _ HS2)) as HS2r.
    inversion HS2r; subst; inversion HS2; subst; inversion HS1; subst.
    eexists; exact HA.
  Qed.

  (** Equal telescopes have heads of one kind. *)
  Lemma ext_eq_ass_kind : forall Γ Ψ Ψ' κ κ' A A', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ▹{κ} A ≈ Ψ' ▹{κ'} A' -> κ = κ'.
  Proof. intros * H; inversion H; subst; reflexivity. Qed.

  (** An instance the normal form of the right head of a telescope
      equation meets is met by the left head's: their normal forms are
      equal up to proofs ([ctxeq_nbe_ty_eq'], [nbe_ty_of_mutual_subtyp]),
      and the right one holds none ([nf_ne_proof_free_eq]).  The instances
      are keyed below both telescopes, alike. *)
  Lemma nf_meet_at_ext : forall Γu Ψ Ψ' κ A A' nu np n pat z,
      all_assumptions Ψ -> gc_deps ⍮ gc_stack ⍮ Γu ⊢ˣ Ψ ▹{κ} A ≈ Ψ' ▹{κ} A' -> List.length Ψ = List.length pat + (np - nu) ->
      nf_meet_at gc_deps gc_stack (Ψ' ++ Γu) nu np n pat A' z -> nf_meet_at gc_deps gc_stack (Ψ ++ Γu) nu np n pat A z.
  Proof.
    intros * HaΨ HE Hl [i HT W HW Hpf gw Hcl g Hk Hin].
    pose proof (ext_eq_ass_inv _ _ _ _ _ _ _ _ HE) as Hhead.
    pose proof (ext_head_tail _ _ _ _ _ _ _ _ Hhead) as HE1.
    pose proof (ext_eq_length _ _ _ _ _ HE1) as Hl'.
    pose proof (rel_ext_under_ctx_eq _ _ _ (proj1 completeness_fundamental_modules _ _ _ (ext_eq_sym_ass _ _ _ _ _ HaΨ HE1))) as HY2D.
    assert (HsΨ : ctx_scoped 0 (Ψ ++ Γu))
      by (destruct Hhead as [? ? ? ? ? HA0 _ _ _]; gen_presups; eapply wf_ctx_scoped; eassumption).
    destruct (ctxeq_nbe_ty_eq' _ _ _ _ _ HT HsΨ HY2D HW) as (W' & HW' & HWW').
    destruct (ext_head_large _ _ _ _ _ _ _ Hhead HT) as [k HT'].
    destruct (nbe_ty_of_mutual_subtyp (ext_head_sub _ _ _ _ _ _ _ _ Hhead) (ext_head_sub_rev _ _ _ _ _ _ _ _ Hhead))
      as (W0 & W0' & HW0 & HW0' & HE0).
    pose proof (functional_nbe_ty _ _ _ _ HW0' HW') as ->.
    assert (EW : W = W0) by (apply (proj1 nf_ne_proof_free_eq _ Hpf); etransitivity; [ exact HWW' | symmetry; exact HE0 ]).
    subst W0.
    rewrite (skipn_ctx_app Ψ' Γu) in Hk by lia.
    refine (mk_nf_meet_at _ _ _ _ _ _ _ _ _ k HT' W HW0 Hpf gw Hcl g _ Hin).
    rewrite (skipn_ctx_app Ψ Γu) by lia; exact Hk.
  Qed.

  (** The instances normal forms meet are of the invariant: typed
      ([nest_key_inv]) and normal. *)
  Lemma nf_meet_at_good : forall Δ Γu nu np n pat T z, all_assumptions Δ -> List.length Δ = List.length pat + (np - nu) ->
      nf_meet_at gc_deps gc_stack (Δ ++ Γu) nu np n pat T z -> key_inv gc_deps gc_stack Γu z /\ key_normal gc_deps gc_stack Γu z.
  Proof.
    intros * Hass Hl [i HT W HW Hpf gw Hcl g Hk Hin].
    rewrite (skipn_ctx_app Δ Γu) in Hk by lia.
    split; [ exact (@nest_key_inv GC _ _ _ _ _ _ _ _ _ _ _ _ Hass Hl HT HW Hpf Hcl Hk Hin) |].
    destruct (written_carg_key_view _ _ _ _ Hk Hin) as (x & _ & Hx); exists x; exact Hx.
  Qed.

  (** The arguments of an instance a proof-free normal form meets, keyed,
      read back to the instance's own: each is the strengthening of an
      argument of the normal form's end, which is its own normal form
      there ([nbe_ind_args]), and normal forms commute with weakening up
      to proofs ([nbe_wk_tele]); with no proof, exactly. *)
  Lemma nf_key_ind_args : forall Δ Γu T W (i : nat) nu np n pat gw qz kz Csz Dz Wz,
      all_assumptions Δ -> List.length Δ = List.length pat + (np - nu) ->
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W -> nf_proof_free W ->
      classify_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some gw ->
      In (vi_ind qz kz Csz) (classified_carg_view gw) -> ind_lookup gc_deps gc_stack qz = Some Dz ->
      nbes gc_deps gc_stack Γu Csz (tele_insts (ind_uparams Dz) sb_id Csz) Wz -> List.map nf_to_exp Wz = Csz.
  Proof.
    intros * Hass Hlen HT HW Hpf Hcls Hin Hlz HWz.
    destruct (classify_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs & E & m & HWe & HE & Hh & Hg & Hm & HC).
    unfold grp_info in Hg; rewrite Hlz in Hg.
    destruct (kz <? ind_ndecl Dz) eqn:Hkz; [ injection Hg as <- | discriminate ].
    apply Nat.ltb_lt in Hkz.
    destruct (List.nth_error (ind_members Dz) kz) as [Mk |] eqn:HMk;
      [| apply List.nth_error_None in HMk; pose proof (ind_ndecl_le Dz); lia ].
    change (ind_member Dz kz = Some Mk) in HMk.
    pose proof (soundness_ty' HT HW) as HTW.
    assert (HWt : Δ ++ Γu ⊢ nf_to_exp W : Typeω@i) by (gen_presups; assumption).
    rewrite HWe in HWt; pose proof (pis_typed_inv _ _ _ _ HWt) as HEt.
    pose proof HW as [ρ0 m0 _ _ Hr0]; pose proof (read_typ_type_nf _ _ _ Hr0) as HWn.
    destruct (nbe_ty_pis_proof_free _ _ _ _ HWn Hpf (nbe_ty_self _ _ _ _ HT HW Hpf) HWe) as (WE & HWE & HpfE & HnE & HWEe).
    rewrite <- HWEe in Hh; destruct (nf_ind_view _ _ _ HWE Hh) as [Rs ->].
    cbn [nf_to_exp] in HWEe; subst E; cbn [nf_proof_free] in HpfE.
    rewrite app_args_apps in HC, Hm; cbn [app_args List.app] in HC, Hm.
    pose proof (ind_type_length _ _ _ _ _ _ _ Hlz HMk HEt) as HRl.
    pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlz HMk HEt HRl) as HRt.
    assert (HΓe : ⊢ doms_ctx Bs ++ Δ ++ Γu) by (gen_presups; assumption).
    assert (HΓu : ⊢ Γu) by (rewrite List.app_assoc in HΓe; eapply ctx_app_wf_tail; exact HΓe).
    destruct (decl_of_lookup _ _ _ _ _ HΓu Hlz) as [Hdt Hc].
    set (L := List.length Bs + List.length pat + (np - nu)) in *.
    set (Ψ := doms_ctx Bs ++ Δ).
    assert (HlΨ : List.length Ψ = L) by (unfold Ψ, L, doms_ctx; rewrite List.length_app, List.length_rev, List.length_map; lia).
    assert (HΨa : all_assumptions Ψ)
      by (unfold Ψ; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, all_assumptions_map_ass | exact Hass ]).
    assert (HΨΓ : ⊢ Ψ ++ Γu) by (unfold Ψ; rewrite <- List.app_assoc; exact HΓe).
    destruct (nbes_nth _ _ _ _ _ _ HWz) as (HlWz & HlTz & Hnthz).
    assert (HCszl : List.length Csz = ind_nu Dz)
      by (apply (f_equal (@List.length _)) in HC; rewrite List.length_firstn, !List.length_map in HC; rewrite ?List.length_map in Hm; lia).
    set (φ := wk_pat (List.repeat true L)) in *.
    assert (HCφ : List.firstn (ind_nu Dz) (List.map nf_to_exp Rs) = List.map (fun C => C[φ]ʷ) Csz) by exact HC.
    apply List.nth_error_ext; intros j.
    destruct (Nat.lt_ge_cases j (ind_nu Dz)) as [Hj | Hj];
      [| rewrite !(proj2 (List.nth_error_None _ _)) by (rewrite ?List.length_map; lia); reflexivity ].
    destruct (nth_error_lt_some' Csz j ltac:(lia)) as [C HCj].
    destruct (nth_error_lt_some' (tele_insts (ind_uparams Dz) Id Csz) j ltac:(lia)) as [T0 HT0].
    destruct (Hnthz _ _ _ HCj HT0) as (W0 & HW0 & HCt & HnC).
    destruct (nbe_wk_tele Ψ Γu C T0 W0 HΨa HΨΓ HCt HnC) as (W' & W'' & HW' & HEw & HW'e).
    rewrite HlΨ in HW', HW'e.
    pose proof (tele_insts_params_uniform_wk Dz Mk Csz (List.map nf_to_exp Rs) φ j T0 (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) HCszl HCφ HT0) as HT0w.
    assert (HPj : List.nth_error (List.map nf_to_exp Rs) j = Some C[φ]ʷ).
    { rewrite <- (List.firstn_skipn (ind_nu Dz) (List.map nf_to_exp Rs)), List.nth_error_app1 by (rewrite List.length_firstn; lia).
      rewrite HCφ, List.nth_error_map, HCj; reflexivity. }
    destruct (nbe_ind_args _ _ _ _ _ _ _ Hlz HMk HRl HRt HnE HpfE j _ _ HPj HT0w) as (R & HR & HnR).
    assert (Eφ : forall M, M[φ]ʷ = M[wk_shiftn L]ʷ) by (intros; apply exp_wk_wk_eq, wk_pat_trues).
    rewrite !Eφ in HnR; unfold Ψ in HW'; rewrite <- List.app_assoc in HW'.
    pose proof (functional_nbe _ _ _ _ _ HnR HW') as ->.
    assert (EW : W' = W'') by (apply (proj1 nf_ne_proof_free_eq _ (all_proof_free_nth _ _ _ HpfE HR)); exact HEw).
    rewrite List.nth_error_map, HR in HPj; cbn in HPj; injection HPj as HPj.
    rewrite EW, HW'e, Eφ in HPj.
    rewrite <- !(exp_wk_wk_eq _ _ _ (wk_pat_trues L)) in HPj; apply exp_wk_pat_inj in HPj.
    rewrite List.nth_error_map, HW0, HCj; cbn; rewrite HPj; reflexivity.
  Qed.

  (** Likewise for a record view the normal form meets. *)
  Lemma nf_key_record_args : forall Δ Γu T W (i : nat) nu np n pat gw qz Isz Rz Wz,
      all_assumptions Δ -> List.length Δ = List.length pat + (np - nu) ->
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W -> nf_proof_free W ->
      classify_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some gw ->
      In (vi_record qz Isz) (classified_carg_view gw) -> record_lookup gc_deps gc_stack qz = Some Rz ->
      nbes gc_deps gc_stack Γu Isz (tele_insts (record_params Rz) sb_id Isz) Wz -> List.map nf_to_exp Wz = Isz.
  Proof.
    intros * Hass Hlen HT HW Hpf Hcls Hin Hlz HWz.
    destruct (nest_record_end _ _ _ _ _ _ _ _ _ _ _ _ HT HW Hpf Hcls Hin) as (Bs & Rz' & Rs & HWe & Hlz' & HEt & HnE & HRl & _ & HC & HpfR).
    rewrite Hlz in Hlz'; injection Hlz' as <-.
    assert (HΓe : ⊢ doms_ctx Bs ++ Δ ++ Γu) by (gen_presups; assumption).
    assert (HΓu : ⊢ Γu) by (rewrite List.app_assoc in HΓe; eapply ctx_app_wf_tail; exact HΓe).
    pose proof (wf_record_closed _ _ _ _ _ HΓu Hlz) as HcR.
    pose proof (record_lookup_typed _ _ (ctx_wf_gctx _ _ _ HΓu) (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ HΓu)) _ _ Hlz) as HRt.
    assert (HRa : all_assumptions (record_params Rz)) by exact (typed_params_ass _ _ _ HRt).
    set (L := List.length Bs + List.length pat + (np - nu)) in *.
    set (Ψ := doms_ctx Bs ++ Δ).
    assert (HlΨ : List.length Ψ = L) by (unfold Ψ, L, doms_ctx; rewrite List.length_app, List.length_rev, List.length_map; lia).
    assert (HΨa : all_assumptions Ψ)
      by (unfold Ψ; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, all_assumptions_map_ass | exact Hass ]).
    assert (HΨΓ : ⊢ Ψ ++ Γu) by (unfold Ψ; rewrite <- List.app_assoc; exact HΓe).
    destruct (nbes_nth _ _ _ _ _ _ HWz) as (HlWz & HlTz & Hnthz).
    set (φ := wk_pat (List.repeat true L)) in *.
    apply List.nth_error_ext; intros j.
    destruct (Nat.lt_ge_cases j (List.length Isz)) as [Hj | Hj];
      [| rewrite !(proj2 (List.nth_error_None _ _)) by (rewrite ?List.length_map; lia); reflexivity ].
    destruct (nth_error_lt_some' Isz j Hj) as [C HCj].
    destruct (nth_error_lt_some' (tele_insts (record_params Rz) Id Isz) j ltac:(lia)) as [T0 HT0].
    destruct (Hnthz _ _ _ HCj HT0) as (W0 & HW0 & HCt & HnC).
    destruct (nbe_wk_tele Ψ Γu C T0 W0 HΨa HΨΓ HCt HnC) as (W' & W'' & HW' & HEw & HW'e).
    rewrite HlΨ in HW', HW'e.
    assert (HT0w : List.nth_error (tele_insts (record_params Rz) Id (List.map nf_to_exp Rs)) j = Some T0[φ]ʷ).
    { rewrite HC, (List.map_ext (fun C => C[φ]ʷ) (fun M => M[ι φ]) (fun M => eq_sym (exp_sub_of_wk M _))).
      rewrite (tele_insts_closed_sub _ _ _ _ _ HRa (closed_params _ HcR) HT0), exp_sub_of_wk; reflexivity. }
    assert (HPj : List.nth_error (List.map nf_to_exp Rs) j = Some C[φ]ʷ) by (rewrite HC, List.nth_error_map, HCj; reflexivity).
    destruct (nbe_record_args _ _ _ _ _ _ Hlz HEt HnE HpfR j _ _ HPj HT0w) as (R & HR & HnR).
    assert (Eφ : forall M, M[φ]ʷ = M[wk_shiftn L]ʷ) by (intros; apply exp_wk_wk_eq, wk_pat_trues).
    rewrite !Eφ in HnR; unfold Ψ in HW'; rewrite <- List.app_assoc in HW'.
    pose proof (functional_nbe _ _ _ _ _ HnR HW') as ->.
    assert (EW : W' = W'') by (apply (proj1 nf_ne_proof_free_eq _ (all_proof_free_nth _ _ _ HpfR HR)); exact HEw).
    rewrite List.nth_error_map, HR in HPj; cbn in HPj; injection HPj as HPj.
    rewrite EW, HW'e, Eφ in HPj.
    rewrite <- !(exp_wk_wk_eq _ _ _ (wk_pat_trues L)) in HPj; apply exp_wk_pat_inj in HPj.
    rewrite List.nth_error_map, HW0, HCj; cbn; rewrite HPj; reflexivity.
  Qed.

  (** ** Normal Keys

      The terms of an instance are equal to their normal forms. *)
  Lemma nbes_self_eq : forall Γ Ms As Ws, nbes gc_deps gc_stack Γ Ms As Ws ->
      forall j N N' A, List.nth_error Ms j = Some N -> List.nth_error (List.map nf_to_exp Ws) j = Some N' ->
        List.nth_error As j = Some A -> Γ ⊢ N ≈ N' : A.
  Proof.
    intros * Hn j N N' A HN HN' HA.
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (_ & _ & Hnth).
    destruct (Hnth _ _ _ HN HA) as (W & HW & HNt & HNW).
    rewrite List.nth_error_map, HW in HN'; cbn in HN'; injection HN' as <-.
    exact (soundness' HNt HNW).
  Qed.

  (** The terms of an instance of a closed telescope are equal to their
      normal forms, as a substitution. *)
  Lemma nbes_sub_eq : forall Γ U Ms Ws, all_assumptions U -> ⊢ U -> ⊢ Γ -> List.length Ms = List.length U ->
      nbes gc_deps gc_stack Γ Ms (tele_insts U Id Ms) Ws -> Γ ⊢ˢ sb_of_list Id Ms ≈ sb_of_list Id (List.map nf_to_exp Ws) : U.
  Proof.
    intros * HUa HU HΓ HlM Hn.
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlW & HlT & _).
    rewrite <- (List.app_nil_r U).
    eapply wf_sub_eq_of_list; [ exact HUa | rewrite List.app_nil_r; exact HU | exact (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HΓ))
                              | exact HlM | rewrite List.length_map, HlW; exact HlM |].
    exact (nbes_self_eq _ _ _ _ Hn).
  Qed.

  (** Two normal keys' arguments equal up to proofs are equal, as
      substitutions: their instances are ([nbes_upto_proofs_eq_nf]). *)
  Lemma nbes_keys_sub_eq : forall Γ U C1 C2 W1 W2, all_assumptions U -> ctx_scoped 0 U -> ⊢ U -> ⊢ Γ ->
      List.length C1 = List.length U ->
      nbes gc_deps gc_stack Γ C1 (tele_insts U Id C1) W1 -> nbes gc_deps gc_stack Γ C2 (tele_insts U Id C2) W2 ->
      nfs_eq_upto_proofs W1 W2 ->
      Γ ⊢ˢ sb_of_list Id (List.map nf_to_exp W1) ≈ sb_of_list Id (List.map nf_to_exp W2) : U.
  Proof.
    intros * HUa HUs HU HΓ Hl1 Hn1 Hn2 HWW.
    pose proof (nbes_sub_eq _ _ _ _ HUa HU HΓ Hl1 Hn1) as H1.
    assert (HUΓ : ⊢ U ++ Γ) by (apply wf_ctx_closed_app; assumption).
    destruct (nbes_nth _ _ _ _ _ _ Hn1) as (HlW1 & _).
    destruct (FiledConstructorTypes.nfs_eq_upto_proofs_nth _ _ HWW) as [HlWW _].
    assert (H2 : Γ ⊢ˢ sb_of_list Id C1 ≈ sb_of_list Id (List.map nf_to_exp W2) : U).
    { rewrite <- (List.app_nil_r U).
      eapply wf_sub_eq_of_list; [ exact HUa | rewrite List.app_nil_r; exact HU | exact (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HΓ))
                                | exact Hl1 | rewrite List.length_map; lia |].
      intros k N N' T HN HN' HT.
      rewrite List.nth_error_map in HN'; destruct (List.nth_error W2 k) as [R |] eqn:HR; cbn in HN'; [ injection HN' as <- | discriminate ].
      exact (nbes_upto_proofs_eq_nf _ _ _ _ _ _ _ _ HUa HUΓ Hn1 Hn2 HWW _ _ _ _ HN HR HT). }
    eapply wf_sub_eq_trans; [ apply wf_sub_eq_sym; exact H1 | exact H2 ].
  Qed.

  (** A normal key of an inductive container: its arguments are the
      normal forms of an instance. *)
  Lemma key_normal_ind : forall Γu qc k Ws D, key_normal gc_deps gc_stack Γu (vk_ind qc k Ws) ->
      ind_lookup gc_deps gc_stack qc = Some D -> exists Cs, nbes gc_deps gc_stack Γu Cs (tele_insts (ind_uparams D) Id Cs) Ws.
  Proof.
    intros * [v Hv] Hl; inversion Hv as [? ? Cs D' ? Hl' Hn |]; subst.
    rewrite Hl in Hl'; injection Hl' as <-; exists Cs; exact Hn.
  Qed.

  (** A normal key of a record. *)
  Lemma key_normal_record : forall Γu qr Ws Rr, key_normal gc_deps gc_stack Γu (vk_record qr Ws) ->
      record_lookup gc_deps gc_stack qr = Some Rr -> exists Is, nbes gc_deps gc_stack Γu Is (tele_insts (record_params Rr) Id Is) Ws.
  Proof.
    intros * [v Hv] Hl; inversion Hv as [| ? Is Rr' ? Hl' Hn]; subst.
    rewrite Hl in Hl'; injection Hl' as <-; exists Is; exact Hn.
  Qed.

  (** The normal forms of a normal key's arguments are them up to proofs. *)
  Lemma key_normal_self : forall Γ U C Ws, all_assumptions U -> ⊢ U -> ⊢ Γ -> List.length Ws = List.length U ->
      nbes gc_deps gc_stack Γ C (tele_insts U Id C) Ws ->
      (forall j N T, List.nth_error (List.map nf_to_exp Ws) j = Some N ->
         List.nth_error (tele_insts U Id (List.map nf_to_exp Ws)) j = Some T -> Γ ⊢ N : T) ->
      exists WQ, nbes gc_deps gc_stack Γ (List.map nf_to_exp Ws) (tele_insts U Id (List.map nf_to_exp Ws)) WQ /\
        nfs_eq_upto_proofs Ws WQ.
  Proof.
    intros * HUa HU HΓ HlU Hn Ht.
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlW & HlA & _).
    destruct (@nbes_exist GC Γ U (List.map nf_to_exp Ws) HUa ltac:(rewrite List.length_map; lia) Ht) as [WQ HWQ].
    exists WQ; split; [ exact HWQ |].
    apply (nbes_conv_inst _ _ _ _ _ _ HUa HU HΓ Hn HWQ ltac:(rewrite List.length_map; lia)).
    exact (nbes_self_eq _ _ _ _ Hn).
  Qed.

  (** The sibling a member [jm] of the group at [qx] gives at a normal
      key's arguments [Ws]: the member its type former is, at the normal
      forms of its uniform arguments at [Ws], up to proofs. *)
  Lemma sibling_of_member : forall Γu qx D kx Ws ss jm Mjm, ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D ->
      List.length Ws = ind_nu D ->
      (forall j C T, List.nth_error (List.map nf_to_exp Ws) j = Some C ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.map nf_to_exp Ws)) j = Some T -> Γu ⊢ C : T) ->
      key_normal gc_deps gc_stack Γu (vk_ind qx kx Ws) ->
      siblings_from gc_deps gc_stack Γu qx Ws 0 (ind_members D) ss -> ind_member D jm = Some Mjm -> im_is_rview Mjm = false ->
      exists Dq WQ e, ind_lookup gc_deps gc_stack (fst (im_ref qx jm Mjm)) = Some Dq /\
        nbes gc_deps gc_stack Γu (im_pre Mjm (List.map nf_to_exp Ws)) (tele_insts (ind_uparams Dq) Id (im_pre Mjm (List.map nf_to_exp Ws))) WQ /\
        In e ss /\ view_key_eq (vk_ind (fst (im_ref qx jm Mjm)) (snd (im_ref qx jm Mjm)) WQ) e.
  Proof.
    intros * Hg HΓu Hl HWl HCt Hkn Hss HM Hnr.
    destruct (siblings_from_nth _ _ _ _ _ _ _ _ Hss) as [_ Hssn].
    destruct (Hssn _ _ HM) as (e & He & Hse); cbn [Nat.add] in Hse.
    inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr']; subst;
      unfold im_ref, im_pre; rewrite Hh; cbn [fst snd].
    3:{ exfalso; unfold im_is_rview in Hnr; rewrite Hh in Hnr; discriminate Hnr. }
    - destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
      destruct (key_normal_ind _ _ _ _ _ Hkn Hl) as [C0 Hn0].
      destruct (key_normal_self _ _ _ _ (decl_closed_ass _ Hc) (decl_typed_uparams_field _ _ _ Hdt) HΓu HWl Hn0 HCt) as (WQ & HWQ & HE).
      exists D, WQ, (vk_ind qx jm Ws); split; [ exact Hl | split; [ exact HWQ | split; [ exact (List.nth_error_In _ _ He) |] ] ].
      apply key_args_upto; symmetry; exact HE.
    - destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [_ Hcv].
      rewrite (tele_insts_sub (ind_uparams Dv) 0 Id Id (sb_of_list sb_id (List.map nf_to_exp Ws)) Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv)
                 ltac:(intros; lia)) in Hnv.
      exists Dv, Wv, (vk_ind qv kv Wv); split; [ exact Hlv | split; [ exact Hnv | split; [ exact (List.nth_error_In _ _ He) | reflexivity ] ] ].
  Qed.

  (** The sibling a record view member [jm] of the group at [qx] gives at
      [Ws]: the record at the normal forms of its instance at [Ws]. *)
  Lemma sibling_of_record_member : forall Γu qx D Ws ss jm Mjm qr Ir fl,
      siblings_from gc_deps gc_stack Γu qx Ws 0 (ind_members D) ss -> ind_member D jm = Some Mjm ->
      im_head Mjm = mh_record qr Ir fl ->
      exists Rr WQ, record_lookup gc_deps gc_stack qr = Some Rr /\
        nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list sb_id (List.map nf_to_exp Ws)]) Ir)
          (List.map (fun T => T[sb_of_list sb_id (List.map nf_to_exp Ws)]) (tele_insts (record_params Rr) sb_id Ir)) WQ /\
        In (vk_record qr WQ) ss.
  Proof.
    intros * Hss HM Hh.
    destruct (siblings_from_nth _ _ _ _ _ _ _ _ Hss) as [_ Hssn].
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
      [qx] at a normal key's arguments [Ws] is, up to proofs, the sibling
      at [Ws] of the member the argument's shape ends in. *)
  Theorem rec_meet_in_siblings : forall Γu qx D kx Ws ss m Mi c gs gs1 t gs2 nu np n pat z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Ws = ind_nu D ->
      (forall j C T, List.nth_error (List.map nf_to_exp Ws) j = Some C ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.map nf_to_exp Ws)) j = Some T -> Γu ⊢ C : T) ->
      key_normal gc_deps gc_stack Γu (vk_ind qx kx Ws) ->
      siblings_from gc_deps gc_stack Γu qx Ws 0 (ind_members D) ss ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      nf_meet_at gc_deps gc_stack (tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id (List.map nf_to_exp Ws)) ++ Γu) nu np n pat
        (ptyp_ty qx D (im_nn Mi) (cargs_pat gs1) t)[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id (List.map nf_to_exp Ws))] z ->
      List.length pat = List.length gs1 -> np - nu = im_nn Mi ->
      key_in z ss.
  Proof.
    intros * Hg HΓu Hl HWl HCt Hkn Hss HM Hcon Heq Hm Hlp Hnn.
    set (Cs := List.map nf_to_exp Ws) in *.
    assert (HCl : List.length Cs = ind_nu D) by (unfold Cs; rewrite List.length_map; exact HWl).
    destruct Hm as [i HT W HW Hpf gz Hcls gk Hk Hzk].
    rewrite (skipn_ctx_app (tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) Γu) in Hk
      by (rewrite length_tele_sub, List.length_app, length_cargs_ctx; unfold im_nn in *; lia).
    destruct (written_carg_key_view _ _ _ _ Hk Hzk) as (z0 & Hin & Hzz).
    (** the instance found, keyed: its key is the sibling's up to proofs
        when its arguments are the sibling's normal forms *)
    assert (Hfin : forall U Q WQ Wz, all_assumptions U -> ⊢ U ->
               nbes gc_deps gc_stack Γu Q (tele_insts U Id Q) WQ ->
               nbes gc_deps gc_stack Γu (List.map nf_to_exp WQ) (tele_insts U Id (List.map nf_to_exp WQ)) Wz ->
               nfs_eq_upto_proofs WQ Wz).
    { intros * HUa HU HnQ HWz.
      destruct (nbes_nth _ _ _ _ _ _ HnQ) as (HlWQ & _).
      apply (nbes_conv_inst _ _ _ _ _ _ HUa HU HΓu HnQ HWz ltac:(rewrite List.length_map; lia)).
      exact (nbes_self_eq _ _ _ _ HnQ). }
    clear Hzk.
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
    destruct (nbe_ty_pis_inv _ _ _ _ HW) as (WBs & WE & HWe & HlWB & HWE & HpfE).
    specialize (HpfE Hpf).
    unfold ind_mty in HT, HWE; destruct (ind_member D (ptyp_mem t)) as [Mjm |] eqn:HMjm.
    2:{ rewrite (nbe_ty_placeholder_type_inv _ _ HWE) in HWe; cbn [nf_to_exp] in HWe.
        assert (HT0 : forall B C, a_prop <> a_pi ak_relevant ak_relevant B C) by (intros B C H0; discriminate H0).
        destruct z0 as [qz kz Csz | qz Isz].
        - destruct (classify_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & mz & HWe2 & HE2 & Hh2 & _).
          rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 HT0 HWe) as [_ ->]; discriminate.
        - destruct (classify_arg_record_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & HWe2 & HE2 & Hh2 & _).
          rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 HT0 HWe) as [_ ->]; discriminate. }
    pose proof (pis_typed_inv _ _ _ _ HT) as HEt.
    set (Ψ := doms_ctx Bs ++ tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) σ).
    assert (HlΨ : List.length Ψ = K)
      by (unfold Ψ, K, doms_ctx; rewrite List.length_app, length_tele_sub, List.length_rev, List.length_map, List.length_app,
            length_cargs_ctx; unfold im_nn; lia).
    assert (HΨa : all_assumptions Ψ).
    { unfold Ψ; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, all_assumptions_map_ass |].
      apply all_assumptions_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ Hdt _ _ HM) ]. }
    assert (HΨΓ : ⊢ Ψ ++ Γu) by (unfold Ψ; rewrite <- List.app_assoc; gen_presups; assumption).
    assert (Hctx : doms_ctx Bs ++ Γ = Ψ ++ Γu) by (unfold Ψ, Γ; rewrite List.app_assoc; reflexivity).
    destruct (im_is_rview Mjm) eqn:Hnr.
    { (** a record view member: the end is the record type at the member's
          instance, whose normal form is the sibling's *)
      unfold im_is_rview in Hnr; destruct (im_head Mjm) as [| | qr Ir fl] eqn:Hh; try discriminate Hnr.
      unfold im_ty_at in HT, HWE, HEt; rewrite Hh in HT, HWE, HEt.
      rewrite <- (im_pre_wk D (ptyp_mem t) Mjm Cs (wk_shiftn K) Hc HMjm HCl) in HT, HWE, HEt.
      destruct (nbe_ty_record_inv _ _ _ _ HWE) as [Rs ->].
      cbn [nf_to_exp] in HWe; cbn [nf_proof_free] in HpfE.
      destruct z0 as [qz kz Csz | qz Isz].
      - exfalso; destruct (classify_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & mz & HWe2 & HE2 & Hh2 & _).
        rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 (apps_record_not_pi _ _) HWe) as [_ ->].
        rewrite app_head_apps in Hh2; discriminate.
      - destruct (classify_arg_record_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & HWe2 & HE2 & Hh2 & _ & _ & HC2).
        rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 (apps_record_not_pi _ _) HWe) as [-> ->].
        rewrite app_head_apps in Hh2; cbn in Hh2; injection Hh2 as <-.
        rewrite app_args_apps in HC2; cbn [app_args List.app] in HC2.
        rewrite List.length_map, HlWB, Hlp, Hnn in HC2.
        replace (List.length Bs + List.length gs1 + im_nn Mi) with K in HC2 by (unfold K; lia).
        destruct (sibling_of_record_member _ _ _ _ _ _ _ _ _ _ Hss HMjm Hh) as (Rr & WQ & HlR & HnQ & HinQ).
        fold Cs in HnQ.
        destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMjm Hh) as [Rr' HRf].
        pose proof (rview_record_lookup _ _ _ _ _ _ HRf) as HlR'; rewrite HlR in HlR'; injection HlR' as <-.
        pose proof (rview_record_count _ _ _ _ _ _ HRf) as HIl.
        pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) HlR) as HcR.
        pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR) as HRt.
        assert (HRa : all_assumptions (record_params Rr)) by exact (typed_params_ass _ _ _ HRt).
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
          destruct (nbe_wk_tele Ψ Γu Qj T0 W0 HΨa HΨΓ HQt HnQj) as (W' & W'' & HW' & HEw & HW'e).
          rewrite HlΨ in HW', HW'e.
          assert (HT0w : List.nth_error (tele_insts (record_params Rr) Id (List.map (fun N => N[wk_shiftn K]ʷ) Q)) j
                         = Some T0[wk_shiftn K]ʷ).
          { rewrite (List.map_ext (fun N => N[wk_shiftn K]ʷ) (fun M => M[ι (wk_shiftn K)]) (fun M => eq_sym (exp_sub_of_wk M _))).
            rewrite (tele_insts_closed_sub _ _ _ _ _ HRa (closed_params _ HcR) HT0), exp_sub_of_wk; reflexivity. }
          assert (HPj : List.nth_error (List.map (fun N => N[wk_shiftn K]ʷ) Q) j = Some Qj[wk_shiftn K]ʷ)
            by (rewrite List.nth_error_map, HQj; reflexivity).
          destruct (nbe_record_args _ _ _ _ _ _ HlR HEt HWE HpfE j _ _ HPj HT0w) as (R & HR & HnR).
          rewrite Hctx in HnR.
          pose proof (functional_nbe _ _ _ _ _ HnR HW') as ->.
          assert (EW : W' = W'') by (apply (proj1 nf_ne_proof_free_eq _ (all_proof_free_nth _ _ _ HpfE HR)); exact HEw).
          assert (HCw : List.nth_error (List.map (fun C => C[wk_pat (List.repeat true K)]ʷ) Isz) j
                        = Some C[wk_pat (List.repeat true K)]ʷ)
            by (rewrite List.nth_error_map, HCj; reflexivity).
          rewrite <- HC2, List.nth_error_map, HR in HCw; cbn in HCw; injection HCw as HCw.
          rewrite EW, HW'e, <- (exp_wk_wk_eq _ _ _ (wk_pat_trues K)) in HCw.
          apply exp_wk_pat_inj in HCw.
          rewrite HCj, List.nth_error_map, HW0; cbn; rewrite HCw; reflexivity. }
        (** the key: the sibling's up to proofs *)
        inversion Hzz as [| ? ? Rr2 Wz Hlr2 HWz]; subst.
        rewrite HlR in Hlr2; injection Hlr2 as <-.
        pose proof (record_typed_fctx_wf _ _ _ HRt 0 ltac:(lia)) as HP; unfold record_fctx in HP; cbn in HP.
        exists (vk_record qr WQ); split; [ exact HinQ |].
        apply record_key_args_upto; symmetry; exact (Hfin _ _ _ _ HRa HP HnQ HWz). }
    destruct z0 as [qz kz Csz | qz Isz].
    2:{ exfalso; rewrite (im_ty_at_not_rview _ _ _ _ _ Hnr) in HWE; destruct (nbe_ty_ind_inv _ _ _ _ _ HWE) as [Rs ->].
        cbn [nf_to_exp] in HWe; destruct (classify_arg_record_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & HWe2 & HE2 & Hh2 & _).
        rewrite HWe2 in HWe; destruct (pis_inj _ _ _ _ HE2 (apps_ind_not_pi _ _ _) HWe) as [_ ->].
        rewrite app_head_apps in Hh2; discriminate. }
    destruct (classify_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs2 & E2 & mz & HWe2 & HE2 & Hh2 & Hg2 & Hm2 & HC2).
    rewrite (im_ty_at_not_rview _ _ _ _ _ Hnr) in HT, HWE, HEt.
    rewrite <- (im_pre_wk D (ptyp_mem t) Mjm Cs (wk_shiftn K) Hc HMjm HCl) in HT, HWE, HEt.
    (** its normal form ends in the member's at the normal forms of its
        arguments: that is where the occurrence is found *)
    destruct (nbe_ty_ind_inv _ _ _ _ _ HWE) as [Rs ->].
    cbn [nf_to_exp] in HWe; rewrite HWe2 in HWe; cbn [nf_proof_free] in HpfE.
    destruct (pis_inj _ _ _ _ HE2 (apps_ind_not_pi _ _ _) HWe) as [-> ->].
    rewrite app_head_apps in Hh2; cbn in Hh2; injection Hh2 as Hqz Hkz.
    rewrite app_args_apps in Hm2, HC2; cbn [app_args List.app] in Hm2, HC2.
    rewrite List.length_map, HlWB, Hlp, Hnn in HC2.
    replace (List.length Bs + List.length gs1 + im_nn Mi) with K in HC2 by (unfold K; lia).
    destruct (sibling_of_member _ _ _ _ _ _ _ _ Hg HΓu Hl HWl HCt Hkn Hss HMjm Hnr) as (Dq & WQ & e & HlQ & HnQ & HinQ & Hee).
    fold Cs in HnQ.
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
      destruct (nbe_wk_tele Ψ Γu Qj T0 W0 HΨa HΨΓ HQt HnQj) as (W' & W'' & HW' & HEw & HW'e).
      rewrite HlΨ in HW', HW'e.
      pose proof (tele_insts_params_uniform_wk Dq Mkr Q args (wk_shiftn K) j T0 (decl_closed_ass _ Hcq) (decl_closed_uparams _ Hcq) HlQu Hfa HT0) as HT0w.
      assert (HPj : List.nth_error args j = Some Qj[wk_shiftn K]ʷ)
        by (unfold args; rewrite List.nth_error_app1 by (rewrite List.length_map; lia); rewrite List.nth_error_map, HQj; reflexivity).
      destruct (nbe_ind_args _ _ _ _ _ _ _ HlQ HMkr HRl HRt HWE HpfE j _ _ HPj HT0w) as (R & HR & HnR).
      rewrite Hctx in HnR.
      pose proof (functional_nbe _ _ _ _ _ HnR HW') as ->.
      assert (EW : W' = W'') by (apply (proj1 nf_ne_proof_free_eq _ (all_proof_free_nth _ _ _ HpfE HR)); exact HEw).
      assert (HCw : List.nth_error (List.map (fun C => C[wk_pat (List.repeat true K)]ʷ) Csz) j = Some C[wk_pat (List.repeat true K)]ʷ)
        by (rewrite List.nth_error_map, HCj; reflexivity).
      rewrite <- HC2, List.nth_error_firstn in HCw.
      destruct (j <? ind_nu Dq) eqn:Ejn; [| apply Nat.ltb_ge in Ejn; lia ].
      rewrite List.nth_error_map, HR in HCw; cbn in HCw; injection HCw as HCw.
      rewrite EW, HW'e, <- (exp_wk_wk_eq _ _ _ (wk_pat_trues K)) in HCw.
      apply exp_wk_pat_inj in HCw.
      rewrite HCj, List.nth_error_map, HW0; cbn; rewrite HCw; reflexivity. }
    (** the key: the sibling's up to proofs *)
    inversion Hzz as [? ? ? D2 Wz Hl2 HWz |]; subst.
    rewrite HlQ in Hl2; injection Hl2 as <-.
    exists e; split; [ exact HinQ |].
    etransitivity; [| exact Hee ].
    apply key_args_upto; symmetry; exact (Hfin _ _ _ _ (decl_closed_ass _ Hcq) (decl_typed_uparams_field _ _ _ Hdtq) HnQ HWz).
  Qed.

  (** ** Instances at the Initial Environment *)

  (** The terms of a typed instance are scoped in its context. *)
  Lemma typed_inst_scoped : forall Γ U Ms, all_assumptions U -> List.length Ms = List.length U ->
      (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts U Id Ms) j = Some T -> Γ ⊢ N : T) ->
      List.Forall (exp_scoped (List.length Γ)) Ms.
  Proof.
    intros * HUa Hl HMs; apply List.Forall_forall; intros N HN.
    destruct (List.In_nth_error _ _ HN) as [j Hj].
    assert (Hjl : j < List.length (tele_insts U Id Ms))
      by (rewrite length_tele_insts by exact HUa; assert (Hj' : j < List.length Ms) by (apply List.nth_error_Some; congruence); lia).
    destruct (nth_error_lt_some' _ _ Hjl) as [T HT].
    exact (wf_exp_scoped_term _ _ _ _ _ (HMs _ _ _ Hj HT)).
  Qed.

  (** Arguments of a closed telescope [C] are related exactly when their
      environments of [C] are. *)
  Lemma closed_tele_args_env_iff : forall C RC, all_assumptions C -> ⊨ C -> EF C ≈ C ∈ per_ctx_env ↘ RC ->
      forall xs ys, List.length xs = List.length C -> List.length ys = List.length C ->
      per_tele_args (List.rev C) nil nil xs ys <-> RC (env_tele nil (List.rev C) xs) (env_tele nil (List.rev C) ys).
  Proof.
    intros * Ha HC HRC xs ys Hlx Hly.
    assert (HRC0 : EF C ++ ⋅ ≈ C ++ ⋅ ∈ per_ctx_env ↘ RC) by (rewrite List.app_nil_r; exact HRC).
    assert (HC0 : ⊨ C ++ ⋅) by (rewrite List.app_nil_r; exact HC).
    split; intros H.
    - exact (tele_args_env_rel_gen C nil (fun _ _ => True) RC nil nil xs ys per_ctx_env_nil_true HRC0 HC0 I Hlx H).
    - assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
      assert (HRC' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ RC)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
      destruct (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true HC' (List.Forall_rev Ha) HRC' nil nil
                  (tele_entries nil (List.rev C) xs) (tele_entries nil (List.rev C) ys)
                  ltac:(rewrite tele_entries_length, List.length_rev; exact Hlx) ltac:(rewrite tele_entries_length, List.length_rev; exact Hly) H)
        as [_ Hg].
      rewrite !tele_entries_values in Hg; exact Hg.
  Qed.

  (** So they are a PER: symmetric ... *)
  Lemma closed_tele_args_sym : forall C xs ys, all_assumptions C -> ⊨ C -> List.length xs = List.length C -> List.length ys = List.length C ->
      per_tele_args (List.rev C) nil nil xs ys -> per_tele_args (List.rev C) nil nil ys xs.
  Proof.
    intros * Ha HC Hlx Hly H.
    destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
    assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
    apply (closed_tele_args_env_iff _ _ Ha HC HRC _ _ Hly Hlx); symmetry; exact (proj1 (closed_tele_args_env_iff _ _ Ha HC HRC _ _ Hlx Hly) H).
  Qed.

  (** ... and transitive. *)
  Lemma closed_tele_args_trans : forall C xs ys zs, all_assumptions C -> ⊨ C ->
      List.length xs = List.length C -> List.length ys = List.length C -> List.length zs = List.length C ->
      per_tele_args (List.rev C) nil nil xs ys -> per_tele_args (List.rev C) nil nil ys zs -> per_tele_args (List.rev C) nil nil xs zs.
  Proof.
    intros * Ha HC Hlx Hly Hlz H1 H2.
    destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
    assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
    apply (closed_tele_args_env_iff _ _ Ha HC HRC _ _ Hlx Hlz).
    etransitivity; [ exact (proj1 (closed_tele_args_env_iff _ _ Ha HC HRC _ _ Hlx Hly) H1)
                   | exact (proj1 (closed_tele_args_env_iff _ _ Ha HC HRC _ _ Hly Hlz) H2) ].
  Qed.

  (** The values, at the initial environment of [Γ], of an instance over
      [Γ] of a closed telescope of types of universes are related at the
      telescope. *)
  Lemma inst_tele_args : forall Γ U Ms ρ, all_assumptions U -> ⊨ U -> ⊢ Γ -> List.length Ms = List.length U ->
      (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts U Id Ms) j = Some T -> Γ ⊢ N : T) ->
      initial_env_f Γ ρ ->
      (exists l, rel_params_evaluated ⋅ U l) ->
      exists us, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ us /\ per_tele_args (List.rev U) nil nil us us /\ List.length us = List.length U.
  Proof.
    intros * HUa HU HΓ Hl HMs Hρ HUr.
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    pose proof (gsub_closed_inst U Γ Ms HUa HU HΓs Hl
                  (fun j N T HN HT => completeness_fundamental_exp _ _ _ (HMs j N T HN HT)) (typed_inst_scoped _ _ _ HUa Hl HMs)) as Hg.
    pose proof (gsub_valid Hg) as Hτ.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    destruct (per_ctx_then_per_env_initial_env HRΓ (wf_ctx_scoped _ _ _ HΓ) (wf_ctx_scoped _ _ _ HΓ)) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hρ) as ->.
    pose proof (functional_initial_env _ _ Hib _ Hρ) as ->.
    (** no entry of [U] is a proposition, so the instance's values are the
        terms' ([closed_instance_tele_args]) *)
    destruct (closed_instance_tele_args U Γ Ms Ms RΓ HUa HU HΓs HRΓ HUr Hτ Hl Hl _ _ Hab) as (us & us' & Eus & Eus' & H0).
    pose proof (functional_eval_exps _ _ _ _ Eus' Eus) as ->.
    pose proof (eval_exps_length _ _ _ Eus) as Hlus.
    exists us; split; [ exact Eus | split; [ exact H0 | lia ] ].
  Qed.

  (** ** Elements of a Telescope

      A telescope of assumptions over a context has elements over any
      environment of the context: its variables, read as fresh
      neutrals. *)
  Lemma tele_args_exist : forall Δ Γ RΓ ρ, all_assumptions Δ -> ⊨ Δ ++ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
      exists xs, per_tele_args (List.rev Δ) ρ ρ xs xs /\ List.length xs = List.length Δ.
  Proof.
    induction Δ as [| e Δ IH]; intros * HΔa HΔ HRΓ Hρ; [ exists nil; split; constructor |].
    assert (He : exists κ A, e = ce_ass κ A) by (inversion HΔa as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (HΔa' : all_assumptions Δ) by (inversion HΔa; assumption).
    destruct (rel_ctx_wf_ass_inv HΔ) as (S & HSk & HA).
    pose proof (sort_kind_type_sort _ _ HSk) as HS.
    destruct (rel_type_of_sort_at HS) as [i Hi].
    pose proof (rel_ctx_wf_tail HΔ) as HΔ'.
    destruct (IH _ _ _ HΔa' HΔ' HRΓ Hρ) as (xs & Hxs & Hl).
    destruct (rel_ctx_wf_per_ctx_env HΔ') as [RΔ HRΔ].
    pose proof (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRΔ HΔ' Hρ Hl Hxs) as HE.
    destruct (rel_type_inversion_simple_at HRΔ (Hi _ _ _ HA) _ _ HE) as (a & a' & Ea & Ea' & [R HR]).
    pose proof (functional_eval_exp _ _ _ _ Ea Ea') as <-.
    destruct (rel_type_not_level_sort_of_sort HS HA _ HRΔ _ _ HE) as (a0 & Ea0 & Hnl).
    pose proof (functional_eval_exp _ _ _ _ Ea0 Ea) as ->.
    (** a fresh variable, an element as its type is no sort of levels
        ([var_per_elem]) *)
    exists (xs ++ ⇑! a 0 :: nil); split; [| rewrite List.length_app; cbn; lia ].
    cbn [List.rev]; apply per_tele_args_snoc with (i := i) (R := R);
      [ rewrite List.length_rev; exact Hl | exact Hxs | econstructor; eassumption | exact (var_per_elem 0 HR Hnl) ].
  Qed.

  (** ** The End of a Chain of [Π]s

      The value of a chain of [Π]s at an environment of its context has, as
      shape end, the value of its end at the environment extended by fresh
      variables of its domains, which is one of the context extended by the
      domains. *)
  Lemma shape_end_at : forall Bs Γ E (i : nat) RΓ ρ w, Γ ⊢ pis Bs E : Typeω@i -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
      ⟦ pis Bs E ⟧ ρ ↘ w ->
      exists wts e RE, EF doms_ctx Bs ++ Γ ≈ doms_ctx Bs ++ Γ ∈ per_ctx_env ↘ RE /\
        RE (env_extend_typed ρ wts) (env_extend_typed ρ wts) /\
        List.length wts = List.length Bs /\ shape_end e w /\ ⟦ E ⟧ env_extend_typed ρ wts ↘ e.
  Proof.
    induction Bs as [| B Bs IH]; intros * HT HRΓ Hρ Ew; cbn [pis] in HT, Ew.
    - exists nil, w, RΓ; cbn; repeat split; [ exact HRΓ | exact Hρ | apply se_here | exact Ew ].
    - destruct (wf_pi_inversion' HT) as [HB HC]; cbn [abs_kind_sort] in HB.
      destruct (rel_type_of_sort_at (type_sort_universe i)) as [jB HjB].
      inversion Ew; subst.
      pose proof (completeness_fundamental_exp _ _ _ HB) as HBsem.
      pose proof (HjB _ _ _ HBsem) as HBs.
      pose proof (@per_ctx_env_of_typ _ _ ak_relevant _ _ _ HRΓ HBs) as HRB.
      match goal with Ha : ⟦ B ⟧ ρ ↘ ?a0 |- _ => rename Ha into EB end.
      destruct (rel_type_inversion_simple_at HRΓ HBs _ _ Hρ) as (a1 & a2 & Ea1 & Ea2 & [Ra HRa]).
      pose proof (functional_eval_exp _ _ _ _ Ea1 EB) as ->; pose proof (functional_eval_exp _ _ _ _ Ea2 EB) as ->.
      destruct (rel_type_not_level_sort_of_sort (type_sort_universe i) HBsem _ HRΓ _ _ Hρ) as (a0 & Ea0 & Hnl).
      pose proof (functional_eval_exp _ _ _ _ Ea0 EB) as ->.
      pose proof (var_per_elem 0 HRa Hnl) as Hv.
      (** the fresh variable of the domain, an entry at its type *)
      assert (Hρ' : per_env_extend B B RΓ (ρ ↦ ⇑! a 0 ⦂ entry_type_value a) (ρ ↦ ⇑! a 0 ⦂ entry_type_value a)).
      { apply per_env_extend_intro'; [ exact Hρ | eapply per_head_of; [ exact EB | exact EB | exact HRa | exact Hv ]
                                    | exact (proj1 (entry_readable_of_elem HRa Hv)) | exact (proj1 (entry_readable_of_elem HRa Hv)) ]. }
      destruct (rel_exp_of_typ_inversion_simple_at HRB (completeness_fundamental_exp _ _ _ HC) _ _ Hρ') as (b & _ & Eb & _ & _).
      destruct (IH _ _ _ _ _ _ HC HRB Hρ' Eb) as (wts & e & RE & HRE & HE & Hl & Hse & Ee).
      exists ((⇑! a 0, entry_type_value a) :: wts), e, RE.
      assert (Hd : doms_ctx (B :: Bs) ++ Γ = doms_ctx Bs ++ (Γ ▹{ak_relevant} B))
        by (unfold doms_ctx; cbn [List.map List.rev]; rewrite <- List.app_assoc; reflexivity).
      rewrite Hd; cbn [List.length env_extend_typed List.fold_left]; repeat split; try assumption; [ lia |].
      econstructor; eassumption.
  Qed.

  (** A telescope's values, past more entries than they fill, read the
      first entries only. *)
  Lemma env_tele_app_tele : forall ρ T X vs, List.length vs <= List.length T -> env_tele ρ (T ++ X) vs = env_tele ρ T vs.
  Proof.
    intros * Hl; rewrite (env_tele_firstn ρ (T ++ X)), (env_tele_firstn ρ T), List.firstn_app, (proj2 (Nat.sub_0_le _ _) Hl).
    cbn [List.firstn]; rewrite List.app_nil_r; reflexivity.
  Qed.

  (** Elements of a telescope's prefix are elements of a longer
      telescope's. *)
  Lemma tele_elems_app_tele : forall ρ T X vs, tele_elems ρ T vs -> tele_elems ρ (T ++ X) vs.
  Proof.
    induction 1 as [| vs κ A t i R v Hvs IH Hn Ht HR Hv]; [ constructor |].
    assert (Hlt : List.length vs < List.length T) by (apply List.nth_error_Some; congruence).
    econstructor; [ exact IH | rewrite List.nth_error_app1 by lia; exact Hn | rewrite env_tele_app_tele by lia; exact Ht
                  | exact HR | exact Hv ].
  Qed.

  (** Arguments related to themselves at a telescope over [ρ] extended by
      elements [pre] of a whole telescope [T] are, appended, elements of
      both. *)
  Lemma per_tele_args_elems : forall ts ρ T pre xs, List.length pre = List.length T -> tele_elems ρ T pre ->
      per_tele_args ts (env_tele ρ T pre) (env_tele ρ T pre) xs xs -> List.length xs = List.length ts ->
      tele_elems ρ (T ++ ts) (pre ++ xs).
  Proof.
    induction ts as [| e ts IH]; intros * HlT HT H Hl.
    - destruct xs; cbn in Hl; [| discriminate ]; rewrite !List.app_nil_r; exact HT.
    - destruct xs as [| x xs]; cbn in Hl; [ discriminate |].
      inversion H as [| i A ? ? ? ? ? ? ? κ R HA Hx Hg]; subst.
      destruct HA as [a a' Ea Ea' HR].
      pose proof (functional_eval_exp _ _ _ _ Ea Ea') as <-.
      assert (Hnth : List.nth_error (T ++ ce_ass κ A :: nil) (List.length pre) = Some (ce_ass κ A))
        by (rewrite List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity).
      assert (Henv : env_tele ρ T pre ↦ x ⦂ entry_type_closure A (env_tele ρ T pre) = env_tele ρ (T ++ ce_ass κ A :: nil) (pre ++ x :: nil))
        by (rewrite (env_tele_snoc_at _ _ _ _ _ _ Hnth), env_tele_app_tele by lia; reflexivity).
      rewrite Henv in Hg.
      replace (T ++ ce_ass κ A :: ts) with ((T ++ ce_ass κ A :: nil) ++ ts) by (rewrite <- List.app_assoc; reflexivity).
      replace (pre ++ x :: xs) with ((pre ++ x :: nil) ++ xs) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ rewrite !List.length_app; cbn; lia | | exact Hg | lia ].
      econstructor; [ apply tele_elems_app_tele; exact HT | exact Hnth | rewrite env_tele_app_tele by lia; exact Ea | exact HR | exact Hx ].
  Qed.

  (** Arguments related to themselves at a constructor's arguments: their
      non-recursive ones are elements of the non-recursive arguments'
      types, each at the non-recursive ones before it. *)
  Lemma nonrec_elems : forall p D m Mi c gs, valid_group p D -> containers_valid D -> ind_member D m = Some Mi ->
      ind_con Mi c = Some gs ->
      forall gs1 gs2 us ms vs, gs = gs1 ++ gs2 -> List.length us = ind_nu D -> List.length ms = im_nn Mi ->
      List.length vs = List.length gs1 ->
      per_tele_args (List.rev (cargs_ctx p D Mi gs1 ++ im_params D Mi)) nil nil (us ++ ms ++ vs) (us ++ ms ++ vs) ->
      tele_elems (components_env D us (List.rev (im_nparams Mi)) ms) (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 vs).
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
      destruct (per_tele_args_app _ _ _ _ _ _ _ _ Hl0 Hg Hl0) as [Hpre Hlast].
      pose proof (IH (g :: gs2) us ms vs' ltac:(rewrite Heq, <- List.app_assoc; reflexivity) Hlu Hlm ltac:(lia) Hpre) as IHg.
      rewrite cargs_nonrec_tele_app, nonrec_arg_vals_app by lia.
      destruct g as [r A | t]; cbn [cargs_nonrec_tele nonrec_arg_vals]; [| rewrite !List.app_nil_r; exact IHg ].
      destruct (valid_group_arg_types p D Hvg Hcv m Mi c gs gs1 r A gs2 us ms vs' HM Hcon
                  ltac:(rewrite Heq, <- List.app_assoc; reflexivity) Hlu Hlm ltac:(lia) Hpre) as (i & R & a & a' & Ea & Ea' & HR).
      cbn [cargs_ctx_aux List.app List.rev] in Hlast.
      inversion Hlast as [| i0 A0 ? ? ? ? ? ? ? κ0 R0 HA0 Hv _]; subst.
      destruct HA0 as [a0 a0' E0 E0' H0].
      pose proof (functional_eval_exp _ _ _ _ E0 Ea) as ->; pose proof (functional_eval_exp _ _ _ _ E0' Ea) as ->.
      assert (Hv' : R v v) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ H0 HR); exact Hv).
      assert (Hln : List.length (nonrec_arg_vals gs1 vs') = List.length (cargs_nonrec_tele gs1))
        by (rewrite length_nonrec_arg_vals, length_cargs_nonrec_tele by lia; reflexivity).
      econstructor; [ apply tele_elems_app_tele; exact IHg | rewrite List.nth_error_app2, Hln, Nat.sub_diag by lia; reflexivity | |
                    exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR) HR) | exact Hv' ].
      rewrite env_tele_app_tele by lia; unfold components_env in *.
      rewrite <- env_tele_app by (rewrite List.length_rev; unfold im_nn in Hlm; exact Hlm); exact Ea'.
  Qed.

  (** The values of an instance over [Γu] of a closed telescope, weakened
      past a telescope [Ψ], at an environment of [Ψ ++ Γu] over the
      initial one of [Γu], are related to the values of the instance at
      the initial environment. *)
  Lemma wk_inst_tele_args : forall Ψ Γu U Ms ρ0 zts RΨ, all_assumptions U -> ⊨ U -> ⊢ Γu -> List.length Ms = List.length U ->
      (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts U Id Ms) j = Some T -> Γu ⊢ N : T) ->
      initial_env_f Γu ρ0 -> EF Ψ ++ Γu ≈ Ψ ++ Γu ∈ per_ctx_env ↘ RΨ -> RΨ (env_extend_typed ρ0 zts) (env_extend_typed ρ0 zts) ->
      List.length zts = List.length Ψ ->
      (exists l, rel_params_evaluated ⋅ U l) ->
      exists us us', ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us /\
        ⟦ List.map (fun M => M[wk_shiftn (List.length Ψ)]ʷ) Ms ⟧* gc_deps ⍮ gc_stack ⍮ env_extend_typed ρ0 zts ↘ us' /\
        per_tele_args (List.rev U) nil nil us' us.
  Proof.
    intros * HUa HU HΓ Hl HMs Hρ0 HRΨ Hρ Hlx HUr.
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    pose proof (gsub_closed_inst U Γu Ms HUa HU HΓs Hl
                  (fun j N T HN HT => completeness_fundamental_exp _ _ _ (HMs j N T HN HT)) (typed_inst_scoped _ _ _ HUa Hl HMs)) as Hg.
    destruct (gsub_props Hg) as [Hτ Hlk].
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    destruct (per_ctx_then_per_env_initial_env HRΓ (wf_ctx_scoped _ _ _ HΓ) (wf_ctx_scoped _ _ _ HΓ)) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hρ0) as ->; pose proof (functional_initial_env _ _ Hib _ Hρ0) as ->.
    (** the weakening past [Ψ], at the extension of [ρ0] *)
    pose proof (rel_wk_shiftn _ _ _ _ HRΨ HRΓ) as Hwk.
    assert (Hwb : forall x, x < List.length Γu -> wk_shiftn (List.length Ψ) x < List.length (Ψ ++ Γu))
      by (intros x Hx; rewrite List.length_app; cbn; lia).
    pose proof (rel_sub_of_wk_rel HRΨ HRΓ Hwk Hwb) as Hσ.
    assert (Hsh : ⟪wk_shiftn (List.length Ψ)⟫ (env_extend_typed ρ0 zts) = ρ0) by (rewrite <- Hlx; apply eval_wk_shiftn_extend_typed).
    assert (Hev : ⟦ ι (wk_shiftn (List.length Ψ)) : Γu ⟧s env_extend_typed ρ0 zts ↘ ctx_retag Γu ρ0)
      by (pose proof (eval_sub_of_wk_rel (φ := wk_shiftn (List.length Ψ)) (ρ := env_extend_typed ρ0 zts) (ρ' := ρ0) HRΓ
                        ltac:(rewrite Hsh; exact Hab)) as Hev0; rewrite Hsh in Hev0; exact Hev0).
    (** the instance's values at [ρ0] and at its retagging, related *)
    pose proof (per_ctx_env_retag_right HRΓ _ _ Hab) as Hρr.
    destruct (closed_instance_tele_args U Γu Ms Ms RΓ HUa HU HΓs HRΓ HUr Hτ Hl Hl _ _ Hρr) as (us & u & Eus & Eu & Hus).
    destruct (closed_instance_moved_tele_args U Γu Ms HUa HU HΓs HUr Hl Hτ Hlk (Ψ ++ Γu) RΨ _ _ _ u HRΨ Hσ Hρ Hev Eu)
      as (w & Ew & Hwu).
    rewrite (List.map_ext (fun V => V[ι (wk_shiftn (List.length Ψ))]) (fun M => M[wk_shiftn (List.length Ψ)]ʷ))
      in Ew by (intros; apply exp_sub_of_wk).
    exists us, w; split; [ exact Eus | split; [ exact Ew |] ].
    pose proof (eval_exps_length _ _ _ Eus) as Hlus; pose proof (eval_exps_length _ _ _ Eu) as Hlu; pose proof (eval_exps_length _ _ _ Ew) as Hlw.
    rewrite List.length_map in Hlw.
    apply (closed_tele_args_trans U w u us HUa HU ltac:(lia) ltac:(lia) ltac:(lia) Hwu).
    exact (closed_tele_args_sym U us u HUa HU ltac:(lia) ltac:(lia) Hus).
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
      per_tele_args (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
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

  (** The values of a typed extension read back when its new entries do. *)
  Lemma extend_typed_readable : forall ρ vts,
      (forall x, x < List.length vts -> entry_readable (env_entry (env_extend_typed ρ vts) x)) ->
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts.
  Proof.
    intros * H; apply List.Forall_forall; intros [v t] Hin.
    destruct (List.In_nth_error _ _ Hin) as [k Hk].
    assert (Hkl : k < List.length vts) by (apply List.nth_error_Some; congruence).
    destruct (env_entry_extend_typed_lt ρ vts (List.length vts - 1 - k) ltac:(lia)) as (v' & t' & Hn & He).
    replace (List.length vts - 1 - (List.length vts - 1 - k)) with k in Hn by lia.
    rewrite Hk in Hn; injection Hn as <- <-.
    pose proof (H (List.length vts - 1 - k) ltac:(lia)) as Hr; rewrite He in Hr; exact Hr.
  Qed.

  (** ** The Shape End of an Argument's Normal Form, Semantically

      A type [X] over a closed telescope [Δ] of a closed telescope [U],
      at an instance [Cs] of [U] over [Γu]: at elements [xs] of [Δ] at the
      values [us] of [Cs], the value of the normal form of [X] at [Cs] is
      related to [X]'s at [us] and [xs], and the end of its [Π]s at fresh
      variables [ws] is the value of the normal form's end. *)
  Lemma arg_shape_end : forall Γu U Δ X SX Cs ρ0 us (i : nat) W Bs E,
      ⊢ Γu -> all_assumptions U -> ⊨ U -> all_assumptions Δ -> ⊨ Δ ++ U -> type_sort SX -> Δ ++ U ⊨ X : SX ->
      List.length Cs = List.length U ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts U Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      tele_sub Δ (sb_of_list Id Cs) ++ Γu ⊢ X[sb_qn (List.length Δ) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub Δ (sb_of_list Id Cs) ++ Γu) X[sb_qn (List.length Δ) (sb_of_list Id Cs)] W ->
      nf_to_exp W = pis Bs E ->
      (exists l, rel_params_evaluated ⋅ U l) ->
      exists xs a w vts e RE, per_tele_args (List.rev (Δ ++ U)) nil nil (us ++ xs) (us ++ xs) /\ List.length us = List.length U /\
        List.length xs = List.length Δ /\
        ⟦ X ⟧ env_tele nil (List.rev (Δ ++ U)) (us ++ xs) ↘ a /\ per_univ i w a /\ shape_end e w /\
        EF (doms_ctx Bs ++ tele_sub Δ (sb_of_list Id Cs)) ++ Γu ≈ (doms_ctx Bs ++ tele_sub Δ (sb_of_list Id Cs)) ++ Γu
          ∈ per_ctx_env ↘ RE /\
        RE (env_extend_typed ρ0 vts) (env_extend_typed ρ0 vts) /\ List.length vts = List.length Δ + List.length Bs /\
        ⟦ E ⟧ env_extend_typed ρ0 vts ↘ e.
  Proof.
    intros * HΓu HUa HUs HΔa' HΔU HSX HXs HCl HCt Hρ0 Eus HT HW HWe HUr.
    destruct (rel_type_of_sort_at HSX) as [jX HjX].
    set (σ := sb_of_list Id Cs) in *.
    destruct (inst_tele_args Γu U Cs ρ0 HUa HUs HΓu HCl HCt Hρ0 HUr) as (us' & Eus' & Hgu & Hlu).
    pose proof (functional_eval_exps' _ _ _ _ Eus' Eus) as ->.
    assert (HΔa : all_assumptions (Δ ++ U)) by (apply List.Forall_app; split; assumption).
    (** the instance along [Cs] over [Γu], at the initial environment *)
    pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
    pose proof (gsub_closed_inst U Γu Cs HUa HUs HΓs HCl
                  (fun j N T HN HT0 => completeness_fundamental_exp _ _ _ (HCt j N T HN HT0)) (typed_inst_scoped _ _ _ HUa HCl HCt)) as Hgs.
    destruct (gsub_props Hgs) as [Hτ _].
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
    destruct (per_ctx_then_per_env_initial_env HRΓu (wf_ctx_scoped _ _ _ HΓu) (wf_ctx_scoped _ _ _ HΓu)) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hρ0) as ->; pose proof (functional_initial_env _ _ Hib _ Hρ0) as ->.
    destruct (rel_ctx_wf_per_ctx_env HUs) as [RU HRU].
    destruct (closed_instance_values_of_sub U Γu Cs RΓu RU HUa HUs HΓs HRΓu HRU HUr Hτ HCl _ _ Hab) as [us1 _ Eus1 _ _ Eσ _].
    pose proof (functional_eval_exps' _ _ _ _ Eus1 Eus) as ->.
    set (tg := tagged_entries Γu (List.rev U) (ctx_retag Γu ρ0) us) in *.
    set (ρσ := env_extend_tagged Γu (List.rev U) (ctx_retag Γu ρ0) us) in *.
    assert (Eρσ : ρσ = env_extend_typed (ctx_retag Γu ρ0) tg) by apply env_extend_tagged_typed.
    assert (Hltg : List.length tg = List.length U) by (unfold tg; rewrite tagged_entries_length by (rewrite List.length_rev; lia); lia).
    destruct (closed_app_sem U Γu HUa HUs HΓs) as [HUΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
    pose proof (rel_sub_under_ctx_at' Hτ HRΓu HRUΓ _ _ _ _ Hab Eσ Eσ) as Hσσ.
    (** the instance's entries read back *)
    assert (Rtg : List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) tg).
    { apply extend_typed_readable with (ρ := ctx_retag Γu ρ0); intros x Hx.
      rewrite <- Eρσ; apply (proj1 (per_ctx_env_entries_readable _ _ _ HRUΓ _ _ Hσσ x ltac:(rewrite List.length_app; lia))). }
    (** fresh elements of the telescope over the instance's value *)
    assert (HΔUΓ : ⊨ Δ ++ U ++ Γu) by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HΔa HΔU HΓs))).
    destruct (tele_args_exist Δ (U ++ Γu) RUΓ ρσ HΔa' HΔUΓ HRUΓ Hσσ) as (xs & Hxsσ & Hlx).
    set (vts := tele_entries ρσ (List.rev Δ) xs).
    pose proof (per_tele_args_entries_readable _ _ _ _ _ Hxsσ) as [Rv _]; fold vts in Rv.
    assert (Hlv : List.length vts = List.length Δ) by (unfold vts; rewrite tele_entries_length; exact Hlx).
    assert (Hxsv : per_tele_args (List.rev Δ) ρσ ρσ (List.map fst vts) (List.map fst vts))
      by (unfold vts; rewrite tele_entries_values; exact Hxsσ).
    destruct (outer_base Δ (U ++ Γu) Γu RΓu σ ρ0 ρσ HΔa' HΔUΓ HRΓu Hτ Hab Eσ vts Hxsv Hlv Rv)
      as (RS & RΔ & Y & HRS & HSS & HRΔ & _ & _ & _).
    assert (HXΓ : Δ ++ U ++ Γu ⊨ᵗ X ≈ X at jX)
      by (apply HjX; rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ HΔa HΔU HΓs HXs)).
    destruct (outer_type_link Δ (U ++ Γu) Γu RΓu σ ρ0 ρσ X jX HΔa' HΔUΓ HXΓ HRΓu Hτ Hab Eσ vts Hxsv Hlv Rv)
      as (t & b & Et & Eb & Htb).
    (** the normal form's value, related to the type's *)
    pose proof (soundness_ty' HT HW) as HTW.
    destruct (rel_exp_of_typ_inversion_simple_at HRS (completeness_fundamental_exp_eq _ _ _ _ HTW) _ _ HSS)
      as (t' & w & Et' & Ew & Htw).
    pose proof (functional_eval_exp _ _ _ _ Et' Et) as ->.
    (** the elements over the closed telescope alone *)
    pose proof (per_tele_args_entries_readable _ _ _ _ _ Hgu) as [Rvu _].
    assert (HUσσ : RU ρσ ρσ) by exact (Hres _ _ HRU HRUΓ _ _ Hσσ).
    assert (HUσE : RU ρσ (env_tele nil (List.rev U) us)).
    { rewrite Eρσ in HUσσ |- *; unfold env_tele.
      apply (closed_env_base U RU tg tg tg (tele_entries nil (List.rev U) us) (ctx_retag Γu ρ0) (ctx_retag Γu ρ0) (ctx_retag Γu ρ0) nil
               HUa HUs HRU Hltg Hltg); [ reflexivity | | exact Rtg | exact Rvu | exact HUσσ ].
      rewrite tele_entries_values; unfold tg; rewrite tagged_entries_fst by (rewrite List.length_rev; lia); reflexivity. }
    pose proof (per_tele_args_base (List.rev Δ) U RU HRU ltac:(rewrite List.rev_involutive; exact HΔU) (List.Forall_rev HΔa')
                  _ _ _ _ xs xs HUσσ HUσE HUσE Hxsσ) as Hxs.
    assert (Hall : per_tele_args (List.rev (Δ ++ U)) nil nil (us ++ xs) (us ++ xs))
      by (rewrite List.rev_app_distr; apply per_tele_args_app_intro; [ rewrite List.length_rev; exact Hlu | exact Hgu | exact Hxs ]).
    destruct (rel_ctx_wf_per_ctx_env HΔU) as [RC HRC].
    assert (Hlen0 : List.length (us ++ xs) = List.length (Δ ++ U)) by (rewrite !List.length_app; lia).
    pose proof (proj1 (closed_tele_args_env_iff _ _ HΔa HΔU HRC _ _ Hlen0 Hlen0) Hall) as HCC.
    pose proof (per_tele_args_entries_readable _ _ _ _ _ Hall) as [RvK _].
    set (vtsK := tele_entries nil (List.rev (Δ ++ U)) (us ++ xs)) in *.
    assert (HlK : List.length vtsK = List.length (Δ ++ U)) by (unfold vtsK; rewrite tele_entries_length; exact Hlen0).
    assert (HCC' : RC (env_extend_typed (ctx_retag Γu ρ0) (tg ++ vts)) (env_extend_typed nil vtsK)).
    { apply (closed_env_base (Δ ++ U) RC vtsK vtsK (tg ++ vts) vtsK nil nil (ctx_retag Γu ρ0) nil HΔa HΔU HRC HlK HlK);
        [ | reflexivity | apply List.Forall_app; split; assumption | exact RvK | exact HCC ].
      unfold vtsK; rewrite List.map_app, !tele_entries_values; unfold vts; rewrite tele_entries_values.
      unfold tg; rewrite tagged_entries_fst by (rewrite List.length_rev; lia); reflexivity. }
    destruct (rel_type_inversion_simple_at HRC (HjX _ _ _ HXs) _ _ HCC') as (b' & a2 & Eb' & Ea2 & Hba).
    rewrite env_extend_typed_app, <- Eρσ in Eb'.
    pose proof (functional_eval_exp _ _ _ _ Eb' Eb) as ->.
    assert (Hwa : per_univ i w a2).
    { eapply per_univ_trans'; [ apply per_univ_sym'; exact Htw |].
      eapply per_univ_trans'; [ exact Htb | exact Hba ]. }
    (** the end of the normal form's [Π]s *)
    assert (HWt : tele_sub Δ σ ++ Γu ⊢ pis Bs E : Typeω@i) by (rewrite <- HWe; gen_presups; assumption).
    rewrite HWe in Ew.
    destruct (shape_end_at Bs _ _ i RS (env_extend_typed ρ0 vts) w HWt HRS HSS Ew) as (wts & e & RE & HRE & HEE & Hlw & Hse & Ee).
    rewrite <- env_extend_typed_app in HEE, Ee.
    exists xs, a2, w, (vts ++ wts), e, RE; repeat split; try assumption.
    - rewrite <- List.app_assoc; exact HRE.
    - rewrite List.length_app; lia.
  Qed.

  (** A member of a filed group at uniform arguments [Csz] over [Γu]
      whose weakenings are the first arguments of the end [apps (a_ind qz
      kz) Rs] of a normal form, evaluated at an extension [zs] of the
      initial environment: the member at the values of [Csz] is related to
      the end's value. *)
  Lemma ind_end_rel : forall Γu Ψ ρ0 zs RE (i : nat) qz kz Rs Dz Csz e,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> initial_env_f Γu ρ0 ->
      EF Ψ ++ Γu ≈ Ψ ++ Γu ∈ per_ctx_env ↘ RE -> RE (env_extend_typed ρ0 zs) (env_extend_typed ρ0 zs) -> List.length zs = List.length Ψ ->
      Ψ ++ Γu ⊢ apps (a_ind qz kz) (List.map nf_to_exp Rs) : Typeω@i ->
      ⟦ apps (a_ind qz kz) (List.map nf_to_exp Rs) ⟧ env_extend_typed ρ0 zs ↘ e ->
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
    apply eval_apps_ind_exp in Ee0 as (f & msE & Ef & EmsE & Eap).
    inversion Ef; match goal with H : _ = f |- _ => subst f | H : f = _ |- _ => subst f end.
    apply eval_apps_ind_inv in Eap; cbn in Eap.
    subst e; clear Ef.
    (** the end's uniform arguments: the values of [Csz] weakened past the
        extension, related to those of [Csz] at the initial environment *)
    destruct (wk_inst_tele_args Ψ Γu (ind_uparams Dz) Csz ρ0 zs RE (decl_closed_ass _ Hcz) (valid_ind_decl_uparams _ (valid_group_valid _ _ Hvgz)) HΓu
                ltac:(rewrite HCzl; reflexivity) HCzt Hρ0 HRE HEE Hlz
                (valid_ind_decl_uparams_evaluated _ (valid_group_valid _ _ Hvgz)))
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
      EF Ψ ++ Γu ≈ Ψ ++ Γu ∈ per_ctx_env ↘ RE -> RE (env_extend_typed ρ0 zs) (env_extend_typed ρ0 zs) -> List.length zs = List.length Ψ ->
      ⟦ apps (a_record qz) (List.map nf_to_exp Rs) ⟧ env_extend_typed ρ0 zs ↘ e ->
      record_lookup gc_deps gc_stack qz = Some Rz -> List.length Isz = List.length (record_params Rz) ->
      (forall j C T, List.nth_error Isz j = Some C -> List.nth_error (tele_insts (record_params Rz) Id Isz) j = Some T ->
         Γu ⊢ C : T) ->
      List.map nf_to_exp Rs = List.map (fun C => C[wk_pat (List.repeat true (List.length Ψ))]ʷ) Isz ->
      exists usz, ⟦ Isz ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ usz /\ List.length usz = List.length (record_params Rz) /\
        exists j : universe_index, exists R, DF d_record qz usz ≈ e ∈ per_univ_elem j ↘ R.
  Proof.
    intros * Hg HΓu Hρ0 HRE HEE Hlz Ee Hlr HIzl HIzt HCz.
    pose proof Ee as Ee0.
    apply eval_apps_record_exp in Ee0 as (f & msE & Ef & EmsE & Eap).
    inversion Ef; match goal with H : _ = f |- _ => subst f | H : f = _ |- _ => subst f end.
    apply eval_apps_record_inv in Eap; cbn in Eap.
    subst e; clear Ef.
    pose proof (valid_rview_record_gc _ _ Hg Hlr) as HvR.
    destruct (wk_inst_tele_args Ψ Γu (record_params Rz) Isz ρ0 zs RE (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HvR))
                (params_valid _ (valid_rview_record_valid _ _ HvR)) HΓu HIzl HIzt Hρ0 HRE HEE Hlz
                (params_evaluated_valid _ (valid_rview_record_valid _ _ HvR)))
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
  Lemma nonrec_step : forall Γu p D k Cs ρ0 us m Mi c gs gs1 r A gs2 (i : nat) W Bs E,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_arg r A :: gs2 ->
      tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu
        ⊢ A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] : Typeω@i ->
      nbe_ty_f (tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs) ++ Γu)
        A[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id Cs)] W ->
      nf_to_exp W = pis Bs E ->
      exists zs e RE,
        EF (doms_ctx Bs ++ tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) ++ Γu
          ≈ (doms_ctx Bs ++ tele_sub (cargs_ctx p D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) ++ Γu ∈ per_ctx_env ↘ RE /\
        RE (env_extend_typed ρ0 zs) (env_extend_typed ρ0 zs) /\ List.length zs = List.length Bs + List.length gs1 + im_nn Mi /\
        ⟦ E ⟧ env_extend_typed ρ0 zs ↘ e /\
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
    assert (HXs : exists SX, type_sort SX /\ Δ ++ ind_uparams D ⊨ A[wk_pat (cargs_pat gs1)]ʷ : SX).
    { destruct (valid_group_cargs_sem_all p D Hvg Hcv m Mi c gs HM Hcon (gs1 ++ ca_arg r A :: nil) gs2
                  ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as [HW1 _].
      rewrite cargs_ctx_snoc in HW1; cbn [cargs_ctx_aux List.app] in HW1.
      unfold Δ, im_params in *; rewrite <- List.app_assoc.
      destruct (rel_ctx_wf_ass_inv HW1) as (S0 & HS0 & HA0); exists S0; split; [ exact (sort_kind_type_sort _ _ HS0) | exact HA0 ]. }
    destruct HXs as (SX & HSX & HXs).
    assert (HΔU : ⊨ Δ ++ ind_uparams D).
    { destruct (valid_group_cargs_sem_all p D Hvg Hcv m Mi c gs HM Hcon gs1 (ca_arg r A :: gs2) Heq) as [HW1 _].
      unfold Δ, im_params in *; rewrite <- List.app_assoc; exact HW1. }
    assert (HΔa : all_assumptions (Δ ++ ind_uparams D)).
    { unfold Δ; rewrite <- List.app_assoc; change (im_nparams Mi ++ ind_uparams D) with (im_params D Mi).
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_params_ass _ _ _ Hc HM) ]. }
    assert (HΔa' : all_assumptions Δ) by (apply List.Forall_app in HΔa as [H _]; exact H).
    destruct (arg_shape_end Γu (ind_uparams D) Δ (A[wk_pat (cargs_pat gs1)]ʷ) SX Cs ρ0 us i W Bs E HΓu (decl_closed_ass _ Hc) HUs
                HΔa' HΔU HSX HXs ltac:(rewrite HCl; reflexivity) HCt Hρ0 Eus HT HW HWe
                (valid_ind_decl_uparams_evaluated _ (valid_group_valid _ _ Hvg)))
      as (xs & a & w & zs & e & RE & Hall & Hlu & Hlx & Ea & Hwa & Hse & HRE & HEE & Hlw & Ee).
    exists zs, e, RE; split; [ exact HRE | split; [ exact HEE | split; [ rewrite Hlw, HlΔ; lia | split; [ exact Ee |] ] ] ].
    (** the type at the elements, as the model reads the argument *)
    set (ms := List.firstn (im_nn Mi) xs); set (vs := List.skipn (im_nn Mi) xs).
    assert (Hxs_eq : xs = ms ++ vs) by (symmetry; apply List.firstn_skipn).
    assert (Hlms : List.length ms = im_nn Mi)
      by (unfold ms; rewrite List.length_firstn; unfold Δ, im_nn in *; rewrite List.length_app in Hlx; lia).
    assert (Hlvs : List.length vs = List.length gs1)
      by (unfold vs; rewrite List.length_skipn; unfold Δ, im_nn in *; rewrite List.length_app, length_cargs_ctx in Hlx; lia).
    assert (Hall' : per_tele_args (List.rev (cargs_ctx p D Mi gs1 ++ im_params D Mi)) nil nil (us ++ ms ++ vs) (us ++ ms ++ vs))
      by (unfold im_params; rewrite List.app_assoc, <- Hxs_eq; exact Hall).
    destruct (valid_group_arg_types p D Hvg Hcv m Mi c gs gs1 r A gs2 us ms vs HM Hcon Heq ltac:(rewrite Hlu; reflexivity) Hlms Hlvs Hall')
      as (iA & RA & a0 & a' & Ea0 & Ea' & HRA).
    assert (EΔ : Δ ++ ind_uparams D = cargs_ctx p D Mi gs1 ++ im_params D Mi) by (unfold Δ, im_params; rewrite List.app_assoc; reflexivity).
    rewrite EΔ, Hxs_eq in Ea; pose proof (functional_eval_exp _ _ _ _ Ea0 Ea) as ->.
    assert (Hwa' : per_univ i w a') by (eapply per_univ_trans'; [ exact Hwa | exists RA; exact HRA ]).
    destruct Hwa' as [R0 HR0].
    intros b j R Hb.
    rewrite <- (List.app_nil_r us).
    assert (Hlnr : List.length (nonrec_arg_vals gs1 vs) = List.length (cargs_nonrec gs1)) by (apply length_nonrec_arg_vals; exact Hlvs).
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (nonrec_arg_vals gs1 vs)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Hlnr, Nat.sub_diag by lia; reflexivity).
    (** the non-uniform parameters' elements *)
    assert (Hlr : List.length ms = List.length (List.rev (im_nparams Mi))) by (rewrite List.length_rev; exact Hlms).
    assert (Hlu' : List.length us = List.length (List.rev (ind_uparams D))) by (rewrite List.length_rev; exact Hlu).
    rewrite List.rev_app_distr in Hall.
    destruct (per_tele_args_app _ _ _ _ _ _ _ _ Hlu' Hall Hlu') as [_ Hxs].
    unfold Δ in Hxs; rewrite List.rev_app_distr, Hxs_eq in Hxs.
    destruct (per_tele_args_app _ _ _ _ _ _ _ _ Hlr Hxs Hlr) as [Hms0 _].
    pose proof (per_tele_args_elems (List.rev (im_nparams Mi)) (decl_env D us) nil nil ms eq_refl (tele_elems_nil _ _) Hms0 Hlr)
      as Hms; cbn [List.app] in Hms.
    (** the non-recursive arguments' elements, over the whole constructor *)
    pose proof (nonrec_elems p D m Mi c gs Hvg Hcv HM Hcon gs1 (ca_arg r A :: gs2) us ms vs Heq ltac:(rewrite Hlu; reflexivity)
                  Hlms Hlvs Hall') as Hvs.
    assert (Ecg : cargs_nonrec_tele gs = cargs_nonrec_tele gs1 ++ cargs_nonrec_tele (ca_arg r A :: gs2))
      by (rewrite Heq; apply cargs_nonrec_tele_app).
    assert (Hlnt : List.length (nonrec_arg_vals gs1 vs) <= List.length (cargs_nonrec_tele gs1))
      by (rewrite length_cargs_nonrec_tele; lia).
    pose proof (tele_elems_app_tele _ _ (cargs_nonrec_tele (ca_arg r A :: gs2)) _ Hvs) as Hvs'; rewrite <- Ecg in Hvs'.
    assert (Ea'' : ⟦ A ⟧ components_env D us (List.rev (im_nparams Mi) ++ cargs_nonrec_tele gs) (ms ++ nonrec_arg_vals gs1 vs) ↘ a').
    { rewrite Ecg, List.app_assoc; unfold components_env in *.
      rewrite env_tele_app_tele by (rewrite !List.length_app; lia); exact Ea'. }
    exact (grp_step_intro b p k D us nil m Mi c gs _ A ms _ a' i R0 w e j R Hl ltac:(rewrite Hlu; reflexivity) HM Hcon HA Hms
             ltac:(rewrite List.length_rev in Hlr; exact Hlr) Hvs' eq_refl Ea'' HR0 Hse Hb).
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
        RE (env_extend_typed ρ0 zs) (env_extend_typed ρ0 zs) /\ List.length zs = List.length Bs + j /\
        ⟦ E ⟧ env_extend_typed ρ0 zs ↘ e /\
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
    destruct (rel_ctx_wf_ass_inv HAF) as (SX & HSX & HXs).
    pose proof (rel_ctx_wf_tail HAF) as HΔU.
    assert (HΔa : all_assumptions (record_fctx Rx j)) by apply record_fctx_ass.
    destruct (arg_shape_end Γu (record_params Rx) (record_fctx Rx j) A SX Isx ρ0 usx i W Bs E HΓu HUa HUs HΔa HΔU
                (sort_kind_type_sort _ _ HSX) HXs HIl HIt
                Hρ0 Eus ltac:(rewrite HlΔ; exact HT) ltac:(rewrite HlΔ; exact HW) HWe
                (params_evaluated_valid _ (valid_rview_record_valid _ _ HvR)))
      as (xs & a & w & zs & e & RE & Hall & Hlu & Hlx & Ea & Hwa & Hse & HRE & HEE & Hlw & Ee).
    exists zs, e, RE; split; [ exact HRE | split; [ exact HEE | split; [ rewrite Hlw, HlΔ; lia | split; [ exact Ee |] ] ] ].
    destruct Hwa as [R0 HR0].
    intros b j' R Hb.
    (** the fields before are a prefix of the record's fields' telescope *)
    assert (Etele : record_fields_tele Rx = List.rev (record_fctx Rx j)
                      ++ List.rev (fields_tele (List.skipn j (record_fields Rx)) (List.skipn j (record_field_kinds Rx)))).
    { unfold record_fields_tele, record_fctx.
      rewrite <- (List.firstn_skipn j (record_fields Rx)) at 1.
      rewrite fields_tele_app, List.length_firstn, Nat.min_l by lia; apply List.rev_app_distr. }
    (** the elements of the fields before, as the record clause reads them *)
    assert (Hlu' : List.length usx = List.length (List.rev (record_params Rx))) by (rewrite List.length_rev; exact Hlu).
    rewrite List.rev_app_distr in Hall.
    destruct (per_tele_args_app _ _ _ _ _ _ _ _ Hlu' Hall Hlu') as [_ Hxs].
    pose proof (per_tele_args_elems (List.rev (record_fctx Rx j)) (env_tele nil (List.rev (record_params Rx)) usx) nil nil xs eq_refl
                  (tele_elems_nil _ _) Hxs ltac:(rewrite List.length_rev; exact Hlx)) as Hvs; cbn [List.app] in Hvs.
    apply (tele_elems_app_tele _ _ (List.rev (fields_tele (List.skipn j (record_fields Rx)) (List.skipn j (record_field_kinds Rx))))) in Hvs.
    rewrite <- Etele in Hvs.
    assert (Ea' : ⟦ A ⟧ record_fields_env Rx usx xs ↘ a).
    { unfold record_fields_env; rewrite Etele, env_tele_app_tele by (rewrite List.length_rev; lia).
      rewrite <- env_tele_closed_app by exact Hlu; exact Ea. }
    exact (grp_step_record b qx Rx usx j f A xs a i R0 w e j' R Hl HfA Hvs ltac:(lia) Ea' HR0 Hse Hb).
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
  Theorem nonrec_meet_below : forall Γu p D k Cs ρ0 us m Mi c gs gs1 r A gs2 (i : nat) W Bs qz kz Rs Dz Csz,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_arg r A :: gs2 ->
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
    destruct (nonrec_step Γu p D k Cs ρ0 us m Mi c gs gs1 r A gs2 i W Bs _ Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe)
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
  Theorem nonrec_meet_below_record : forall Γu p D k Cs ρ0 us m Mi c gs gs1 r A gs2 (i : nat) W Bs qz Rs Rz Isz,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu ->
      ind_lookup gc_deps gc_stack p = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      initial_env_f Γu ρ0 -> ⟦ Cs ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ us ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ ca_arg r A :: gs2 ->
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
    destruct (nonrec_step Γu p D k Cs ρ0 us m Mi c gs gs1 r A gs2 i W Bs _ Hg HΓu Hl HCl HCt Hρ0 Eus HM Hcon Heq HT HW HWe)
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
  ; below_uparams_eval : ⟦ List.map nf_to_exp (view_key_args x) ⟧* Θ ⍮ Ξ ⍮ below_env ↘ below_uparams
    (** The values of the arguments the lower view's key fixes *)
  ; below_meet_uparams : list domain
    (** They are those of its arguments at the environment *)
  ; below_meet_uparams_eval : ⟦ List.map nf_to_exp (view_key_args z) ⟧* Θ ⍮ Ξ ⍮ below_env ↘ below_meet_uparams
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
    forall x ρ usx nsx, initial_env Θ Ξ Γu ρ -> ⟦ List.map nf_to_exp (view_key_args x) ⟧* Θ ⍮ Ξ ⍮ ρ ↘ usx ->
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
Theorem record_view_inv_acc : forall Θ Ξ Γu qx Wsx, ⊢ᵍ Θ ⍮ Ξ -> record_view_typed Θ Ξ Γu qx (List.map nf_to_exp Wsx) ->
    Acc (view_lt Θ Ξ Γu) (vk_record qx Wsx).
Proof.
  intros * Hg [Rx Hl Hlen Hty HΓu].
  pose proof (@valid_rview_record_gc (gc_mk Θ Ξ) _ _ Hg Hl) as HvR.
  pose proof (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ HΓu) as HΓs.
  destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
  destruct (per_ctx_then_per_env_initial_env HRΓ (wf_ctx_scoped _ _ _ HΓu) (wf_ctx_scoped _ _ _ HΓu)) as (ρ & _ & Hρ & _ & _).
  destruct (@inst_tele_args (gc_mk Θ Ξ) Γu (record_params Rx) (List.map nf_to_exp Wsx) ρ (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HvR))
              (params_valid _ (valid_rview_record_valid _ _ HvR)) HΓu Hlen Hty Hρ
              (params_evaluated_valid _ (valid_rview_record_valid _ _ HvR))) as (us & Eus & Hgu & Hlu).
  destruct (@vrr_type_rel (gc_mk Θ Ξ) qx Rx us us HvR Hgu Hlu) as [i HR].
  exact (view_below_acc Θ Ξ Γu _ (@per_univ_nest_acc_rel (gc_mk Θ Ξ) _ _ _ _ _ _ _ HR HR) (vk_record qx Wsx) ρ us nil Hρ Eus
           (ex_intro _ Rx (conj Hl Hlu)) eq_refl).
Qed.

(** A typed view is accessible for [view_lt]: its type is one of the
    model. *)
Theorem view_inv_acc : forall Θ Ξ Γu qx kx Wsx, ⊢ᵍ Θ ⍮ Ξ -> view_typed Θ Ξ Γu qx kx (List.map nf_to_exp Wsx) ->
    Acc (view_lt Θ Ξ Γu) (vk_ind qx kx Wsx).
Proof.
  intros * Hg [Dx Hl Hk Hlen Hty HΓu].
  destruct (List.nth_error (ind_members Dx) kx) as [Mk |] eqn:HM;
    [| apply List.nth_error_None in HM; pose proof (ind_ndecl_le Dx); lia ].
  change (ind_member Dx kx = Some Mk) in HM.
  destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
  pose proof (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ HΓu) as HΓs.
  destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
  destruct (per_ctx_then_per_env_initial_env HRΓ (wf_ctx_scoped _ _ _ HΓu) (wf_ctx_scoped _ _ _ HΓu)) as (ρ & _ & Hρ & _ & _).
  destruct (@inst_tele_args (gc_mk Θ Ξ) Γu (ind_uparams Dx) (List.map nf_to_exp Wsx) ρ (decl_closed_ass _ Hc)
              (@completeness_fundamental_ctx (gc_mk Θ Ξ) _ (decl_typed_uparams_field _ _ _ Hdt)) HΓu
              ltac:(rewrite Hlen; reflexivity) Hty Hρ
              (valid_ind_decl_uparams_evaluated _ (@valid_ind_decl_gc (gc_mk Θ Ξ) _ _ Hg Hl))) as (us & Eus & Hgu & Hlu).
  destruct (@decl_member_type (gc_mk Θ Ξ) qx Dx kx Mk us Hg Hl HM Hk Hgu Hlu) as (ns & i & R & HR).
  exact (view_below_acc Θ Ξ Γu _ (@per_univ_nest_acc_rel (gc_mk Θ Ξ) _ _ _ _ _ _ _ HR HR) (vk_ind qx kx Wsx) ρ us ns Hρ Eus
           (ex_intro _ Dx (conj Hl Hlu)) eq_refl).
Qed.

(** A view of the invariant is accessible for [view_lt]. *)
Corollary key_inv_acc : forall Θ Ξ Γu x, ⊢ᵍ Θ ⍮ Ξ -> key_inv Θ Ξ Γu x -> Acc (view_lt Θ Ξ Γu) x.
Proof. intros * Hg Hx; destruct x; [ exact (view_inv_acc _ _ _ _ _ _ Hg Hx) | exact (record_view_inv_acc _ _ _ _ _ Hg Hx) ]. Qed.

Section MeetsOffMembers.
  Context {GC : GCtx}.

  (** ** A View Sibling Is Its Member *)

  (** The view equations of the member [i] of the group at [qx], a view of
      the member [kv] of the group at [qv], at [Cs]: its sibling's
      parameters and constructors' arguments are the member's at [Cs]. *)
  Theorem view_sibling_link : forall Γu qx D Cs i Mi qv kv Iv vm Dqv Wv My,
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
    pose proof (ext_eq_trans_ass _ _ _ _ (all_assumptions_sub _ _ (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi))
                  (all_assumptions_sub _ _ (decl_typed_nparams_ass _ _ _ Hdtv _ _ HMy)) H1' H2) as HNP.
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
    pose proof (ctxsub_ext_rev _ _ _ _ _ H1' (all_assumptions_sub _ _ (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi))) as Hid.
    pose proof (ctxsub_sub_eq _ _ _ _ _ _ _ Hid HqY) as HqY'.
    change (List.length (im_nparams My)) with (im_nn My) in HqY'.
    destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg (fun pq D0 Hl0 => proj1 (decl_of_glookup _ _ _ _ Hg Hl0)) Hlv HMy HIn' gs' nil
                ltac:(rewrite List.app_nil_r; reflexivity)) as (HWc & _).
    pose proof (tele_sub_eq_ext (cargs_ctx qv Dqv My gs') (im_params Dqv My) _ _ _ (cargs_ctx_aux_ass _ _ _ _ _) HWc HqY') as H4.
    eapply ext_eq_trans_ass; [ apply all_assumptions_sub, cargs_ctx_aux_ass | apply all_assumptions_sub, cargs_ctx_aux_ass | | exact H4 ].
    rewrite Hnn; apply ext_eq_sym_ass; [ apply all_assumptions_sub, cargs_ctx_aux_ass | exact H3' ].
  Qed.

  (** ** Where the Meets Off a Member of the Cluster Land

      A nested occurrence the classification finds in the normal form of
      an argument of a constructor of a member of the group at [qx], at a
      normal key's arguments [Ws] over [Γu], is a sibling at [Ws] up to
      proofs when the argument is recursive, and below every view of the
      group at [Ws] otherwise. *)
  Theorem meet_off_member : forall Γu qx D kx Ws ss m Mi c gs gs1 g gs2 nu n pat z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Ws = ind_nu D ->
      (forall j C T, List.nth_error (List.map nf_to_exp Ws) j = Some C ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.map nf_to_exp Ws)) j = Some T -> Γu ⊢ C : T) ->
      key_normal gc_deps gc_stack Γu (vk_ind qx kx Ws) ->
      siblings_from gc_deps gc_stack Γu qx Ws 0 (ind_members D) ss ->
      ind_member D m = Some Mi -> ind_con Mi c = Some gs -> gs = gs1 ++ g :: gs2 ->
      nf_meet_at gc_deps gc_stack (tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id (List.map nf_to_exp Ws)) ++ Γu)
        nu (im_nn Mi + nu) n pat
        (carg_ty qx D (im_nn Mi) (cargs_pat gs1) g)[sb_qn (List.length gs1 + im_nn Mi) (sb_of_list Id (List.map nf_to_exp Ws))] z ->
      List.length pat = List.length gs1 ->
      key_in z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Ws).
  Proof.
    intros * Hg HΓu Hl HWl HCt Hkn Hss HM Hcon Heq Hm Hlp.
    destruct g as [r A | t].
    2:{ (** a recursive argument: a sibling *)
        left; eapply rec_meet_in_siblings; try eassumption; lia. }
    (** a non-recursive argument: a nesting step *)
    right.
    set (Cs := List.map nf_to_exp Ws) in *.
    assert (HCl : List.length Cs = ind_nu D) by (unfold Cs; rewrite List.length_map; exact HWl).
    destruct Hm as [i HT W HW Hpf gz Hcls gk Hk Hzk]; cbn [carg_ty] in HT, HW.
    rewrite (skipn_ctx_app (tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) Γu) in Hk
      by (rewrite length_tele_sub, List.length_app, length_cargs_ctx; unfold im_nn in *; lia).
    destruct (written_carg_key_view _ _ _ _ Hk Hzk) as (z0 & Hin & Hzz).
    clear Hzk.
    set (Δ := tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) (sb_of_list Id Cs)) in *.
      destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
      assert (HΔa : all_assumptions Δ)
        by (apply all_assumptions_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ Hdt _ _ HM) ]).
      assert (HlΔ : List.length Δ = List.length pat + (im_nn Mi + nu - nu))
        by (unfold Δ; rewrite length_tele_sub, List.length_app, length_cargs_ctx; unfold im_nn; lia).
      pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
      destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
      destruct (per_ctx_then_per_env_initial_env HRΓu (wf_ctx_scoped _ _ _ HΓu) (wf_ctx_scoped _ _ _ HΓu)) as (ρ0 & _ & Hρ0 & _ & _).
      destruct (inst_tele_args Γu (ind_uparams D) Cs ρ0 (decl_closed_ass _ Hc) (completeness_fundamental_ctx _ (decl_typed_uparams_field _ _ _ Hdt)) HΓu
                  ltac:(rewrite HCl; reflexivity) HCt Hρ0
                  (valid_ind_decl_uparams_evaluated _ (valid_ind_decl_gc _ _ Hg Hl))) as (us & Eus & _ & _).
      destruct z0 as [qz kz Csz | qz Isz].
      2:{ (** a record view: a step into the record type *)
          destruct (nest_record_view_typed _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcls Hin) as [Rz Hlz HIzl HIzt _].
          destruct (nest_record_end _ _ _ _ _ _ _ _ _ _ _ _ HT HW Hpf Hcls Hin) as (Bs & Rz' & Rs & HWe & Hlz' & _ & _ & _ & _ & HC & _).
          rewrite Hlz in Hlz'; injection Hlz' as <-.
          inversion Hzz as [| ? ? Rz2 Wz Hlz2 HWz]; subst.
          rewrite Hlz in Hlz2; injection Hlz2 as <-.
          pose proof (nf_key_record_args _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcls Hin Hlz HWz) as HWzI.
          replace (List.length Bs + List.length pat + (im_nn Mi + nu - nu)) with (List.length Bs + List.length gs1 + im_nn Mi) in HC
            by lia.
          destruct (nonrec_meet_below_record Γu qx D kx Cs ρ0 us m Mi c _ gs1 r A gs2 i W Bs qz Rs Rz Isz Hg HΓu Hl HCl HCt Hρ0 Eus
                      HM Hcon eq_refl HT HW HWe Hlz HIzl HIzt HC) as (usz & Eusz & Hlusz & Hstep).
          rewrite <- HWzI in Eusz.
          clear - Hρ0 Eus Eusz Hlz Hlusz Hstep; destruct GC as [Θ0 Ξ0].
          refine (mk_view_below _ _ _ (vk_record qz Wz) (vk_ind qx kx Ws) ρ0 Hρ0 us Eus usz Eusz nil
                    (ex_intro _ Rz (conj Hlz Hlusz)) _).
          cbn [key_type]; rewrite List.app_nil_r; exact Hstep. }
      destruct (nest_view_typed _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcls Hin) as [Dz Hlz Hkz HCzl HCzt _].
      inversion Hzz as [? ? ? Dz2 Wz Hlz2 HWz |]; subst.
      rewrite Hlz in Hlz2; injection Hlz2 as <-.
      pose proof (nf_key_ind_args _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcls Hin Hlz HWz) as HWzC.
      destruct (classify_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs & E & mz & HWe & HE & Hh & Hg2 & Hm & HC).
      pose proof HW as [ρw mw _ _ Hrw]; pose proof (read_typ_type_nf _ _ _ Hrw) as HWn.
      destruct (nf_pis_end _ _ _ HWn HWe) as (WE & HWE & HWEe).
      rewrite <- HWEe in Hh; destruct (nf_ind_view _ _ _ HWE Hh) as [Rs ->].
      cbn [nf_to_exp] in HWEe; subst E.
      rewrite app_args_apps in HC; cbn [app_args List.app] in HC.
      unfold grp_info in Hg2; rewrite Hlz in Hg2.
      destruct (kz <? ind_ndecl Dz); [ injection Hg2 as <- | discriminate ].
      replace (List.length Bs + List.length pat + (im_nn Mi + nu - nu)) with (List.length Bs + List.length gs1 + im_nn Mi) in HC
        by lia.
      destruct (nonrec_meet_below Γu qx D kx Cs ρ0 us m Mi c _ gs1 r A gs2 i W Bs qz kz Rs Dz Csz Hg HΓu Hl HCl HCt Hρ0 Eus
                  HM Hcon eq_refl HT HW HWe Hlz Hkz HCzl HCzt HC) as (usz & nsz & Eusz & Hlusz & Hstep).
      rewrite <- HWzC in Eusz.
      clear - Hρ0 Eus Eusz Hlz Hlusz Hstep; destruct GC as [Θ0 Ξ0].
      refine (mk_view_below _ _ _ (vk_ind qz kz Wz) (vk_ind qx kx Ws) ρ0 Hρ0 us Eus usz Eusz nsz
                (ex_intro _ Dz (conj Hlz Hlusz)) _).
      cbn [key_type]; rewrite List.app_nil_r; exact Hstep.
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
      = X ++ ce_ass (carg_kind g) (carg_ty pq D (im_nn M) (cargs_pat gs1) g)[sb_qn (List.length gs1 + im_nn M) σ]
          :: tele_sub (cargs_ctx pq D M gs1) (sb_qn (im_nn M) σ) /\ List.length X = List.length gs2.
  Proof.
    intros; rewrite cargs_ctx_split, !tele_sub_app; cbn [tele_sub List.length centry_sub].
    eexists; split; [ rewrite length_cargs_ctx, (sb_qn_plus (List.length gs1) (im_nn M) σ); reflexivity |].
    rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity.
  Qed.

  (** The constructors of the member [j] of the group at [qx] at the
      arguments [Ws], each argument over those before it: the positions
      its constructors' arguments are classified at. *)
  Definition member_rcs (qx : qname) (D : ind_decl) (Mj : imember) (Ws : list nf) : list (string * list (string * abs_kind * exp)) :=
    List.map (fun cg => (fst cg, ctx_args (tele_sub (cargs_ctx qx D Mj (snd cg)) (sb_qn (im_nn Mj) (sb_of_list sb_id (List.map nf_to_exp Ws))))))
      (im_cons Mj).

  (** The instances the normal forms of the arguments of the constructors
      of the member [j] of the group at [qx] at a normal key's arguments
      [Ws] meet are siblings at [Ws] up to proofs, or below every view of
      the group at [Ws]. *)
  Theorem member_meets : forall Γu qx D kx Ws ss j Mj nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Ws = ind_nu D ->
      (forall j C T, List.nth_error (List.map nf_to_exp Ws) j = Some C ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.map nf_to_exp Ws)) j = Some T -> Γu ⊢ C : T) ->
      key_normal gc_deps gc_stack Γu (vk_ind qx kx Ws) ->
      siblings_from gc_deps gc_stack Γu qx Ws 0 (ind_members D) ss ->
      ind_member D j = Some Mj ->
      nf_meet_in gc_deps gc_stack (tele_sub (im_nparams Mj) (sb_of_list sb_id (List.map nf_to_exp Ws)) ++ Γu) nu (im_nn Mj + nu) n
        (member_rcs qx D Mj Ws) z ->
      key_in z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Ws).
  Proof.
    intros * Hg HΓu Hl HWl HCt Hkn Hss HMj [rc Hrc pre y κ T post Hsnd pat Hlp Hm].
    unfold member_rcs in Hrc; apply List.in_map_iff in Hrc as ([c gs] & <- & HIn); cbn [fst snd] in Hsnd.
    destruct (cargs_sub_split _ _ _ _ _ _ _ _ _ _ Hsnd) as (gs1 & g' & gs2 & Heq & Hl1 & Hpre & _ & ->).
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ Hdt _ _ HMj) HIn) as Hcon.
    rewrite Hpre, cargs_pre_ctx in Hm.
    exact (meet_off_member Γu qx D kx Ws ss j Mj c _ gs1 g' gs2 nu n pat z Hg HΓu Hl HWl HCt Hkn Hss HMj Hcon Heq Hm ltac:(lia)).
  Qed.

  (** The instances a view sibling's constructors meet: those of the
      member of the group at [qx] it is, at [Cs], by the view
      equations. *)
  Theorem view_sibling_meets : forall Γu qx D kx Ws ss i Mi qv kv Iv vm Dqv Wv My nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Ws = ind_nu D ->
      (forall j C T, List.nth_error (List.map nf_to_exp Ws) j = Some C ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.map nf_to_exp Ws)) j = Some T -> Γu ⊢ C : T) ->
      key_normal gc_deps gc_stack Γu (vk_ind qx kx Ws) ->
      siblings_from gc_deps gc_stack Γu qx Ws 0 (ind_members D) ss ->
      ind_member D i = Some Mi -> im_head Mi = mh_view qv kv Iv vm -> ind_lookup gc_deps gc_stack qv = Some Dqv ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list Id (List.map nf_to_exp Ws)]) Iv)
        (List.map (fun T => T[sb_of_list Id (List.map nf_to_exp Ws)]) (tele_insts (ind_uparams Dqv) Id Iv)) Wv ->
      ind_member Dqv kv = Some My ->
      nf_meet_in gc_deps gc_stack (tele_sub (im_nparams My) (sb_of_list sb_id (List.map nf_to_exp Wv)) ++ Γu) nu (im_nn My + nu) n
        (member_rcs qv Dqv My Wv) z ->
      key_in z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Ws).
  Proof.
    intros * Hg HΓu Hl HWl HCt Hkn Hss HMi Hh Hlv Hnv HMy [rc Hrc pre y κ T post Hsnd pat Hlp Hm].
    set (Cs := List.map nf_to_exp Ws) in *.
    assert (HCl : List.length Cs = ind_nu D) by (unfold Cs; rewrite List.length_map; exact HWl).
    unfold member_rcs in Hrc; apply List.in_map_iff in Hrc as ([c gs'] & <- & HIn'); cbn [fst snd] in Hsnd.
    destruct (cargs_sub_split _ _ _ _ _ _ _ _ _ _ Hsnd) as (gs1y & gy & gs2y & Heqy & Hl1y & Hpre & _ & ->).
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [Hdtv _].
    pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ Hdtv _ _ HMy) HIn') as Hc'.
    destruct (view_sibling_link Γu qx D Cs i Mi qv kv Iv vm Dqv Wv My Hg HΓu Hl HCl HCt HMi Hh Hlv Hnv HMy) as (Hnn & HNP & Hcons).
    destruct (Hcons c gs' Hc') as (gs & Hcon & HE2).
    rewrite Hpre in Hm.
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
    assert (HaD : all_assumptions (tele_sub (cargs_ctx qx D Mi (gs1 ++ g' :: gs2)) (sb_qn (im_nn Mi) σC)))
      by (apply all_assumptions_sub, cargs_ctx_aux_ass).
    rewrite EX in HaD.
    (** the parameters and the arguments before, and the argument's
        types, equal *)
    pose proof (ext_eq_app _ _ _ _ _ _ _ (all_assumptions_sub _ _ (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi)) HaD HNP HE2) as HEall.
    rewrite <- !List.app_assoc in HEall; cbn [List.app] in HEall.
    apply ext_eq_app_inv in HEall; [| rewrite HlX, HlXy; rewrite !List.length_app in Hlg; cbn in Hlg; lia ].
    pose proof (ext_eq_ass_kind _ _ _ _ _ _ _ HEall) as Hκ; rewrite <- Hκ in HEall.
    assert (HaY : all_assumptions (tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC) ++ tele_sub (im_nparams Mi) σC))
      by (apply List.Forall_app; split; apply all_assumptions_sub; [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ Hdt _ _ HMi) ]).
    (** so the same instance met, in the member's context *)
    rewrite List.app_assoc in Hm.
    assert (HlD : List.length (tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC) ++ tele_sub (im_nparams Mi) σC)
                  = List.length pat + (im_nn My + nu - nu))
      by (rewrite List.length_app, !length_tele_sub, length_cargs_ctx; change (List.length (im_nparams Mi)) with (im_nn Mi); lia).
    pose proof (nf_meet_at_ext _ _ _ _ _ _ _ _ _ _ _ HaY HEall HlD Hm) as Hm'.
    rewrite <- List.app_assoc, cargs_pre_ctx in Hm'.
    rewrite <- Hnn in Hm'.
    exact (meet_off_member Γu qx D kx Ws ss i Mi c _ gs1 g' gs2 nu n pat z Hg HΓu Hl HWl HCt Hkn Hss HMi Hcon eq_refl Hm' ltac:(lia)).
  Qed.

  (** The record view equations of the member [i] of the group at [qx], a
      record view of the record at [qr], at [Cs]: the record's fields at
      the normal forms of its instance there are the member's
      constructor's arguments at [Cs]. *)
  Theorem record_sibling_link : forall Γu qx D Cs i Mi qr Ir fl Rr Wr c gs,
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
    destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMi Hh) as [Rr' HRf].
    pose proof (rview_record_lookup _ _ _ _ _ _ HRf) as Hlr'; rewrite Hlr in Hlr'; injection Hlr' as <-.
    pose proof (rview_record_count _ _ _ _ _ _ HRf) as HIl.
    pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) Hlr) as HcR.
    pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hlr) as HRt.
    assert (HRa : all_assumptions (record_params Rr)) by exact (typed_params_ass _ _ _ HRt).
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
    assert (HFa : all_assumptions F) by apply record_fctx_ass.
    pose proof (tele_sub_eq_ext F (record_params Rr) Γu _ _ HFa (record_typed_fctx_wf _ _ _ HRt _ (le_n _)) HσIY) as H2.
    eapply ext_eq_trans_ass; [ apply all_assumptions_sub, HFa | apply all_assumptions_sub, HFa | apply ext_eq_sym_ass; [ apply all_assumptions_sub, HFa | exact H2 ] |].
    exact H1.
  Qed.

  (** The constructor of a record view at the record [Rr] at the arguments
      [Wr]: its fields, each over those before it. *)
  Definition record_rcs (Rr : record_decl) (Wr : list nf) : list (string * list (string * abs_kind * exp)) :=
    (rview_con, ctx_args (tele_sub (record_fctx Rr (List.length (record_fields Rr))) (sb_of_list sb_id (List.map nf_to_exp Wr)))) :: nil.

  (** The instances the normal forms of a record view sibling's
      constructor's fields meet: those of the member of the group at [qx]
      it is, at [Ws], by the record view equations. *)
  Theorem record_sibling_meets : forall Γu qx D kx Ws ss i Mi qr Ir fl Rr Wr nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Ws = ind_nu D ->
      (forall j C T, List.nth_error (List.map nf_to_exp Ws) j = Some C ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.map nf_to_exp Ws)) j = Some T -> Γu ⊢ C : T) ->
      key_normal gc_deps gc_stack Γu (vk_ind qx kx Ws) ->
      siblings_from gc_deps gc_stack Γu qx Ws 0 (ind_members D) ss ->
      ind_member D i = Some Mi -> im_head Mi = mh_record qr Ir fl -> record_lookup gc_deps gc_stack qr = Some Rr ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list Id (List.map nf_to_exp Ws)]) Ir)
        (List.map (fun T => T[sb_of_list Id (List.map nf_to_exp Ws)]) (tele_insts (record_params Rr) Id Ir)) Wr ->
      nf_meet_in gc_deps gc_stack Γu nu nu n (record_rcs Rr Wr) z ->
      key_in z ss \/ view_lt gc_deps gc_stack Γu z (vk_ind qx kx Ws).
  Proof.
    intros * Hg HΓu Hl HWl HCt Hkn Hss HMi Hh Hlr Hnr [rc Hrc pre y κ T post Hsnd pat Hlp Hm].
    set (Cs := List.map nf_to_exp Ws) in *.
    assert (HCl : List.length Cs = ind_nu D) by (unfold Cs; rewrite List.length_map; exact HWl).
    destruct Hrc as [<- | []]; cbn [snd] in Hsnd.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMi Hh) as (gs & Hcs & _).
    destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMi Hh) as [_ Hnn].
    pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMi Hh) as HnP.
    pose proof (record_sibling_link Γu qx D Cs i Mi qr Ir fl Rr Wr rview_con gs Hg HΓu Hl HCl HCt HMi Hh Hlr Hnr Hcs) as HE2.
    set (σC := sb_of_list Id Cs) in *; set (σY := sb_of_list Id (List.map nf_to_exp Wr)) in *.
    set (ΔY := tele_sub (record_fctx Rr (List.length (record_fields Rr))) σY) in *.
    assert (HaY : all_assumptions ΔY) by (apply all_assumptions_sub, record_fctx_ass).
    (** the fields, split at the one met *)
    assert (EY : ΔY = raw_args_tele post ++ ce_ass κ T :: raw_args_tele pre).
    { rewrite <- (raw_args_tele_ctx_args ΔY HaY), Hsnd; unfold raw_args_tele; rewrite List.map_app, List.rev_app_distr; cbn [List.map List.rev].
      rewrite <- List.app_assoc; reflexivity. }
    (** the member's arguments, split at the same position *)
    assert (Hlg : List.length gs = List.length pre + S (List.length post)).
    { pose proof (ext_eq_length _ _ _ _ _ HE2) as E; rewrite EY, length_tele_sub, length_cargs_ctx in E.
      unfold raw_args_tele in E; rewrite List.length_app, List.length_rev, List.length_map in E; cbn in E.
      rewrite List.length_rev, List.length_map in E; lia. }
    assert (Hj : List.length pre < List.length gs) by lia.
    destruct (nth_error_lt_some' gs _ Hj) as [g' Hg'].
    destruct (List.nth_error_split _ _ Hg') as (gs1 & gs2 & -> & Hl1).
    destruct (cargs_sub_at qx D Mi gs1 g' gs2 σC) as (X & EX & HlX).
    rewrite EY, EX in HE2.
    apply ext_eq_app_inv in HE2;
      [| unfold raw_args_tele; rewrite List.length_rev, List.length_map, HlX; rewrite List.length_app in Hlg; cbn in Hlg; lia ].
    pose proof (ext_eq_ass_kind _ _ _ _ _ _ _ HE2) as Hκ; rewrite <- Hκ in HE2.
    (** so the same instance met, in the member's context *)
    assert (HaPT : all_assumptions (raw_args_tele pre ▹{κ} T)).
    { constructor; [ do 2 eexists; reflexivity |].
      unfold raw_args_tele, all_assumptions; apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; do 2 eexists; reflexivity. }
    pose proof (ext_eq_sym_ass _ _ _ _ _ HaPT HE2) as HE3.
    assert (HaD : all_assumptions (tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC))) by (apply all_assumptions_sub, cargs_ctx_aux_ass).
    assert (HlD : List.length (tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC)) = List.length pat + (nu - nu))
      by (rewrite length_tele_sub, length_cargs_ctx; lia).
    pose proof (nf_meet_at_ext _ _ _ _ _ _ _ _ _ _ _ HaD HE3 HlD Hm) as Hm'.
    assert (EΓ : tele_sub (cargs_ctx qx D Mi gs1) (sb_qn (im_nn Mi) σC) ++ Γu
                 = tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) σC ++ Γu)
      by (rewrite HnP, List.app_nil_r, Hnn; reflexivity).
    rewrite EΓ in Hm'.
    assert (Hm'' : nf_meet_at gc_deps gc_stack (tele_sub (cargs_ctx qx D Mi gs1 ++ im_nparams Mi) σC ++ Γu) nu (im_nn Mi + nu) n pat
                     (carg_ty qx D (im_nn Mi) (cargs_pat gs1) g')[sb_qn (List.length gs1 + im_nn Mi) σC] z)
      by (rewrite Hnn in Hm' |- *; exact Hm').
    assert (Hcon : ind_con Mi rview_con = Some (gs1 ++ g' :: gs2))
      by (unfold ind_con; rewrite Hcs; cbn; reflexivity).
    exact (meet_off_member Γu qx D kx Ws ss i Mi rview_con _ gs1 g' gs2 nu n pat z Hg HΓu Hl HWl HCt Hkn Hss HMi Hcon eq_refl Hm''
             ltac:(lia)).
  Qed.

  (** ** The Meets of a Record View Are Below It

      A record view is its own cluster: an instance its constructor's
      classified fields meet, at a field's normal form at the instance, is
      one nesting step out of the record type at the instance. *)
  Theorem record_view_meets_below : forall Γu qx Wsx Rx nu n z,
      ⊢ᵍ gc_deps ⍮ gc_stack -> record_view_typed gc_deps gc_stack Γu qx (List.map nf_to_exp Wsx) ->
      record_lookup gc_deps gc_stack qx = Some Rx ->
      nf_meet_in gc_deps gc_stack Γu nu nu n (record_rcs Rx Wsx) z -> view_lt gc_deps gc_stack Γu z (vk_record qx Wsx).
  Proof.
    intros * Hg [Rx' Hl' HIl HIt HΓu] Hl [rc Hrc pre y κ T post Hsnd pat Hlp Hm].
    set (Isx := List.map nf_to_exp Wsx) in *.
    rewrite Hl in Hl'; injection Hl' as <-.
    destruct Hrc as [<- | []]; cbn [snd] in Hsnd.
    destruct (fctx_sub_split _ _ _ _ _ _ _ Hsnd) as (f & A & HfA & Hpre & _ & ->).
    set (j := List.length pre) in *.
    rewrite Hpre in Hm.
    destruct Hm as [i HT W HW Hpf gz Hcl gk Hk Hzk].
    assert (Hjl0 : j < List.length (record_fields Rx)) by (apply List.nth_error_Some; congruence).
    rewrite (skipn_ctx_app (tele_sub (record_fctx Rx j) (sb_of_list Id Isx)) Γu) in Hk
      by (rewrite length_tele_sub, length_record_fctx_le by lia; lia).
    destruct (written_carg_key_view _ _ _ _ Hk Hzk) as (z0 & Hin & Hzz).
    clear Hzk.
    set (Δ := tele_sub (record_fctx Rx j) (sb_of_list Id Isx)) in *.
    assert (Hjl : j < List.length (record_fields Rx)) by (apply List.nth_error_Some; congruence).
    assert (HΔa : all_assumptions Δ) by (apply all_assumptions_sub, record_fctx_ass).
    assert (HlΔ : List.length Δ = List.length pat + (nu - nu))
      by (unfold Δ; rewrite length_tele_sub, length_record_fctx_le by lia; lia).
    pose proof (completeness_fundamental_ctx _ HΓu) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓu HRΓu].
    destruct (per_ctx_then_per_env_initial_env HRΓu (wf_ctx_scoped _ _ _ HΓu) (wf_ctx_scoped _ _ _ HΓu)) as (ρ0 & _ & Hρ0 & _ & _).
    pose proof (valid_rview_record_gc _ _ Hg Hl) as HvR.
    destruct (inst_tele_args Γu (record_params Rx) Isx ρ0 (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HvR))
                (params_valid _ (valid_rview_record_valid _ _ HvR)) HΓu HIl HIt Hρ0
                (params_evaluated_valid _ (valid_rview_record_valid _ _ HvR))) as (usx & Eusx & _ & _).
    assert (HlΨ : forall Bs, List.length (doms_ctx Bs ++ Δ) = List.length Bs + j)
      by (intros Bs; unfold doms_ctx, Δ; rewrite List.length_app, List.length_rev, List.length_map, length_tele_sub,
            length_record_fctx_le by lia; reflexivity).
    destruct z0 as [qz kz Csz | qz Isz].
    - (** a nested occurrence: the member at its instance *)
      destruct (nest_view_typed _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcl Hin) as [Dz Hlz Hkz HCzl HCzt _].
      inversion Hzz as [? ? ? Dz2 Wz Hlz2 HWz |]; subst.
      rewrite Hlz in Hlz2; injection Hlz2 as <-.
      pose proof (nf_key_ind_args _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcl Hin Hlz HWz) as HWzC.
      destruct (classify_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcl Hin) as (Bs & E & mz & HWe & HE & Hh & Hg2 & Hm & HC).
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
      rewrite <- HWzC in Eusz.
      clear - Hρ0 Eusx Eusz Hlz HlZ Hstep HEZ; destruct GC as [Θ0 Ξ0].
      exact (mk_view_below _ _ _ (vk_ind qz kz Wz) (vk_record qx Wsx) ρ0 Hρ0 usx Eusx usz Eusz nsz
               (ex_intro _ Dz (conj Hlz HlZ)) (Hstep _ _ _ HEZ)).
    - (** a record view: the record at its instance *)
      destruct (nest_record_view_typed _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcl Hin) as [Rz Hlz HIzl HIzt _].
      destruct (nest_record_end _ _ _ _ _ _ _ _ _ _ _ _ HT HW Hpf Hcl Hin) as (Bs & Rz' & Rs & HWe & Hlz' & _ & _ & _ & _ & HC & _).
      rewrite Hlz in Hlz'; injection Hlz' as <-.
      inversion Hzz as [| ? ? Rz2 Wz Hlz2 HWz]; subst.
      rewrite Hlz in Hlz2; injection Hlz2 as <-.
      pose proof (nf_key_record_args _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΔa HlΔ HT HW Hpf Hcl Hin Hlz HWz) as HWzI.
      destruct (field_step Γu qx Rx Isx ρ0 usx j f A i W Bs _ Hg HΓu Hl HIl HIt Hρ0 Eusx HfA HT HW HWe)
        as (zs & e & RE & HRE & HEE & Hlzs & Ee & Hstep).
      rewrite <- (HlΨ Bs) in Hlzs.
      replace (List.length Bs + List.length pat + (nu - nu)) with (List.length (doms_ctx Bs ++ Δ)) in HC by (rewrite HlΨ; lia).
      destruct (record_end_rel Γu (doms_ctx Bs ++ Δ) ρ0 zs RE qz Rs Rz Isz e Hg HΓu Hρ0 HRE HEE Hlzs Ee Hlz HIzl HIzt HC)
        as (usz & Eusz & HlZ & jz & R2 & HEZ).
      rewrite <- HWzI in Eusz.
      clear - Hρ0 Eusx Eusz Hlz HlZ Hstep HEZ; destruct GC as [Θ0 Ξ0].
      exact (mk_view_below _ _ _ (vk_record qz Wz) (vk_record qx Wsx) ρ0 Hρ0 usx Eusx usz Eusz nil
               (ex_intro _ Rz (conj Hlz HlZ)) (Hstep _ _ _ HEZ)).
  Qed.

End MeetsOffMembers.
