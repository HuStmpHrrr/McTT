(** * The Filed Constructor Types of a Declaration

    A run of a group's declaration files, for each declared member, the
    constructor types the user wrote, up to conversion, with each [Self_i]
    the type former of the member [i] at the frames' parameters
    ([run_cmd_ind_con_types]).  An argument classified as written is filed as
    its own image under that instantiation; one classified as its normal
    form is equal to it by soundness, and the equality moves through the
    instantiation of the [Self]s and the [Π]s over the arguments before it.
    A nested occurrence, found on a normal form only, is filed as the view
    of its instance, whose type is the container's member at the instance
    with the [Self]s instantiated. *)

From Stdlib Require Import Lia List String PeanoNat Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import SystemOpt CtxSub.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Syntax.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Syntactic.System Require Import Command.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Syntax *)

Lemma wk_pat_app_lt : forall pre rest x, x < pat_nargs pre -> wk_pat (pre ++ rest) x = wk_pat pre x.
Proof.
  induction pre as [| [] pre IH]; intros rest x Hx; cbn in Hx |- *; [ lia | |].
  - unfold wk_compose; rewrite IH by exact Hx; reflexivity.
  - destruct x as [| x]; cbn; [ reflexivity |]; rewrite IH by lia; reflexivity.
Qed.

Lemma wk_pat_app_ge : forall pre rest y, wk_pat (pre ++ rest) (pat_nargs pre + y) = List.length pre + wk_pat rest y.
Proof.
  induction pre as [| [] pre IH]; intros rest y; cbn [List.app pat_nargs wk_pat List.length]; [ reflexivity | |].
  - unfold wk_compose, wk_shift; rewrite IH; lia.
  - cbn; rewrite IH; reflexivity.
Qed.

Lemma wk_pat_falses_trues : forall np n y,
    wk_pat (List.repeat false np ++ List.repeat true n) y = if y <? np then y else y + n.
Proof.
  induction np as [| np IH]; intros n y; cbn [List.repeat List.app wk_pat].
  - induction n as [| n IHn]; cbn [List.repeat wk_pat]; [ destruct (y <? 0) eqn:E; [ apply Nat.ltb_lt in E; lia | lia ] |].
    unfold wk_compose, wk_shift; rewrite IHn; destruct (y <? 0) eqn:E; [ apply Nat.ltb_lt in E; lia | lia ].
  - destruct y as [| y]; cbn; [ reflexivity |]; rewrite IH.
    change (S (if y <? np then y else y + n) = (if S y <? S np then S y else S y + n)).
    destruct (y <? np) eqn:E; destruct (S y <? S np) eqn:E'; apply Nat.ltb_lt in E || apply Nat.ltb_ge in E;
      apply Nat.ltb_lt in E' || apply Nat.ltb_ge in E'; lia.
Qed.

Lemma wk_pat_trues : forall m x, wk_pat (List.repeat true m) x = x + m.
Proof. induction m as [| m IH]; intros x; cbn; [ lia | unfold wk_compose, wk_shift; rewrite IH; lia ]. Qed.

(** A term over the pattern [pre], weakened past [np] more binders and [n]
    [Self]s, with the [Self]s instantiated by [Xs], is the term over
    [pre]. *)
Lemma wk_cls_sub : forall pre np n A Xs, List.length Xs = n ->
    A[wk_pat (pre ++ List.repeat false np ++ List.repeat true n)]ʷ[sb_qn (List.length pre + np) (sb_of_list Id Xs)] = A[wk_pat pre]ʷ.
Proof.
  intros * HXs; rewrite <- exp_sub_of_wk, exp_sub_sub, <- (exp_sub_of_wk A (wk_pat _)).
  apply exp_sub_sb_eq; intros x; rewrite sb_compose_var, !sb_of_wk_var; cbn [sentry_sub].
  destruct (Nat.lt_ge_cases x (pat_nargs pre)) as [Hx | Hx].
  - rewrite wk_pat_app_lt by exact Hx.
    pose proof (wk_pat_bound pre 0 x ltac:(lia)) as Hb.
    rewrite sb_qn_lt by lia; reflexivity.
  - replace x with (pat_nargs pre + (x - pat_nargs pre)) by lia.
    rewrite wk_pat_app_ge, wk_pat_ge, wk_pat_falses_trues.
    set (y := x - pat_nargs pre).
    destruct (y <? np) eqn:E; [ apply Nat.ltb_lt in E | apply Nat.ltb_ge in E ].
    + rewrite sb_qn_lt by lia; reflexivity.
    + rewrite sb_qn_ge by lia.
      replace (List.length pre + (y + n) - (List.length pre + np)) with (List.length Xs + (y - np)) by lia.
      rewrite sb_of_list_ge; cbn; f_equal; lia.
Qed.

Lemma img_pat_some : forall pat T A, img_pat pat T = Some A -> T = A[wk_pat pat]ʷ.
Proof.
  intros * H; unfold img_pat in H.
  destruct (exp_eq_dec T T[unwk_pat pat]ʷ[wk_pat pat]ʷ) as [E |]; [| discriminate ].
  injection H as <-; exact E.
Qed.

Lemma img_pats_some : forall pat Ts As, img_pats pat Ts = Some As -> Ts = List.map (fun A => A[wk_pat pat]ʷ) As.
Proof.
  induction Ts as [| T Ts IH]; intros As H; cbn in H; [ injection H as <-; reflexivity |].
  destruct (img_pat pat T) as [A |] eqn:E1; [| discriminate ].
  destruct (img_pats pat Ts) as [As' |] eqn:E2; [| discriminate ].
  injection H as <-; cbn; rewrite <- (img_pat_some _ _ _ E1), <- (IH _ eq_refl); reflexivity.
Qed.

Lemma apps_app_head_args : forall M, M = apps (app_head M) (app_args M).
Proof.
  induction M; cbn; try reflexivity.
  rewrite apps_exp_app; cbn; rewrite <- IHM1; reflexivity.
Qed.

(** ** The [Self]s Instantiated

    [sb_selfs p b n t] sends the [n] [Self]s, [b] binders up, to the type
    formers of the members of the group at [p] at the [t] frames'
    parameters. *)

Lemma length_self_insts : forall p n t,
    List.length (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n)) = n.
Proof. intros; rewrite List.length_map, List.length_seq; reflexivity. Qed.

Lemma self_var_sub : forall p b n t x, b <= x -> x < b + n ->
    (a_var x)[sb_selfs p b n t] = apps (a_ind p (n - 1 - (x - b))) (vars_from b t).
Proof.
  intros * H1 H2; unfold sb_selfs; cbn [exp_sub].
  rewrite sb_qn_ge by lia.
  rewrite (sb_of_list_nth _ _ _ a_True) by (rewrite length_self_insts; lia).
  rewrite length_self_insts.
  rewrite (List.nth_indep _ a_True (apps (a_ind p 0) (vars_from 0 t))) by (rewrite length_self_insts; lia).
  rewrite (List.map_nth (fun j => apps (a_ind p j) (vars_from 0 t))), List.seq_nth by lia.
  cbn [sentry_wk sentry_exp]; rewrite apps_exp_wk, vars_from_wk_shiftn; cbn; reflexivity.
Qed.

(** ** A Classified Argument Is Its Filed Entry

    An argument classified ([cls_arg]) and numbered ([rcarg_num]) is filed
    as an entry whose type is the argument with the [Self]s instantiated,
    when the filed group [D] has the declared members as type formers
    ([Hdecl]) and the views at their instances ([Hview]): its [n]-th member
    on is the [v]-th view, the container's member at the view's uniform
    arguments with the [Self]s instantiated. *)

(** The type of the entry a filed argument adds to the arguments' context
    ([cargs_ctx_aux]), the arguments before it recursive as [pat] says. *)
Definition carg_entry (pq : qname) (D : ind_decl) (nn : nat) (pat : list bool) (g : carg) : typ :=
  match g with ca_arg A => A[wk_pat pat]ʷ | ca_rec t => ptyp_ty pq D nn pat t end.

Lemma cargs_ctx_aux_single : forall pq D nn pat g,
    cargs_ctx_aux pq D nn pat (g :: nil) = ce_ass (carg_entry pq D nn pat g) :: nil.
Proof. intros; destruct g; reflexivity. Qed.

Lemma rcarg_num_bit : forall n Vs g g', rcarg_num n Vs g = Some g' ->
    rcarg_bit g = match g' with ca_rec _ => true | ca_arg _ => false end.
Proof.
  intros * H; destruct g as [A | r]; cbn in H; [ injection H as <-; reflexivity |].
  destruct (rptyp_num n Vs r); [ injection H as <-; reflexivity | discriminate ].
Qed.

Section Filed.
  Variables (p : qname) (D : ind_decl) (Ks : list view_key) (nu n t nn : nat).
  Hypothesis HDnu : ind_nu D = nu + t.
  Hypothesis Hdecl : forall i Us Ns, i < n -> ind_mty p D i Us Ns = apps (a_ind p i) (Us ++ Ns).
  Hypothesis Hview : forall v x, List.nth_error Ks v = Some x ->
    (forall C, In C (view_key_args x) -> exp_scoped (nu + t) C[sb_selfs p nu n t] /\ exp_mvc 0 C[sb_selfs p nu n t]) /\
    forall Us Ns, ind_mty p D (n + v) Us Ns
                  = apps (view_key_head x) (List.map (fun C => C[sb_selfs p nu n t][sb_of_list Id Us]) (view_key_args x) ++ Ns).
  Variable grp_nu : qname -> nat -> option nat.
  Variable rec_np : qname -> option nat.

  Lemma cls_head_filed : forall pat d T r s,
      match app_head T with
      | a_var x => cls_self nu (nn + nu) n pat d x (app_args T)
      | a_ind qc k => cls_nest grp_nu nu (nn + nu) n pat d qc k (app_args T)
      | a_record qr => cls_record_view rec_np nu (nn + nu) n pat d qr (app_args T)
      | _ => None
      end = Some r ->
      rptyp_num n Ks r = Some s ->
      T[sb_selfs p (d + List.length pat + (nn + nu)) n t] = ptyp_ty p D nn (List.repeat false d ++ pat) s.
  Proof.
    intros * H Hs; rewrite (apps_app_head_args T); set (args := app_args T) in *.
    destruct (app_head T) eqn:Eh; try discriminate.
    - (** A nested occurrence: the view of its instance. *)
      match goal with Eh : app_head T = a_ind ?a ?b |- _ => rename a into qc; rename b into k end.
      unfold cls_nest in H.
      destruct (grp_nu qc k) as [m |] eqn:Em; [| discriminate ].
      destruct (m <=? List.length args) eqn:Eml; [| discriminate ].
      destruct (img_pats (List.repeat true (d + List.length pat + (nn + nu - nu))) (List.firstn m args)) as [Cs |] eqn:ECs;
        [| discriminate ].
      destruct (img_pats (cls_pat d (nn + nu) n pat) (List.skipn m args)) as [Ns |] eqn:ENs; [| discriminate ].
      destruct (selfs_occur nu n Cs); [| discriminate ].
      injection H as <-; cbn [rptyp_num] in Hs.
      destruct (view_key_index (vk_ind qc k Cs) Ks) as [v |] eqn:Ev; [| discriminate ]; cbn in Hs; injection Hs as <-.
      apply view_key_index_in in Ev.
      destruct (Hview _ _ Ev) as [HsC Hty]; cbn [view_key_head view_key_args] in HsC, Hty.
      cbn [ptyp_ty]; rewrite Hty.
      rewrite apps_exp_sub; cbn [exp_sub].
      rewrite <- (List.firstn_skipn m args), List.map_app.
      rewrite (img_pats_some _ _ _ ECs), (img_pats_some _ _ _ ENs), !List.map_map.
      f_equal; f_equal.
      + apply List.map_ext_in; intros C HC.
        destruct (HsC _ HC) as [HCs HCm].
        unfold ind_uvars; rewrite HDnu, List.length_app, List.repeat_length.
        rewrite exp_at_vars by assumption.
        rewrite <- exp_sub_of_wk with (φ := wk_pat _),
          exp_sub_sb_eq with (σ := ι (wk_pat _)) (τ := ι (wk_shiftn (d + List.length pat + nn))).
        * rewrite exp_sub_of_wk.
          unfold sb_selfs; replace (d + List.length pat + (nn + nu)) with ((d + List.length pat + nn) + nu) by lia.
          rewrite exp_shiftn_sub_qn; reflexivity.
        * intros x; cbn; rewrite wk_pat_trues; f_equal; lia.
      + apply List.map_ext; intros P.
        unfold cls_pat; rewrite List.app_assoc.
        replace (d + List.length pat + (nn + nu)) with (List.length (List.repeat false d ++ pat) + (nn + nu))
          by (rewrite List.length_app, List.repeat_length; lia).
        unfold sb_selfs; apply wk_cls_sub; apply length_self_insts.
    - (** A [Self]: the type former of its declared member. *)
      match goal with Eh : app_head T = a_var ?a |- _ => rename a into x end.
      unfold cls_self in H.
      set (b := d + List.length pat + (nn + nu)) in *.
      destruct ((b <=? x) && (x <? b + n))%bool eqn:Eb; [| discriminate ].
      apply andb_prop in Eb as [Eb1 Eb2]; apply Nat.leb_le in Eb1; apply Nat.ltb_lt in Eb2.
      destruct (list_eq_dec exp_eq_dec (List.firstn nu args) (vars_from (d + List.length pat + (nn + nu - nu)) nu))
        as [Ef |]; [| discriminate ].
      destruct (img_pats (cls_pat d (nn + nu) n pat) (List.skipn nu args)) as [Ps |] eqn:EPs; [| discriminate ].
      cbn in H; injection H as <-; cbn in Hs; injection Hs as <-.
      cbn [ptyp_ty]; rewrite Hdecl by lia.
      rewrite apps_exp_sub, self_var_sub by lia.
      rewrite <- (List.firstn_skipn nu args), List.map_app, Ef, (img_pats_some _ _ _ EPs), List.map_map.
      unfold sb_selfs at 1; rewrite vars_from_sub by (unfold b; lia); fold (sb_selfs p b n t).
      rewrite <- !apps_exp_app; f_equal.
      unfold ind_uvars; rewrite HDnu, List.length_app, List.repeat_length.
      rewrite List.app_assoc; f_equal.
      * replace (d + List.length pat + (nn + nu - nu)) with (d + List.length pat + nn) by lia.
        replace (nu + t) with (t + nu) by lia; rewrite <- vars_from_app; f_equal; f_equal; unfold b; lia.
      * apply List.map_ext; intros P.
        unfold cls_pat; rewrite List.app_assoc.
        replace b with (List.length (List.repeat false d ++ pat) + (nn + nu))
          by (unfold b; rewrite List.length_app, List.repeat_length; lia).
        unfold sb_selfs; apply wk_cls_sub; apply length_self_insts.
    - (** A record at its instance: the record view of the instance. *)
      match goal with Eh : app_head T = a_record ?a |- _ => rename a into qr end.
      unfold cls_record_view in H.
      destruct (rec_np qr) as [m |] eqn:Em; [| discriminate ].
      destruct (Nat.eqb m (List.length args)) eqn:Eml; [| discriminate ].
      destruct (img_pats (List.repeat true (d + List.length pat + (nn + nu - nu))) args) as [Is |] eqn:EIs; [| discriminate ].
      destruct (selfs_occur nu n Is && selfs_guarded nu n Is)%bool; [| discriminate ].
      injection H as <-; cbn [rptyp_num] in Hs.
      destruct (view_key_index (vk_record qr Is) Ks) as [v |] eqn:Ev; [| discriminate ]; cbn in Hs; injection Hs as <-.
      apply view_key_index_in in Ev.
      destruct (Hview _ _ Ev) as [HsC Hty]; cbn [view_key_head view_key_args] in HsC, Hty.
      cbn [ptyp_ty List.map]; rewrite Hty, List.app_nil_r.
      rewrite apps_exp_sub; cbn [exp_sub].
      rewrite (img_pats_some _ _ _ EIs), !List.map_map.
      f_equal.
      apply List.map_ext_in; intros C HC.
      destruct (HsC _ HC) as [HCs HCm].
      unfold ind_uvars; rewrite HDnu, List.length_app, List.repeat_length.
      rewrite exp_at_vars by assumption.
      rewrite <- exp_sub_of_wk with (φ := wk_pat _),
        exp_sub_sb_eq with (σ := ι (wk_pat _)) (τ := ι (wk_shiftn (d + List.length pat + nn))).
      + rewrite exp_sub_of_wk.
        unfold sb_selfs; replace (d + List.length pat + (nn + nu)) with ((d + List.length pat + nn) + nu) by lia.
        rewrite exp_shiftn_sub_qn; reflexivity.
      + intros x; cbn; rewrite wk_pat_trues; f_equal; lia.
  Qed.

  Lemma cls_sh_filed : forall pat T d r s, cls_sh grp_nu rec_np nu (nn + nu) n pat d T = Some r -> rptyp_num n Ks r = Some s ->
      T[sb_selfs p (d + List.length pat + (nn + nu)) n t] = ptyp_ty p D nn (List.repeat false d ++ pat) s.
  Proof.
    intros pat T; induction T; intros d0 r0 s0 Hcls Hnum.
    all: try solve [ eapply cls_head_filed; [ exact Hcls | exact Hnum ] ].
    (** A [Π] over a [Self]-free domain. *)
    cbn [cls_sh] in Hcls.
    destruct (img_pat (cls_pat d0 (nn + nu) n pat) T1) as [B0 |] eqn:EB; [| discriminate ].
    destruct (cls_sh grp_nu rec_np nu (nn + nu) n pat (S d0) T2) as [r' |] eqn:Er; [| discriminate ].
    cbn in Hcls; injection Hcls as <-; cbn [rptyp_num] in Hnum.
    destruct (rptyp_num n Ks r') as [s' |] eqn:Es; [| discriminate ]; cbn in Hnum; injection Hnum as <-.
    cbn [exp_sub ptyp_ty]; f_equal.
    - rewrite (img_pat_some _ _ _ EB); unfold cls_pat; rewrite List.app_assoc.
      replace (d0 + List.length pat + (nn + nu)) with (List.length (List.repeat false d0 ++ pat) + (nn + nu))
        by (rewrite List.length_app, List.repeat_length; lia).
      unfold sb_selfs; apply wk_cls_sub; apply length_self_insts.
    - exact (IHT2 _ _ _ Er Es).
  Qed.

  Lemma cls_arg_filed : forall pat T g g', cls_arg grp_nu rec_np nu (nn + nu) n pat T = Some g -> rcarg_num n Ks g = Some g' ->
      T[sb_selfs p (List.length pat + (nn + nu)) n t] = carg_entry p D nn pat g'.
  Proof.
    intros * Hc Hn; unfold cls_arg in Hc.
    destruct (img_pat (cls_pat 0 (nn + nu) n pat) T) as [A |] eqn:EA.
    - injection Hc as <-; cbn in Hn; injection Hn as <-; cbn [carg_entry].
      rewrite (img_pat_some _ _ _ EA); unfold cls_pat; cbn [List.repeat List.app].
      unfold sb_selfs; apply wk_cls_sub; apply length_self_insts.
    - destruct (cls_sh grp_nu rec_np nu (nn + nu) n pat 0 T) as [r |] eqn:Er; [| discriminate ].
      injection Hc as <-; cbn in Hn.
      destruct (rptyp_num n Ks r) as [s |] eqn:Es; [| discriminate ]; injection Hn as <-; cbn [carg_entry].
      exact (cls_sh_filed _ _ _ _ _ Er Es).
  Qed.

End Filed.

(** ** The Filed Group

    [rd_filed] files the declared members in order, then the views, each
    the container's member at its instance. *)

Lemma Forall2_nth_error_l : forall {X Y} (Rl : X -> Y -> Prop) l1 l2 i a,
    Forall2 Rl l1 l2 -> List.nth_error l1 i = Some a -> exists b, List.nth_error l2 i = Some b /\ Rl a b.
Proof.
  intros X Y Rl l1 l2 i a H; revert i; induction H as [| a1 b1 l1 l2 Hab H IH]; intros [| i] Hi; cbn in Hi; try discriminate.
  - injection Hi as <-; exists b1; split; [ reflexivity | exact Hab ].
  - exact (IH _ Hi).
Qed.

Lemma rms_filed_length : forall Ξ n Vs ms css Ms, rms_filed Ξ n Vs ms css = Some Ms -> List.length Ms = List.length ms.
Proof.
  induction ms as [| Mr ms IH]; intros [| cs css] Ms H; cbn in H; try discriminate; [ injection H as <-; reflexivity |].
  destruct (rcons_num n Vs cs); [| discriminate ].
  destruct (rms_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ]; injection H as <-; cbn; f_equal; eapply IH; exact E.
Qed.

Lemma rms_filed_nth : forall Ξ n Vs ms css Ms, rms_filed Ξ n Vs ms css = Some Ms ->
    forall j Mr cs, List.nth_error ms j = Some Mr -> List.nth_error css j = Some cs ->
      List.nth_error Ms j
      = option_map (fun cs' => mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') (rcons_num n Vs cs).
Proof.
  induction ms as [| Mr0 ms IH]; intros [| cs0 css] Ms H j Mr cs Hj Hc; cbn in H; try discriminate; [ destruct j; discriminate |].
  destruct (rcons_num n Vs cs0) as [cs0' |] eqn:E0; [| discriminate ].
  destruct (rms_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ]; injection H as <-.
  destruct j as [| j]; cbn in Hj, Hc |- *.
  - injection Hj as <-; injection Hc as <-; rewrite E0; reflexivity.
  - exact (IH _ _ E _ _ _ Hj Hc).
Qed.

Lemma rms_filed_decl : forall Ξ n Vs ms css Ms, rms_filed Ξ n Vs ms css = Some Ms -> Forall (fun M => im_is_decl M = true) Ms.
Proof.
  induction ms as [| Mr ms IH]; intros [| cs css] Ms H; cbn in H; try discriminate; [ injection H as <-; constructor |].
  destruct (rcons_num n Vs cs); [| discriminate ].
  destruct (rms_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ]; injection H as <-.
  constructor; [ reflexivity | eapply IH; exact E ].
Qed.

Lemma rv_filed_view : forall Θ Ξ σ n Ks x ss cs Nv M, rv_filed Θ Ξ σ n Ks x ss cs Nv = Some M -> im_is_decl M = false.
Proof.
  intros * H; destruct x as [qc k Cs | qr Is]; unfold rv_filed in H.
  - destruct (ind_lookup Θ Ξ qc); [| discriminate ].
    destruct (ind_member _ k); [| discriminate ].
    destruct (rcons_num n Ks cs); [| discriminate ].
    injection H as <-; reflexivity.
  - destruct (record_lookup Θ Ξ qr); [| discriminate ].
    destruct (rcons_num n Ks cs); [| discriminate ].
    injection H as <-; reflexivity.
Qed.

Lemma rvs_filed_views : forall Θ Ξ σ n Ks xs Vs Ss css Nvs Mvs, rvs_filed Θ Ξ σ n Ks xs Vs Ss css Nvs = Some Mvs ->
    Forall (fun M => im_is_decl M = false) Mvs.
Proof.
  induction xs as [| x xs IH]; intros * H; cbn in H; [ injection H as <-; constructor |].
  destruct (view_key_index x Vs) as [w |]; [| discriminate ].
  destruct (rv_filed _ _ _ _ _ _ _ _ _) as [M |] eqn:E1; [| discriminate ].
  destruct (rvs_filed Θ Ξ σ n Ks xs Vs Ss css Nvs) as [Ms' |] eqn:E2; [| discriminate ]; injection H as <-.
  constructor; [ exact (rv_filed_view _ _ _ _ _ _ _ _ _ _ E1) | eapply IH; exact E2 ].
Qed.

(** The [v]-th view filed is the [v]-th key's, its data read off the
    tables at the key's position among the views found. *)
Lemma rvs_filed_nth : forall Θ Ξ σ n Ks xs Vs Ss css Nvs Mvs, rvs_filed Θ Ξ σ n Ks xs Vs Ss css Nvs = Some Mvs ->
    forall v x, List.nth_error xs v = Some x ->
      exists w, view_key_index x Vs = Some w /\
        List.nth_error Mvs v = rv_filed Θ Ξ σ n Ks x (List.nth w Ss nil) (List.nth w css nil) (List.nth w Nvs nil).
Proof.
  induction xs as [| x0 xs IH]; intros * H v x Hx; cbn in H; [ destruct v; discriminate |].
  destruct (view_key_index x0 Vs) as [w0 |] eqn:Ew; [| discriminate ].
  destruct (rv_filed _ _ _ _ _ _ _ _ _) as [M |] eqn:E1; [| discriminate ].
  destruct (rvs_filed Θ Ξ σ n Ks xs Vs Ss css Nvs) as [Ms' |] eqn:E2; [| discriminate ]; injection H as <-.
  destruct v as [| v]; cbn in Hx |- *.
  - injection Hx as <-; exists w0; split; [ exact Ew | symmetry; exact E1 ].
  - exact (IH _ _ _ _ _ E2 _ _ Hx).
Qed.

Lemma rvs_filed_length : forall Θ Ξ σ n Ks xs Vs Ss css Nvs Mvs, rvs_filed Θ Ξ σ n Ks xs Vs Ss css Nvs = Some Mvs ->
    List.length Mvs = List.length xs.
Proof.
  induction xs as [| x xs IH]; intros * H; cbn in H; [ injection H as <-; reflexivity |].
  destruct (view_key_index x Vs) as [w |]; [| discriminate ].
  destruct (rv_filed _ _ _ _ _ _ _ _ _) as [M |] eqn:E1; [| discriminate ].
  destruct (rvs_filed Θ Ξ σ n Ks xs Vs Ss css Nvs) as [Ms' |] eqn:E2; [| discriminate ]; injection H as <-.
  cbn; f_equal; eapply IH; exact E2.
Qed.

Lemma rtele_cons : forall y T args, rtele ((y, T) :: args) = rtele args ++ ce_ass T :: nil.
Proof. reflexivity. Qed.

Lemma length_rtele : forall args, List.length (rtele args) = List.length args.
Proof. intros; unfold rtele; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma rtele_app : forall args1 args2, rtele (args1 ++ args2) = rtele args2 ++ rtele args1.
Proof. intros; unfold rtele; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

(** A [Π] over assumptions of equal bodies. *)
Lemma ctx_pi_ass_eq : forall Θ Ξ Δ Γ A A' i,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A ≈ A' : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A ≈ ctx_pi Δ A' : Typeω@j.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΔ HA; cbn in *; [ eauto |].
  inversion Hass as [| ? ? [B ->] Hass']; subst.
  destruct (ctx_decomp HΔ) as [HΔ' [k HB]].
  eapply IH with (i := max k i); [ exact Hass' | exact HΔ' |].
  eapply wf_exp_eq_pi_cong_large; [ eapply lift_exp_max_left; exact HB | apply wf_exp_eq_refl; eapply lift_exp_max_left; exact HB
                            | eapply lift_exp_eq_ge; [| exact HA ]; lia ].
Qed.

Lemma rd_selfs_from_snoc : forall R j l Mr,
    rd_selfs_from R j (l ++ Mr :: nil) = ce_ass (rd_self_ty R Mr)[wk_shiftn (j + List.length l)]ʷ :: rd_selfs_from R j l.
Proof.
  intros R j l; revert j; induction l as [| M0 l IH]; intros; cbn [List.app rd_selfs_from List.length].
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IH; cbn [List.app]; do 4 f_equal; lia.
Qed.

Lemma tele_wk_shiftn_sb_of_list : forall Δ Xs σ,
    tele_sub (tele_wk Δ (wk_shiftn (List.length Xs))) (sb_of_list σ Xs) = tele_sub Δ σ.
Proof.
  intros; rewrite <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
  intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]; rewrite Nat.add_comm; apply sb_of_list_ge.
Qed.

Lemma rcons_num_in : forall n Vs cs cs' c gsr, rcons_num n Vs cs = Some cs' -> In (c, gsr) cs ->
    exists gs, rcargs_num n Vs gsr = Some gs /\ In (c, gs) cs'.
Proof.
  induction cs as [| [c0 gs0] cs IH]; intros * H Hin; [ destruct Hin |]; cbn in H.
  destruct (rcargs_num n Vs gs0) as [gs0' |] eqn:E1; [| discriminate ].
  destruct (rcons_num n Vs cs) as [cs0 |] eqn:E2; [| discriminate ].
  injection H as <-.
  destruct Hin as [[= <- <-] | Hin].
  - exists gs0'; split; [ exact E1 | left; reflexivity ].
  - destruct (IH _ _ _ eq_refl Hin) as (gs & Hgs & Hin'); exists gs; split; [ exact Hgs | right; exact Hin' ].
Qed.

Lemma cls_args_in_length : forall Θ Ξ Γp nu np n pat args1 args gs,
    cls_args_in Θ Ξ Γp nu np n pat args1 args gs -> List.length gs = List.length args.
Proof. induction 1; cbn; auto. Qed.

(** The type of a constructor of the declared member [j], [Mr], with the
    arguments [args] as written, over the filed parameters: the member's
    own, the group's uniform ones and the frames' [T]; the [Self]s are
    instantiated as the type formers at the frames' parameters
    ([sb_selfs]), and the result is [Self_j] at all the member's
    parameters. *)
Definition user_con_ty (p : qname) (R : raw_decl) (Mr : raw_member) (j : nat) (T : ctx) (args : list (string * exp)) : typ :=
  let np := (List.length (raw_member_nparams Mr) + rd_nu R)%nat in
  ctx_pi (raw_member_nparams Mr ++ raw_decl_uparams R ++ T)
    (ctx_pi (rtele args) (apps (a_var (List.length args + np + (rd_n R - 1 - j))) (vars_from (List.length args) np)))
      [sb_selfs p np (rd_n R) (List.length T)].

(** The constructor [c] of the member [j] of the group at [p] is filed, of
    a type equal to [U]. *)
#[warnings="-cannot-define-projection"]
Record filed_con_ty (Θ : gdeps) (Ξ : gstack) (p : qname) (j : nat) (c : string) (U : typ) : Prop := mk_filed_con_ty
  { (** The filed group *)
    filed_con_ty_decl : ind_decl
    (** The member [j] *)
  ; filed_con_ty_member : imember
    (** The constructor's filed argument kinds *)
  ; filed_con_ty_args : list carg
    (** The group is found at [p] *)
  ; filed_con_ty_lookup : ind_lookup Θ Ξ p = Some filed_con_ty_decl
    (** The member is the group's [j]-th *)
  ; filed_con_ty_member_at : ind_member filed_con_ty_decl j = Some filed_con_ty_member
    (** [c] is one of its constructors *)
  ; filed_con_ty_con : ind_con filed_con_ty_member c = Some filed_con_ty_args
    (** The constructor's type is equal to [U] *)
  ; filed_con_ty_ty : exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p filed_con_ty_decl j filed_con_ty_member filed_con_ty_args ≈ U : Typeω@i }.

(** A filed constructor stays filed, at its type, along an embedding. *)
Lemma filed_con_ty_emb : forall Θ Ξ Θ2 Ξ2 p j c U,
    Emb Θ Ξ Θ2 Ξ2 -> filed_con_ty Θ Ξ p j c U -> filed_con_ty Θ2 Ξ2 p j c U.
Proof.
  intros * He [D M gs Hl Hm Hc (i & Hty)].
  apply (mk_filed_con_ty _ _ _ _ _ _ D M gs);
    [ exact (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ He) Hl) | exact Hm | exact Hc
    | exists i; exact (proj1 (proj2 (proj2 (emb_preserves_wf _ _ _ _ He))) _ _ _ _ Hty) ].
Qed.

(** ** The Constructor Types of a Run

    The premises of [run_cmd_ind_case], the group filed as [D] at [p] in the stack
    [Ξf] the entries make. *)

Section ConTypes.
  Variables (Θ : gdeps) (Ξ : gstack) (pv : bool) (R : raw_decl) (Mr0 : raw_member) (Mrs : list raw_member)
    (csD : list (list (string * list rcarg))) (Vs : list view_key) (Ss : list (list view_key))
    (csV : list (list (string * list rcarg))) (Nvs : list ctx) (Ms Mvs : list imember) (Ξf : gstack).

  #[local] Abbreviation p := (ind_qname Ξ (raw_member_name Mr0)).
  #[local] Abbreviation n := (rd_n R).
  #[local] Abbreviation nu := (rd_nu R).
  #[local] Abbreviation t := (List.length (gs_tele Ξ)).
  #[local] Abbreviation D := (mk_ind (raw_decl_uparams R ++ gs_tele Ξ) (raw_member_sort Mr0) (Ms ++ Mvs)).
  (** The views in filing order *)
  #[local] Abbreviation Ks := (filed_keys (meets_tbl Vs csV) Vs).

  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis HMr : raw_decl_members R = Mr0 :: Mrs.
  Hypothesis Hsort : Forall (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) Mrs.
  Hypothesis Hcls : Forall2 (rm_cls Θ Ξ R) (raw_decl_members R) csD.
  Hypothesis Hsibs : Forall2 (view_sibs Θ Ξ R) Vs Ss.
  Hypothesis Hvcls : Forall2 (view_cls Θ Ξ R) Vs csV.
  Hypothesis Hnps : Forall2 (view_nps Θ Ξ R) Vs Nvs.
  Hypothesis Hms : rms_filed Ξ n Ks (raw_decl_members R) csD = Some Ms.
  Hypothesis Hmvs : rvs_filed Θ Ξ (sb_selfs p nu n t) n Ks Ks Vs Ss csV Nvs = Some Mvs.
  (** The stack the declared members end on: well formed, the stack before
      embedded in it, the group found at its first member's path *)
  Hypothesis Hfwf : ⊢ᵍ Θ ⍮ Ξf.
  Hypothesis Hfemb : Emb Θ Ξ Θ Ξf.
  Hypothesis Hflk : ind_lookup Θ Ξf p = Some D.

  Lemma filed_wf : ⊢ᵍ Θ ⍮ Ξf.
  Proof. exact Hfwf. Qed.

  Lemma filed_emb : Emb Θ Ξ Θ Ξf.
  Proof. exact Hfemb. Qed.

  Lemma filed_lookup : ind_lookup Θ Ξf p = Some D.
  Proof. exact Hflk. Qed.

  Lemma filed_decl_typed : decl_typed Θ Ξf D.
  Proof. exact (proj1 (decl_of_lookup _ _ ⋅ _ _ (wf_ctx_empty _ _ filed_wf) filed_lookup)). Qed.

  Lemma filed_decl_closed : decl_closed D.
  Proof. exact (proj2 (decl_of_lookup _ _ ⋅ _ _ (wf_ctx_empty _ _ filed_wf) filed_lookup)). Qed.

  Lemma length_filed_decls : List.length Ms = n.
  Proof. exact (rms_filed_length _ _ _ _ _ _ Hms). Qed.

  Lemma filed_nu : ind_nu D = nu + t.
  Proof. unfold ind_nu, rd_nu; cbn; apply List.length_app. Qed.

  Lemma filed_ndecl : ind_ndecl D = n.
  Proof.
    unfold ind_ndecl; cbn [ind_members]; rewrite List.filter_app.
    assert (H1 : forall l, Forall (fun M => im_is_decl M = true) l -> List.filter im_is_decl l = l)
      by (induction 1 as [| M l HM _ IH]; cbn; [ reflexivity | rewrite HM, IH; reflexivity ]).
    assert (H2 : forall l, Forall (fun M => im_is_decl M = false) l -> List.filter im_is_decl l = nil)
      by (induction 1 as [| M l HM _ IH]; cbn; [ reflexivity | rewrite HM, IH; reflexivity ]).
    rewrite (H1 _ (rms_filed_decl _ _ _ _ _ _ Hms)), (H2 _ (rvs_filed_views _ _ _ _ _ _ _ _ _ _ _ Hmvs)), List.app_nil_r.
    exact length_filed_decls.
  Qed.

  (** The declared members are the type formers, the views the containers'
      members at their instances. *)
  Lemma filed_mty_decl : forall i Us Ns, i < n -> ind_mty p D i Us Ns = apps (a_ind p i) (Us ++ Ns).
  Proof.
    intros * Hi; unfold ind_mty, ind_member; cbn [ind_members].
    rewrite List.nth_error_app1 by (rewrite length_filed_decls; exact Hi).
    destruct (nth_error_lt_some Ms i ltac:(rewrite length_filed_decls; exact Hi)) as [M HM]; rewrite HM.
    pose proof (proj1 (List.Forall_forall _ _) (rms_filed_decl _ _ _ _ _ _ Hms) M (List.nth_error_In _ _ HM)) as Hd.
    unfold im_ty_at, im_ref, im_pre, im_is_decl in *; destruct (im_head M); [ reflexivity | discriminate | discriminate ].
  Qed.

  Lemma filed_view : forall v x, List.nth_error Ks v = Some x ->
      (forall C, In C (view_key_args x) -> exp_scoped (nu + t) C[sb_selfs p nu n t] /\ exp_mvc 0 C[sb_selfs p nu n t]) /\
      forall Us Ns, ind_mty p D (n + v) Us Ns
                    = apps (view_key_head x) (List.map (fun C => C[sb_selfs p nu n t][sb_of_list Id Us]) (view_key_args x) ++ Ns).
  Proof.
    intros * Hv.
    destruct (rvs_filed_nth _ _ _ _ _ _ _ _ _ _ _ Hmvs _ _ Hv) as (w & _ & Hnth).
    assert (Hlt : v < List.length Mvs)
      by (rewrite (rvs_filed_length _ _ _ _ _ _ _ _ _ _ _ Hmvs); apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some Mvs v Hlt) as [M HM].
    assert (Hk : ind_member D (n + v) = Some M).
    { unfold ind_member; cbn [ind_members]; rewrite List.nth_error_app2 by (rewrite length_filed_decls; lia).
      rewrite length_filed_decls; replace (n + v - n) with v by lia; exact HM. }
    rewrite HM in Hnth; symmetry in Hnth; unfold rv_filed in Hnth.
    destruct (decl_mvc_members _ (decl_typed_mvc _ _ _ filed_decl_typed) _ _ Hk) as (_ & Hmv & _).
    destruct x as [qc k Cs | qr Is]; cbn [view_key_head view_key_args].
    - destruct (ind_lookup Θ Ξ qc); [| discriminate ].
      destruct (ind_member _ k); [| discriminate ].
      destruct (rcons_num n Ks _); [| discriminate ].
      injection Hnth as <-.
      split.
      + intros C HC.
        pose proof (decl_closed_head_scoped _ filed_decl_closed _ _ _ _ _ _ Hk eq_refl) as Hsc.
        cbn in Hmv; rewrite List.Forall_forall in Hsc, Hmv.
        pose proof (List.in_map (fun C0 => C0[sb_selfs p nu n t]) _ _ HC) as HC'.
        rewrite filed_nu in Hsc; split; [ apply Hsc | apply Hmv ]; exact HC'.
      + intros Us Ns; unfold ind_mty; rewrite Hk; unfold im_ty_at, im_ref, im_pre; cbn [im_head fst snd].
        rewrite List.map_map; reflexivity.
    - destruct (record_lookup Θ Ξ qr); [| discriminate ].
      destruct (rcons_num n Ks _); [| discriminate ].
      injection Hnth as <-.
      split.
      + intros C HC.
        pose proof (decl_closed_rhead_scoped _ filed_decl_closed _ _ _ _ _ Hk eq_refl) as Hsc.
        cbn in Hmv; rewrite List.Forall_forall in Hsc, Hmv.
        pose proof (List.in_map (fun C0 => C0[sb_selfs p nu n t]) _ _ HC) as HC'.
        rewrite filed_nu in Hsc; split; [ apply Hsc | apply Hmv ]; exact HC'.
      + intros Us Ns; unfold ind_mty; rewrite Hk; unfold im_ty_at, im_pre; cbn [im_head].
        rewrite List.map_map; reflexivity.
  Qed.

  Lemma filed_member : forall j Mr cs, List.nth_error (raw_decl_members R) j = Some Mr -> List.nth_error csD j = Some cs ->
      exists cs', rcons_num n Ks cs = Some cs' /\
        ind_member D j = Some (mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs').
  Proof.
    intros * Hj Hc.
    pose proof (rms_filed_nth _ _ _ _ _ _ Hms _ _ _ Hj Hc) as H.
    assert (Hlt : j < List.length Ms)
      by (rewrite length_filed_decls; unfold rd_n; apply List.nth_error_Some; congruence).
    unfold ind_member; cbn [ind_members]; rewrite List.nth_error_app1 by exact Hlt.
    destruct (rcons_num n Ks cs) as [cs' |]; cbn in H.
    - exists cs'; split; [ reflexivity | exact H ].
    - exfalso; apply List.nth_error_None in H; lia.
  Qed.

  Lemma member_sort : forall Mr, In Mr (raw_decl_members R) -> raw_member_sort Mr = raw_member_sort Mr0.
  Proof.
    intros Mr Hin; rewrite HMr in Hin; destruct Hin as [<- | Hin]; [ reflexivity |].
    exact (proj1 (List.Forall_forall _ _) Hsort _ Hin).
  Qed.

  Lemma filed_ind_ty : forall j Mr cs', List.nth_error (raw_decl_members R) j = Some Mr ->
      ind_ty D (mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') = ctx_pi (gs_tele Ξ) (rd_self_ty R Mr).
  Proof.
    intros * Hj; unfold ind_ty, rd_self_ty, im_params, im_nn; cbn [im_nparams ind_uparams ind_sort].
    rewrite (member_sort _ (List.nth_error_In _ _ Hj)), List.app_assoc, ctx_pi_app; reflexivity.
  Qed.

  (** The frames' parameters, the outer part of the filed group's uniform
      ones. *)
  Lemma frames_ass : tele_ass (gs_tele Ξ).
  Proof.
    pose proof (decl_typed_ass _ _ _ filed_decl_typed) as H; cbn [ind_uparams] in H.
    unfold tele_ass in *; apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  Lemma frames_scoped : ctx_scoped 0 (gs_tele Ξ).
  Proof.
    pose proof (decl_closed_uparams _ filed_decl_closed) as H; cbn [ind_uparams] in H.
    apply ctx_scoped_app in H as [_ H]; exact H.
  Qed.

  Lemma frames_mvc : ctx_mvc (gs_tele Ξ).
  Proof.
    pose proof (decl_mvc_uparams _ (decl_typed_mvc _ _ _ filed_decl_typed)) as H; cbn [ind_uparams] in H.
    unfold ctx_mvc in *; apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  Lemma frames_wf : ⊢ Θ ⍮ Ξf ⍮ gs_tele Ξ.
  Proof. pose proof (decl_typed_uparams_field _ _ _ filed_decl_typed) as H; cbn [ind_uparams] in H; exact (ctx_app_wf_tail _ _ _ _ H). Qed.

  (** The type former of a declared member at the frames' parameters is of
      its [Self]'s type. *)
  Lemma self_frames_typed : forall i Mr, List.nth_error (raw_decl_members R) i = Some Mr ->
      Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ apps (a_ind p i) (vars_from 0 t) : rd_self_ty R Mr.
  Proof.
    intros * Hi.
    destruct (Forall2_nth_error_l _ _ _ _ _ Hcls Hi) as (cs & Hcs & _).
    destruct (filed_member _ _ _ Hi Hcs) as (cs' & _ & Hk).
    set (Mi := mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') in *.
    pose proof filed_decl_typed as HD; pose proof filed_decl_closed as Hc.
    pose proof (filed_ind_ty _ _ cs' Hi) as Hty; fold Mi in Hty.
    assert (Hlt : i < ind_ndecl D) by (rewrite filed_ndecl; unfold rd_n; apply List.nth_error_Some; congruence).
    pose proof (wf_ind _ _ _ _ _ _ _ frames_wf filed_lookup Hk Hlt) as Hind; rewrite Hty in Hind.
    (** The [Self]'s type over the frames' parameters: typed, scoped and
        free of module variables. *)
    pose proof (member_params_wf _ _ _ _ _ HD Hk) as HP.
    destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([j Hj] & _).
    unfold im_params in HP, Hj; cbn [im_nparams ind_uparams] in HP, Hj; rewrite List.app_assoc in HP, Hj.
    destruct (ctx_pi_wf _ _ _ _ _ _ HP Hj) as [j' Hj'].
    assert (EB : ctx_pi (raw_member_nparams Mr ++ raw_decl_uparams R) (ind_sort D)[wk_shiftn (im_nn Mi)]ʷ = rd_self_ty R Mr)
      by (unfold rd_self_ty, im_nn; cbn [ind_sort im_nparams]; rewrite (member_sort _ (List.nth_error_In _ _ Hi)); reflexivity).
    change (im_nparams Mi) with (raw_member_nparams Mr) in Hj'; rewrite EB in Hj'.
    assert (HsB : exp_scoped t (rd_self_ty R Mr)).
    { rewrite <- EB; pose proof (decl_closed_params _ _ _ Hc Hk) as Hs; unfold im_params in Hs; cbn [im_nparams ind_uparams Mi] in Hs.
      rewrite List.app_assoc in Hs; apply ctx_scoped_app in Hs as [Hs _]; rewrite Nat.add_0_r in Hs.
      apply ctx_pi_scoped; [ exact Hs |].
      eapply exp_scoped_wk; [ exact (decl_closed_sort _ Hc) |]; intros x Hx; cbn [ind_nu ind_uparams] in Hx.
      rewrite filed_nu in Hx; unfold wk_shiftn, im_nn, rd_nu in *; cbn [im_nparams Mi]; rewrite !List.length_app in *; lia. }
    assert (HmB : exp_mvc 0 (rd_self_ty R Mr)).
    { rewrite <- EB; pose proof (decl_typed_mvc _ _ _ HD) as Hm.
      destruct (decl_mvc_members _ Hm _ _ Hk) as (HnM & _ & _); pose proof (decl_mvc_uparams _ Hm) as HuM.
      cbn [ind_uparams im_nparams Mi] in HnM, HuM.
      apply ctx_pi_mvc.
      - pose proof (decl_closed_params_ass _ _ _ Hc Hk) as Ha; unfold im_params in Ha; cbn [im_nparams ind_uparams Mi] in Ha.
        rewrite List.app_assoc in Ha; unfold tele_ass in *; apply List.Forall_app in Ha as [Ha _]; exact Ha.
      - unfold ctx_mvc in HuM; apply List.Forall_app in HuM as [HuM _]; apply List.Forall_app; split; assumption.
      - eapply exp_mvc_mono; [| apply exp_mvc_wk; exact (decl_mvc_sort _ Hm) ]; lia. }
    replace (rd_self_ty R Mr) with ((rd_self_ty R Mr)[sb_of_list Id (vars_from 0 t)]).
    - eapply wf_apps_closed_pi; [ exact frames_ass | exact frames_scoped | exact HsB | exact Hj' | exact frames_wf | exact Hind
                                | rewrite length_vars_from; reflexivity |].
      pose proof (wf_vars_tele Θ Ξf nil (gs_tele Ξ) frames_ass frames_scoped frames_mvc) as H.
      cbn [List.app List.length] in H; exact (H frames_wf).
    - rewrite (exp_at_vars _ _ _ HsB HmB).
      apply (exp_scoped_wk_id _ _ _ HsB); intros; unfold wk_shiftn; lia.
  Qed.

  (** The [Self]s instantiated, a substitution from the frames'
      parameters. *)
  Lemma selfs_sub_typed : ⊢ Θ ⍮ Ξf ⍮ rd_selfs R ++ gs_tele Ξ ->
      Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ˢ sb_of_list Id (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n))
        : rd_selfs R ++ gs_tele Ξ.
  Proof.
    intros HS.
    assert (H : forall m, m <= n ->
      ⊢ Θ ⍮ Ξf ⍮ rd_selfs_from R 0 (List.firstn m (raw_decl_members R)) ++ gs_tele Ξ ->
      Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ˢ sb_of_list Id (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 m))
        : rd_selfs_from R 0 (List.firstn m (raw_decl_members R)) ++ gs_tele Ξ).
    { induction m as [| m IH]; intros Hm Hctx.
      - cbn; apply wf_sub_id; exact frames_wf.
      - destruct (List.nth_error (raw_decl_members R) m) as [Mm |] eqn:HMm;
          [| apply List.nth_error_None in HMm; unfold rd_n in Hm; lia ].
        rewrite (firstn_S_nth_error _ _ _ HMm) in Hctx |- * .
        rewrite rd_selfs_from_snoc in Hctx |- *; cbn [Nat.add] in Hctx |- *.
        rewrite List.length_firstn in Hctx |- *;
          replace (Nat.min m (List.length (raw_decl_members R))) with m in * by (unfold rd_n in Hm; lia).
        rewrite List.seq_S, List.map_app, sb_of_list_app; cbn [List.map sb_of_list Nat.add].
        destruct (ctx_decomp Hctx) as [Hctx' [i Hi]].
        eapply wf_sub_extend; [ apply IH; [ lia | exact Hctx' ] | exact Hi |].
        rewrite exp_sub_wk.
        rewrite (exp_sub_sb_eq _ _ Id).
        + rewrite exp_sub_id; exact (self_frames_typed _ _ HMm).
        + intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
          replace (x + m) with (List.length (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 m)) + x)
            by (rewrite List.length_map, List.length_seq; lia).
          apply sb_of_list_ge. }
    pose proof (H n (le_n _)) as H'; unfold rd_selfs; rewrite List.firstn_all2 in H' by (unfold rd_n; lia).
    exact (H' HS).
  Qed.

  (** The [Self]s instantiated, from the filed parameters of a declared
      member into the context its arguments are written in. *)
  Lemma base_sub : forall Mr, ⊢ Θ ⍮ Ξf ⍮ rm_pctx Ξ R Mr -> ⊢ Θ ⍮ Ξf ⍮ raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ ->
      Θ ⍮ Ξf ⍮ raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ ⊢ˢ sb_selfs p (List.length (raw_member_nparams Mr) + nu) n t : rm_pctx Ξ R Mr.
  Proof.
    intros Mr Hb HP; unfold rm_pctx in *.
    pose proof (selfs_sub_typed (ctx_app_wf_tail _ _ _ _ Hb)) as Hσ.
    pose proof (wf_sub_ext _ _ (tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn n)) _ _ _ Hσ) as H.
    assert (E : tele_sub (tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn n))
                (sb_of_list Id (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n)))
              = raw_member_nparams Mr ++ raw_decl_uparams R)
      by (pose proof (tele_wk_shiftn_sb_of_list (raw_member_nparams Mr ++ raw_decl_uparams R)
                        (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n)) Id) as E;
          rewrite length_self_insts, tele_sub_id in E; exact E).
    rewrite E, length_tele_wk, List.length_app, <- List.app_assoc in H.
    unfold sb_selfs, rd_nu; apply H; [ exact HP | exact Hb ].
  Qed.

  (** The arguments after [args1], as written with the [Self]s instantiated
      and as filed, give equal [Π]s into the member, when the arguments
      before give contexts the one below the other. *)
  Lemma conv_tail : forall j Mr Mj c gsall,
      List.nth_error (raw_decl_members R) j = Some Mr -> ind_member D j = Some Mj -> im_nparams Mj = raw_member_nparams Mr ->
      In (c, gsall) (im_cons Mj) ->
      forall pat args1 args gsr2, cls_args_in Θ Ξ (rm_pctx Ξ R Mr) nu (List.length (raw_member_nparams Mr) + nu) n pat args1 args gsr2 ->
      forall gs1 gs2, rcargs_num n Ks gsr2 = Some gs2 -> gsall = gs1 ++ gs2 -> pat = cargs_pat gs1 ->
      List.length args1 = List.length gs1 ->
      Θ ⍮ Ξf ⊢ tele_sub (rtele args1) (sb_selfs p (List.length (raw_member_nparams Mr) + nu) n t) ++ im_params D Mj
        ⊆ cargs_ctx p D Mj gs1 ++ im_params D Mj ->
      exists i, Θ ⍮ Ξf ⍮ tele_sub (rtele args1) (sb_selfs p (List.length (raw_member_nparams Mr) + nu) n t) ++ im_params D Mj
        ⊢ ctx_pi (tele_sub (rtele args) (sb_selfs p (List.length args1 + (List.length (raw_member_nparams Mr) + nu)) n t))
            (ind_mty p D j (ind_uvars D (im_nn Mj) (List.length gsall)) (vars_from (List.length gsall) (im_nn Mj)))
        ≈ ctx_pi (cargs_ctx_aux p D (im_nn Mj) pat gs2)
            (ind_mty p D j (ind_uvars D (im_nn Mj) (List.length gsall)) (vars_from (List.length gsall) (im_nn Mj)))
        : Typeω@i.
  Proof.
    intros j Mr Mj c gsall Hj Hk Hnp Hin.
    set (np := List.length (raw_member_nparams Mr) + nu).
    induction 1 as [pat args1 | pat args1 y T args g gsr Hg Hgs IH]; intros gs1 gs2 Hn Hall Hpat Hlen Hsub.
    - (** No argument left: the result type. *)
      cbn in Hn; injection Hn as <-; rewrite List.app_nil_r in Hall; subst gsall.
      pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ filed_decl_typed _ _ Hk) Hin) as Hcon.
      destruct (con_cod_typed _ _ _ _ _ _ _ _ filed_wf (decls_of_ctx _ _ _ (wf_ctx_empty _ _ filed_wf)) filed_lookup Hk Hcon)
        as [i Hi].
      exists i; cbn [rtele tele_sub ctx_pi List.rev List.map cargs_ctx_aux].
      apply wf_exp_eq_refl.
      pose proof (ctx_sub_escape _ _ _ _ Hsub) as Hid.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hi Hid) as H; rewrite !exp_sub_id in H; exact H.
    - (** An argument: equal at its type as written and as filed, then the
          rest. *)
      cbn [rcargs_num] in Hn.
      destruct (rcarg_num n Ks g) as [g' |] eqn:Eg; [| discriminate ].
      destruct (rcargs_num n Ks gsr) as [gs2' |] eqn:Egs; [| discriminate ].
      injection Hn as <-.
      set (τ := sb_selfs p (List.length args1 + np) n t).
      (** The argument as classified, as written or as its normal form, and
          its filed entry. *)
      assert (HT' : exists grp recs T', cls_arg grp recs nu np n pat T' = Some g /\
                (T' = T \/ exists i, Θ ⍮ Ξ ⍮ rtele args1 ++ rm_pctx Ξ R Mr ⊢ T ≈ T' : Typeω@i)).
      { destruct Hg as [g0 Hc | i W g0 _ HTt HW Hc]; [ exists grp_none, rec_none, T; split; [ exact Hc | left; reflexivity ] |].
        exists (grp_info Θ Ξ), (rec_info Θ Ξ), (nf_to_exp W); split; [ exact Hc | right; exists i ].
        exact (@soundness_ty' (gc_mk Θ Ξ) _ _ _ _ HTt HW). }
      destruct HT' as (grp & recs & T' & Hc & HTT).
      assert (Hentry : T'[τ] = carg_entry p D (im_nn Mj) pat g').
      { unfold τ; replace (List.length args1) with (List.length pat) by (rewrite Hpat, length_cargs_pat; lia).
        unfold im_nn; rewrite Hnp.
        exact (cls_arg_filed p D Ks nu n t (List.length (raw_member_nparams Mr)) filed_nu filed_mty_decl filed_view grp recs
                 _ _ _ _ Hc Eg). }
      assert (EP : im_params D Mj = raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ) by (unfold im_params; rewrite Hnp; reflexivity).
      (** The filed entry is a type after the filed arguments before it. *)
      assert (Hin' : In (c, (gs1 ++ g' :: nil) ++ gs2') (im_cons Mj))
        by (rewrite <- List.app_assoc; cbn; rewrite <- Hall; exact Hin).
      destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ filed_wf (decls_of_ctx _ _ _ (wf_ctx_empty _ _ filed_wf)) filed_lookup Hk Hin'
                  (gs1 ++ g' :: nil) gs2' eq_refl) as (HRk & _ & _).
      rewrite cargs_ctx_snoc, cargs_ctx_aux_single, <- Hpat in HRk; cbn [List.app] in HRk.
      destruct (ctx_decomp HRk) as [_ [i1 HT'i]].
      pose proof (ctx_sub_escape _ _ _ _ Hsub) as Hid.
      assert (HT'L : Θ ⍮ Ξf ⍮ tele_sub (rtele args1) (sb_selfs p np n t) ++ im_params D Mj ⊢ T'[τ] : Typeω@i1)
        by (rewrite Hentry; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HT'i Hid) as H; rewrite !exp_sub_id in H; exact H).
      (** The argument as written and as classified are equal, the [Self]s
          instantiated. *)
      assert (HTe : exists i2, Θ ⍮ Ξf ⍮ tele_sub (rtele args1) (sb_selfs p np n t) ++ im_params D Mj
                                 ⊢ T[τ] ≈ T'[τ] : Typeω@i2).
      { destruct HTT as [-> | [i2 HTe]]; [ exists i1; apply wf_exp_eq_refl; exact HT'L |].
        exists i2.
        pose proof (proj1 (proj2 (proj2 (emb_preserves_wf _ _ _ _ filed_emb))) _ _ _ _ HTe) as HTe'.
        pose proof (presup_exp_eq_ctx HTe') as Hraw.
        assert (Hb : ⊢ Θ ⍮ Ξf ⍮ rm_pctx Ξ R Mr) by exact (ctx_app_wf_tail _ _ _ _ Hraw).
        assert (HP : ⊢ Θ ⍮ Ξf ⍮ raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ)
          by (rewrite <- EP; exact (member_params_wf _ _ _ _ _ filed_decl_typed Hk)).
        pose proof (wf_sub_ext _ _ (rtele args1) _ _ _ (base_sub Mr Hb HP)) as Hτ.
        rewrite <- EP in Hτ; specialize (Hτ (ctx_sub_dom _ _ _ _ Hsub) Hraw).
        rewrite length_rtele in Hτ; unfold sb_selfs in Hτ; rewrite <- sb_qn_plus in Hτ;
          fold (sb_selfs p (List.length args1 + np) n t) in Hτ.
        exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HTe' Hτ). }
      destruct HTe as [i2 HTe].
      assert (HTL : Θ ⍮ Ξf ⍮ tele_sub (rtele args1) (sb_selfs p np n t) ++ im_params D Mj ⊢ T[τ] : Typeω@i2)
        by (gen_presups; assumption).
      set (m := max i1 i2).
      (** The context after it. *)
      assert (Hsub' : Θ ⍮ Ξf ⊢ tele_sub (rtele (args1 ++ (y, T) :: nil)) (sb_selfs p np n t) ++ im_params D Mj
                        ⊆ cargs_ctx p D Mj (gs1 ++ g' :: nil) ++ im_params D Mj).
      { rewrite rtele_app, tele_sub_app; cbn [rtele List.map List.rev List.app tele_sub centry_sub List.length snd].
        rewrite length_rtele.
        rewrite cargs_ctx_snoc, cargs_ctx_aux_single, <- Hpat, <- Hentry; cbn [List.app].
        change (sb_qn 0 ?x) with x.
        replace (sb_qn (List.length args1) (sb_selfs p np n t)) with τ
          by (unfold τ, sb_selfs; rewrite sb_qn_plus; reflexivity).
        eapply ctx_sub_extend with (i := m);
          [ exact Hsub | rewrite Hentry; eapply lift_exp_ge; [| exact HT'i ]; lia | eapply lift_exp_ge; [| exact HTL ]; lia
          | apply wf_subtyp_refl' with (i := i2); exact HTe ]. }
      assert (Hpat' : rcarg_bit g :: pat = cargs_pat (gs1 ++ g' :: nil))
        by (rewrite cargs_pat_snoc, <- (rcarg_num_bit _ _ _ _ Eg), Hpat; reflexivity).
      destruct (IH (gs1 ++ g' :: nil) gs2' eq_refl ltac:(rewrite <- List.app_assoc; exact Hall) Hpat'
                  ltac:(rewrite !List.length_app, Hlen; reflexivity) Hsub') as [j0 Hj0].
      exists (max m j0).
      (** The two sides as [Π]s. *)
      rewrite rtele_cons, tele_sub_app; cbn [tele_sub centry_sub List.length]; rewrite ctx_pi_snoc.
      assert (Ecg : cargs_ctx_aux p D (im_nn Mj) pat (g' :: gs2')
                    = cargs_ctx_aux p D (im_nn Mj) (rcarg_bit g :: pat) gs2' ++ ce_ass (carg_entry p D (im_nn Mj) pat g') :: nil)
        by (rewrite (rcarg_num_bit _ _ _ _ Eg); destruct g'; reflexivity).
      rewrite Ecg, ctx_pi_snoc.
      rewrite rtele_app, tele_sub_app in Hj0; cbn [rtele List.map List.rev List.app tele_sub centry_sub List.length snd] in Hj0.
      rewrite length_rtele, List.length_app in Hj0; cbn [List.length] in Hj0.
      replace (List.length args1 + 1 + np) with (1 + (List.length args1 + np)) in Hj0 by lia.
      assert (E1 : sb_qn (List.length args1) (sb_selfs p np n t) = τ) by (unfold τ, sb_selfs; rewrite sb_qn_plus; reflexivity).
      assert (E2 : sb_selfs p (1 + (List.length args1 + np)) n t = sb_qn 1 τ)
        by (unfold τ, sb_selfs; rewrite sb_qn_plus; reflexivity).
      change (sb_qn 0 ?x) with x in Hj0 |- *.
      rewrite E1, E2 in Hj0.
      rewrite <- Hentry.
      eapply wf_exp_eq_pi_cong_large;
        [ eapply lift_exp_ge; [| exact HTL ]; lia | eapply lift_exp_eq_ge; [| exact HTe ]; lia
        | eapply lift_exp_eq_ge; [| exact Hj0 ]; lia ].
  Qed.

  (** A constructor of a declared member is filed at a type equal to the
      user's. *)
  Lemma member_con_ty : forall j Mr c args, List.nth_error (raw_decl_members R) j = Some Mr -> In (c, args) (raw_member_cons Mr) ->
      filed_con_ty Θ Ξf p j c (user_con_ty p R Mr j (gs_tele Ξ) args).
  Proof.
    intros * Hj Hin.
    destruct (Forall2_nth_error_l _ _ _ _ _ Hcls Hj) as (cs & Hcs & Hcl).
    destruct (Forall2_in_left _ _ _ _ Hcl Hin) as ([c' gsr] & Hin' & Heq & Hc); cbn [fst snd] in Heq, Hc; subst c'.
    destruct (filed_member _ _ _ Hj Hcs) as (cs' & Hcs' & Hk).
    set (Mj := mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') in *.
    destruct (rcons_num_in _ _ _ _ _ _ Hcs' Hin') as (gs & Hgs & Hing).
    assert (HinM : In (c, gs) (im_cons Mj)) by exact Hing.
    pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ filed_decl_typed _ _ Hk) HinM) as Hcon.
    apply (mk_filed_con_ty _ _ _ _ _ _ D Mj gs filed_lookup Hk Hcon).
    pose proof (cls_args_in_length _ _ _ _ _ _ _ _ _ _ Hc) as Hlen.
    assert (Hjn : j < n) by (unfold rd_n; apply List.nth_error_Some; congruence).
    unfold con_ty, user_con_ty, cargs_ctx; rewrite ctx_pi_sub.
    set (np := List.length (raw_member_nparams Mr) + nu) in *.
    rewrite length_rtele.
    assert (Lgs : List.length gs = List.length args).
    { rewrite <- Hlen; clear -Hgs; revert gs Hgs; induction gsr as [| g gsr IH]; intros gs H; cbn in H;
        [ injection H as <-; reflexivity |].
      destruct (rcarg_num n Ks g); [| discriminate ]; destruct (rcargs_num n Ks gsr) eqn:E; [| discriminate ].
      injection H as <-; cbn; f_equal; apply IH; reflexivity. }
    (** The result type: [Self_j] at the member's parameters is the type
        former at the frames' and the member's parameters. *)
    assert (Eres : (apps (a_var (List.length args + np + (n - 1 - j))) (vars_from (List.length args) np))
                     [sb_qn (List.length args) (sb_selfs p np n t)]
                   = ind_mty p D j (ind_uvars D (im_nn Mj) (List.length gs)) (vars_from (List.length gs) (im_nn Mj))).
    { replace (sb_qn (List.length args) (sb_selfs p np n t)) with (sb_selfs p (List.length args + np) n t)
        by (unfold sb_selfs; rewrite sb_qn_plus; reflexivity).
      rewrite apps_exp_sub, self_var_sub by lia.
      replace (n - 1 - (List.length args + np + (n - 1 - j) - (List.length args + np))) with j by lia.
      unfold sb_selfs at 1; rewrite vars_from_sub by lia.
      rewrite (filed_mty_decl _ _ _ Hjn), <- apps_exp_app; f_equal.
      unfold ind_uvars; rewrite filed_nu, Lgs; cbn [im_nn im_nparams Mj]; unfold np.
      change (im_nn Mj) with (List.length (raw_member_nparams Mr)).
      set (a := List.length args); set (k := List.length (raw_member_nparams Mr)).
      replace (k + nu) with (nu + k) by lia; rewrite <- (vars_from_app a nu k).
      replace (nu + t) with (t + nu) by lia; rewrite <- (vars_from_app (a + k) t nu).
      rewrite List.app_assoc; do 3 f_equal; lia. }
    rewrite Eres.
    (** The arguments, from none before. *)
    assert (HP : ⊢ Θ ⍮ Ξf ⍮ im_params D Mj) by exact (member_params_wf _ _ _ _ _ filed_decl_typed Hk).
    assert (Hsub0 : Θ ⍮ Ξf ⊢ tele_sub (rtele nil) (sb_selfs p np n t) ++ im_params D Mj ⊆ cargs_ctx p D Mj nil ++ im_params D Mj)
      by (cbn; apply ctx_sub_refl; exact HP).
    destruct (conv_tail j Mr Mj c gs Hj Hk eq_refl HinM nil nil args gsr Hc nil gs Hgs eq_refl eq_refl eq_refl Hsub0) as [i Hi].
    cbn [rtele tele_sub List.app List.length List.rev List.map] in Hi; rewrite Nat.add_0_l in Hi.
    assert (HP0 : ⊢ Θ ⍮ Ξf ⍮ im_params D Mj ++ ⋅) by (rewrite List.app_nil_r; exact HP).
    destruct (ctx_pi_ass_eq _ _ _ ⋅ _ _ _ (decl_closed_params_ass _ _ _ filed_decl_closed Hk) HP0
                ltac:(rewrite List.app_nil_r; exact Hi)) as [i' Hi'].
    exists i'; apply wf_exp_eq_sym; exact Hi'.
  Qed.

End ConTypes.

(** A run of a group's declaration files, for each declared member, the
    constructors the user wrote, at types equal to the user's with the
    [Self]s the members' type formers at the frames' parameters, in the
    global context the run makes. *)
Theorem run_cmd_ind_con_types : forall load_path read to_core ch B Rb Θ Ξ pv R B' Rb' Θ' Ξ' Mr0 Mrs,
    Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind pv R ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> ⊢ᵍ Θ ⍮ Ξ ->
    raw_decl_members R = Mr0 :: Mrs ->
    forall j Mr c args, List.nth_error (raw_decl_members R) j = Some Mr -> In (c, args) (raw_member_cons Mr) ->
      filed_con_ty Θ' Ξ' (ind_qname Ξ (raw_member_name Mr0)) j c
        (user_con_ty (ind_qname Ξ (raw_member_name Mr0)) R Mr j (gs_tele Ξ) args).
Proof.
  intros * Hr HΞ HMr * Hj Hin.
  inversion Hr; subst.
  (** The group as filed: its declared members, then its views. *)
  match goal with
  | Hfiled : rd_filed _ _ R _ _ _ _ _ = Some _ |- _ => pose proof (rd_filed_uparams _ _ _ _ _ _ _ _ _ Hfiled) as Hu
  end.
  match goal with
  | HM : raw_decl_members R = _ :: _, Hfiled : rd_filed _ _ R _ _ _ _ _ = Some _ |- _ =>
      rewrite HMr in HM; injection HM as <- <-;
      unfold rd_filed in Hfiled; rewrite HMr in Hfiled;
      destruct (rms_filed _ _ _ _ _) as [Ms |] eqn:Hms; [| discriminate ];
      destruct (rvs_filed _ _ _ _ _ _ _ _ _ _) as [Mvs |] eqn:Hmvs; [| discriminate ];
      injection Hfiled as <-; rewrite <- HMr in Hms
  end.
  (** The declared members, each with its module, file no unit and embed the
      stack; the group is found at its first member's path. *)
  match goal with
  | Hm : run_ind_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?Ξf |- _ =>
      pose proof Hm as Hm'; rewrite HMr in Hm'; cbn [List.map] in Hm';
      pose proof (ind_members_run_lookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' HΞ Hu) as Hlk;
      destruct (ind_members_run_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HΞ Hu) as [-> -> -> Hwf1 Hsub1]
  end.
  (** The recursor module, if any, is filed after the members. *)
  match goal with
  | Hrec : run_cmds _ _ _ _ _ _ _ _ (rec_cmds _ _ _ _ _) _ _ _ _, Hwf1 : ⊢ᵍ Θ ⍮ ?Ξf |- _ =>
      destruct (rec_cmds_run_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrec Hwf1) as [-> -> -> Hwf Hsub];
      apply (filed_con_ty_emb Θ Ξf); [ constructor; assumption |]
  end.
  eapply member_con_ty; try eassumption; constructor; assumption.
Qed.
