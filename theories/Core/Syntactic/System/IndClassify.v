(** * Classifying the Arguments of a Declaration as Written

    A declaration as written ([raw_decl]) has the declared type as an
    ordinary variable [Self] in its constructors' argument types, and every
    argument a binder.  The command classifies each argument type
    ([cls_arg]): one in which [Self] does not occur, nor any recursive
    argument before it, is non-recursive, strengthened past them; [Self]
    applied to such terms is recursive, of the shape [pt_self 0], and so is
    a function into it over domains in which it does not occur, of the
    shape [pt_pi B (… (pt_self 0))] ([cls_sh]); anything else is rejected.  The classification is syntactic: it decides
    membership in the image of the weakening [cls_wk] by computing the
    candidate and comparing ([img_dec]).  A later stage classifies normal
    forms instead.

    The structural declaration it files has the user's constructor types,
    with [Self] the type former at the uniform parameters
    ([cls_con_ty]). *)

From Stdlib Require Import Lia List PeanoNat String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command.
From Mctt.Core.Syntactic.System Require Import IndSyntax.
Import Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Decidable Equality of Terms *)

Definition qname_eq_dec : forall (x y : qname), {x = y} + {x <> y}.
Proof. decide equality; apply list_eq_dec, string_dec. Defined.

Fixpoint exp_eq_dec (M N : exp) {struct M} : {M = N} + {M <> N}
with modexp_eq_dec (M N : modexp) {struct M} : {M = N} + {M <> N}
with bnd_eq_dec (M N : bnd) {struct M} : {M = N} + {M <> N}
with gunit_eq_dec (M N : gunit) {struct M} : {M = N} + {M <> N}
with moddef_eq_dec (M N : moddef) {struct M} : {M = N} + {M <> N}
with gmod_eq_dec (M N : gmod) {struct M} : {M = N} + {M <> N}
with gentry_eq_dec (M N : gentry) {struct M} : {M = N} + {M <> N}
with centry_eq_dec (M N : centry) {struct M} : {M = N} + {M <> N}.
Proof.
  all: decide equality;
    first [ apply Nat.eq_dec | apply string_dec | apply qname_eq_dec | apply bool_dec
          | apply list_eq_dec, string_dec | apply o2_eq_dec | idtac ].
  all: try (decide equality; fail).
  - (* the branches of an eliminator *)
    revert l0; induction l as [| [[c k] B] l IHl]; intros [| [[c' k'] B'] l0];
      try (right; discriminate); [ left; reflexivity |].
    destruct (string_dec c c') as [<- |]; [| right; congruence ].
    destruct (Nat.eq_dec k k') as [<- |]; [| right; congruence ].
    destruct (exp_eq_dec B B') as [<- |]; [| right; congruence ].
    destruct (IHl l0) as [<- |]; [ left; reflexivity | right; congruence ].
  - (* the items of an open *)
    apply list_eq_dec; intros; repeat (decide equality || apply string_dec || apply bool_dec).
  - (* a declaration *)
    try clear g g0.
    destruct i as [nu ps S cs], i0 as [nu' ps' S' cs'].
    destruct (Nat.eq_dec nu nu') as [<- |]; [| right; congruence ].
    destruct (exp_eq_dec S S') as [<- |]; [| right; congruence ].
    assert (Hps : {ps = ps'} + {ps <> ps'}).
    { revert ps'; induction ps as [| e ps IH]; intros [| e' ps']; try (right; discriminate); [ left; reflexivity |].
      destruct (centry_eq_dec e e') as [<- |]; [| right; congruence ].
      destruct (IH ps') as [<- |]; [ left; reflexivity | right; congruence ]. }
    destruct Hps as [<- |]; [| right; congruence ].
    assert (Hcs : {cs = cs'} + {cs <> cs'}).
    { revert cs'; induction cs as [| [c gs] cs IH]; intros [| [c' gs'] cs']; try (right; discriminate); [ left; reflexivity |].
      destruct (string_dec c c') as [<- |]; [| right; congruence ].
      assert (Hgs : {gs = gs'} + {gs <> gs'}).
      { revert gs'; induction gs as [| g gs IHg]; intros [| g' gs']; try (right; discriminate); [ left; reflexivity |].
        assert (Hg : {g = g'} + {g <> g'}).
        { destruct g as [A | t], g' as [A' | t']; try (right; discriminate).
          - destruct (exp_eq_dec A A') as [<- |]; [ left; reflexivity | right; congruence ].
          - assert (Ht : {t = t'} + {t <> t'}).
            { revert t'; induction t as [k Ps | k Ps | A t IHt]; intros [k' Ps' | k' Ps' | A' t'];
                try (right; discriminate).
              1, 2: destruct (Nat.eq_dec k k') as [<- |]; [| right; congruence ];
                    assert (HP : {Ps = Ps'} + {Ps <> Ps'})
                      by (revert Ps'; induction Ps as [| P Ps IHP]; intros [| P' Ps']; try (right; discriminate);
                          [ left; reflexivity |];
                          destruct (exp_eq_dec P P') as [<- |]; [| right; congruence ];
                          destruct (IHP Ps') as [<- |]; [ left; reflexivity | right; congruence ]);
                    destruct HP as [<- |]; [ left; reflexivity | right; congruence ].
              destruct (exp_eq_dec A A') as [<- |]; [| right; congruence ].
              destruct (IHt t') as [<- |]; [ left; reflexivity | right; congruence ]. }
            destruct Ht as [<- |]; [ left; reflexivity | right; congruence ]. }
        destruct Hg as [<- |]; [| right; congruence ].
        destruct (IHg gs') as [<- |]; [ left; reflexivity | right; congruence ]. }
      destruct Hgs as [<- |]; [| right; congruence ].
      destruct (IH cs') as [<- |]; [ left; reflexivity | right; congruence ]. }
    destruct Hcs as [<- |]; [ left; reflexivity | right; congruence ].
Defined.

(** ** The Image of a Pattern Weakening

    [wk_pat pat] has the left inverse [unwk_pat pat], so a term is in its
    image exactly when it is the image of its own preimage candidate. *)

Fixpoint unwk_pat (pat : list bool) : wk :=
  match pat with
  | nil => fun x => x
  | false :: pat' => wk_q (unwk_pat pat')
  | true :: pat' => wk_compose pred (unwk_pat pat')
  end.

Lemma unwk_pat_wk_pat : forall pat x, unwk_pat pat (wk_pat pat x) = x.
Proof.
  induction pat as [| [] pat IH]; intros x; cbn; [ reflexivity | apply IH |].
  destruct x; cbn; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma exp_wk_pat_inv : forall pat A, A[wk_pat pat]ʷ[unwk_pat pat]ʷ = A.
Proof.
  intros; rewrite exp_wk_wk; apply exp_wk_id_ext; intros x; cbn; apply unwk_pat_wk_pat.
Qed.

Definition img_dec (pat : list bool) (T : exp) :
  {A | T = A[wk_pat pat]ʷ} + {forall A, T <> A[wk_pat pat]ʷ} :=
  match exp_eq_dec T (T[unwk_pat pat]ʷ)[wk_pat pat]ʷ with
  | left E => inleft (exist _ _ E)
  | right N => inright (fun A E => N (eq_trans E (f_equal (fun B => B[wk_pat pat]ʷ)
                                                   (eq_sym (eq_trans (f_equal (fun B => B[unwk_pat pat]ʷ) E)
                                                                     (exp_wk_pat_inv pat A))))))
  end.

(** The arguments' pattern: the recursive arguments before, the [np]
    parameters of the declaration, then [Self], outside them. *)
Definition cls_wk (np : nat) (gs1 : list carg) : wk := wk_pat (cargs_pat gs1 ++ List.repeat false np ++ true :: nil).


Lemma cls_wk_eq : forall np gs1 x,
    cls_wk np gs1 x = wk_qn (List.length gs1 + np) wk_shift (wk_pat (cargs_pat gs1) x).
Proof.
  intros; unfold cls_wk; rewrite List.app_assoc, wk_pat_app_true, wk_pat_app_false, List.length_app,
    List.repeat_length, length_cargs_pat; reflexivity.
Qed.

Lemma wk_qn_shift_ne : forall n y, wk_qn n wk_shift y <> n.
Proof.
  intros n y; destruct (Nat.lt_ge_cases y n).
  - rewrite wk_qn_lt by assumption; lia.
  - rewrite wk_qn_ge by assumption; cbn; lia.
Qed.

(** Under [d] domains of a function shape: the domains are no recursive
    arguments.  [cls_wkd 0] is [cls_wk]. *)
Definition cls_wkd (d np : nat) (gs1 : list carg) : wk :=
  wk_pat (List.repeat false d ++ cargs_pat gs1 ++ List.repeat false np ++ true :: nil).

Lemma cls_wkd_eq : forall d np gs1 x,
    cls_wkd d np gs1 x = wk_qn (d + List.length gs1 + np) wk_shift (wk_pat (List.repeat false d ++ cargs_pat gs1) x).
Proof.
  intros; unfold cls_wkd; rewrite !List.app_assoc, wk_pat_app_true, wk_pat_app_false, !List.length_app,
    !List.repeat_length, length_cargs_pat; reflexivity.
Qed.

Lemma cls_wkd_avoids : forall d np gs1 x, cls_wkd d np gs1 x <> d + List.length gs1 + np.
Proof. intros; rewrite cls_wkd_eq; apply wk_qn_shift_ne. Qed.

(** ** The Classification

    [nu] and [np] are the declaration's own uniform parameters and all its
    own parameters: those of the enclosing frames are not written. *)

(** A shape under [d] of its domains: [Self] at the uniform parameters, then
    at terms in which it does not occur; or a [Π] over a domain in which it
    does not occur, into a shape.  [Self] thus occurs only strictly
    positively. *)
Inductive cls_sh (nu np : nat) (gs1 : list carg) : nat -> exp -> ptyp -> Prop :=
| cls_sh_self : forall d Ps,
    cls_sh nu np gs1 d
      (apps (a_var (d + List.length gs1 + np))
         (vars_from (d + List.length gs1 + (np - nu)) nu ++ List.map (fun P => P[cls_wkd d np gs1]ʷ) Ps))
      (pt_self 0 Ps)
| cls_sh_pi : forall d B T t,
    cls_sh nu np gs1 (S d) T t ->
    cls_sh nu np gs1 d (a_pi B[cls_wkd d np gs1]ʷ T) (pt_pi B t).

Inductive cls_arg (nu np : nat) (gs1 : list carg) : exp -> carg -> Prop :=
(** [Self] does not occur, nor any recursive argument before. *)
| cls_free : forall A, cls_arg nu np gs1 A[cls_wk np gs1]ʷ (ca_arg A)
(** A recursive argument, of a shape. *)
| cls_rec : forall T t, cls_sh nu np gs1 0 T t -> cls_arg nu np gs1 T (ca_rec t).

Inductive cls_args (nu np : nat) : list carg -> list (string * exp) -> list carg -> Prop :=
| cls_args_nil : forall gs1, cls_args nu np gs1 nil nil
| cls_args_cons : forall gs1 y T args g gs,
    cls_arg nu np gs1 T g -> cls_args nu np (gs1 ++ g :: nil) args gs -> cls_args nu np gs1 ((y, T) :: args) (g :: gs).

(** The structural declaration of a declaration as written. *)
Definition rd_filed (R : raw_decl) (cs : list (string * list carg)) : ind_decl :=
  mk_ind (rd_nu R) (rd_params R) (rd_sort R) cs.

(** ** The Classification Is Functional *)

Fixpoint app_head (M : exp) : exp :=
  match M with
  | a_app M _ => app_head M
  | _ => M
  end.

Lemma app_head_wk : forall M φ, app_head M[φ]ʷ = (app_head M)[φ]ʷ.
Proof. induction M; intros; cbn; auto. Qed.

Lemma app_head_apps : forall Ms M, app_head (apps M Ms) = app_head M.
Proof. induction Ms as [| N Ms IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma app_head_apps_var : forall Ms x, app_head (apps (a_var x) Ms) = a_var x.
Proof. intros; rewrite app_head_apps; reflexivity. Qed.

Fixpoint app_args (M : exp) : list exp :=
  match M with
  | a_app M N => app_args M ++ N :: nil
  | _ => nil
  end.

Lemma app_args_apps : forall Ms M, app_args (apps M Ms) = app_args M ++ Ms.
Proof.
  induction Ms as [| N Ms IH]; intros; cbn; [ rewrite List.app_nil_r; reflexivity |].
  rewrite IH; cbn; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma app_args_apps_var : forall Ms x, app_args (apps (a_var x) Ms) = Ms.
Proof. intros; rewrite app_args_apps; reflexivity. Qed.

Lemma apps_var_inj : forall Ms Ns x y, apps (a_var x) Ms = apps (a_var y) Ns -> x = y /\ Ms = Ns.
Proof.
  intros * E; split.
  - apply (f_equal app_head) in E; rewrite !app_head_apps_var in E; injection E; auto.
  - apply (f_equal app_args) in E; rewrite !app_args_apps_var in E; exact E.
Qed.

Lemma exp_wk_inj : forall pat A B, A[wk_pat pat]ʷ = B[wk_pat pat]ʷ -> A = B.
Proof.
  intros * E; rewrite <- (exp_wk_pat_inv pat A), <- (exp_wk_pat_inv pat B), E; reflexivity.
Qed.

Lemma map_wk_inj : forall pat Ps Qs,
    List.map (fun P => P[wk_pat pat]ʷ) Ps = List.map (fun P => P[wk_pat pat]ʷ) Qs -> Ps = Qs.
Proof.
  induction Ps as [| P Ps IH]; intros [| Q Qs] E; cbn in E; try discriminate; [ reflexivity |].
  injection E as E1 E2; rewrite (exp_wk_inj _ _ _ E1), (IH _ E2); reflexivity.
Qed.

Lemma cls_sh_not_free : forall nu np gs1 d T t, cls_sh nu np gs1 d T t -> forall A, T <> A[cls_wkd d np gs1]ʷ.
Proof.
  induction 1 as [d Ps | d B T t H IH]; intros A E.
  - apply (f_equal app_head) in E; rewrite app_head_wk, app_head_apps_var in E.
    destruct (app_head A); cbn in E; try discriminate.
    injection E as E; exact (cls_wkd_avoids _ _ _ _ (eq_sym E)).
  - destruct A; cbn in E; try discriminate.
    injection E as _ E; exact (IH _ E).
Qed.

Lemma cls_sh_functional : forall nu np gs1 d T t t', cls_sh nu np gs1 d T t -> cls_sh nu np gs1 d T t' -> t = t'.
Proof.
  intros * H; revert t'; induction H as [d Ps | d B T t H IH]; intros t' H'; inversion H'; subst.
  - match goal with E : apps (a_var _) _ = apps (a_var _) _ |- _ =>
      apply apps_var_inj in E as [_ E]; apply List.app_inv_head in E;
      unfold cls_wkd in E; rewrite (map_wk_inj _ _ _ E); reflexivity end.
  - exfalso; match goal with E : _ = _ |- _ =>
      apply (f_equal app_head) in E; rewrite !app_head_apps_var in E; cbn in E; discriminate end.
  - exfalso; match goal with E : _ = _ |- _ =>
      apply (f_equal app_head) in E; rewrite !app_head_apps_var in E; cbn in E; discriminate end.
  - match goal with E : B0[_]ʷ = B[_]ʷ, Hs : cls_sh _ _ _ _ T ?t0 |- _ =>
      unfold cls_wkd in E; rewrite (exp_wk_inj _ _ _ E), (IH _ Hs); reflexivity end.
Qed.

Lemma cls_arg_functional : forall nu np gs1 T g g', cls_arg nu np gs1 T g -> cls_arg nu np gs1 T g' -> g = g'.
Proof.
  intros * H H'; destruct H as [A | T t Hs]; inversion H' as [A' E | T' t' Hs' E]; subst.
  - unfold cls_wk in E; rewrite (exp_wk_inj _ _ _ E); reflexivity.
  - exfalso; exact (cls_sh_not_free _ _ _ _ _ _ Hs' A eq_refl).
  - exfalso; exact (cls_sh_not_free _ _ _ _ _ _ Hs A' eq_refl).
  - rewrite (cls_sh_functional _ _ _ _ _ _ _ Hs Hs'); reflexivity.
Qed.

(** ** The Filed Constructor Types Are the User's

    The telescope of a constructor's arguments as written, innermost first;
    [Self] instantiated as the generated definition of the type former, the
    former at the [t] parameters of the enclosing frames; and the user's
    type of the constructor, over the filed parameters, with [Self]
    instantiated: [Self] at all the declaration's own parameters, the
    uniform ones included. *)
Definition rtele (args : list (string * exp)) : ctx := List.rev (List.map (fun a => ce_ass (snd a)) args).

Definition self_inst (p : qname) (t : nat) : exp := apps (a_ind p) (vars_from 0 t).

Definition user_con_ty (p : qname) (D : ind_decl) (np : nat) (args : list (string * exp)) : typ :=
  ctx_pi (ind_params D)
    (ctx_pi (rtele args) (apps (a_var (List.length args + np)) (vars_from (List.length args) np)))
      [sb_qn np (Id,,self_inst p (ind_np D - np))].

Lemma cls_wk_sub : forall np gs1 A X,
    A[cls_wk np gs1]ʷ[sb_qn (List.length gs1 + np) (Id,,X)] = A[wk_pat (cargs_pat gs1)]ʷ.
Proof.
  intros; rewrite <- exp_sub_of_wk, exp_sub_sub, <- (exp_sub_of_wk A (wk_pat _)).
  apply exp_sub_sb_eq; intros x; rewrite sb_compose_var, !sb_of_wk_var; cbn [sentry_sub].
  rewrite cls_wk_eq.
  set (y := wk_pat (cargs_pat gs1) x); set (n := List.length gs1 + np).
  destruct (Nat.lt_ge_cases y n) as [Hy | Hy].
  - rewrite wk_qn_lt, sb_qn_lt by assumption; reflexivity.
  - rewrite wk_qn_ge by assumption; cbn [wk_shift].
    rewrite sb_qn_ge by lia; replace (S (y - n) + n - n) with (S (y - n)) by lia; cbn.
    f_equal; lia.
Qed.

Lemma cls_wkd_sub : forall d np gs1 A X,
    A[cls_wkd d np gs1]ʷ[sb_qn (d + List.length gs1 + np) (Id,,X)] = A[wk_pat (List.repeat false d ++ cargs_pat gs1)]ʷ.
Proof.
  intros; rewrite <- exp_sub_of_wk, exp_sub_sub, <- (exp_sub_of_wk A (wk_pat _)).
  apply exp_sub_sb_eq; intros x; rewrite sb_compose_var, !sb_of_wk_var; cbn [sentry_sub].
  rewrite cls_wkd_eq.
  set (y := wk_pat (List.repeat false d ++ cargs_pat gs1) x); set (n := d + List.length gs1 + np).
  destruct (Nat.lt_ge_cases y n) as [Hy | Hy].
  - rewrite wk_qn_lt, sb_qn_lt by assumption; reflexivity.
  - rewrite wk_qn_ge by assumption; cbn [wk_shift].
    rewrite sb_qn_ge by lia; replace (S (y - n) + n - n) with (S (y - n)) by lia; cbn.
    f_equal; lia.
Qed.

Lemma var_self_sub : forall n X, (a_var n)[sb_qn n (Id,,X)] = X[wk_shiftn n]ʷ.
Proof.
  intros; cbn [exp_sub]; rewrite sb_qn_ge by lia; replace (n - n) with 0 by lia; cbn; reflexivity.
Qed.

Lemma vars_from_wk_shiftn : forall n m k,
    List.map (fun M => M[wk_shiftn n]ʷ) (vars_from m k) = vars_from (m + n) k.
Proof.
  intros; unfold vars_from; rewrite List.map_map; apply List.map_ext; intros i; cbn; f_equal; lia.
Qed.

Lemma vars_from_sub_below : forall m j k σ, j + k <= m ->
    List.map (fun M => M[sb_qn m σ]) (vars_from j k) = vars_from j k.
Proof.
  intros * Hle; unfold vars_from; rewrite List.map_map; apply List.map_ext_in; intros i Hi.
  apply List.in_rev, List.in_seq in Hi; cbn [exp_sub]; rewrite sb_qn_lt by lia; reflexivity.
Qed.

Lemma apps_exp_app : forall Ms Ns M, apps M (Ms ++ Ns) = apps (apps M Ms) Ns.
Proof. induction Ms as [| N Ms IH]; intros; cbn; [ reflexivity | apply IH ]. Qed.

Lemma self_inst_wk : forall p t n, (self_inst p t)[wk_shiftn n]ʷ = apps (a_ind p) (vars_from n t).
Proof. intros; unfold self_inst; rewrite apps_exp_wk, vars_from_wk_shiftn; reflexivity. Qed.

Lemma cls_args_length : forall nu np gs1 args gs, cls_args nu np gs1 args gs -> List.length gs = List.length args.
Proof. induction 1; cbn; auto. Qed.

(** The type of a recursive argument as written, [Self] instantiated, is the
    type of its shape. *)
Lemma cls_sh_ty : forall p D t nu np gs1 d T s, cls_sh nu np gs1 d T s ->
    ind_nu D = nu + t -> ind_np D = np + t -> nu <= np ->
    T[sb_qn (d + List.length gs1 + np) (Id,,self_inst p t)] = ptyp_ty p D (List.repeat false d ++ cargs_pat gs1) s.
Proof.
  intros * H Hu Hp Hle; induction H as [d Ps | d B T s H IH].
  - rewrite apps_exp_sub, var_self_sub, self_inst_wk, List.map_app, vars_from_sub_below by lia.
    cbn [ptyp_ty ptyp_ps]; rewrite List.map_map, <- apps_exp_app, List.app_assoc.
    rewrite List.length_app, List.repeat_length, length_cargs_pat.
    unfold ind_uvars; replace (ind_nn D) with (np - nu) by (unfold ind_nn; lia).
    rewrite Hu; replace (d + List.length gs1 + np) with (d + List.length gs1 + (np - nu) + nu) by lia.
    rewrite vars_from_app; replace (t + nu) with (nu + t) by lia.
    do 2 f_equal; apply List.map_ext; intros P.
    replace (d + List.length gs1 + (np - nu) + nu) with (d + List.length gs1 + np) by lia; apply cls_wkd_sub.
  - cbn [exp_sub ptyp_ty]; f_equal; [ apply cls_wkd_sub | exact IH ].
Qed.

(** The arguments' context of the filed constructor is the one as written,
    [Self] instantiated. *)
Theorem cls_args_cargs_ctx : forall p D t nu np gs1 args gs, cls_args nu np gs1 args gs ->
    ind_nu D = nu + t -> ind_np D = np + t -> nu <= np ->
    cargs_ctx_aux p D (cargs_pat gs1) gs = tele_sub (rtele args) (sb_qn (List.length gs1 + np) (Id,,self_inst p t)).
Proof.
  intros * H Hu Hp Hle; induction H as [gs1 | gs1 y T args g gs Hg Hgs IH]; [ reflexivity |].
  unfold rtele; cbn [List.map List.rev]; fold (rtele args); rewrite tele_sub_app; cbn [tele_sub List.length].
  rewrite cargs_pat_snoc, List.length_app in IH; cbn [List.length] in IH.
  replace (List.length gs1 + 1 + np) with (S (List.length gs1 + np)) in IH by lia.
  destruct Hg as [A | T s Hs]; cbn [cargs_ctx_aux]; rewrite IH; cbn [sb_qn]; f_equal; cbn [centry_sub sb_qn snd].
  - rewrite cls_wk_sub; reflexivity.
  - do 2 f_equal; exact (eq_sym (cls_sh_ty p D t nu np gs1 0 T s Hs Hu Hp Hle)).
Qed.

(** A filed constructor's type is the user's. *)
Theorem cls_con_ty : forall p D t nu np args gs, cls_args nu np nil args gs ->
    ind_nu D = nu + t -> ind_np D = np + t -> nu <= np ->
    con_ty p D gs = user_con_ty p D np args.
Proof.
  intros * H Hu Hp Hle; unfold con_ty, user_con_ty, cargs_ctx; f_equal.
  rewrite ctx_pi_sub; unfold rtele at 2; rewrite List.length_rev, List.length_map; fold (rtele args).
  replace (ind_np D - np) with t by lia.
  rewrite (cls_args_cargs_ctx _ _ _ _ _ _ _ _ H Hu Hp Hle); cbn [List.length cargs_pat]; f_equal.
  rewrite <- sb_qn_plus, apps_exp_sub, var_self_sub, self_inst_wk, vars_from_sub_below by lia.
  rewrite <- apps_exp_app; unfold ind_pvars; rewrite (cls_args_length _ _ _ _ _ H).
  rewrite vars_from_app, Hp; do 2 f_equal; lia.
Qed.
