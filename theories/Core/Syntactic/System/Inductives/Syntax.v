(** * The Types of a Declaration under Weakening and Substitution

    What typing reads off a declaration ([Inductives]) commutes with the
    operations: the declaration is closed ([decl_closed]), so only the
    terms it is instantiated at move, and a motive moves under the binders
    of the scrutinee and the non-uniform parameters.  The laws are proved
    for substitutions; those for weakenings follow through [ι]. *)

From Stdlib Require Import Lia List PeanoNat Morphisms.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Export MemberLemmas.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Substitutions Built of Lists *)

Lemma sb_of_list_app : forall Ms Ns σ, sb_of_list σ (Ms ++ Ns) = sb_of_list (sb_of_list σ Ms) Ns.
Proof. induction Ms; intros; cbn; auto. Qed.

(** [sb_of_list ρ Ms] followed by [τ] is [q^|Ms| σ] followed by the list
    moved by [τ], when [ρ] followed by [τ] is [σ] followed by [ρ']. *)
Lemma sb_of_list_compose : forall Ms ρ τ σ ρ',
    sb_eq (ρ ⨟ τ) (σ ⨟ ρ') ->
    sb_eq (sb_of_list ρ Ms ⨟ τ) (sb_qn (List.length Ms) σ ⨟ sb_of_list ρ' (List.map (fun M => M[τ]) Ms)).
Proof.
  induction Ms as [| M Ms IH]; intros * H; cbn; [ exact H |].
  intros x; rewrite (IH _ τ (q σ) (ρ' ,, M[τ])).
  - cbn [sb_compose]; f_equal.
    pose proof (sb_qn_add (List.length Ms) 1 σ x) as Hq; cbn in Hq.
    rewrite Hq, Nat.add_1_r; reflexivity.
  - intros [| y]; cbn [sb_compose sb_extend]; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
    rewrite sentry_sub_shift_extend; apply H.
Qed.

Lemma sb_id_compose_comm : forall τ, sb_eq (Id ⨟ τ) (τ ⨟ Id).
Proof. intros τ x; cbn; rewrite sentry_sub_id; reflexivity. Qed.

Lemma exp_sub_sb_of_list : forall A Ms τ,
    A[sb_of_list Id Ms][τ] = A[sb_qn (List.length Ms) τ][sb_of_list Id (List.map (fun M => M[τ]) Ms)].
Proof.
  intros; rewrite !exp_sub_sub; apply exp_sub_sb_eq, sb_of_list_compose, sb_id_compose_comm.
Qed.

(** The variables the list sends are moved by [τ]. *)
Lemma sb_of_list_lt_compose : forall Ms τ x,
    x < List.length Ms -> sentry_sub (sb_of_list Id Ms x) τ = sb_of_list Id (List.map (fun M => M[τ]) Ms) x.
Proof.
  intros * Hx; pose proof (sb_of_list_compose Ms Id τ τ Id (sb_id_compose_comm τ) x) as H.
  cbn [sb_compose] in H; rewrite H, sb_qn_lt by assumption; reflexivity.
Qed.

(** A shift by [m] followed by [q^m τ] is [τ] followed by the shift. *)
Lemma sb_shiftn_qn_comm : forall m τ, sb_eq (ι (wk_shiftn m) ⨟ sb_qn m τ) (τ ⨟ ι (wk_shiftn m)).
Proof.
  intros m τ x; cbn [sb_compose sb_of_wk sentry_sub]; rewrite sentry_sub_of_wk, sb_qn_ge by (cbn; lia).
  cbn; replace (x + m - m) with x by lia; reflexivity.
Qed.

Lemma exp_shiftn_sub_qn : forall M s r τ,
    M[wk_shiftn s]ʷ[sb_qn (s + r) τ] = M[sb_qn r τ][wk_shiftn s]ʷ.
Proof.
  intros; apply exp_wk_sub_comm_ext; intros x.
  rewrite <- (sb_qn_add s r τ (wk_shiftn s x)), sb_qn_ge by (cbn; lia).
  cbn; replace (x + s - s) with x by lia; reflexivity.
Qed.

Corollary exp_shiftn_sub_qn0 : forall M s τ, M[wk_shiftn s]ʷ[sb_qn s τ] = M[τ][wk_shiftn s]ʷ.
Proof. intros; pose proof (exp_shiftn_sub_qn M s 0 τ) as H; rewrite Nat.add_0_r in H; exact H. Qed.

Lemma vars_from_sub : forall k n m τ,
    k + n <= m -> List.map (fun M => M[sb_qn m τ]) (vars_from k n) = vars_from k n.
Proof.
  intros * H; unfold vars_from; rewrite map_map; apply map_ext_in; intros i Hi.
  apply List.in_rev, List.in_seq in Hi; cbn; rewrite sb_qn_lt by lia; reflexivity.
Qed.

Lemma sb_of_list_cong : forall Ms σ τ, sb_eq σ τ -> sb_eq (sb_of_list σ Ms) (sb_of_list τ Ms).
Proof. induction Ms; intros * H; cbn; [ exact H | apply IHMs, sb_extend_cong, H ]. Qed.

(** A list filled over [β], followed by [τ], is the moved list over [β]
    followed by [τ]. *)
Lemma sb_of_list_compose_gen : forall Ms β τ,
    sb_eq (sb_of_list β Ms ⨟ τ) (sb_of_list (β ⨟ τ) (List.map (fun M => M[τ]) Ms)).
Proof.
  induction Ms as [| M Ms IH]; intros β τ; cbn [sb_of_list List.map]; [ reflexivity |].
  etransitivity; [ apply IH |]; apply sb_of_list_cong, sb_extend_compose.
Qed.

(** Lifting [σ] over the binders a list fills, then filling them, is
    filling them over [σ]. *)
Lemma sb_qn_of_list : forall Ms σ ρ,
    sb_eq (sb_qn (List.length Ms) σ ⨟ sb_of_list ρ Ms) (sb_of_list (σ ⨟ ρ) Ms).
Proof.
  induction Ms as [| M Ms IH]; intros; cbn; [ reflexivity |].
  assert (Hq : sb_eq (sb_qn (S (List.length Ms)) σ) (sb_qn (List.length Ms) (q σ))).
  { rewrite <- Nat.add_1_r; symmetry; exact (sb_qn_add (List.length Ms) 1 σ). }
  cbn [sb_qn] in Hq; rewrite Hq, IH; apply sb_of_list_cong, sb_q_compose_extend.
Qed.

Corollary exp_sub_qn_of_list : forall A Ms σ,
    A[sb_qn (List.length Ms) σ][sb_of_list Id Ms] = A[sb_of_list σ Ms].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq.
  rewrite sb_qn_of_list; apply sb_of_list_cong, sb_compose_id_right.
Qed.

(** ** Telescopes at Lists of Terms *)

Lemma tele_insts_snoc : forall Δ A σ M Ms,
    tele_insts (Δ ++ ce_ass A :: nil) σ (M :: Ms) = A[σ] :: tele_insts Δ (σ ,, M) Ms.
Proof. intros; unfold tele_insts; rewrite rev_app_distr; reflexivity. Qed.

Lemma tele_insts_sub : forall Δ k σ σ' τ Ms,
    tele_ass Δ -> ctx_scoped k Δ ->
    (forall x, x < k -> sentry_sub (σ x) τ = σ' x) ->
    List.map (fun T => T[τ]) (tele_insts Δ σ Ms) = tele_insts Δ σ' (List.map (fun M => M[τ]) Ms).
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ; [ reflexivity |].
  unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He].
  inversion_clear He as [| ? ? [A ->] _].
  apply ctx_scoped_app in HΔ as [HΔ [HA _]]; cbn in HA, HΔ.
  destruct Ms as [| M Ms]; [ unfold tele_insts; rewrite rev_app_distr; reflexivity |].
  cbn [List.map]; rewrite !tele_insts_snoc; cbn [List.map]; f_equal.
  - rewrite exp_sub_sub; eapply exp_scoped_sub_agree; [ exact HA |]; intros; cbn; apply Hσ; assumption.
  - apply (IH (S k)); [ assumption | assumption |].
    intros [| x] Hx; cbn; [ reflexivity | apply Hσ; lia ].
Qed.

Lemma tele_insts_aux_sb_eq : forall Δr σ τ Ms,
    sb_eq σ τ -> tele_insts_aux Δr σ Ms = tele_insts_aux Δr τ Ms.
Proof.
  induction Δr as [| [] Δr IH]; intros σ τ [| M Ms] H; cbn; try reflexivity.
  f_equal; [ apply exp_sub_sb_eq, H | apply IH, sb_extend_cong, H ].
Qed.

Lemma tele_insts_sb_eq : forall Δ σ τ Ms, sb_eq σ τ -> tele_insts Δ σ Ms = tele_insts Δ τ Ms.
Proof. intros; apply tele_insts_aux_sb_eq; assumption. Qed.

Lemma tele_insts_tele_sub : forall Δ σ τ Ms,
    tele_insts (tele_sub Δ σ) τ Ms = tele_insts Δ (σ ⨟ τ) Ms.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros; [ reflexivity |].
  rewrite tele_sub_app; cbn [tele_sub List.length sb_qn].
  destruct e as [A | A N | U | A N U];
    [| unfold tele_insts; rewrite !rev_app_distr; reflexivity
     | unfold tele_insts; rewrite !rev_app_distr; reflexivity
     | unfold tele_insts; rewrite !rev_app_distr; reflexivity ].
  destruct Ms as [| M Ms]; [ unfold tele_insts; rewrite !rev_app_distr; reflexivity |].
  cbn [centry_sub]; rewrite !tele_insts_snoc, IH, exp_sub_sub; f_equal.
  apply tele_insts_sb_eq, sb_q_compose_extend.
Qed.

Lemma ctx_pi_snoc : forall Δ A B, ctx_pi (Δ ++ ce_ass A :: nil) B = a_pi A (ctx_pi Δ B).
Proof. intros; rewrite ctx_pi_app; reflexivity. Qed.

(** ** Positions in Lists of Terms *)

Lemma sb_of_list_ge : forall Ms σ x, sb_of_list σ Ms (List.length Ms + x) = σ x.
Proof. induction Ms as [| M Ms IH]; intros; cbn; [ reflexivity |]; rewrite <- Nat.add_succ_r, IH; reflexivity. Qed.

Lemma sb_of_list_nth : forall Ms σ x d,
    x < List.length Ms -> sb_of_list σ Ms x = se_exp (List.nth (List.length Ms - 1 - x) Ms d).
Proof.
  induction Ms as [| M Ms IH]; intros * Hx; cbn in *; [ lia |].
  destruct (Nat.lt_ge_cases x (List.length Ms)) as [Hlt | Hge].
  - rewrite (IH _ _ d Hlt); replace (List.length Ms - 0 - x) with (S (List.length Ms - 1 - x)) by lia; reflexivity.
  - replace x with (List.length Ms + 0) by lia; rewrite sb_of_list_ge.
    replace (List.length Ms - 0 - (List.length Ms + 0)) with 0 by lia; reflexivity.
Qed.

Lemma vars_from_nth : forall j k x d, x < k -> List.nth (k - 1 - x) (vars_from j k) d = a_var (j + x).
Proof.
  intros * Hx; unfold vars_from.
  rewrite (List.nth_indep _ _ (a_var (j + 0))) by (rewrite List.length_map, List.length_rev, List.length_seq; lia).
  rewrite (List.map_nth (fun i => a_var (j + i)) _ 0), List.rev_nth by (rewrite List.length_seq; lia).
  rewrite List.length_seq, List.seq_nth by lia; f_equal; lia.
Qed.

Lemma vars_from_nth_error : forall j k t N,
    List.nth_error (vars_from j k) t = Some N -> t < k /\ N = a_var (j + (k - 1 - t)).
Proof.
  intros * H; assert (Ht : t < k) by (rewrite <- (length_vars_from j k); apply List.nth_error_Some; congruence).
  split; [ exact Ht |].
  apply (List.nth_error_nth _ _ (a_var 0)) in H; rewrite <- H.
  replace t with (k - 1 - (k - 1 - t)) at 1 by lia; apply vars_from_nth; lia.
Qed.

Lemma vars_from_S : forall j n, vars_from j (S n) = a_var (j + n) :: vars_from j n.
Proof. intros; unfold vars_from; rewrite List.seq_S, List.rev_app_distr; reflexivity. Qed.

Lemma vars_from_app : forall j a b, vars_from (j + b) a ++ vars_from j b = vars_from j (a + b).
Proof.
  induction a as [| a IH]; intros; [ reflexivity |].
  cbn [Nat.add]; rewrite !vars_from_S; cbn [List.app]; rewrite IH; do 2 f_equal; lia.
Qed.

Lemma vars_from_wk_shiftn : forall n m k,
    List.map (fun M => M[wk_shiftn n]ʷ) (vars_from m k) = vars_from (m + n) k.
Proof.
  intros; unfold vars_from; rewrite List.map_map; apply List.map_ext; intros i; cbn; f_equal; lia.
Qed.

Lemma sb_of_list_vars : forall σ j k x, x < k -> sb_of_list σ (vars_from j k) x = se_exp (a_var (j + x)).
Proof.
  intros * Hx; rewrite (sb_of_list_nth _ _ _ (a_var 0)) by (rewrite length_vars_from; exact Hx).
  rewrite length_vars_from, vars_from_nth by exact Hx; reflexivity.
Qed.

Lemma sb_of_list_firstn_vars : forall σ m n k x,
    x < k -> k <= n -> sb_of_list σ (List.firstn k (vars_from m n)) x = se_exp (a_var (m + (n - k + x))).
Proof.
  intros * Hx Hk.
  assert (Hl : List.length (List.firstn k (vars_from m n)) = k) by (rewrite List.length_firstn, length_vars_from; lia).
  rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia; rewrite Hl, List.nth_firstn.
  destruct (Nat.ltb_spec (k - 1 - x) k) as [_ | ?]; [| lia ].
  replace (k - 1 - x) with (n - 1 - (n - k + x)) by lia; rewrite vars_from_nth by lia; reflexivity.
Qed.

Lemma map_shift_sb_of_list : forall Us Ns σ,
    List.map (fun U => U[wk_shiftn (List.length Ns)]ʷ[sb_of_list σ Ns]) Us = List.map (fun U => U[σ]) Us.
Proof.
  intros; apply List.map_ext; intros U; rewrite exp_sub_wk; apply exp_sub_sb_eq.
  intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]; rewrite Nat.add_comm; apply sb_of_list_ge.
Qed.

Lemma vars_from_sb_of_list : forall Ns σ,
    List.map (fun M => M[sb_of_list σ Ns]) (vars_from 0 (List.length Ns)) = Ns.
Proof.
  intros; apply (List.nth_ext _ _ (a_var 0) (a_var 0)); rewrite List.length_map, length_vars_from; [ reflexivity |].
  intros t Ht.
  rewrite (List.nth_indep _ (a_var 0) ((a_var 0)[sb_of_list σ Ns])) by (rewrite List.length_map, length_vars_from; lia).
  rewrite (List.map_nth (fun M : typ => M[sb_of_list σ Ns]) (vars_from 0 (List.length Ns)) (a_var 0) t).
  replace t with (List.length Ns - 1 - (List.length Ns - 1 - t)) at 1 by lia.
  rewrite vars_from_nth by lia; cbn.
  rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia; cbn; f_equal; lia.
Qed.

(** The instances of a telescope, position by position. *)
Lemma tele_insts_aux_nth : forall Δr σ Ms k T,
    List.nth_error (tele_insts_aux Δr σ Ms) k = Some T ->
    exists A, List.nth_error Δr k = Some (ce_ass A) /\ T = A[sb_of_list σ (List.firstn k Ms)].
Proof.
  induction Δr as [| [A | A N | U | A N U] Δr IH]; intros σ [| M Ms] k T H; cbn in H; try (destruct k; discriminate).
  destruct k as [| k]; cbn in H.
  - injection H as <-; exists A; split; reflexivity.
  - destruct (IH _ _ _ _ H) as (A' & HA' & ->); exists A'; split; [ exact HA' | reflexivity ].
Qed.

Lemma tele_insts_nth : forall Δ σ Ms k T,
    List.nth_error (tele_insts Δ σ Ms) k = Some T ->
    exists A, List.nth_error (List.rev Δ) k = Some (ce_ass A) /\ T = A[sb_of_list σ (List.firstn k Ms)].
Proof. intros; apply tele_insts_aux_nth; assumption. Qed.

Lemma tele_insts_aux_app : forall Δr Δr' σ Ms Ns,
    List.Forall (fun e => exists A, e = ce_ass A) Δr -> List.length Ms = List.length Δr ->
    tele_insts_aux (Δr ++ Δr') σ (Ms ++ Ns) = tele_insts_aux Δr σ Ms ++ tele_insts_aux Δr' (sb_of_list σ Ms) Ns.
Proof.
  intros Δr Δr' σ Ms Ns Hr; revert σ Ms; induction Hr as [| e Δr [A ->] Hr IH]; intros σ [| M Ms] Hl;
    cbn in Hl; try lia; [ reflexivity |].
  cbn; f_equal; apply IH; lia.
Qed.

Lemma tele_insts_app : forall Δ1 Δ2 σ Ms Ns,
    tele_ass Δ2 -> List.length Ms = List.length Δ2 ->
    tele_insts (Δ1 ++ Δ2) σ (Ms ++ Ns) = tele_insts Δ2 σ Ms ++ tele_insts Δ1 (sb_of_list σ Ms) Ns.
Proof.
  intros * Hass Hl; unfold tele_insts; rewrite List.rev_app_distr.
  apply tele_insts_aux_app; [ apply List.Forall_rev; exact Hass | rewrite List.length_rev; exact Hl ].
Qed.

(** ** The Arguments Before a Constructor's Argument *)

Lemma length_cargs_pat : forall gs, List.length (cargs_pat gs) = List.length gs.
Proof. intros; unfold cargs_pat; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma cargs_pat_snoc : forall gs g,
    cargs_pat (gs ++ g :: nil) = match g with ca_rec _ => true | ca_arg _ => false end :: cargs_pat gs.
Proof. intros; unfold cargs_pat; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma pat_nargs_app : forall l1 l2, pat_nargs (l1 ++ l2) = pat_nargs l1 + pat_nargs l2.
Proof. induction l1 as [| [] l1 IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

Lemma cargs_pat_cons : forall g gs,
    cargs_pat (g :: gs) = cargs_pat gs ++ (match g with ca_rec _ => true | ca_arg _ => false end :: nil).
Proof. reflexivity. Qed.

Lemma pat_nargs_cargs_pat : forall gs, pat_nargs (cargs_pat gs) = List.length (cargs_strat gs).
Proof.
  induction gs as [| [] gs IH]; [ reflexivity | |]; rewrite cargs_pat_cons, pat_nargs_app, IH; cbn;
    rewrite ?List.length_app; cbn; lia.
Qed.

Lemma cargs_strat_snoc_arg : forall gs A, cargs_strat (gs ++ ca_arg A :: nil) = ce_ass A :: cargs_strat gs.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

Lemma cargs_strat_snoc_rec : forall gs Ps, cargs_strat (gs ++ ca_rec Ps :: nil) = cargs_strat gs.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

Lemma cargs_ctx_aux_app : forall pq D nn gs1 gs2 pat,
    cargs_ctx_aux pq D nn pat (gs1 ++ gs2) = cargs_ctx_aux pq D nn (cargs_pat gs1 ++ pat) gs2 ++ cargs_ctx_aux pq D nn pat gs1.
Proof.
  induction gs1 as [| [A | t] gs1 IH]; intros; cbn [List.app cargs_ctx_aux]; [ rewrite List.app_nil_r; reflexivity | |];
    rewrite IH, cargs_pat_cons, <- !List.app_assoc; reflexivity.
Qed.

Lemma cargs_ctx_snoc : forall pq D M gs g,
    cargs_ctx pq D M (gs ++ g :: nil) = cargs_ctx_aux pq D (im_nn M) (cargs_pat gs) (g :: nil) ++ cargs_ctx pq D M gs.
Proof. intros; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; reflexivity. Qed.

(** Past the non-recursive arguments, [wk_pat] shifts past all of them. *)
Lemma wk_pat_ge : forall pat y, wk_pat pat (pat_nargs pat + y) = List.length pat + y.
Proof.
  induction pat as [| [] pat IH]; intros; cbn; [ reflexivity | rewrite IH; lia | rewrite IH; reflexivity ].
Qed.

Lemma wk_pat_app_true : forall pat x, wk_pat (pat ++ true :: nil) x = wk_qn (List.length pat) wk_shift (wk_pat pat x).
Proof.
  induction pat as [| [] pat IH]; intros x; cbn [List.app wk_pat List.length]; [ reflexivity | |].
  - cbn; rewrite IH; reflexivity.
  - destruct x; cbn; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma wk_pat_app_false : forall pat n x, wk_pat (pat ++ List.repeat false n) x = wk_pat pat x.
Proof.
  induction pat as [| [] pat IH]; intros n x; cbn [List.app wk_pat].
  - revert x; induction n as [| n IHn]; intros [| x]; cbn; auto.
  - cbn; rewrite IH; reflexivity.
  - destruct x; cbn; [ reflexivity | rewrite IH; reflexivity ].
Qed.

(** The substitution of the parameters and the non-recursive arguments
    [As] of [gs], over [σ]: what a shape's components after [gs] are
    instantiated by. *)
Fixpoint cargs_sub (σ : sub) (gs : list carg) (As : list exp) : sub :=
  match gs, As with
  | ca_arg _ :: gs', N :: As' => cargs_sub (σ ,, N) gs' As'
  | ca_rec _ :: gs', _ :: As' => cargs_sub σ gs' As'
  | _, _ => σ
  end.

(** The arguments [As] before, filled over [σ], read through the pattern's
    weakening. *)
Lemma cargs_sub_pat : forall gs σ As, List.length As = List.length gs ->
    sb_eq (ι (wk_pat (cargs_pat gs)) ⨟ sb_of_list σ As) (cargs_sub σ gs As).
Proof.
  induction gs as [| g gs IH]; intros σ [| N As] Hl; cbn in Hl; try discriminate.
  - intros x; reflexivity.
  - injection Hl as Hl; rewrite cargs_pat_cons; cbn [sb_of_list].
    destruct g as [B | t]; cbn [cargs_sub].
    + etransitivity; [| apply (IH (σ ,, N) As Hl) ]; intros x; cbn [sb_compose sb_of_wk sentry_sub].
      replace (cargs_pat gs ++ false :: nil) with (cargs_pat gs ++ List.repeat false 1) by reflexivity.
      rewrite wk_pat_app_false; reflexivity.
    + etransitivity; [| apply (IH σ As Hl) ]; intros x; cbn [sb_compose sb_of_wk sentry_sub].
      rewrite wk_pat_app_true, length_cargs_pat, <- Hl.
      set (y := wk_pat (cargs_pat gs) x).
      destruct (Nat.lt_ge_cases y (List.length As)) as [Hy | Hy].
      * rewrite wk_qn_lt by exact Hy.
        rewrite (sb_of_list_nth _ _ _ (a_var 0)), (sb_of_list_nth _ _ _ (a_var 0)) by lia; reflexivity.
      * rewrite wk_qn_ge by exact Hy; cbn [wk_shift].
        replace (S (y - List.length As) + List.length As) with (List.length As + S (y - List.length As)) by lia.
        replace y with (List.length As + (y - List.length As)) at 2 by lia.
        rewrite !sb_of_list_ge; reflexivity.
Qed.

Lemma cargs_sub_firstn : forall gs σ As, cargs_sub σ gs (List.firstn (List.length gs) As) = cargs_sub σ gs As.
Proof. induction gs as [| [] gs IH]; intros σ [| N As]; cbn; auto. Qed.

Lemma cargs_sub_snoc_arg : forall gs B σ As N, List.length As = List.length gs ->
    cargs_sub σ (gs ++ ca_arg B :: nil) (As ++ N :: nil) = (cargs_sub σ gs As ,, N).
Proof. induction gs as [| [] gs IH]; intros B σ [| M As] N Hl; cbn in *; try discriminate; auto. Qed.

Lemma cargs_sub_snoc_rec : forall gs t σ As N, List.length As = List.length gs ->
    cargs_sub σ (gs ++ ca_rec t :: nil) (As ++ N :: nil) = cargs_sub σ gs As.
Proof. induction gs as [| [] gs IH]; intros t σ [| M As] N Hl; cbn in *; try discriminate; auto. Qed.

(** The same for a telescope whose types have no free module variable: the
    substitutions need only send the same terms. *)
Lemma tele_insts_sub_mvc : forall Δ k σ σ' τ Ms,
    tele_ass Δ -> ctx_mvc Δ -> ctx_scoped k Δ ->
    (forall x, x < k -> sentry_exp (sentry_sub (σ x) τ) = sentry_exp (σ' x)) ->
    List.map (fun T => T[τ]) (tele_insts Δ σ Ms) = tele_insts Δ σ' (List.map (fun M => M[τ]) Ms).
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass Hmv HΔ Hσ; [ reflexivity |].
  unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He].
  apply List.Forall_cons_iff in He as [[A ->] _].
  unfold ctx_mvc in Hmv; apply List.Forall_app in Hmv as [Hmv HmA]; apply List.Forall_cons_iff in HmA as [HmA _].
  apply ctx_scoped_app in HΔ as [HΔ [HA _]]; cbn in HA, HΔ, HmA.
  destruct Ms as [| M Ms]; [ unfold tele_insts; rewrite List.rev_app_distr; reflexivity |].
  cbn [List.map]; rewrite !tele_insts_snoc; cbn [List.map]; f_equal.
  - rewrite exp_sub_sub; eapply exp_scoped_mvc_agree; [ exact HA | exact HmA |]; intros; cbn; apply Hσ; assumption.
  - apply (IH (S k)); [ assumption | assumption | assumption |].
    intros [| x] Hx; cbn; [ reflexivity | apply Hσ; lia ].
Qed.

(** ** Facts of a Closed Declaration *)

Section Closed.
  Context (D : ind_decl) (HD : decl_closed D).

  Lemma decl_closed_nparams_scoped : forall k M, ind_member D k = Some M -> ctx_scoped (ind_nu D) (im_nparams M).
  Proof. intros * HM; exact (member_closed_nparams _ _ (decl_closed_members _ HD _ _ HM)). Qed.

  Lemma decl_closed_nparams_ass : forall k M, ind_member D k = Some M -> tele_ass (im_nparams M).
  Proof. intros * HM; exact (member_closed_ass _ _ (decl_closed_members _ HD _ _ HM)). Qed.

  Lemma decl_closed_head_scoped : forall k M qc k' Is vm,
      ind_member D k = Some M -> im_head M = mh_view qc k' Is vm -> List.Forall (exp_scoped (ind_nu D)) Is.
  Proof. intros * HM Hh; exact (member_closed_head _ _ (decl_closed_members _ HD _ _ HM) _ _ _ _ Hh). Qed.

  Lemma decl_closed_rhead_scoped : forall k M qr Is fl,
      ind_member D k = Some M -> im_head M = mh_record qr Is fl -> List.Forall (exp_scoped (ind_nu D)) Is.
  Proof. intros * HM Hh; exact (member_closed_rhead _ _ (decl_closed_members _ HD _ _ HM) _ _ _ Hh). Qed.

  Lemma decl_closed_cargs_scoped : forall pq k M c gs,
      ind_member D k = Some M -> In (c, gs) (im_cons M) -> ctx_scoped (im_np D M) (cargs_ctx pq D M gs).
  Proof.
    intros * HM Hin; pose proof (decl_closed_members _ HD _ _ HM) as HMc.
    apply (cargs_ctx_aux_scoped pq D (im_nn M) gs nil 0 HD eq_refl); intros; cbn.
    - eapply (member_closed_args _ _ HMc); eassumption.
    - eapply (member_closed_recs _ _ HMc); eassumption.
  Qed.
End Closed.

Lemma length_nparams_sub : forall M σ, List.length (tele_sub (im_nparams M) σ) = im_nn M.
Proof. intros; rewrite length_tele_sub; reflexivity. Qed.

(** The non-uniform parameters at the uniform ones [Us]. *)
Lemma nparams_sub : forall D k M Us τ,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    tele_sub (tele_sub (im_nparams M) (sb_of_list Id Us)) τ
    = tele_sub (im_nparams M) (sb_of_list Id (List.map (fun U => U[τ]) Us)).
Proof.
  intros * HD HM Hl; rewrite tele_sub_sub.
  eapply tele_scoped_sub_agree; [ eapply decl_closed_nparams_scoped; eassumption |].
  intros x Hx; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
Qed.

(** The uniform arguments of a member's type at [Us], moved. *)
Lemma im_pre_sub : forall D k M Us τ,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    List.map (fun N => N[τ]) (im_pre M Us) = im_pre M (List.map (fun U => U[τ]) Us).
Proof.
  intros * HD HM Hl; unfold im_pre.
  destruct (im_head M) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; [ reflexivity | |].
  - rewrite map_map; apply map_ext_in; intros I HI.
    rewrite exp_sub_sub; eapply exp_scoped_sub_agree;
      [ exact (proj1 (List.Forall_forall _ _) (decl_closed_head_scoped _ HD _ _ _ _ _ _ HM Hh) I HI) |].
    intros x Hx; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
  - rewrite map_map; apply map_ext_in; intros I HI.
    rewrite exp_sub_sub; eapply exp_scoped_sub_agree;
      [ exact (proj1 (List.Forall_forall _ _) (decl_closed_rhead_scoped _ HD _ _ _ _ _ HM Hh) I HI) |].
    intros x Hx; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
Qed.

(** A member at uniform and non-uniform parameters, moved. *)
Lemma ind_mty_sub : forall pq D j Us Ns τ,
    decl_closed D -> List.length Us = ind_nu D ->
    (ind_mty pq D j Us Ns)[τ] = ind_mty pq D j (List.map (fun U => U[τ]) Us) (List.map (fun N => N[τ]) Ns).
Proof.
  intros * HD Hl; unfold ind_mty.
  destruct (ind_member D j) as [M |] eqn:HM; [| reflexivity ].
  unfold im_ty_at; destruct (im_head M);
    rewrite apps_exp_sub, map_app; cbn [exp_sub]; erewrite im_pre_sub by eassumption; reflexivity.
Qed.

(** The member at the uniform parameters [Us] under its non-uniform ones,
    as variables, moved under those: the type an annotation and the
    scrutinee in a motive's context are of. *)
Lemma ind_mty_shift_sub : forall pq D j nn Us τ,
    decl_closed D -> List.length Us = ind_nu D ->
    (ind_mty pq D j (List.map (fun U => U[wk_shiftn nn]ʷ) Us) (vars_from 0 nn))[sb_qn nn τ]
    = ind_mty pq D j (List.map (fun U => U[wk_shiftn nn]ʷ) (List.map (fun U => U[τ]) Us)) (vars_from 0 nn).
Proof.
  intros * HD Hl; rewrite ind_mty_sub by (try assumption; rewrite length_map; exact Hl); f_equal.
  - rewrite !map_map; apply map_ext; intros U; apply exp_shiftn_sub_qn0.
  - apply vars_from_sub; lia.
Qed.

(** The type of the scrutinee at parameters [Ps], moved. *)
Lemma ind_mty_split_sub : forall pq D j Ps τ,
    decl_closed D -> ind_nu D <= List.length Ps ->
    (ind_mty pq D j (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps))[τ]
    = ind_mty pq D j (List.firstn (ind_nu D) (List.map (fun P => P[τ]) Ps)) (List.skipn (ind_nu D) (List.map (fun P => P[τ]) Ps)).
Proof.
  intros * HD Hl; rewrite ind_mty_sub, List.firstn_map, List.skipn_map; [ reflexivity | assumption |].
  rewrite List.length_firstn; lia.
Qed.

Lemma elim_mctx_sub : forall pq D k M Us τ,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    tele_sub (elim_mctx pq D k M Us) τ = elim_mctx pq D k M (List.map (fun U => U[τ]) Us).
Proof.
  intros * HD HM Hl; unfold elim_mctx; cbn [tele_sub]; rewrite length_nparams_sub.
  f_equal; [| eapply nparams_sub; eassumption ].
  cbn [centry_sub]; f_equal; apply ind_mty_shift_sub; assumption.
Qed.

(** ** Shapes under Substitution

    The type of a recursive result depends on its shape's components only
    through the substitution moving them, at the variables they are scoped
    in. *)
Lemma sb_of_list_lt_base : forall Ms σ σ' x, x < List.length Ms -> sb_of_list σ Ms x = sb_of_list σ' Ms x.
Proof. intros * Hx; rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by exact Hx; reflexivity. Qed.

(** Two substitutions agreeing below [k], each extended by the same list,
    agree below its length past [k]. *)
Lemma sb_of_list_agree : forall Ms σ σ' k,
    (forall y, y < k -> σ y = σ' y) -> forall y, y < List.length Ms + k -> sb_of_list σ Ms y = sb_of_list σ' Ms y.
Proof.
  intros * Hσ y Hy; destruct (Nat.lt_ge_cases y (List.length Ms)) as [Hl | Hl].
  - apply sb_of_list_lt_base; exact Hl.
  - replace y with (List.length Ms + (y - List.length Ms)) by lia; rewrite !sb_of_list_ge; apply Hσ; lia.
Qed.

Lemma length_projections_of : forall ns x, List.length (projections_of ns x) = List.length ns.
Proof. intros; unfold projections_of; apply List.length_map. Qed.

Lemma projections_of_sub : forall ns x τ, List.map (fun N => N[τ]) (projections_of ns x) = projections_of ns x[τ].
Proof. intros; unfold projections_of; rewrite map_map; reflexivity. Qed.

(** The projections of all the fields [fs], seen past the pattern of their
    kinds, are those of the non-recursive ones. *)
Lemma wk_pat_projections : forall fs pat τ x,
    sb_eq (ι (wk_pat (cargs_pat (List.map snd fs) ++ pat)) ⨟ sb_of_list τ (projections_of (List.map fst fs) x))
          (sb_of_list (ι (wk_pat pat) ⨟ τ) (projections_of (fields_args fs) x)).
Proof.
  induction fs as [| [f [A | t]] fs IH]; intros pat τ x; cbn [List.map fst snd fields_args].
  - intros z; reflexivity.
  - rewrite cargs_pat_cons, <- List.app_assoc; cbn [List.app projections_of List.map sb_of_list].
    rewrite (IH (false :: pat) (τ ,, a_proj f x) x); apply sb_of_list_cong.
    intros [| z]; reflexivity.
  - rewrite cargs_pat_cons, <- List.app_assoc; cbn [List.app projections_of List.map sb_of_list].
    rewrite (IH (true :: pat) (τ ,, a_proj f x) x); apply sb_of_list_cong.
    intros z; reflexivity.
Qed.

Lemma leaf_ihty_sb_agree : forall l As β σ σ' x k,
    leaf_scoped k l -> (forall y, y < k -> σ y = σ' y) ->
    leaf_ihty As β σ x l = leaf_ihty As β σ' x l.
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros * Ht Hσ; cbn in *.
  - do 2 f_equal; f_equal; apply map_ext_in; intros P HP;
      eapply exp_scoped_sub_agree; [ exact (proj1 (List.Forall_forall _ _) Ht P HP) | exact Hσ ].
  - destruct Ht as [HB Ht]; f_equal; [ eapply exp_scoped_sub_agree; eassumption |].
    eapply IH; [ exact Ht |]; apply sb_q_agree; exact Hσ.
  - eapply IH; [ exact Ht |]; rewrite <- (length_projections_of ns x); apply sb_of_list_agree; exact Hσ.
Qed.

Lemma leaf_ihty_sb_eq : forall l As β β' σ σ' x, sb_eq β β' -> sb_eq σ σ' ->
    leaf_ihty As β σ x l = leaf_ihty As β' σ' x l.
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros * Hβ Hσ; cbn in *.
  - apply exp_sub_sb_eq; etransitivity; [ apply sb_of_list_cong, Hβ |];
      rewrite (map_ext (fun P => P[σ]) (fun P => P[σ'])) by (intros; apply exp_sub_sb_eq, Hσ); reflexivity.
  - f_equal; [ apply exp_sub_sb_eq, Hσ |].
    apply IH; [ intros y; cbn [sb_compose]; rewrite Hβ; reflexivity | apply sb_q_cong, Hσ ].
  - apply IH; [ exact Hβ | apply sb_of_list_cong, Hσ ].
Qed.

(** A weakening under [Ms] followed by the list [Ms] over [σ] is the list
    over the weakening followed by [σ]. *)
Lemma sb_wk_qn_of_list : forall Ms φ σ,
    sb_eq (ι (wk_qn (List.length Ms) φ) ⨟ sb_of_list σ Ms) (sb_of_list (ι φ ⨟ σ) Ms).
Proof.
  intros Ms φ σ x; cbn [sb_compose sb_of_wk sentry_sub].
  destruct (Nat.lt_ge_cases x (List.length Ms)) as [Hx | Hx].
  - rewrite wk_qn_lt by exact Hx; apply sb_of_list_lt_base; exact Hx.
  - rewrite wk_qn_ge by exact Hx.
    replace x with (List.length Ms + (x - List.length Ms)) at 2 by lia.
    rewrite Nat.add_comm, !sb_of_list_ge; reflexivity.
Qed.

(** The type of a recursive result along a leaf path moved by [φ] is that
    along the path, its components' substitution after [φ]. *)
Lemma leaf_ihty_wk : forall l As β σ x φ,
    leaf_ihty As β σ x (leaf_wk φ l) = leaf_ihty As β (ι φ ⨟ σ) x l.
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros *; cbn [leaf_wk leaf_ihty].
  - rewrite map_map; do 3 f_equal; apply map_ext; intros P; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity.
  - rewrite IH, <- exp_sub_of_wk, exp_sub_sub; f_equal; apply leaf_ihty_sb_eq; [ reflexivity |].
    intros y; cbn [sb_compose]; apply (sb_q_wk_pre_ext φ σ (ι φ ⨟ σ)); intros z; reflexivity.
  - rewrite IH; apply leaf_ihty_sb_eq; [ reflexivity |].
    rewrite <- (length_projections_of ns x); apply sb_wk_qn_of_list.
Qed.

(** A shift by [s] followed by [q^(s + r) τ] is [q^r τ] followed by the
    shift. *)
Lemma sb_shiftn_qn_comm' : forall s r τ, sb_eq (ι (wk_shiftn s) ⨟ sb_qn (s + r) τ) (sb_qn r τ ⨟ ι (wk_shiftn s)).
Proof.
  intros s r τ x; cbn [sb_compose sb_of_wk sentry_sub]; rewrite sentry_sub_of_wk.
  rewrite sb_qn_plus, sb_qn_ge by (cbn; lia); cbn [wk_shiftn]; replace (x + s - s) with x by lia; reflexivity.
Qed.

(** The type of a recursive result under [τ]. *)
Lemma leaf_ihty_sub : forall l As β σ x τ,
    (leaf_ihty As β σ x l)[τ] = leaf_ihty As (β ⨟ τ) (σ ⨟ τ) x[τ] l.
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros *; cbn in *.
  - rewrite exp_sub_sub; apply exp_sub_sb_eq; etransitivity; [ apply sb_of_list_compose_gen |];
      rewrite map_app, !map_map; cbn [List.map];
      rewrite (map_ext (fun P => P[σ][τ]) (fun P => P[σ ⨟ τ])) by (intros; apply exp_sub_sub); reflexivity.
  - f_equal; [ apply exp_sub_sub |].
    rewrite IH; cbn [exp_sub]; rewrite exp_wk_shift_sub_q, sb_q_zero; apply leaf_ihty_sb_eq.
    + intros y; cbn [sb_compose]; rewrite !sentry_sub_sub; apply sentry_sub_sb_eq.
      intros z; cbn [sb_compose sb_of_wk sentry_sub]; rewrite sb_q_succ, sentry_sub_of_wk; reflexivity.
    + apply sb_q_compose.
  - rewrite IH; cbn [exp_sub]; apply leaf_ihty_sb_eq; [ reflexivity |].
    rewrite <- projections_of_sub; apply sb_of_list_compose_gen.
Qed.

(** A base [τ] followed by [β] is the motives moved by [τ] under their
    binders, at the base [β]: the motive of the member the path ends in
    binds as many variables as the path's end has parameters, and the
    scrutinee. *)
Lemma leaf_ihty_base : forall l As As' τ β σ x,
    List.nth (leaf_mem l) As' a_True = (List.nth (leaf_mem l) As a_True)[sb_qn (S (List.length (leaf_ps l))) τ] ->
    leaf_ihty As (τ ⨟ β) σ x l = leaf_ihty As' β σ x l.
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros * HA; cbn in *.
  - rewrite HA; symmetry; rewrite exp_sub_sub; apply exp_sub_sb_eq.
    pose proof (sb_qn_of_list (List.map (fun P => P[σ]) Ps ++ x :: nil) τ β) as E.
    rewrite length_app, length_map, Nat.add_1_r in E; exact E.
  - f_equal; rewrite <- (IH As As' τ) by exact HA; apply leaf_ihty_sb_eq; [| reflexivity ].
    intros y; cbn [sb_compose]; rewrite sentry_sub_sub; reflexivity.
  - apply IH; exact HA.
Qed.

(** The type of an argument of a shape, at an instance. *)
Lemma ptyp_ty_at_sb_eq : forall pq D t Us σ σ', sb_eq σ σ' -> ptyp_ty_at pq D Us σ t = ptyp_ty_at pq D Us σ' t.
Proof.
  intros pq D t; induction t as [j Ps | B t IH]; intros * Hσ; cbn in *.
  - f_equal; apply map_ext; intros; apply exp_sub_sb_eq, Hσ.
  - f_equal; [ apply exp_sub_sb_eq, Hσ | apply IH, sb_q_cong, Hσ ].
Qed.

Lemma ptyp_ty_at_sub : forall pq D t Us σ τ,
    decl_closed D -> List.length Us = ind_nu D ->
    (ptyp_ty_at pq D Us σ t)[τ] = ptyp_ty_at pq D (List.map (fun U => U[τ]) Us) (σ ⨟ τ) t.
Proof.
  intros pq D t; induction t as [j Ps | B t IH]; intros * HD Hl; cbn [ptyp_ty_at].
  - rewrite ind_mty_sub by assumption; rewrite map_map; f_equal; apply map_ext; intros; apply exp_sub_sub.
  - cbn [exp_sub]; f_equal; [ apply exp_sub_sub |].
    rewrite IH by (try assumption; rewrite length_map; exact Hl).
    rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ _ (sb_q_compose σ τ)), !map_map; f_equal.
    apply map_ext; intros U; apply exp_wk_shift_sub_q.
Qed.

(** [ptyp_ty] is the type at the uniform parameters as variables, the
    components moved by the pattern's weakening. *)
Lemma ptyp_ty_eq_at : forall pq D nn t pat,
    ptyp_ty pq D nn pat t = ptyp_ty_at pq D (ind_uvars D nn (List.length pat)) (ι (wk_pat pat)) t.
Proof.
  intros pq D nn t; induction t as [j Ps | B t IH]; intros pat; cbn [ptyp_ty ptyp_ty_at].
  - f_equal; apply map_ext; intros; symmetry; apply exp_sub_of_wk.
  - rewrite exp_sub_of_wk, IH; f_equal; cbn [List.length wk_pat].
    rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ _ (sb_q_of_wk (wk_pat pat))); f_equal.
    unfold ind_uvars, vars_from; rewrite map_map; apply map_ext; intros i; cbn; f_equal; lia.
Qed.

(** The components' move into a branch, followed by [τ] under the branch's
    binders, is their move at the uniform parameters moved by [τ]. *)
Lemma ihs_sub_compose : forall nn Us na pat j τ x,
    List.length pat <= na -> x < pat_nargs pat + (nn + List.length Us) ->
    sentry_sub (ihs_sub nn Us na pat j x) (sb_qn (j + na + nn) τ) = ihs_sub nn (List.map (fun U => U[τ]) Us) na pat j x.
Proof.
  intros * Hna Hx; unfold ihs_sub; cbn [sb_compose].
  rewrite sentry_sub_sub.
  replace (j + na + nn) with ((na - List.length pat + j) + (List.length pat + nn)) by lia.
  rewrite (sentry_sub_sb_eq _ _ _ (sb_shiftn_qn_comm' _ _ τ)), <- sentry_sub_sub; f_equal.
  cbn [sb_of_wk sentry_sub].
  pose proof (wk_pat_bound pat (nn + List.length Us) x Hx) as Hy.
  change (sentry_sub (sb_qn (length pat + nn) (sb_of_list Id Us) (wk_pat pat x)) (sb_qn (length pat + nn) τ))
    with ((sb_qn (length pat + nn) (sb_of_list Id Us) ⨟ sb_qn (length pat + nn) τ) (wk_pat pat x)).
  rewrite (sb_qn_compose_ext _ _ _ _ (fun z => eq_refl) (wk_pat pat x)).
  eapply (sb_qn_agree _ _ _ (List.length Us)); [| lia ].
  intros z Hz; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
Qed.

(** The recursive results: the motive at a recursive argument moves under
    the scrutinee and the non-uniform parameters of the member its shape
    ends in. *)
(** The recursive results of one recursive argument, along its leaf
    paths, under [τ]. *)
Lemma leaves_ctx_sub : forall nn As As' Us na τ pat ls j,
    List.length pat < na ->
    List.Forall (leaf_scoped (pat_nargs pat + (nn + List.length Us))) ls ->
    (forall l, In l ls ->
       List.nth (leaf_mem l) As' a_True = (List.nth (leaf_mem l) As a_True)[sb_qn (S (List.length (leaf_ps l))) τ]) ->
    tele_sub (leaves_ctx nn As Us na pat j ls) (sb_qn (j + na + nn) τ)
    = leaves_ctx nn As' (List.map (fun U => U[τ]) Us) na pat j ls.
Proof.
  induction ls as [| l ls IH]; intros j Hna Hs HA; cbn [leaves_ctx]; [ reflexivity |].
  inversion Hs as [| ? ? Hs0 Hs']; subst.
  rewrite tele_sub_app; cbn [tele_sub List.length]; f_equal.
  - rewrite (tele_sub_sb_eq _ _ (sb_qn (S j + na + nn) τ)) by (intros x; symmetry; apply (sb_qn_add 1 (j + na + nn) τ x)).
    apply IH; [ lia | exact Hs' | intros l' Hl'; apply HA; right; exact Hl' ].
  - cbn [centry_sub sb_qn]; f_equal; f_equal.
    rewrite leaf_ihty_sub.
    rewrite (leaf_ihty_sb_eq _ _ _ (τ ⨟ ι (wk_shiftn (j + na + nn))) _ _ _ (sb_shiftn_qn_comm _ τ) (fun z => eq_refl)).
    rewrite (leaf_ihty_base _ _ _ _ _ _ _ (HA l (or_introl eq_refl))).
    cbn [exp_sub]; rewrite sb_qn_lt by lia; cbn [sentry_exp sb_qn].
    eapply leaf_ihty_sb_agree; [ exact Hs0 |].
    intros y Hy; cbn [sb_compose]; apply ihs_sub_compose; lia.
Qed.

Lemma ihs_ctx_aux_sub : forall D nn As As' Us na τ gs pat j,
    decl_closed D -> List.length Us = ind_nu D ->
    List.length pat + List.length gs = na ->
    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
       ptyp_scoped (pat_nargs pat + List.length (cargs_strat gs1) + (nn + List.length Us)) t /\
       (forall l, In l (shape_leaves (rv_leaves D) (pat_nargs pat + List.length (cargs_strat gs1) + nn) t) ->
          List.nth (leaf_mem l) As' a_True = (List.nth (leaf_mem l) As a_True)[sb_qn (S (List.length (leaf_ps l))) τ])) ->
    tele_sub (ihs_ctx_aux (rv_leaves D) nn As Us na pat j gs) (sb_qn (j + na + nn) τ)
    = ihs_ctx_aux (rv_leaves D) nn As' (List.map (fun U => U[τ]) Us) na pat j gs.
Proof.
  intros D nn As As' Us na τ; induction gs as [| [B | t] gs IH]; intros * HD HU Hna HPs; cbn [ihs_ctx_aux];
    [ reflexivity | |].
  - apply (IH (false :: pat) j HD HU); [ cbn in *; lia |].
    intros gs1 t gs2 Egs; destruct (HPs (ca_arg B :: gs1) t gs2 ltac:(rewrite Egs; reflexivity)) as [HPs' HA]; cbn in HPs'.
    rewrite length_app in HPs'; cbn in HPs'; split.
    + eapply ptyp_scoped_mono; [| exact HPs' ]; cbn [pat_nargs]; lia.
    + intros l Hl; apply HA; cbn [pat_nargs] in Hl; cbn [cargs_strat]; rewrite length_app; cbn [List.length].
      replace (pat_nargs pat + (length (cargs_strat gs1) + 1) + nn) with (S (pat_nargs pat) + length (cargs_strat gs1) + nn) by lia;
        exact Hl.
  - destruct (HPs nil t gs eq_refl) as [HPs0 HA0]; cbn in HPs0, HA0; rewrite Nat.add_0_r in HPs0, HA0.
    cbn in Hna.
    rewrite tele_sub_app; f_equal.
    + rewrite length_leaves_ctx.
      set (nl := List.length (shape_leaves (rv_leaves D) (pat_nargs pat + nn) t)).
      rewrite (tele_sub_sb_eq _ _ (sb_qn (nl + j + na + nn) τ))
        by (intros x; replace (nl + j + na + nn) with (nl + (j + na + nn)) by lia;
            apply (sb_qn_add nl (j + na + nn) τ x)).
      apply (IH (true :: pat) (nl + j) HD HU); [ cbn; lia |].
      intros gs1 t' gs2 Egs; exact (HPs (ca_rec t :: gs1) t' gs2 ltac:(rewrite Egs; reflexivity)).
    + apply leaves_ctx_sub; [ lia | | exact HA0 ].
      pose proof (shape_leaves_scoped (rv_leaves D) (ind_nu D) t (pat_nargs pat + nn) (rv_leaves_scoped D HD)) as Hs.
      rewrite <- HU in Hs; replace (pat_nargs pat + nn + List.length Us) with (pat_nargs pat + (nn + List.length Us)) in Hs by lia.
      apply Hs; exact HPs0.
Qed.

Lemma elim_bctx_sub : forall pq D k M c gs As As' Us τ,
    decl_closed D -> ind_member D k = Some M -> In (c, gs) (im_cons M) -> List.length Us = ind_nu D ->
    (forall j Mj, ind_member D j = Some Mj -> List.nth j As' a_True = (List.nth j As a_True)[sb_qn (S (im_nn Mj)) τ]) ->
    tele_sub (elim_bctx pq D M gs As Us) τ = elim_bctx pq D M gs As' (List.map (fun U => U[τ]) Us).
Proof.
  intros * HD HM Hin Hl HAs; unfold elim_bctx.
  pose proof (decl_closed_members _ HD _ _ HM) as HMc.
  rewrite !tele_sub_app, length_app, length_tele_sub, length_cargs_ctx, length_nparams_sub.
  f_equal; [| f_equal ].
  - apply (ihs_ctx_aux_sub D (im_nn M) As As' Us (List.length gs) τ gs nil 0 HD Hl eq_refl).
    intros * Heq; split.
    + rewrite Hl; exact (member_closed_recs _ _ HMc _ _ _ _ _ Hin Heq).
    + intros l Hlf; pose proof (cargs_leaves_plen _ _ _ _ _ _ _ _ (pat_nargs nil + length (cargs_strat gs1) + im_nn M) HD HM Hin Heq) as Hp.
      rewrite List.Forall_forall in Hp; destruct (Hp l Hlf) as (Mj & HMj & HlMj).
      rewrite HlMj; apply HAs; exact HMj.
  - rewrite tele_sub_sub.
    rewrite (tele_sub_sb_eq _ _ (sb_qn (im_nn M) (sb_of_list Id Us ⨟ τ))) by (apply sb_qn_compose_ext; reflexivity).
    eapply tele_scoped_sub_agree; [ eapply decl_closed_cargs_scoped; eassumption |].
    intros x Hx; eapply (sb_qn_agree _ _ _ (ind_nu D)); [| unfold im_np in Hx; lia ].
    intros z Hz; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
  - eapply nparams_sub; eassumption.
Qed.

Lemma elim_bty_sub : forall pq D k M c gs A Us τ,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    (elim_bty pq D k M c gs A Us)[sb_qn (im_nn M + List.length gs + cargs_nrec D gs) τ]
    = elim_bty pq D k M c gs A[sb_qn (S (im_nn M)) τ] (List.map (fun U => U[τ]) Us).
Proof.
  intros * HD HM Hl; unfold elim_bty; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
  rewrite sb_of_list_compose with (σ := τ) (ρ' := ι (wk_shiftn (im_nn M + List.length gs + cargs_nrec D gs)))
    by apply sb_shiftn_qn_comm.
  rewrite length_app, length_vars_from; cbn [List.length]; rewrite Nat.add_1_r.
  intros x; cbn [sb_compose]; f_equal; f_equal.
  rewrite map_app; cbn [List.map]; f_equal; [ apply vars_from_sub; lia |]; f_equal.
  rewrite apps_exp_sub, !map_app; cbn [exp_sub]; f_equal; f_equal; [| f_equal; apply vars_from_sub; lia ].
  erewrite im_pre_sub by (try eassumption; rewrite length_map; exact Hl).
  f_equal; rewrite !map_map; apply map_ext; intros U; apply exp_shiftn_sub_qn0.
Qed.

(** ** Blocks under Substitution *)

(** The branches moved: each under as many binders as it binds. *)
Definition brs_sub (Bs : list (String.string * nat * exp)) (τ : sub) : list (String.string * nat * exp) :=
  List.map (fun b => (fst b, (snd b)[sb_qn (snd (fst b)) τ])) Bs.

(** The blocks moved ([exp_sub] unfolds to it): the annotation under the
    non-uniform parameters, the motive under them and the scrutinee, each
    branch under its binders. *)
Definition eblock_sub (b : eblock) (τ : sub) : eblock :=
  match b with
  | eb_mk nm oZ A Bs => eb_mk nm (option_map (fun Z => Z[sb_qn (nm - 1) τ]) oZ) A[sb_qn nm τ] (brs_sub Bs τ)
  end.

(** The blocks of an eliminator moved, each by [eblock_sub]. *)
Definition blocks_sub (Bks : list eblock) (τ : sub) : list eblock := List.map (fun b => eblock_sub b τ) Bks.

Lemma exp_sub_elim : forall oq Us m Bks M τ,
    (a_elim oq Us m Bks M)[τ] = a_elim oq (List.map (fun U => U[τ]) Us) m (blocks_sub Bks τ) M[τ].
Proof.
  intros; cbn [exp_sub]; f_equal; unfold blocks_sub; apply map_ext; intros [nm oZ A Bs]; reflexivity.
Qed.

Lemma nth_error_blocks_sub : forall Bks τ k,
    List.nth_error (blocks_sub Bks τ) k = option_map (fun b => eblock_sub b τ) (List.nth_error Bks k).
Proof. intros; unfold blocks_sub; apply List.nth_error_map. Qed.

Lemma length_blocks_sub : forall Bks τ, List.length (blocks_sub Bks τ) = List.length Bks.
Proof. intros; apply List.length_map. Qed.

Lemma blocks_nm_ok_sub : forall D Bks τ, blocks_nm_ok D Bks -> blocks_nm_ok D (blocks_sub Bks τ).
Proof.
  intros * H k Mk b HM Hb; rewrite nth_error_blocks_sub in Hb.
  destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:E; cbn in Hb; [| discriminate ].
  injection Hb as <-; cbn; exact (H _ _ _ HM E).
Qed.

(** The motive of the member [j], moved under its binders. *)
Lemma blocks_motives_sub : forall D Bks τ j Mj,
    blocks_nm_ok D Bks -> ind_member D j = Some Mj ->
    List.nth j (blocks_motives (blocks_sub Bks τ)) a_True = (List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) τ].
Proof.
  intros * Hnm HMj; unfold blocks_motives.
  destruct (List.nth_error Bks j) as [[nm oZ A Bs] |] eqn:Hb.
  - pose proof (Hnm _ _ _ HMj Hb) as E; cbn in E; subst nm.
    assert (E1 : List.nth j (List.map eb_motive Bks) a_True = A)
      by (apply List.nth_error_nth; rewrite List.nth_error_map, Hb; reflexivity).
    assert (E2 : List.nth j (List.map eb_motive (blocks_sub Bks τ)) a_True = A[sb_qn (S (im_nn Mj)) τ])
      by (apply List.nth_error_nth; rewrite List.nth_error_map, nth_error_blocks_sub, Hb; reflexivity).
    rewrite E1, E2; reflexivity.
  - apply List.nth_error_None in Hb.
    rewrite (List.nth_overflow (List.map eb_motive Bks)) by (rewrite List.length_map; exact Hb).
    rewrite List.nth_overflow by (rewrite List.length_map, length_blocks_sub; exact Hb); reflexivity.
Qed.

(** Weakening, then substituting, the blocks, as for a term. *)
Lemma blocks_sub_wk_comm : forall Bks φ σ τ ψ,
    (forall x, σ (φ x) = sentry_wk (τ x) ψ) -> blocks_sub (blocks_wk Bks φ) σ = blocks_wk (blocks_sub Bks τ) ψ.
Proof.
  intros * H; unfold blocks_sub, blocks_wk; rewrite !map_map; apply map_ext; intros [nm oZ A Bs]; cbn.
  f_equal; [ destruct oZ; cbn; [ f_equal |] | | ].
  - apply exp_wk_sub_comm_ext, sb_qn_comm_ext, H.
  - reflexivity.
  - apply exp_wk_sub_comm_ext, sb_qn_comm_ext, H.
  - unfold brs_sub; rewrite !map_map; apply map_ext; intros [[c k] B]; cbn [fst snd]; f_equal.
    apply exp_wk_sub_comm_ext, sb_qn_comm_ext, H.
Qed.

Lemma blocks_sub_wk_shift : forall Bks τ, blocks_sub (blocks_wk Bks ↑) (q τ) = blocks_wk (blocks_sub Bks τ) ↑.
Proof. intros; apply blocks_sub_wk_comm; intros; reflexivity. Qed.

Lemma blocks_sub_sb_eq : forall Bks σ σ', sb_eq σ σ' -> blocks_sub Bks σ = blocks_sub Bks σ'.
Proof.
  intros * H; unfold blocks_sub; apply map_ext; intros [nm oZ A Bs]; cbn.
  f_equal; [ destruct oZ; cbn; [ f_equal; apply exp_sub_sb_eq, sb_qn_cong, H | reflexivity ]
           | apply exp_sub_sb_eq, sb_qn_cong, H |].
  unfold brs_sub; apply map_ext; intros [[c k] B]; cbn; f_equal; apply exp_sub_sb_eq, sb_qn_cong, H.
Qed.

Lemma hd_error_blocks_sub : forall Bks τ, List.hd_error (blocks_sub Bks τ) = option_map (fun b => eblock_sub b τ) (List.hd_error Bks).
Proof. intros [| b Bks] τ; reflexivity. Qed.

(** The motive of the block at the member [m], moved, at the non-uniform
    parameters and the scrutinee moved. *)
Lemma elim_type_sub : forall D Mm bm Ps M τ,
    List.length Ps = im_np D Mm -> eb_nm bm = S (im_nn Mm) ->
    ((eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])[τ]
    = (eb_motive (eblock_sub bm τ))[sb_of_list Id (List.skipn (ind_nu D) (List.map (fun P => P[τ]) Ps) ++ M[τ] :: nil)].
Proof.
  intros * Hl Hnm; destruct bm as [nm oZ A Bs]; cbn in Hnm |- *; subst nm.
  rewrite exp_sub_sb_of_list, List.map_app, List.skipn_map; cbn [List.map].
  replace (List.length (List.skipn (ind_nu D) Ps ++ M :: nil)) with (S (im_nn Mm))
    by (rewrite List.length_app, List.length_skipn; cbn; unfold im_np in Hl; lia); reflexivity.
Qed.

Lemma elim_at_sub : forall pq D oq Us Bks j M τ,
    decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks ->
    (elim_at pq D oq Us Bks j M)[τ] = elim_at pq D oq (List.map (fun U => U[τ]) Us) (blocks_sub Bks τ) j M[τ].
Proof.
  intros * HD Hl Hnm; unfold elim_at; destruct (ind_has_views D); rewrite exp_sub_elim; reflexivity.
Qed.

Lemma leaf_ih_sb_eq : forall pq D oq l Us Bks σ σ' M, sb_eq σ σ' ->
    leaf_ih pq D oq Us Bks σ M l = leaf_ih pq D oq Us Bks σ' M l.
Proof.
  intros pq D oq l; induction l as [j Ps | B l IH | f ns l IH]; intros * Hσ; cbn; [ reflexivity | |].
  - f_equal; [ apply exp_sub_sb_eq, Hσ | apply IH, sb_q_cong, Hσ ].
  - apply IH, sb_of_list_cong, Hσ.
Qed.

(** The recursive result along a leaf path moved by [φ] is that along the
    path, its components' substitution after [φ]. *)
Lemma leaf_ih_wk : forall pq D oq l Us Bks σ M φ,
    leaf_ih pq D oq Us Bks σ M (leaf_wk φ l) = leaf_ih pq D oq Us Bks (ι φ ⨟ σ) M l.
Proof.
  intros pq D oq l; induction l as [j Ps | B l IH | f ns l IH]; intros *; cbn [leaf_wk leaf_ih]; [ reflexivity | |].
  - rewrite IH, <- exp_sub_of_wk, exp_sub_sub; f_equal; apply leaf_ih_sb_eq.
    intros y; cbn [sb_compose]; apply (sb_q_wk_pre_ext φ σ (ι φ ⨟ σ)); intros z; reflexivity.
  - rewrite IH; apply leaf_ih_sb_eq.
    rewrite <- (length_projections_of ns M); apply sb_wk_qn_of_list.
Qed.

(** The recursive result along a leaf path under [τ]. *)
Lemma leaf_ih_sub : forall pq D oq l Us Bks σ M τ,
    decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks ->
    (leaf_ih pq D oq Us Bks σ M l)[τ] = leaf_ih pq D oq (List.map (fun U => U[τ]) Us) (blocks_sub Bks τ) (σ ⨟ τ) M[τ] l.
Proof.
  intros pq D oq l; induction l as [j Ps | B l IH | f ns l IH]; intros * HD Hl Hnm; cbn [leaf_ih].
  - apply elim_at_sub; assumption.
  - cbn [exp_sub]; f_equal; [ apply exp_sub_sub |].
    rewrite IH by first [ assumption | rewrite length_map; exact Hl | apply blocks_nm_ok_wk; exact Hnm ].
    rewrite (leaf_ih_sb_eq _ _ _ _ _ _ _ _ _ (sb_q_compose σ τ)); f_equal.
    + rewrite !map_map; apply map_ext; intros U; apply exp_wk_shift_sub_q.
    + apply blocks_sub_wk_shift.
    + cbn [exp_sub]; rewrite exp_wk_shift_sub_q, sb_q_zero; reflexivity.
  - rewrite IH by assumption; cbn [exp_sub]; apply leaf_ih_sb_eq.
    rewrite <- projections_of_sub; apply sb_of_list_compose_gen.
Qed.

Lemma elim_ihs_sb_eq : forall pq D oq Us Bks gs σ σ' m As, sb_eq σ σ' ->
    elim_ihs pq D oq Us Bks σ m gs As = elim_ihs pq D oq Us Bks σ' m gs As.
Proof.
  intros pq D oq Us Bks gs; induction gs as [| [] gs IH]; intros σ σ' m [| N As] Hσ; cbn [elim_ihs]; try reflexivity.
  - apply IH, sb_extend_cong, Hσ.
  - f_equal; [ apply map_ext; intros l; apply leaf_ih_sb_eq, Hσ | apply IH, Hσ ].
Qed.

Lemma elim_ihs_sub : forall pq D oq Us Bks gs σ m As τ,
    decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks ->
    List.map (fun N => N[τ]) (elim_ihs pq D oq Us Bks σ m gs As)
    = elim_ihs pq D oq (List.map (fun U => U[τ]) Us) (blocks_sub Bks τ) (σ ⨟ τ) m gs (List.map (fun N => N[τ]) As).
Proof.
  intros pq D oq Us Bks gs; induction gs as [| [] gs IH]; intros σ m [| N As] τ HD Hl Hnm; cbn [elim_ihs List.map];
    try reflexivity.
  - rewrite IH by assumption; apply elim_ihs_sb_eq, sb_extend_compose.
  - rewrite List.map_app, IH by assumption; f_equal; rewrite map_map; apply map_ext; intros l.
    apply leaf_ih_sub; assumption.
Qed.

Lemma leaf_ih_agree : forall pq D oq l Us Bks σ σ' M k,
    leaf_scoped k l -> (forall y, y < k -> σ y = σ' y) ->
    leaf_ih pq D oq Us Bks σ M l = leaf_ih pq D oq Us Bks σ' M l.
Proof.
  intros pq D oq l; induction l as [j Ps | B l IH | f ns l IH]; intros * Ht Hσ; cbn in *; [ reflexivity | |].
  - destruct Ht as [HB Ht]; f_equal; [ eapply exp_scoped_sub_agree; eassumption |].
    eapply IH; [ exact Ht |]; apply sb_q_agree; exact Hσ.
  - eapply IH; [ exact Ht |]; rewrite <- (length_projections_of ns M); apply sb_of_list_agree; exact Hσ.
Qed.

Lemma elim_ihs_agree : forall pq D oq Us Bks gs σ σ' m As k,
    decl_closed D -> k = m + ind_nu D ->
    (forall y, y < k -> σ y = σ' y) ->
    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ptyp_scoped (List.length (cargs_strat gs1) + k) t) ->
    elim_ihs pq D oq Us Bks σ m gs As = elim_ihs pq D oq Us Bks σ' m gs As.
Proof.
  intros pq D oq Us Bks gs; induction gs as [| [A0 | t] gs IH]; intros σ σ' m [| N As] k HD Hk Hσ Ht; cbn [elim_ihs];
    try reflexivity.
  - apply (IH _ _ _ _ (S k) HD); [ lia | |].
    + intros [| y] Hy; cbn; [ reflexivity | apply Hσ; lia ].
    + intros gs1 t gs2 E; specialize (Ht (ca_arg A0 :: gs1) t gs2 ltac:(rewrite E; reflexivity)); cbn in Ht;
        rewrite length_app in Ht; cbn in Ht.
      eapply ptyp_scoped_mono; [| exact Ht ]; lia.
  - f_equal.
    + apply map_ext_in; intros l Hlf; eapply leaf_ih_agree; [| exact Hσ ].
      pose proof (shape_leaves_scoped (rv_leaves D) (ind_nu D) t m (rv_leaves_scoped D HD)) as Hs.
      specialize (Ht nil t gs eq_refl); cbn in Ht; subst k.
      exact (proj1 (List.Forall_forall _ _) (Hs Ht) l Hlf).
    + eapply IH; [ exact HD | exact Hk | exact Hσ |]; intros gs1 t' gs2 E;
        exact (Ht (ca_rec t :: gs1) t' gs2 ltac:(rewrite E; reflexivity)).
Qed.

(** The recursive results of [ι] under [τ]: the parameters the shapes'
    domains are instantiated at move. *)
Lemma elim_ihs_sub_inst : forall pq D oq k M c gs Bks Ps As τ,
    decl_closed D -> ind_member D k = Some M -> In (c, gs) (im_cons M) -> List.length Ps = im_np D M ->
    blocks_nm_ok D Bks ->
    List.map (fun N => N[τ]) (elim_ihs pq D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) (im_nn M) gs As)
    = elim_ihs pq D oq (List.firstn (ind_nu D) (List.map (fun P => P[τ]) Ps)) (blocks_sub Bks τ)
        (sb_of_list Id (List.map (fun P => P[τ]) Ps)) (im_nn M) gs (List.map (fun N => N[τ]) As).
Proof.
  intros * HD HM Hin Hl Hnm.
  rewrite elim_ihs_sub by (try assumption; rewrite List.length_firstn; unfold im_np in Hl; lia).
  rewrite List.firstn_map.
  eapply (elim_ihs_agree _ _ _ _ _ _ _ _ _ _ (List.length Ps) HD); [ unfold im_np in Hl; lia | |].
  - intros y Hy; cbn [sb_compose]; apply sb_of_list_lt_compose; exact Hy.
  - intros gs1 t gs2 E; rewrite Hl; exact (member_closed_recs _ _ (decl_closed_members _ HD _ _ HM) _ _ _ _ _ Hin E).
Qed.

(** ** Lists of Branches *)

Section Branches.
  Context (g : String.string * nat * exp -> exp).

  Lemma brs_names_map : forall cs Bs,
      brs_names cs (List.map (fun b => (fst b, g b)) Bs) <-> brs_names cs Bs.
  Proof. intros; unfold brs_names; rewrite map_map; reflexivity. Qed.

  Lemma brs_fst_map : forall Bs, List.map fst (List.map (fun b => (fst b, g b)) Bs) = List.map fst Bs.
  Proof. intros; rewrite map_map; reflexivity. Qed.

  Lemma brs_in_map : forall Bs c n B',
      In (c, n, B') (List.map (fun b => (fst b, g b)) Bs) -> exists B, In (c, n, B) Bs /\ B' = g (c, n, B).
  Proof.
    intros * Hin; apply List.in_map_iff in Hin as ([[c' n'] B] & Heq & Hin); cbn in Heq.
    injection Heq as Hc Hn HB; subst; eauto.
  Qed.

  Lemma brs_lookup_map : forall Bs c n B,
      brs_lookup Bs c = Some (n, B) -> brs_lookup (List.map (fun b => (fst b, g b)) Bs) c = Some (n, g (c, n, B)).
  Proof.
    induction Bs as [| [[c' n'] B'] Bs IH]; cbn; intros * H; [ discriminate |].
    destruct (String.eqb_spec c c') as [-> | _]; [ injection H as -> ->; reflexivity | auto ].
  Qed.
End Branches.

(** ** The Types of the Type Former and the Constructors *)

Lemma ind_ty_sub : forall D k M τ, decl_closed D -> ind_member D k = Some M -> (ind_ty D M)[τ] = ind_ty D M.
Proof. intros; apply exp_closed_sub; eapply decl_closed_ind_ty; eassumption. Qed.

Lemma con_ty_sub : forall pq D k M c gs τ, decl_closed D -> ind_member D k = Some M -> ind_con M c = Some gs ->
    (con_ty pq D k M gs)[τ] = con_ty pq D k M gs.
Proof.
  intros; apply exp_closed_sub; eapply decl_closed_con_ty; [ eassumption | eassumption | apply cons_lookup_in; eassumption ].
Qed.

(** The parameters typed one by one at the instances of their telescope,
    and the arguments at the instances of theirs at the parameters. *)
Lemma params_insts_sub : forall D k M Ps τ,
    decl_closed D -> ind_member D k = Some M ->
    List.map (fun T => T[τ]) (tele_insts (im_params D M) Id Ps)
    = tele_insts (im_params D M) Id (List.map (fun P => P[τ]) Ps).
Proof.
  intros * HD HM; apply (tele_insts_sub _ 0);
    [ eapply decl_closed_params_ass; eassumption | eapply decl_closed_params; eassumption | lia ].
Qed.

Lemma cargs_insts_sub : forall pq D k M c gs Ps As τ,
    decl_closed D -> ind_member D k = Some M -> ind_con M c = Some gs -> List.length Ps = im_np D M ->
    List.map (fun T => T[τ]) (tele_insts (cargs_ctx pq D M gs) (sb_of_list Id Ps) As)
    = tele_insts (cargs_ctx pq D M gs) (sb_of_list Id (List.map (fun P => P[τ]) Ps)) (List.map (fun N => N[τ]) As).
Proof.
  intros * HD HM Hc Hl; apply (tele_insts_sub _ (im_np D M)).
  - apply cargs_ctx_aux_ass.
  - eapply decl_closed_cargs_scoped; [ eassumption | eassumption | apply cons_lookup_in; eassumption ].
  - intros; apply sb_of_list_lt_compose; lia.
Qed.

Lemma nth_error_map_inv : forall {A B} (f : A -> B) l k y,
    nth_error (List.map f l) k = Some y -> exists x, nth_error l k = Some x /\ y = f x.
Proof.
  intros * H; rewrite nth_error_map in H.
  destruct (nth_error l k) as [x |]; cbn in H; [ injection H as <-; eauto | discriminate ].
Qed.

(** ** Weakenings *)

Lemma map_sub_of_wk : forall Ms φ, List.map (fun M => M[ι φ]) Ms = List.map (fun M => M[φ]ʷ) Ms.
Proof. intros; apply map_ext; intros; apply exp_sub_of_wk. Qed.

Lemma exp_sub_qn_of_wk : forall M n φ, M[sb_qn n (ι φ)] = M[wk_qn n φ]ʷ.
Proof. intros; apply exp_sub_of_wk_ext, sb_qn_of_wk_ext; reflexivity. Qed.

Lemma exp_wk_sb_of_list : forall A Ms φ,
    A[sb_of_list Id Ms][φ]ʷ = A[wk_qn (List.length Ms) φ]ʷ[sb_of_list Id (List.map (fun M => M[φ]ʷ) Ms)].
Proof.
  intros; rewrite <- exp_sub_of_wk, exp_sub_sb_of_list, exp_sub_qn_of_wk, map_sub_of_wk; reflexivity.
Qed.

Lemma brs_sub_of_wk : forall Bs φ,
    brs_sub Bs (ι φ) = List.map (fun b => (fst b, (snd b)[wk_qn (snd (fst b)) φ]ʷ)) Bs.
Proof. intros; apply map_ext; intros; rewrite exp_sub_qn_of_wk; reflexivity. Qed.

Lemma blocks_sub_of_wk : forall Bks φ, blocks_sub Bks (ι φ) = blocks_wk Bks φ.
Proof.
  intros; unfold blocks_sub, blocks_wk; apply map_ext; intros [nm oZ A Bs]; cbn.
  f_equal; [ destruct oZ; cbn; [ f_equal; apply exp_sub_qn_of_wk | reflexivity ] | apply exp_sub_qn_of_wk |].
  apply brs_sub_of_wk.
Qed.

Lemma blocks_motives_wk : forall D Bks φ j Mj,
    blocks_nm_ok D Bks -> ind_member D j = Some Mj ->
    List.nth j (blocks_motives (blocks_wk Bks φ)) a_True = (List.nth j (blocks_motives Bks) a_True)[wk_qn (S (im_nn Mj)) φ]ʷ.
Proof. intros; rewrite <- blocks_sub_of_wk, <- exp_sub_qn_of_wk; eapply blocks_motives_sub; eassumption. Qed.

Lemma elim_mctx_wk : forall pq D k M Us φ,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    tele_wk (elim_mctx pq D k M Us) φ = elim_mctx pq D k M (List.map (fun U => U[φ]ʷ) Us).
Proof. intros; rewrite <- tele_sub_of_wk; erewrite elim_mctx_sub by eassumption; rewrite map_sub_of_wk; reflexivity. Qed.

Lemma elim_bctx_wk : forall pq D k M c gs As As' Us φ,
    decl_closed D -> ind_member D k = Some M -> In (c, gs) (im_cons M) -> List.length Us = ind_nu D ->
    (forall j Mj, ind_member D j = Some Mj -> List.nth j As' a_True = (List.nth j As a_True)[wk_qn (S (im_nn Mj)) φ]ʷ) ->
    tele_wk (elim_bctx pq D M gs As Us) φ = elim_bctx pq D M gs As' (List.map (fun U => U[φ]ʷ) Us).
Proof.
  intros * HD HM Hin Hl HAs; rewrite <- tele_sub_of_wk; erewrite elim_bctx_sub; [ rewrite map_sub_of_wk; reflexivity | eassumption .. |].
  intros j Mj HMj; rewrite exp_sub_qn_of_wk; exact (HAs _ _ HMj).
Qed.

Lemma elim_bty_wk : forall pq D k M c gs A Us φ,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    (elim_bty pq D k M c gs A Us)[wk_qn (im_nn M + List.length gs + cargs_nrec D gs) φ]ʷ
    = elim_bty pq D k M c gs A[wk_qn (S (im_nn M)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us).
Proof.
  intros; rewrite <- exp_sub_qn_of_wk; erewrite elim_bty_sub by eassumption.
  rewrite exp_sub_qn_of_wk, map_sub_of_wk; reflexivity.
Qed.

Lemma elim_ihs_wk_inst : forall pq D oq k M c gs Bks Ps As φ,
    decl_closed D -> ind_member D k = Some M -> In (c, gs) (im_cons M) -> List.length Ps = im_np D M ->
    blocks_nm_ok D Bks ->
    List.map (fun N => N[φ]ʷ) (elim_ihs pq D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) (im_nn M) gs As)
    = elim_ihs pq D oq (List.firstn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ps)) (blocks_wk Bks φ)
        (sb_of_list Id (List.map (fun P => P[φ]ʷ) Ps)) (im_nn M) gs (List.map (fun N => N[φ]ʷ) As).
Proof.
  intros; rewrite <- !map_sub_of_wk; erewrite elim_ihs_sub_inst by eassumption.
  rewrite blocks_sub_of_wk; reflexivity.
Qed.

Lemma ind_ty_wk : forall D k M φ, decl_closed D -> ind_member D k = Some M -> (ind_ty D M)[φ]ʷ = ind_ty D M.
Proof. intros; apply exp_closed_wk; eapply decl_closed_ind_ty; eassumption. Qed.

Lemma con_ty_wk : forall pq D k M c gs φ, decl_closed D -> ind_member D k = Some M -> ind_con M c = Some gs ->
    (con_ty pq D k M gs)[φ]ʷ = con_ty pq D k M gs.
Proof.
  intros; apply exp_closed_wk; eapply decl_closed_con_ty; [ eassumption | eassumption | apply cons_lookup_in; eassumption ].
Qed.

Lemma params_insts_wk : forall D k M Ps φ,
    decl_closed D -> ind_member D k = Some M ->
    List.map (fun T => T[φ]ʷ) (tele_insts (im_params D M) Id Ps)
    = tele_insts (im_params D M) Id (List.map (fun P => P[φ]ʷ) Ps).
Proof. intros; rewrite <- !map_sub_of_wk; eapply params_insts_sub; eassumption. Qed.

Lemma cargs_insts_wk : forall pq D k M c gs Ps As φ,
    decl_closed D -> ind_member D k = Some M -> ind_con M c = Some gs -> List.length Ps = im_np D M ->
    List.map (fun T => T[φ]ʷ) (tele_insts (cargs_ctx pq D M gs) (sb_of_list Id Ps) As)
    = tele_insts (cargs_ctx pq D M gs) (sb_of_list Id (List.map (fun P => P[φ]ʷ) Ps)) (List.map (fun N => N[φ]ʷ) As).
Proof. intros; rewrite <- !map_sub_of_wk; eapply cargs_insts_sub; eassumption. Qed.

Lemma ind_mty_wk : forall pq D j Us Ns φ,
    decl_closed D -> List.length Us = ind_nu D ->
    (ind_mty pq D j Us Ns)[φ]ʷ = ind_mty pq D j (List.map (fun U => U[φ]ʷ) Us) (List.map (fun N => N[φ]ʷ) Ns).
Proof. intros; rewrite <- exp_sub_of_wk, ind_mty_sub, !map_sub_of_wk by assumption; reflexivity. Qed.

Lemma im_pre_wk : forall D k M Us φ,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    List.map (fun N => N[φ]ʷ) (im_pre M Us) = im_pre M (List.map (fun U => U[φ]ʷ) Us).
Proof. intros; rewrite <- !map_sub_of_wk; eapply im_pre_sub; eassumption. Qed.

(** ** The Container's Blocks at a View under Substitution *)

Lemma sb_qn_shiftn : forall n τ x, sb_qn n τ (wk_shiftn n x) = sentry_wk (τ x) (wk_shiftn n).
Proof. intros; rewrite sb_qn_ge by (cbn; lia); cbn; replace (x + n - n) with x by lia; reflexivity. Qed.

Lemma blocks_sub_wk_shiftn : forall Bks n τ,
    blocks_sub (blocks_wk Bks (wk_shiftn n)) (sb_qn n τ) = blocks_wk (blocks_sub Bks τ) (wk_shiftn n).
Proof. intros; apply blocks_sub_wk_comm, sb_qn_shiftn. Qed.

Lemma brs_lookup_sub : forall Bs c τ,
    brs_lookup (brs_sub Bs τ) c = option_map (fun nB => (fst nB, (snd nB)[sb_qn (fst nB) τ])) (brs_lookup Bs c).
Proof.
  induction Bs as [| [[c' n'] B'] Bs IH]; intros; cbn; [ reflexivity |].
  destruct (String.eqb c c'); [ reflexivity | apply IH ].
Qed.

Lemma wrap_leaves_sub : forall D' t' ls ihs r' nr' σ,
    (forall x, x < S nr' -> σ x = se_var x) ->
    List.map (fun N => N[σ]) (wrap_leaves D' t' ls ihs r' nr') = wrap_leaves D' t' ls (List.map (fun N => N[σ]) ihs) r' nr'.
Proof.
  induction ls as [| l ls IH]; intros [| ih ihs] r' nr' σ Hσ; cbn [wrap_leaves List.map]; try reflexivity.
  destruct (leaf_in D' t' l); cbn [List.map]; f_equal; try (apply IH; exact Hσ).
  cbn [exp_sub]; rewrite Hσ by lia; reflexivity.
Qed.

Lemma wrap_ihs_sub : forall D' D gs' gs ihs r' nr' σ,
    (forall x, x < nr' + List.length gs' -> σ x = se_var x) ->
    List.map (fun N => N[σ]) (wrap_ihs D' D gs' gs ihs r' nr') = wrap_ihs D' D gs' gs (List.map (fun N => N[σ]) ihs) r' nr'.
Proof.
  intros D' D; induction gs' as [| g' gs' IH]; intros [| g gs] ihs r' nr' σ Hσ; cbn [wrap_ihs]; try reflexivity;
    [ destruct g'; reflexivity |].
  cbn [List.length] in Hσ.
  destruct g' as [A' | t'], g as [A | t]; cbn [wrap_ihs].
  - apply IH; intros; apply Hσ; lia.
  - rewrite List.map_app, List.firstn_map, List.skipn_map, IH by (intros; apply Hσ; lia); reflexivity.
  - apply IH; intros; apply Hσ; lia.
  - rewrite List.map_app, wrap_leaves_sub, List.firstn_map, List.skipn_map, IH by (intros; apply Hσ; lia); reflexivity.
Qed.

(** A branch of the container's block, moved under its binders. *)
Lemma wrap_br_sub : forall pq D D' vm Us Bks v Mv Bs c gs' gs τ,
    decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks -> ind_member D v = Some Mv ->
    ind_con Mv c = Some gs -> cargs_corr vm gs' gs ->
    (forall n B, In (c, n, B) Bs -> n = (im_nn Mv + List.length gs + cargs_nrec D gs)%nat) ->
    (fst (wrap_br pq D D' Us Bks Mv Bs c gs'),
     (snd (wrap_br pq D D' Us Bks Mv Bs c gs'))[sb_qn (snd (fst (wrap_br pq D D' Us Bks Mv Bs c gs'))) τ])
    = wrap_br pq D D' (List.map (fun U => U[τ]) Us) (blocks_sub Bks τ) Mv (brs_sub Bs τ) c gs'.
Proof.
  intros * HD Hl Hnm HMv Hgs Hc Hn.
  pose proof (cargs_corr_length _ _ _ Hc) as Hlen.
  unfold wrap_br; rewrite Hgs, brs_lookup_sub; cbv zeta; cbn [fst snd].
  destruct (brs_lookup Bs c) as [[n B] |] eqn:Hb; cbn [option_map fst snd]; [| reflexivity ].
  pose proof (Hn _ _ (brs_lookup_in _ _ _ _ Hb)) as En; subst n.
  f_equal.
  set (n' := (im_nn Mv + length gs' + cargs_nrec D' gs')%nat).
  match goal with |- B[sb_of_list _ ?L][_] = B[_][sb_of_list _ ?L'] => set (LL := L); set (LL' := L') end.
  assert (HLL : List.map (fun N => N[sb_qn n' τ]) LL = LL').
  { subst LL LL'; rewrite !map_app.
    rewrite (vars_from_sub _ _ n') by (subst n'; lia).
    rewrite (vars_from_sub _ _ n') by (subst n'; lia).
    do 2 f_equal.
    rewrite wrap_ihs_sub by (intros x Hx; apply sb_qn_lt; subst n'; lia).
    f_equal.
    rewrite elim_ihs_sub by first [ assumption | rewrite length_map; exact Hl | apply blocks_nm_ok_wk; exact Hnm ].
    rewrite (vars_from_sub _ _ n') by (subst n'; lia).
    rewrite blocks_sub_wk_shiftn.
    assert (HUs : List.map (fun U => U[sb_qn n' τ]) (List.map (fun U => U[wk_shiftn n']ʷ) Us)
                  = List.map (fun U => U[wk_shiftn n']ʷ) (List.map (fun U => U[τ]) Us))
      by (rewrite !map_map; apply map_ext; intros U; apply exp_shiftn_sub_qn0).
    rewrite HUs.
    eapply (elim_ihs_agree _ _ _ _ _ _ _ _ _ _ (im_nn Mv + ind_nu D) HD); [ lia | |].
    - intros y Hy; rewrite (sb_of_list_compose_gen _ _ _ y), map_app, HUs, (vars_from_sub _ _ n') by (subst n'; lia).
      apply sb_of_list_lt_base; rewrite length_app, !length_map, length_vars_from; lia.
    - intros gs1 t gs2 E; exact (member_closed_recs _ _ (decl_closed_members _ HD _ _ HMv) _ _ _ _ _ (cons_lookup_in _ _ _ Hgs) E). }
  assert (HL' : List.length LL' = (im_nn Mv + length gs + cargs_nrec D gs)%nat)
    by (subst LL'; rewrite !length_app, !length_vars_from, (length_wrap_ihs _ _ _ _ _ _ _ _ Hc)
          by (rewrite length_elim_ihs by (rewrite length_vars_from; lia); reflexivity); lia).
  rewrite !exp_sub_sub; apply exp_sub_sb_eq.
  rewrite <- HL', sb_qn_of_list, sb_of_list_compose_gen, HLL.
  apply sb_of_list_cong, sb_shiftn_qn_comm.
Qed.

(** The container's block for its member [i'], moved. *)
Lemma vwrap_block_sub : forall pq D D' vm Us Bks i' Mi' τ,
    decl_closed D -> vwrap_ok D D' vm -> List.length Us = ind_nu D -> blocks_nm_ok D Bks ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    ind_member D' i' = Some Mi' ->
    eblock_sub (vwrap_block pq D D' vm Us Bks i' Mi') τ
    = vwrap_block pq D D' vm (List.map (fun U => U[τ]) Us) (blocks_sub Bks τ) i' Mi'.
Proof.
  intros * HD Hvw Hl Hnm Hn HMi'.
  destruct (List.nth_error vm i') as [v |] eqn:Hv;
    [| apply List.nth_error_None in Hv; pose proof (vwrap_ok_length _ _ _ Hvw) as Hlv;
       assert (Hk : List.nth_error (ind_members D') i' <> None) by (unfold ind_member in HMi'; congruence);
       apply List.nth_error_Some in Hk; lia ].
  destruct (vwrap_ok_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv & HMv & _ & Hcs & Hcorr).
  unfold vwrap_block; rewrite (List.nth_error_nth _ _ _ Hv), nth_error_blocks_sub, HMv.
  destruct (List.nth_error Bks v) as [[nm oZ A Bs] |] eqn:Hb; cbn [option_map eblock_sub]; [| reflexivity ].
  f_equal; unfold brs_sub; rewrite map_map; apply map_ext_in; intros [c gs'] Hin; cbn [fst snd].
  assert (Hc : In c (List.map fst (im_cons Mv))) by (rewrite Hcs; apply List.in_map_iff; exists (c, gs'); auto).
  apply List.in_map_iff in Hc as ([c0 gs0] & E0 & Hin0); cbn in E0; subst c0.
  destruct (cons_lookup_of_in _ _ _ Hin0) as [gs Hgs].
  eapply wrap_br_sub; [ eassumption .. | exact (Hcorr _ _ _ Hin Hgs) |].
  intros n B HB; exact (Hn _ _ _ _ _ _ _ HMv Hb Hgs HB).
Qed.

(** The container's blocks at a view, moved. *)
Lemma vwrap_sub : forall pq D D' vm Us Bks τ,
    decl_closed D -> vwrap_ok D D' vm -> List.length Us = ind_nu D -> blocks_nm_ok D Bks ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    blocks_sub (vwrap pq D D' vm Us Bks) τ = vwrap pq D D' vm (List.map (fun U => U[τ]) Us) (blocks_sub Bks τ).
Proof.
  intros * HD Hvw Hl Hnm Hn; unfold vwrap.
  assert (H : forall ms s, (forall i Mi', List.nth_error ms i = Some Mi' -> ind_member D' (s + i) = Some Mi') ->
            blocks_sub (vwrap_from pq D D' vm Us Bks s ms) τ
            = vwrap_from pq D D' vm (List.map (fun U => U[τ]) Us) (blocks_sub Bks τ) s ms).
  { induction ms as [| Mi' ms IH]; intros s Hms; [ reflexivity |].
    unfold blocks_sub in *; cbn [vwrap_from List.map]; f_equal.
    - eapply vwrap_block_sub; try eassumption; rewrite <- (Nat.add_0_r s); exact (Hms 0 _ eq_refl).
    - apply IH; intros i Mi Hi; replace (S s + i) with (s + S i) by lia; exact (Hms (S i) _ Hi). }
  apply H; intros i Mi' Hi; exact (proj1 (ind_bmembers_member _ _ _ Hi)).
Qed.

Lemma vwrap_wk : forall pq D D' vm Us Bks φ,
    decl_closed D -> vwrap_ok D D' vm -> List.length Us = ind_nu D -> blocks_nm_ok D Bks ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    blocks_wk (vwrap pq D D' vm Us Bks) φ = vwrap pq D D' vm (List.map (fun U => U[φ]ʷ) Us) (blocks_wk Bks φ).
Proof. intros; rewrite <- !blocks_sub_of_wk, <- map_sub_of_wk; apply vwrap_sub; assumption. Qed.
