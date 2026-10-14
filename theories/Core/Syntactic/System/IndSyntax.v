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
From Mctt.Core.Syntactic.System Require Export MemberLemmas.
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
  destruct e as [A | A N | U];
    [| unfold tele_insts; rewrite !rev_app_distr; reflexivity
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
  induction Δr as [| [A | A N | U] Δr IH]; intros σ [| M Ms] k T H; cbn in H; try (destruct k; discriminate).
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

Lemma cargs_ctx_aux_app : forall p D gs1 gs2 pat,
    cargs_ctx_aux p D pat (gs1 ++ gs2) = cargs_ctx_aux p D (cargs_pat gs1 ++ pat) gs2 ++ cargs_ctx_aux p D pat gs1.
Proof.
  induction gs1 as [| [A | Ps] gs1 IH]; intros; cbn [List.app cargs_ctx_aux]; [ rewrite List.app_nil_r; reflexivity | |];
    rewrite IH, cargs_pat_cons, <- !List.app_assoc; reflexivity.
Qed.

Lemma cargs_ctx_snoc : forall p D gs g,
    cargs_ctx p D (gs ++ g :: nil) = cargs_ctx_aux p D (cargs_pat gs) (g :: nil) ++ cargs_ctx p D gs.
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

  Lemma decl_closed_uparams_length : List.length (ind_uparams D) = ind_nu D.
  Proof. apply length_ind_uparams, decl_closed_nu, HD. Qed.

  Lemma decl_closed_nparams_scoped : ctx_scoped (ind_nu D) (ind_nparams D).
  Proof.
    destruct HD as (_ & _ & HΔ & _).
    rewrite <- (firstn_skipn (ind_nn D) (ind_params D)) in HΔ.
    apply ctx_scoped_app in HΔ as [H _]; fold (ind_nparams D) (ind_uparams D) in H.
    rewrite decl_closed_uparams_length, Nat.add_0_r in H; exact H.
  Qed.

  Lemma decl_closed_nparams_ass : tele_ass (ind_nparams D).
  Proof. apply Forall_firstn', decl_closed_params, HD. Qed.

  Lemma decl_closed_cargs_scoped : forall p c gs,
      In (c, gs) (ind_cons D) -> ctx_scoped (ind_np D) (cargs_ctx p D gs).
  Proof.
    intros * Hin; destruct HD as (_ & Hle & _ & _ & HA & HPs & _).
    apply (cargs_ctx_aux_scoped p D gs nil 0 Hle eq_refl); intros; cbn; eauto.
  Qed.
End Closed.

Lemma length_ind_nparams_sub : forall D σ, List.length (tele_sub (ind_nparams D) σ) = ind_nn D.
Proof. intros; rewrite length_tele_sub; apply length_nparams. Qed.

(** The non-uniform parameters at the uniform ones [Us]. *)
Lemma nparams_sub : forall D Us τ,
    decl_closed D -> List.length Us = ind_nu D ->
    tele_sub (tele_sub (ind_nparams D) (sb_of_list Id Us)) τ
    = tele_sub (ind_nparams D) (sb_of_list Id (List.map (fun U => U[τ]) Us)).
Proof.
  intros * HD Hl; rewrite tele_sub_sub.
  eapply tele_scoped_sub_agree; [ apply decl_closed_nparams_scoped, HD |].
  intros x Hx; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
Qed.

Lemma elim_mctx_sub : forall p D Us τ,
    decl_closed D -> List.length Us = ind_nu D ->
    tele_sub (elim_mctx p D Us) τ = elim_mctx p D (List.map (fun U => U[τ]) Us).
Proof.
  intros * HD Hl; unfold elim_mctx; cbn [tele_sub]; rewrite length_ind_nparams_sub.
  f_equal; [| apply nparams_sub; assumption ].
  cbn [centry_sub]; f_equal; rewrite apps_exp_sub, map_app, !map_map; cbn [exp_sub]; f_equal; f_equal.
  - apply map_ext; intros U; apply exp_shiftn_sub_qn0.
  - rewrite <- (map_map (fun x => x) (fun M => M[sb_qn (ind_nn D) τ])), map_id.
    apply vars_from_sub; lia.
Qed.

(** ** Shapes under Substitution

    The type of a recursive result depends on its shape's components only
    through the substitution moving them, at the variables they are scoped
    in. *)
Lemma ptyp_ihty_sb_agree : forall t A β σ σ' x k,
    ptyp_scoped k t -> (forall y, y < k -> σ y = σ' y) ->
    ptyp_ihty A β σ x t = ptyp_ihty A β σ' x t.
Proof.
  induction t as [k0 Ps | k0 Ps | B t IH]; intros * Ht Hσ; cbn in *.
  1, 2: do 2 f_equal; f_equal; apply map_ext_in; intros P HP;
    eapply exp_scoped_sub_agree; [ exact (proj1 (List.Forall_forall _ _) Ht P HP) | exact Hσ ].
  destruct Ht as [HB Ht]; f_equal; [ eapply exp_scoped_sub_agree; eassumption |].
  eapply IH; [ exact Ht |]; apply sb_q_agree; exact Hσ.
Qed.

Lemma ptyp_ihty_sb_eq : forall t A β β' σ σ' x, sb_eq β β' -> sb_eq σ σ' ->
    ptyp_ihty A β σ x t = ptyp_ihty A β' σ' x t.
Proof.
  induction t as [k0 Ps | k0 Ps | B t IH]; intros * Hβ Hσ; cbn in *.
  1, 2: apply exp_sub_sb_eq; etransitivity; [ apply sb_of_list_cong, Hβ |];
    rewrite (map_ext (fun P => P[σ]) (fun P => P[σ'])) by (intros; apply exp_sub_sb_eq, Hσ); reflexivity.
  f_equal; [ apply exp_sub_sb_eq, Hσ |].
  apply IH; [ intros y; cbn [sb_compose]; rewrite Hβ; reflexivity | apply sb_q_cong, Hσ ].
Qed.

(** A shift by [s] followed by [q^(s + r) τ] is [q^r τ] followed by the
    shift. *)
Lemma sb_shiftn_qn_comm' : forall s r τ, sb_eq (ι (wk_shiftn s) ⨟ sb_qn (s + r) τ) (sb_qn r τ ⨟ ι (wk_shiftn s)).
Proof.
  intros s r τ x; cbn [sb_compose sb_of_wk sentry_sub]; rewrite sentry_sub_of_wk.
  rewrite sb_qn_plus, sb_qn_ge by (cbn; lia); cbn [wk_shiftn]; replace (x + s - s) with x by lia; reflexivity.
Qed.

(** The type of a recursive result under [τ]. *)
Lemma ptyp_ihty_sub : forall t A β σ x τ,
    (ptyp_ihty A β σ x t)[τ] = ptyp_ihty A (β ⨟ τ) (σ ⨟ τ) x[τ] t.
Proof.
  induction t as [k0 Ps | k0 Ps | B t IH]; intros *; cbn in *.
  1, 2: rewrite exp_sub_sub; apply exp_sub_sb_eq; etransitivity; [ apply sb_of_list_compose_gen |];
    rewrite map_app, !map_map; cbn [List.map];
    rewrite (map_ext (fun P => P[σ][τ]) (fun P => P[σ ⨟ τ])) by (intros; apply exp_sub_sub); reflexivity.
  f_equal; [ apply exp_sub_sub |].
  rewrite IH; cbn [exp_sub]; rewrite exp_wk_shift_sub_q, sb_q_zero; apply ptyp_ihty_sb_eq.
  - intros y; cbn [sb_compose]; rewrite !sentry_sub_sub; apply sentry_sub_sb_eq.
    intros z; cbn [sb_compose sb_of_wk sentry_sub]; rewrite sb_q_succ, sentry_sub_of_wk; reflexivity.
  - apply sb_q_compose.
Qed.

(** A base [τ] followed by [β] is the motive moved by [τ] under its
    binders, at the base [β]. *)
Lemma ptyp_ihty_base : forall t A τ β σ x n, List.length (ptyp_ps t) = n ->
    ptyp_ihty A (τ ⨟ β) σ x t = ptyp_ihty A[sb_qn (S n) τ] β σ x t.
Proof.
  induction t as [k0 Ps | k0 Ps | B t IH]; intros * Hl; cbn in *.
  1, 2: symmetry; rewrite exp_sub_sub; apply exp_sub_sb_eq;
    pose proof (sb_qn_of_list (List.map (fun P => P[σ]) Ps ++ x :: nil) τ β) as E;
    rewrite length_app, length_map, Hl, Nat.add_1_r in E; exact E.
  f_equal; rewrite <- IH by exact Hl; apply ptyp_ihty_sb_eq; [| reflexivity ].
  intros y; cbn [sb_compose]; rewrite sentry_sub_sub; reflexivity.
Qed.

(** The type of an argument of a shape, at an instance. *)
Lemma ptyp_ty_at_sb_eq : forall p t Us σ σ', sb_eq σ σ' -> ptyp_ty_at p Us σ t = ptyp_ty_at p Us σ' t.
Proof.
  intros p t; induction t as [k0 Ps | k0 Ps | B t IH]; intros * Hσ; cbn in *.
  1, 2: f_equal; f_equal; apply map_ext; intros; apply exp_sub_sb_eq, Hσ.
  f_equal; [ apply exp_sub_sb_eq, Hσ | apply IH, sb_q_cong, Hσ ].
Qed.

Lemma ptyp_ty_at_sub : forall p t Us σ τ,
    (ptyp_ty_at p Us σ t)[τ] = ptyp_ty_at p (List.map (fun U => U[τ]) Us) (σ ⨟ τ) t.
Proof.
  intros p t; induction t as [k0 Ps | k0 Ps | B t IH]; intros *; cbn [ptyp_ty_at].
  1, 2: rewrite apps_exp_sub, map_app, !map_map; cbn [exp_sub]; f_equal; f_equal; apply map_ext; intros; apply exp_sub_sub.
  cbn [exp_sub]; f_equal; [ apply exp_sub_sub |].
  rewrite IH, (ptyp_ty_at_sb_eq _ _ _ _ _ (sb_q_compose σ τ)), !map_map; f_equal.
  apply map_ext; intros U; apply exp_wk_shift_sub_q.
Qed.

(** [ptyp_ty] is the type at the uniform parameters as variables, the
    components moved by the pattern's weakening. *)
Lemma ptyp_ty_eq_at : forall p D t pat,
    ptyp_ty p D pat t = ptyp_ty_at p (ind_uvars D (List.length pat)) (ι (wk_pat pat)) t.
Proof.
  intros p D t; induction t as [k0 Ps | k0 Ps | B t IH]; intros pat; cbn [ptyp_ty ptyp_ty_at].
  1, 2: f_equal; f_equal; apply map_ext; intros; symmetry; apply exp_sub_of_wk.
  rewrite exp_sub_of_wk, IH; f_equal; cbn [List.length wk_pat].
  rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ (sb_q_of_wk (wk_pat pat))); f_equal.
  unfold ind_uvars, vars_from; rewrite map_map; apply map_ext; intros i; cbn; f_equal; lia.
Qed.

(** The components' move into a branch, followed by [τ] under the branch's
    binders, is their move at the uniform parameters moved by [τ]. *)
Lemma ihs_sub_compose : forall D Us na pat j τ x,
    decl_closed D -> List.length Us = ind_nu D -> List.length pat <= na ->
    x < pat_nargs pat + ind_np D ->
    sentry_sub (ihs_sub D Us na pat j x) (sb_qn (j + na + ind_nn D) τ) = ihs_sub D (List.map (fun U => U[τ]) Us) na pat j x.
Proof.
  intros * HD Hl Hna Hx; unfold ihs_sub; cbn [sb_compose].
  rewrite sentry_sub_sub.
  replace (j + na + ind_nn D) with ((na - List.length pat + j) + (List.length pat + ind_nn D)) by lia.
  rewrite (sentry_sub_sb_eq _ _ _ (sb_shiftn_qn_comm' _ _ τ)), <- sentry_sub_sub; f_equal.
  cbn [sb_of_wk sentry_sub].
  pose proof (wk_pat_bound pat (ind_np D) x Hx) as Hy.
  change (sentry_sub (sb_qn (length pat + ind_nn D) (sb_of_list Id Us) (wk_pat pat x)) (sb_qn (length pat + ind_nn D) τ))
    with ((sb_qn (length pat + ind_nn D) (sb_of_list Id Us) ⨟ sb_qn (length pat + ind_nn D) τ) (wk_pat pat x)).
  rewrite (sb_qn_compose_ext _ _ _ _ (fun z => eq_refl) (wk_pat pat x)).
  eapply (sb_qn_agree _ _ _ (ind_nu D)); [| pose proof (decl_closed_nu D HD); unfold ind_nn, ind_np in *; lia ].
  intros z Hz; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
Qed.

(** The recursive results: the motive at a recursive argument moves under
    the scrutinee and the non-uniform parameters. *)
Lemma ihs_ctx_aux_sub : forall D A Us na τ gs pat j,
    decl_closed D -> List.length Us = ind_nu D ->
    List.length pat + List.length gs = na ->
    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
       ptyp_scoped (pat_nargs pat + List.length (cargs_strat gs1) + ind_np D) t /\
       List.length (ptyp_ps t) = ind_nn D) ->
    tele_sub (ihs_ctx_aux D A Us na pat j gs) (sb_qn (j + na + ind_nn D) τ)
    = ihs_ctx_aux D A[sb_qn (S (ind_nn D)) τ] (List.map (fun U => U[τ]) Us) na pat j gs.
Proof.
  induction gs as [| [B | t] gs IH]; intros * HD Hl Hna HPs; cbn [ihs_ctx_aux]; [ reflexivity | |].
  - apply (IH (false :: pat) j HD Hl); [ cbn in *; lia |].
    intros gs1 t gs2 ->; destruct (HPs (ca_arg B :: gs1) t gs2 eq_refl) as [HPs' HPl]; cbn in HPs'.
    rewrite length_app in HPs'; cbn in HPs'; split; [| assumption ].
    eapply ptyp_scoped_mono; [| exact HPs' ]; cbn [pat_nargs]; lia.
  - destruct (HPs nil t gs eq_refl) as [HPs0 HPl]; cbn in HPs0; rewrite Nat.add_0_r in HPs0.
    cbn in Hna.
    rewrite tele_sub_app; cbn [tele_sub List.length]; f_equal.
    + rewrite (tele_sub_sb_eq _ _ (sb_qn (S j + na + ind_nn D) τ)) by (intros x; symmetry; apply (sb_qn_add 1 (j + na + ind_nn D) τ x)).
      apply (IH (true :: pat) (S j) HD Hl); [ cbn; lia |].
      intros gs1 Ps' gs2 ->; destruct (HPs (ca_rec t :: gs1) Ps' gs2 eq_refl) as [HPs' HPl']; cbn in HPs'; auto.
    + cbn [centry_sub sb_qn]; f_equal; f_equal.
      rewrite ptyp_ihty_sub.
      rewrite (ptyp_ihty_sb_eq _ _ _ (τ ⨟ ι (wk_shiftn (j + na + ind_nn D))) _ _ _ (sb_shiftn_qn_comm _ τ) (fun z => eq_refl)).
      rewrite (ptyp_ihty_base _ _ _ _ _ _ _ HPl).
      cbn [exp_sub]; rewrite sb_qn_lt by lia; cbn [sentry_exp sb_qn].
      eapply ptyp_ihty_sb_agree; [ exact HPs0 |].
      intros y Hy; cbn [sb_compose]; apply ihs_sub_compose; auto; lia.
Qed.

Lemma elim_bctx_sub : forall p D c gs A Us τ,
    decl_closed D -> In (c, gs) (ind_cons D) -> List.length Us = ind_nu D ->
    tele_sub (elim_bctx p D gs A Us) τ = elim_bctx p D gs A[sb_qn (S (ind_nn D)) τ] (List.map (fun U => U[τ]) Us).
Proof.
  intros * HD Hin Hl; unfold elim_bctx.
  rewrite !tele_sub_app, length_app, length_tele_sub, length_cargs_ctx, length_ind_nparams_sub.
  f_equal; [| f_equal ].
  - apply (ihs_ctx_aux_sub D A Us (List.length gs) τ gs nil 0 HD Hl eq_refl).
    destruct HD as (_ & _ & _ & _ & _ & HPs & HPl).
    intros * Heq; split; [ exact (HPs _ _ _ _ _ Hin Heq) | exact (HPl _ _ _ _ _ Hin Heq) ].
  - rewrite tele_sub_sub.
    rewrite (tele_sub_sb_eq _ _ (sb_qn (ind_nn D) (sb_of_list Id Us ⨟ τ))) by (apply sb_qn_compose_ext; reflexivity).
    eapply tele_scoped_sub_agree; [ eapply decl_closed_cargs_scoped; eassumption |].
    intros x Hx; eapply (sb_qn_agree _ _ _ (ind_nu D)); [| pose proof (decl_closed_nu D HD); unfold ind_nn; lia ].
    intros z Hz; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
  - apply nparams_sub; assumption.
Qed.

Lemma elim_bty_sub : forall p D c gs A Us τ,
    (elim_bty p D c gs A Us)[sb_qn (ind_nn D + List.length gs + cargs_nrec gs) τ]
    = elim_bty p D c gs A[sb_qn (S (ind_nn D)) τ] (List.map (fun U => U[τ]) Us).
Proof.
  intros; unfold elim_bty; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
  rewrite sb_of_list_compose with (σ := τ) (ρ' := ι (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)))
    by apply sb_shiftn_qn_comm.
  rewrite length_app, length_vars_from; cbn [List.length]; rewrite Nat.add_1_r.
  intros x; cbn [sb_compose]; f_equal; f_equal.
  rewrite map_app; cbn [List.map]; f_equal; [ apply vars_from_sub; lia |]; f_equal.
  rewrite apps_exp_sub, !map_app, !map_map; cbn [exp_sub]; f_equal; f_equal; [| f_equal; apply vars_from_sub; lia ].
  apply map_ext; intros U; apply exp_shiftn_sub_qn0.
Qed.

(** The branches moved: each under as many binders as it binds. *)
Definition brs_sub (Bs : list (String.string * nat * exp)) (τ : sub) : list (String.string * nat * exp) :=
  List.map (fun b => (fst b, (snd b)[sb_qn (snd (fst b)) τ])) Bs.

Lemma ptyp_ih_sb_eq : forall p nm t A Bs σ σ' M, sb_eq σ σ' -> ptyp_ih p nm A Bs σ M t = ptyp_ih p nm A Bs σ' M t.
Proof.
  intros p nm t; induction t as [k0 Ps | k0 Ps | B t IH]; intros * Hσ; cbn; [ reflexivity | reflexivity |].
  f_equal; [ apply exp_sub_sb_eq, Hσ | apply IH, sb_q_cong, Hσ ].
Qed.

Lemma brs_sub_wk_shift : forall Bs τ, brs_sub (brs_wk Bs ↑) (q τ) = brs_wk (brs_sub Bs τ) ↑.
Proof.
  intros; unfold brs_sub, brs_wk; rewrite !map_map; apply map_ext; intros [[c k] B]; cbn [fst snd]; f_equal.
  apply exp_wk_sub_comm_ext, sb_qn_comm_ext; intros; reflexivity.
Qed.

(** The recursive result of a shape under [τ]. *)
Lemma ptyp_ih_sub : forall p nm t A Bs σ M τ,
    (ptyp_ih p nm A Bs σ M t)[τ] = ptyp_ih p nm A[sb_qn nm τ] (brs_sub Bs τ) (σ ⨟ τ) M[τ] t.
Proof.
  intros p nm t; induction t as [k0 Ps | k0 Ps | B t IH]; intros *; cbn [ptyp_ih];
    [ cbn [exp_sub]; rewrite ?qname_mod_sub; reflexivity .. |].
  cbn [exp_sub]; f_equal; [ apply exp_sub_sub |].
  rewrite IH, (ptyp_ih_sb_eq _ _ _ _ _ _ _ _ (sb_q_compose σ τ)); f_equal.
  - apply exp_wk_sub_comm_ext, sb_qn_comm_ext; intros; reflexivity.
  - apply brs_sub_wk_shift.
  - cbn [exp_sub]; rewrite exp_wk_shift_sub_q, sb_q_zero; reflexivity.
Qed.

Lemma elim_ihs_sb_eq : forall p nm A Bs gs σ σ' As, sb_eq σ σ' -> elim_ihs p nm A Bs σ gs As = elim_ihs p nm A Bs σ' gs As.
Proof.
  intros p nm A Bs gs; induction gs as [| [] gs IH]; intros σ σ' [| N As] Hσ; cbn [elim_ihs]; try reflexivity.
  - apply IH, sb_extend_cong, Hσ.
  - f_equal; [ apply ptyp_ih_sb_eq, Hσ | apply IH, Hσ ].
Qed.

Lemma elim_ihs_sub : forall p nm A Bs gs σ As τ,
    List.map (fun N => N[τ]) (elim_ihs p nm A Bs σ gs As)
    = elim_ihs p nm A[sb_qn nm τ] (brs_sub Bs τ) (σ ⨟ τ) gs (List.map (fun N => N[τ]) As).
Proof.
  intros p nm A Bs gs; induction gs as [| [] gs IH]; intros σ [| N As] τ; cbn [elim_ihs List.map]; try reflexivity.
  - rewrite IH; apply elim_ihs_sb_eq, sb_extend_compose.
  - rewrite ptyp_ih_sub, IH; reflexivity.
Qed.

Lemma ptyp_ih_agree : forall p nm t A Bs σ σ' M k,
    ptyp_scoped k t -> (forall y, y < k -> σ y = σ' y) -> ptyp_ih p nm A Bs σ M t = ptyp_ih p nm A Bs σ' M t.
Proof.
  intros p nm t; induction t as [k0 Ps | k0 Ps | B t IH]; intros * Ht Hσ; cbn in *; [ reflexivity | reflexivity |].
  destruct Ht as [HB Ht]; f_equal; [ eapply exp_scoped_sub_agree; eassumption |].
  eapply IH; [ exact Ht |]; apply sb_q_agree; exact Hσ.
Qed.

Lemma elim_ihs_agree : forall p nm A Bs gs σ σ' As k,
    (forall y, y < k -> σ y = σ' y) ->
    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ptyp_scoped (List.length (cargs_strat gs1) + k) t) ->
    elim_ihs p nm A Bs σ gs As = elim_ihs p nm A Bs σ' gs As.
Proof.
  intros p nm A Bs gs; induction gs as [| [A0 | t] gs IH]; intros σ σ' [| N As] k Hσ Ht; cbn [elim_ihs]; try reflexivity.
  - apply (IH _ _ _ (S k)).
    + intros [| y] Hy; cbn; [ reflexivity | apply Hσ; lia ].
    + intros gs1 t gs2 ->; specialize (Ht (ca_arg A0 :: gs1) t gs2 eq_refl); cbn in Ht; rewrite length_app in Ht; cbn in Ht.
      eapply ptyp_scoped_mono; [| exact Ht ]; lia.
  - f_equal; [ eapply ptyp_ih_agree; [ exact (Ht nil t gs eq_refl) | exact Hσ ] |].
    eapply IH; [ exact Hσ |]; intros gs1 t' gs2 ->; exact (Ht (ca_rec t :: gs1) t' gs2 eq_refl).
Qed.

(** The recursive results of [ι] under [τ]: the parameters the shapes'
    domains are instantiated at move. *)
Lemma elim_ihs_sub_inst : forall D c gs p nm A Bs Ps As τ,
    decl_closed D -> In (c, gs) (ind_cons D) -> List.length Ps = ind_np D ->
    List.map (fun N => N[τ]) (elim_ihs p nm A Bs (sb_of_list Id Ps) gs As)
    = elim_ihs p nm A[sb_qn nm τ] (brs_sub Bs τ) (sb_of_list Id (List.map (fun P => P[τ]) Ps)) gs (List.map (fun N => N[τ]) As).
Proof.
  intros * HD Hin Hl; rewrite elim_ihs_sub.
  eapply (elim_ihs_agree _ _ _ _ _ _ _ _ (List.length Ps)).
  - intros y Hy; cbn [sb_compose]; apply sb_of_list_lt_compose; exact Hy.
  - intros gs1 t gs2 E; pose proof HD as (_ & _ & _ & _ & _ & Ht & _); rewrite Hl; exact (Ht _ _ _ _ _ Hin E).
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

Lemma ind_ty_sub : forall D τ, decl_closed D -> (ind_ty D)[τ] = ind_ty D.
Proof. intros; apply exp_closed_sub, decl_closed_ind_ty; assumption. Qed.

Lemma con_ty_sub : forall p D c gs τ, decl_closed D -> ind_con D c = Some gs -> (con_ty p D gs)[τ] = con_ty p D gs.
Proof. intros; apply exp_closed_sub; eapply decl_closed_con_ty; [ eassumption | apply cons_lookup_in; eassumption ]. Qed.

(** The parameters typed one by one at the instances of their telescope,
    and the arguments at the instances of theirs at the parameters. *)
Lemma params_insts_sub : forall D Ps τ,
    decl_closed D ->
    List.map (fun T => T[τ]) (tele_insts (ind_params D) Id Ps)
    = tele_insts (ind_params D) Id (List.map (fun P => P[τ]) Ps).
Proof.
  intros * HD; apply (tele_insts_sub _ 0); [ apply decl_closed_params, HD | apply HD | lia ].
Qed.

Lemma cargs_insts_sub : forall p D c gs Ps As τ,
    decl_closed D -> ind_con D c = Some gs -> List.length Ps = ind_np D ->
    List.map (fun T => T[τ]) (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As)
    = tele_insts (cargs_ctx p D gs) (sb_of_list Id (List.map (fun P => P[τ]) Ps)) (List.map (fun N => N[τ]) As).
Proof.
  intros * HD Hc Hl; apply (tele_insts_sub _ (ind_np D)).
  - apply cargs_ctx_aux_ass.
  - eapply decl_closed_cargs_scoped; [ eassumption | apply cons_lookup_in; eassumption ].
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

Lemma elim_mctx_wk : forall p D Us φ,
    decl_closed D -> List.length Us = ind_nu D ->
    tele_wk (elim_mctx p D Us) φ = elim_mctx p D (List.map (fun U => U[φ]ʷ) Us).
Proof. intros; rewrite <- tele_sub_of_wk, elim_mctx_sub, map_sub_of_wk by assumption; reflexivity. Qed.

Lemma elim_bctx_wk : forall p D c gs A Us φ,
    decl_closed D -> In (c, gs) (ind_cons D) -> List.length Us = ind_nu D ->
    tele_wk (elim_bctx p D gs A Us) φ = elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us).
Proof.
  intros; rewrite <- tele_sub_of_wk; erewrite elim_bctx_sub by eassumption.
  rewrite exp_sub_qn_of_wk, map_sub_of_wk; reflexivity.
Qed.

Lemma elim_bty_wk : forall p D c gs A Us φ,
    (elim_bty p D c gs A Us)[wk_qn (ind_nn D + List.length gs + cargs_nrec gs) φ]ʷ
    = elim_bty p D c gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us).
Proof. intros; rewrite <- exp_sub_qn_of_wk, elim_bty_sub, exp_sub_qn_of_wk, map_sub_of_wk; reflexivity. Qed.

Lemma elim_ihs_wk_inst : forall D c gs p nm A Bs Ps As φ,
    decl_closed D -> In (c, gs) (ind_cons D) -> List.length Ps = ind_np D ->
    List.map (fun N => N[φ]ʷ) (elim_ihs p nm A Bs (sb_of_list Id Ps) gs As)
    = elim_ihs p nm A[wk_qn nm φ]ʷ (List.map (fun b => (fst b, (snd b)[wk_qn (snd (fst b)) φ]ʷ)) Bs)
        (sb_of_list Id (List.map (fun P => P[φ]ʷ) Ps)) gs (List.map (fun N => N[φ]ʷ) As).
Proof.
  intros; rewrite <- !map_sub_of_wk; erewrite elim_ihs_sub_inst by eassumption.
  rewrite exp_sub_qn_of_wk, brs_sub_of_wk; reflexivity.
Qed.

Lemma ind_ty_wk : forall D φ, decl_closed D -> (ind_ty D)[φ]ʷ = ind_ty D.
Proof. intros; apply exp_closed_wk, decl_closed_ind_ty; assumption. Qed.

Lemma ind_ty_at_wk : forall D Us φ, decl_closed D -> List.length Us <= ind_np D ->
    (ind_ty_at D Us)[φ]ʷ = ind_ty_at D (List.map (fun U => U[φ]ʷ) Us).
Proof.
  intros * Hc Hl; unfold ind_ty_at; rewrite exp_wk_sb_of_list, List.length_map; f_equal.
  apply exp_scoped_wk_id with (n := List.length Us); [ apply decl_closed_ind_ty_at; assumption |].
  intros; apply wk_qn_lt; assumption.
Qed.

Lemma ind_ty_at_sub : forall D Us τ, decl_closed D -> List.length Us <= ind_np D ->
    (ind_ty_at D Us)[τ] = ind_ty_at D (List.map (fun U => U[τ]) Us).
Proof.
  intros * Hc Hl; unfold ind_ty_at; rewrite exp_sub_sb_of_list, List.length_map; f_equal.
  apply exp_scoped_sub_id with (n := List.length Us); [ apply decl_closed_ind_ty_at; assumption |].
  intros; apply sb_qn_lt; assumption.
Qed.

Lemma ind_ty_at_nil : forall D, ind_ty_at D nil = ind_ty D.
Proof. intros; unfold ind_ty_at, ind_ty, ind_np; cbn [List.length sb_of_list]; rewrite Nat.sub_0_r, List.firstn_all; apply exp_sub_id. Qed.

Lemma con_ty_wk : forall p D c gs φ, decl_closed D -> ind_con D c = Some gs -> (con_ty p D gs)[φ]ʷ = con_ty p D gs.
Proof. intros; apply exp_closed_wk; eapply decl_closed_con_ty; [ eassumption | apply cons_lookup_in; eassumption ]. Qed.

Lemma params_insts_wk : forall D Ps φ,
    decl_closed D ->
    List.map (fun T => T[φ]ʷ) (tele_insts (ind_params D) Id Ps)
    = tele_insts (ind_params D) Id (List.map (fun P => P[φ]ʷ) Ps).
Proof. intros; rewrite <- !map_sub_of_wk; apply params_insts_sub; assumption. Qed.

Lemma cargs_insts_wk : forall p D c gs Ps As φ,
    decl_closed D -> ind_con D c = Some gs -> List.length Ps = ind_np D ->
    List.map (fun T => T[φ]ʷ) (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As)
    = tele_insts (cargs_ctx p D gs) (sb_of_list Id (List.map (fun P => P[φ]ʷ) Ps)) (List.map (fun N => N[φ]ʷ) As).
Proof. intros; rewrite <- !map_sub_of_wk; eapply cargs_insts_sub; eassumption. Qed.
