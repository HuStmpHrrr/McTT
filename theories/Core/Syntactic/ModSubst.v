(** * The Algebra of Module Substitution

    [M[μ]ᵐ] replaces module parameters and globals; it leaves λ-variables alone
    and weakens what it puts in as it goes under binders.  It therefore commutes
    with weakening and substitution in the evident way.  The two instances
    resolution uses are [↑ₘ n] and [close mp c]; the equations between them come
    down to the arithmetic of paths, which is the first section. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution.
Import Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Paths

    Each equation is a case split on the qualifier and a little arithmetic on
    truncated subtraction. *)

Ltac path_open_solve :=
  intros; repeat match goal with r : path |- _ => destruct r as [[? | ?] ?] end;
  cbn; rewrite ?Nat.sub_0_r, ?Nat.add_0_r;
  try reflexivity; try (do 2 f_equal; lia);
  try (replace (1 - S _) with 0 by lia; cbn; do 2 f_equal; lia).

Lemma path_open_here : forall r : path, r[p_rel 0 nil]ᵖ = r.
Proof. path_open_solve. Qed.

Lemma path_open_shift_add : forall a b (r : path), r[p_rel a nil]ᵖ[p_rel b nil]ᵖ = r[p_rel (b + a) nil]ᵖ.
Proof. path_open_solve. Qed.

(** Reading out through a nested module undoes pushing a frame. *)
Lemma path_open_shift_in : forall x (r : path), r[p_rel 1 nil]ᵖ[p_rel 0 (x :: nil)]ᵖ = r.
Proof. path_open_solve. Qed.

Lemma path_open_shift_succ_in : forall n x (r : path),
    r[p_rel (S n) nil]ᵖ[p_rel 0 (x :: nil)]ᵖ = r[p_rel n nil]ᵖ.
Proof. path_open_solve. Qed.

(** What comes out of a filed unit is absolute, so no further opening moves it. *)
Lemma path_open_abs_absorb : forall fp t (r : path), r[p_abs fp nil]ᵖ[t]ᵖ = r[p_abs fp nil]ᵖ.
Proof. path_open_solve. Qed.

Lemma path_open_rel_abs : forall n fp (r : path), r[p_rel n nil]ᵖ[p_abs fp nil]ᵖ = r[p_abs fp nil]ᵖ.
Proof. path_open_solve. Qed.

Lemma path_open_in_rel : forall x ip, (p_rel 0 ip)[p_rel 0 (x :: nil)]ᵖ = p_rel 0 (x :: ip).
Proof. reflexivity. Qed.

Lemma path_open_in_succ : forall x m ip, (p_rel (S m) ip)[p_rel 0 (x :: nil)]ᵖ = p_rel m ip.
Proof. intros; cbn; rewrite Nat.sub_0_r; reflexivity. Qed.

Lemma path_open_shift_rel : forall n ip, (p_rel n ip)[p_rel 1 nil]ᵖ = p_rel (S n) ip.
Proof. intros; cbn; rewrite Nat.sub_0_r; reflexivity. Qed.

(** A shifted path is never in the innermost frame. *)
Lemma path_open_shift_qual : forall n (r : path),
    p_qual r[p_rel (S n) nil]ᵖ <> qu_rel 0.
Proof. intros n [[fp | m] ip]; cbn; congruence. Qed.

(** ** Pointwise Equality *)

Definition ms_eq (μ μ' : msub) : Prop :=
  (forall lp, ms_param μ lp = ms_param μ' lp) /\ (forall p, ms_glob μ p = ms_glob μ' p).

Lemma ms_q_cong : forall μ μ', ms_eq μ μ' -> ms_eq (ms_q μ) (ms_q μ').
Proof. intros * [H1 H2]; split; intros; cbn; rewrite ?H1, ?H2; reflexivity. Qed.

Lemma exp_msub_ext : forall (M : exp) μ μ', ms_eq μ μ' -> M[μ]ᵐ = M[μ']ᵐ.
Proof.
  induction M; intros μ μ' H; cbn; try solve [ apply H ]; f_equal; eauto using ms_q_cong.
Qed.

Lemma ms_qn_cong : forall n μ μ', ms_eq μ μ' -> ms_eq (ms_qn n μ) (ms_qn n μ').
Proof. induction n; intros; cbn; [ assumption | apply ms_q_cong; auto ]. Qed.

(** ** The Two Instances under Binders *)

Lemma ms_q_shift : forall n, ms_eq (ms_q (↑ₘ n)) (↑ₘ n).
Proof. intros; split; intros; reflexivity. Qed.

Lemma ms_qn_shift : forall k n, ms_eq (ms_qn k (↑ₘ n)) (↑ₘ n).
Proof.
  induction k; intros; cbn [ms_qn]; [ split; reflexivity |].
  destruct (IHk n) as [H1 H2]; split; intros; cbn; rewrite ?H1, ?H2; reflexivity.
Qed.

Lemma app_vars_wk_shift : forall M d c,
    (app_vars M d c)[↑]ʷ = app_vars M[↑]ʷ (S d) c.
Proof.
  intros M d c; revert M; induction c; intros; cbn; [ reflexivity |].
  rewrite IHc; reflexivity.
Qed.

Lemma ms_q_close : forall mp c d, ms_eq (ms_q (ms_close mp c d)) (ms_close mp c (S d)).
Proof.
  intros; split.
  - intros [[| m] k]; reflexivity.
  - intros [[fp | [| m]] ip]; cbn; rewrite ?app_vars_wk_shift; reflexivity.
Qed.

Lemma ms_qn_close : forall k mp c d, ms_eq (ms_qn k (ms_close mp c d)) (ms_close mp c (k + d)).
Proof.
  induction k; intros; cbn [ms_qn]; [ split; reflexivity |].
  destruct (IHk mp c d) as [H1 H2]; destruct (ms_q_close mp c (k + d)) as [H3 H4].
  split; intros; cbn; rewrite ?H1, ?H2; [ apply H3 | apply H4 ].
Qed.

(** ** Commuting with Weakening and Substitution *)

Definition ms_wk (μ : msub) (φ : wk) : msub :=
  ms_mk (fun lp => (ms_param μ lp)[φ]ʷ) (fun p => (ms_glob μ p)[φ]ʷ).

Lemma exp_msub_wk : forall (M : exp) μ φ, M[μ]ᵐ[φ]ʷ = M[φ]ʷ[ms_wk μ φ]ᵐ.
Proof.
  induction M; intros μ φ; cbn; f_equal; auto;
    rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4; apply exp_msub_ext; split; intros; cbn;
    rewrite ?exp_wk_shift_wk_q; reflexivity.
Qed.

Corollary exp_msub_shift_wk : forall (M : exp) μ, M[μ]ᵐ[↑]ʷ = M[↑]ʷ[ms_q μ]ᵐ.
Proof. intros; rewrite exp_msub_wk; reflexivity. Qed.

(** A substitution [σ] before [ρ] is [τ] before [σ'], when they agree on what
    each puts in; the agreement survives going under a binder. *)
Definition ms_sub_agree (σ σ' : sub) (τ ρ : msub) : Prop :=
  (forall lp, (ms_param τ lp)[σ'] = ms_param ρ lp) /\
  (forall p, (ms_glob τ p)[σ'] = ms_glob ρ p) /\
  (forall x, (σ x)[ρ]ᵐ = σ' x).

Lemma ms_sub_agree_q : forall σ σ' τ ρ,
    ms_sub_agree σ σ' τ ρ -> ms_sub_agree (q σ) (q σ') (ms_q τ) (ms_q ρ).
Proof.
  intros * (H1 & H2 & H3); repeat split.
  - intros lp; cbn; rewrite exp_wk_shift_sub_q, H1; reflexivity.
  - intros p; cbn; rewrite exp_wk_shift_sub_q, H2; reflexivity.
  - intros [| x]; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
    rewrite <- exp_msub_shift_wk, H3; reflexivity.
Qed.

Lemma exp_msub_sub_gen : forall (M : exp) σ σ' τ ρ,
    ms_sub_agree σ σ' τ ρ ->
    M[σ][ρ]ᵐ = M[τ]ᵐ[σ'].
Proof.
  induction M; intros * H; pose proof H as (H1 & H2 & H3); cbn; try reflexivity;
    try solve [ auto | symmetry; auto ];
    f_equal; auto using ms_sub_agree_q.
Qed.

Corollary exp_msub_sub1 : forall (A N : exp) μ,
    A[Id,,N][μ]ᵐ = A[ms_q μ]ᵐ[Id,,N[μ]ᵐ].
Proof.
  intros; apply exp_msub_sub_gen; repeat split.
  - intros lp; cbn; rewrite exp_sub_shift_extend, exp_sub_id; reflexivity.
  - intros p; cbn; rewrite exp_sub_shift_extend, exp_sub_id; reflexivity.
  - intros [| x]; reflexivity.
Qed.

Corollary exp_msub_sub2 : forall (A M N : exp) μ,
    A[Id,,M,,N][μ]ᵐ = A[ms_q (ms_q μ)]ᵐ[Id,,M[μ]ᵐ,,N[μ]ᵐ].
Proof.
  intros; apply exp_msub_sub_gen; repeat split.
  - intros lp; cbn; rewrite !exp_sub_shift_extend, exp_sub_id; reflexivity.
  - intros p; cbn; rewrite !exp_sub_shift_extend, exp_sub_id; reflexivity.
  - intros [| [| x]]; reflexivity.
Qed.

Corollary exp_msub_sub_succ : forall (A : exp) μ,
    A[Wk⨟Wk,,succ #1][ms_q (ms_q μ)]ᵐ = A[ms_q μ]ᵐ[Wk⨟Wk,,succ #1].
Proof.
  intros; apply exp_msub_sub_gen; repeat split.
  - intros lp; cbn; rewrite exp_sub_shift_extend, <- exp_sub_sub, !exp_sub_of_shift; reflexivity.
  - intros p; cbn; rewrite exp_sub_shift_extend, <- exp_sub_sub, !exp_sub_of_shift; reflexivity.
  - intros [| x]; reflexivity.
Qed.

(** ** Composition *)

Definition ms_id : msub := ms_mk a_param a_glob.

Lemma exp_msub_id : forall (M : exp), M[ms_id]ᵐ = M.
Proof.
  induction M; cbn; f_equal; auto;
    rewrite <- ?IHM, <- ?IHM1, <- ?IHM2, <- ?IHM3, <- ?IHM4 at 2;
    apply exp_msub_ext; split; intros; reflexivity.
Qed.

Definition ms_comp (μ μ' : msub) : msub :=
  ms_mk (fun lp => (ms_param μ lp)[μ']ᵐ) (fun p => (ms_glob μ p)[μ']ᵐ).

Lemma exp_msub_msub : forall (M : exp) μ μ', M[μ]ᵐ[μ']ᵐ = M[ms_comp μ μ']ᵐ.
Proof.
  induction M; intros; cbn; f_equal; auto;
    rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4; apply exp_msub_ext; split; intros; cbn;
    rewrite ?exp_msub_shift_wk; reflexivity.
Qed.

Lemma exp_msub_shift_shift : forall (M : exp) a b, M[↑ₘ a]ᵐ[↑ₘ b]ᵐ = M[↑ₘ (b + a)]ᵐ.
Proof.
  intros; rewrite exp_msub_msub; apply exp_msub_ext; split.
  - intros [m k]; cbn; do 2 f_equal; lia.
  - intros p; cbn; rewrite path_open_shift_add; reflexivity.
Qed.

Lemma exp_msub_shift_zero : forall (M : exp), M[↑ₘ 0]ᵐ = M.
Proof.
  intros; rewrite <- (exp_msub_id M) at 2; apply exp_msub_ext; split.
  - intros [m k]; reflexivity.
  - intros p; cbn; rewrite path_open_here; reflexivity.
Qed.

(** Closing a nested module undoes a shift. *)
Lemma exp_msub_shift_close : forall (M : exp) n x c d,
    M[↑ₘ (S n)]ᵐ[ms_close (p_rel 0 (x :: nil)) c d]ᵐ = M[↑ₘ n]ᵐ.
Proof.
  intros; rewrite exp_msub_msub; apply exp_msub_ext; split.
  - intros [m k]; reflexivity.
  - intros p; cbn; destruct (p_qual p[p_rel (S n) nil]ᵖ) as [fp | [| m]] eqn:E;
      [| exfalso; eapply path_open_shift_qual; eassumption |];
      rewrite path_open_shift_succ_in; reflexivity.
Qed.

(** ** Parameters Read off a Telescope *)

(** A frame's parameter type, moved one frame out. *)
Lemma exp_params_shift : forall (M : exp) n,
    M[↑ₘ (S n)]ᵐ[sb_params n][↑ₘ 1]ᵐ = M[↑ₘ (S (S n))]ᵐ[sb_params (S n)].
Proof.
  intros; rewrite (exp_msub_sub_gen _ (sb_params n) (sb_params (S n)) (↑ₘ 1) (↑ₘ 1)),
    exp_msub_shift_shift by (repeat split; intros; reflexivity); reflexivity.
Qed.

Lemma app_vars_shiftn : forall M d c,
    (app_vars M 0 c)[ι (wk_shiftn d)] = app_vars M[ι (wk_shiftn d)] d c.
Proof.
  intros M d c; revert M; induction c; intros; cbn; [ reflexivity |].
  rewrite IHc; cbn; do 3 f_equal; lia.
Qed.

(** The parameters of the nested module being closed become the λ-variables
    past [d]. *)
Lemma exp_params_close_here : forall (M : exp) x c d,
    M[↑ₘ 1]ᵐ[sb_params 0][ms_close (p_rel 0 (x :: nil)) c d]ᵐ = M[wk_shiftn d]ʷ.
Proof.
  intros.
  rewrite (exp_msub_sub_gen _ (sb_params 0) (ι (wk_shiftn d)) (ms_close (p_rel 0 (x :: nil)) c 0)).
  - rewrite exp_msub_shift_close, exp_msub_shift_zero, exp_sub_of_wk; reflexivity.
  - repeat split.
    + intros [[| m] k]; cbn; [ f_equal; lia | reflexivity ].
    + intros [[fp | [| m]] ip]; cbn; rewrite ?app_vars_shiftn; reflexivity.
    + intros y; cbn; f_equal; lia.
Qed.

Lemma sb_qn_lt : forall k σ x, x < k -> sb_qn k σ x = #x.
Proof.
  induction k; intros * Hx; [ lia |]; destruct x as [| x]; cbn [sb_qn];
    rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  rewrite IHk by lia; reflexivity.
Qed.

Lemma sb_qn_params_ge : forall k m x, k <= x -> sb_qn k (sb_params m) x = $[m, x - k].
Proof.
  induction k; intros * Hx; cbn [sb_qn]; [ rewrite Nat.sub_0_r; reflexivity |].
  destruct x as [| x]; [ lia |]; rewrite sb_q_succ, IHk by lia; reflexivity.
Qed.

(** Those of a frame further out move one frame nearer. *)
Lemma exp_params_close_out_gen : forall (M : exp) k n x c d,
    M[↑ₘ (S (S n))]ᵐ[sb_qn k (sb_params (S n))][ms_close (p_rel 0 (x :: nil)) c (k + d)]ᵐ
    = M[↑ₘ (S n)]ᵐ[sb_qn k (sb_params n)].
Proof.
  induction M; intros; cbn; f_equal; auto.
  (* under a binder: the substitution is lifted, and the shift and close with it *)
  all: try rewrite !(exp_msub_ext _ _ _ (ms_q_shift _)).
  all: try rewrite !(exp_msub_ext _ _ _ (ms_q_close _ _ _)).
  all: try rewrite !(exp_msub_ext _ (ms_q (ms_q (↑ₘ _))) _ (ms_qn_shift 2 _)).
  all: try rewrite !(exp_msub_ext _ (ms_q (ms_q (ms_close _ _ _))) _ (ms_qn_close 2 _ _ _)).
  all: try solve [ exact (IHM1 (S k) n x c d) | exact (IHM2 (S k) n x c d)
                 | exact (IHM3 (S (S k)) n x c d) ].
  (* a variable: bound inside, or a parameter of the frame read off *)
  - match goal with |- (sb_qn ?k _ ?y)[_]ᵐ = _ => destruct (Nat.lt_ge_cases y k) end.
    + rewrite !sb_qn_lt by assumption; reflexivity.
    + rewrite !sb_qn_params_ge by assumption; reflexivity.
  (* a global of a frame further out *)
  - destruct (p_qual p[p_rel (S (S n)) nil]ᵖ) as [fp | [| m]] eqn:E;
      [| exfalso; eapply path_open_shift_qual; eassumption |];
      rewrite path_open_shift_succ_in; reflexivity.
Qed.

Corollary exp_params_close_out : forall (M : exp) n x c d,
    M[↑ₘ (S (S n))]ᵐ[sb_params (S n)][ms_close (p_rel 0 (x :: nil)) c d]ᵐ = M[↑ₘ (S n)]ᵐ[sb_params n].
Proof. intros; exact (exp_params_close_out_gen M 0 n x c d). Qed.

(** ** Telescopes *)

Lemma ctx_msub_length : forall μ (Δ : ctx), length Δ[μ]ᵐ = length Δ.
Proof. induction Δ; cbn; auto. Qed.

Lemma ms_qn_add : forall a b μ, ms_qn a (ms_qn b μ) = ms_qn (a + b) μ.
Proof. induction a; intros; cbn; [ reflexivity | rewrite IHa; reflexivity ]. Qed.

Lemma ctx_msub_app : forall μ (Δ Δ' : ctx),
    (Δ ++ Δ')[μ]ᵐ = Δ[ms_qn (length Δ') μ]ᵐ ++ Δ'[μ]ᵐ.
Proof.
  induction Δ as [| A Δ IH]; intros; cbn; [ reflexivity |].
  rewrite List.length_app, IH, ms_qn_add; reflexivity.
Qed.

Lemma ctx_pi_msub : forall μ (Δ : ctx) (A : exp), (ctx_pi Δ A)[μ]ᵐ = ctx_pi Δ[μ]ᵐ A[ms_qn (length Δ) μ]ᵐ.
Proof.
  induction Δ as [| B Δ IH]; intros; cbn; [ reflexivity |].
  rewrite IH; reflexivity.
Qed.

Lemma ctx_fn_msub : forall μ (Δ : ctx) (M : exp), (ctx_fn Δ M)[μ]ᵐ = ctx_fn Δ[μ]ᵐ M[ms_qn (length Δ) μ]ᵐ.
Proof.
  induction Δ as [| B Δ IH]; intros; cbn; [ reflexivity |].
  rewrite IH; reflexivity.
Qed.
