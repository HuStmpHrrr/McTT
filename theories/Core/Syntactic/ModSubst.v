(** * The Algebra of Module Substitution

    [M[μ]ᵐ] replaces module parameters and globals; it leaves λ-variables alone
    and weakens what it puts in as it goes under binders.  It therefore commutes
    with weakening and substitution in the evident way.  The one instance the
    judgments use is [ms_close], which closes a frame; frames are addressed by
    level, so pushing one needs no substitution at all. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution.
Import Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

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

(** ** Closing under Binders *)

Lemma app_vars_wk_shift : forall M d c,
    (app_vars M d c)[↑]ʷ = app_vars M[↑]ʷ (S d) c.
Proof.
  intros M d c; revert M; induction c; intros; cbn; [ reflexivity |].
  rewrite IHc; reflexivity.
Qed.

Lemma ms_q_close : forall L mp c d, ms_eq (ms_q (ms_close L mp c d)) (ms_close L mp c (S d)).
Proof.
  intros; split.
  - intros [m k]; cbn; destruct (Nat.eqb m L); reflexivity.
  - intros [[fp | m] ip]; cbn; [ reflexivity |].
    destruct (Nat.eqb m L); cbn; rewrite ?app_vars_wk_shift; reflexivity.
Qed.

Lemma ms_qn_close : forall k L mp c d, ms_eq (ms_qn k (ms_close L mp c d)) (ms_close L mp c (k + d)).
Proof.
  induction k; intros; cbn [ms_qn]; [ split; reflexivity |].
  destruct (IHk L mp c d) as [H1 H2]; destruct (ms_q_close L mp c (k + d)) as [H3 H4].
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

(** ** The Identity *)

Definition ms_id : msub := ms_mk a_param a_glob.

Lemma exp_msub_id : forall (M : exp), M[ms_id]ᵐ = M.
Proof.
  induction M; cbn; f_equal; auto;
    rewrite <- ?IHM, <- ?IHM1, <- ?IHM2, <- ?IHM3, <- ?IHM4 at 2;
    apply exp_msub_ext; split; intros; reflexivity.
Qed.

Lemma app_vars_shiftn : forall M d c,
    (app_vars M 0 c)[ι (wk_shiftn d)] = app_vars M[ι (wk_shiftn d)] d c.
Proof.
  intros M d c; revert M; induction c; intros; cbn; [ reflexivity |].
  rewrite IHc; cbn; do 3 f_equal; lia.
Qed.

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

(** ** Parameter Types

    [ctx_ptys] lists one type per parameter, outermost first; the [j]-th is the
    binding with [j] bindings below it, read with those as parameters. *)

Lemma ctx_ptys_length : forall L Δ, length (ctx_ptys L Δ) = length Δ.
Proof.
  induction Δ; cbn; [ reflexivity |]; rewrite List.length_app, IHΔ; cbn; lia.
Qed.

Lemma ctx_ptys_nth_last : forall L A Δ,
    List.nth_error (ctx_ptys L (A :: Δ)) (length Δ) = Some A[sb_params L (length Δ)].
Proof.
  intros; cbn; rewrite List.nth_error_app2 by (rewrite ctx_ptys_length; lia).
  rewrite ctx_ptys_length, Nat.sub_diag; reflexivity.
Qed.

Lemma ctx_ptys_nth_old : forall L A Δ j,
    j < length Δ ->
    List.nth_error (ctx_ptys L (A :: Δ)) j = List.nth_error (ctx_ptys L Δ) j.
Proof.
  intros; cbn; rewrite List.nth_error_app1 by (rewrite ctx_ptys_length; lia); reflexivity.
Qed.

(** The telescope [Δa ++ Δb] has the parameter types of [Δb], the outer part,
    as a prefix. *)
Lemma ctx_ptys_app : forall L Δa Δb,
    exists ps, ctx_ptys L (Δa ++ Δb) = ctx_ptys L Δb ++ ps.
Proof.
  induction Δa as [| A Δa IH]; intros; cbn; [ exists nil; rewrite List.app_nil_r; reflexivity |].
  destruct (IH Δb) as [ps Hps]; rewrite Hps, <- List.app_assoc; eexists; reflexivity.
Qed.
