(** * Discharge: Closing a Frame

    Closing a module turns its parameters into λ-variables, and each reference
    to one of its members into the member, generalized, applied to them.  This
    file shows that closing a frame preserves the judgments, given that the
    members closed so far are well typed outside; and then that every member is,
    by induction on the order the members were inserted in: each entry was
    checked against the module so far, so closing it needs only the members
    before it. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Structural.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Lookup past a Telescope *)

Lemma ctx_lookup_app_r : forall E T x A,
    T ∋ #x : A ->
    E ++ T ∋ #(x + length E) : A[wk_shiftn (length E)]ʷ.
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, (exp_wk_wk_eq _ _ _ wk_shiftn_zero), exp_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- (exp_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- exp_wk_wk.
    constructor; auto.
Qed.

(** Weakening a telescope's judgments past what sits above it. *)
Lemma wf_wk_shiftn_app : forall Θ Ξ E T,
    ⊢ Θ ⍮ Ξ ⍮ E ++ T ->
    ⊢ Θ ⍮ Ξ ⍮ T ->
    Θ ⍮ Ξ ⍮ E ++ T ⊢w wk_shiftn (length E) : T.
Proof.
  intros; econstructor; [ eassumption | assumption |].
  intros; apply ctx_lookup_app_r; assumption.
Qed.

Lemma ctx_app_wf_right : forall Θ Ξ E T, ⊢ Θ ⍮ Ξ ⍮ E ++ T -> ⊢ Θ ⍮ Ξ ⍮ T.
Proof.
  induction E as [| B E IH]; intros * H; cbn in *; [ assumption |].
  apply IH; eapply ctx_decomp_left; eassumption.
Qed.

(** ** Applying to the Parameters *)

Lemma app_vars_last : forall M d c, app_vars M d (S c) = a_app (app_vars M (S d) c) (a_var d).
Proof.
  intros M d c; revert M; induction c; intros.
  - cbn; rewrite Nat.add_0_r; reflexivity.
  - change (app_vars M d (S (S c))) with (app_vars (a_app M (a_var (d + S c))) d (S c)).
    rewrite IHc; cbn [app_vars]; replace (d + S c) with (S d + c) by lia; reflexivity.
Qed.

Lemma app_vars_wk : forall M d d' c φ,
    (forall i, i < c -> φ (d + i) = d' + i) ->
    (app_vars M d c)[φ]ʷ = app_vars M[φ]ʷ d' c.
Proof.
  intros M d d' c; revert M; induction c; intros * Hφ; [ reflexivity |].
  cbn [app_vars]; rewrite IHc by (intros; apply Hφ; lia); cbn.
  rewrite Hφ by lia; reflexivity.
Qed.

(** A generalized member applied to the parameters below the local context. *)
(** One parameter applied: the innermost one sits just past [Γ]. *)
Lemma ctx_lookup_app_mid : forall Γ P B,
    Γ ++ P ▹ B ∋ #(length Γ) : B[wk_shiftn (S (length Γ))]ʷ.
Proof.
  intros; pose proof (ctx_lookup_app_r Γ (P ▹ B) 0 B[↑]ʷ ltac:(constructor)) as Hl; cbn in Hl.
  rewrite exp_wk_wk in Hl.
  replace B[wk_shiftn (S (length Γ))]ʷ with B[↑ ⊙ wk_shiftn (length Γ)]ʷ; [ exact Hl |].
  apply exp_wk_wk_eq; intros x; cbn; unfold wk_shiftn; lia.
Qed.

Lemma exp_wk_shiftn_inst : forall Y n,
    Y[wk_shiftn n]ʷ = Y[wk_q (wk_shiftn (S n))]ʷ[Id,,#n].
Proof.
  intros; rewrite exp_sub_wk_q_extend, <- exp_sub_of_wk.
  apply exp_sub_sb_eq; intros [| x]; cbn; unfold wk_shiftn; f_equal; lia.
Qed.

(** Peeling the innermost parameter [B] off [P ▹ B]: what the step of each
    [app_vars] lemma below needs, at the common level. *)
Lemma app_vars_step : forall Θ Ξ Γ P B Y i,
    ⊢ Θ ⍮ Ξ ⍮ (Γ ++ B :: nil) ++ P ->
    Θ ⍮ Ξ ⍮ P ▹ B ⊢ Y : Type@i ->
    exists k, i <= k /\ Θ ⍮ Ξ ⍮ P ⊢ Π B Y : Type@k /\
      Θ ⍮ Ξ ⍮ (Γ ++ B :: nil) ++ P ⊢ B[wk_shiftn (S (length Γ))]ʷ : Type@k /\
      Θ ⍮ Ξ ⍮ ((Γ ++ B :: nil) ++ P) ▹ B[wk_shiftn (S (length Γ))]ʷ
        ⊢w wk_q (wk_shiftn (S (length Γ))) : P ▹ B /\
      Θ ⍮ Ξ ⍮ ((Γ ++ B :: nil) ++ P) ▹ B[wk_shiftn (S (length Γ))]ʷ
        ⊢ Y[wk_q (wk_shiftn (S (length Γ)))]ʷ : Type@k.
Proof.
  intros * HΓP HY.
  assert (HP : ⊢ Θ ⍮ Ξ ⍮ P ▹ B) by mauto 2.
  destruct (ctx_decomp_right HP) as [j HB].
  assert (Hlen : length (Γ ++ B :: nil) = S (length Γ)) by (rewrite List.length_app; cbn; lia).
  assert (Hφ : Θ ⍮ Ξ ⍮ (Γ ++ B :: nil) ++ P ⊢w wk_shiftn (S (length Γ)) : P)
    by (rewrite <- Hlen; apply wf_wk_shiftn_app; [ assumption | eapply ctx_app_wf_right; eassumption ]).
  pose proof (wk_preserves_exp _ _ _ _ _ _ _ (lift_exp_max_left _ _ _ _ _ i HB) Hφ) as HB'; cbn in HB'.
  pose proof (wf_wk_q _ _ _ _ _ _ _ Hφ (lift_exp_max_left _ _ _ _ _ i HB) HB') as Hq.
  pose proof (wk_preserves_exp _ _ _ _ _ _ _ (lift_exp_max_right _ _ _ _ j _ HY) Hq) as HY'; cbn in HY'.
  exists (max j i); refine (conj _ (conj _ (conj HB' (conj Hq HY')))); [ lia |].
  eapply wf_pi_max; eassumption.
Qed.

Lemma app_vars_typed : forall P Θ Ξ Γ F Y i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ++ P ->
    Θ ⍮ Ξ ⍮ P ⊢ Y : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ++ P ⊢ F : (ctx_pi P Y)[wk_shiftn (length Γ + length P)]ʷ ->
    Θ ⍮ Ξ ⍮ Γ ++ P ⊢ app_vars F (length Γ) (length P) : Y[wk_shiftn (length Γ)]ʷ.
Proof.
  induction P as [| B P IH]; intros * HΓP HY HF; cbn [length ctx_pi] in *.
  - cbn [app_vars]; rewrite Nat.add_0_r in HF; exact HF.
  - assert (Heq : Γ ++ B :: P = (Γ ++ B :: nil) ++ P) by (rewrite <- List.app_assoc; reflexivity).
    assert (Hlen : length (Γ ++ B :: nil) = S (length Γ)) by (rewrite List.length_app; cbn; lia).
    rewrite !app_vars_last, exp_wk_shiftn_inst.
    rewrite Heq in *.
    destruct (app_vars_step _ _ _ _ _ _ _ HΓP HY) as (k & _ & HΠ & HB' & _ & HY').
    pose proof (IH _ _ (Γ ++ B :: nil) F _ _ HΓP HΠ) as IH'.
    rewrite Hlen, (Nat.add_succ_comm (length Γ)) in IH'; specialize (IH' HF); cbn in IH'.
    eapply wf_app; [ exact HB' | exact HY' | exact IH' |].
    econstructor; [ assumption | rewrite <- Heq; apply ctx_lookup_app_mid ].
Qed.

Lemma app_vars_eq : forall P Θ Ξ Γ F F' Y i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ++ P ->
    Θ ⍮ Ξ ⍮ P ⊢ Y : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ++ P ⊢ F ≈ F' : (ctx_pi P Y)[wk_shiftn (length Γ + length P)]ʷ ->
    Θ ⍮ Ξ ⍮ Γ ++ P ⊢ app_vars F (length Γ) (length P) ≈ app_vars F' (length Γ) (length P)
      : Y[wk_shiftn (length Γ)]ʷ.
Proof.
  induction P as [| B P IH]; intros * HΓP HY HF; cbn [length ctx_pi] in *.
  - cbn [app_vars]; rewrite Nat.add_0_r in HF; exact HF.
  - assert (Heq : Γ ++ B :: P = (Γ ++ B :: nil) ++ P) by (rewrite <- List.app_assoc; reflexivity).
    assert (Hlen : length (Γ ++ B :: nil) = S (length Γ)) by (rewrite List.length_app; cbn; lia).
    rewrite !app_vars_last, exp_wk_shiftn_inst.
    rewrite Heq in *.
    destruct (app_vars_step _ _ _ _ _ _ _ HΓP HY) as (k & _ & HΠ & HB' & _ & HY').
    pose proof (IH _ _ (Γ ++ B :: nil) F F' _ _ HΓP HΠ) as IH'.
    rewrite Hlen, (Nat.add_succ_comm (length Γ)) in IH'; specialize (IH' HF); cbn in IH'.
    eapply wf_exp_eq_app_cong; [ exact HB' | exact HY' | exact IH' |].
    econstructor; [ assumption | rewrite <- Heq; apply ctx_lookup_app_mid ].
Qed.

(** β, once per parameter. *)
Lemma app_vars_beta : forall P Θ Ξ Γ Z Y i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ++ P ->
    Θ ⍮ Ξ ⍮ P ⊢ Y : Type@i ->
    Θ ⍮ Ξ ⍮ P ⊢ Z : Y ->
    Θ ⍮ Ξ ⍮ Γ ++ P ⊢ app_vars (ctx_fn P Z)[wk_shiftn (length Γ + length P)]ʷ (length Γ) (length P)
      ≈ Z[wk_shiftn (length Γ)]ʷ : Y[wk_shiftn (length Γ)]ʷ.
Proof.
  induction P as [| B P IH]; intros * HΓP HY HZ; cbn [length ctx_pi ctx_fn] in *.
  - cbn [app_vars]; rewrite Nat.add_0_r; apply wf_exp_eq_refl.
    eapply wk_preserves_exp; [ eassumption | apply wf_wk_shiftn_app; [ assumption | mauto 2 ] ].
  - assert (Heq : Γ ++ B :: P = (Γ ++ B :: nil) ++ P) by (rewrite <- List.app_assoc; reflexivity).
    assert (Hlen : length (Γ ++ B :: nil) = S (length Γ)) by (rewrite List.length_app; cbn; lia).
    rewrite !app_vars_last, (exp_wk_shiftn_inst Y), (exp_wk_shiftn_inst Z).
    rewrite Heq in *.
    destruct (app_vars_step _ _ _ _ _ _ _ HΓP HY) as (k & _ & HΠ & HB' & Hq & HY').
    assert (HP : ⊢ Θ ⍮ Ξ ⍮ P ▹ B) by mauto 2.
    destruct (ctx_decomp_right HP) as [j HB].
    pose proof (IH _ _ (Γ ++ B :: nil) (λ B Z) _ _ HΓP HΠ ltac:(econstructor; eassumption)) as IH'.
    rewrite Hlen, (Nat.add_succ_comm (length Γ)) in IH'; cbn in IH'.
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ HZ Hq) as HZ'.
    assert (Hv : Θ ⍮ Ξ ⍮ (Γ ++ B :: nil) ++ P ⊢ #(length Γ) : B[wk_shiftn (S (length Γ))]ʷ)
      by (econstructor; [ assumption | rewrite <- Heq; apply ctx_lookup_app_mid ]).
    eapply wf_exp_eq_trans.
    + eapply wf_exp_eq_app_cong; [ exact HB' | exact HY' | exact IH' | mauto 2 ].
    + eapply wf_exp_eq_pi_beta; eassumption.
Qed.

(** ** Closing under Binders *)

(** Closing [k] binders in is closing at the top and then weakening past those
    binders' own context. *)
Lemma exp_msub_close_wk : forall (X : exp) k cs mp c d,
    exp_scoped k cs X ->
    X[ms_close mp c k]ᵐ[wk_qn k (wk_shiftn d)]ʷ = X[ms_close mp c (k + d)]ᵐ.
Proof.
  induction X; intros * HX; cbn in *; destruct_all; f_equal.
  all: try rewrite !(exp_msub_ext _ _ _ (ms_q_close _ _ _)).
  all: try rewrite !(exp_msub_ext _ (ms_q (ms_q (ms_close _ _ _))) _ (ms_qn_close 2 _ _ _)).
  all: try solve [ eauto ].
  all: try solve [ exact (IHX1 (S k) _ _ _ _ ltac:(eassumption))
                 | exact (IHX2 (S k) _ _ _ _ ltac:(eassumption))
                 | exact (IHX3 (S (S k)) _ _ _ _ ltac:(eassumption)) ].
  - apply wk_qn_lt; assumption.
  - destruct l as [[| m] j]; cbn; [| reflexivity ].
    rewrite wk_qn_ge by lia; unfold wk_shiftn; f_equal; lia.
  - destruct p as [[fp | [| m]] ip]; cbn; try reflexivity.
    apply app_vars_wk; intros i Hi; rewrite wk_qn_ge by lia; unfold wk_shiftn; lia.
Qed.

Corollary exp_msub_close_shiftn : forall (X : exp) cs mp c d,
    exp_scoped 0 cs X ->
    X[close mp c]ᵐ[wk_shiftn d]ʷ = X[ms_close mp c d]ᵐ.
Proof.
  intros * H; exact (exp_msub_close_wk X 0 cs mp c d H).
Qed.

Lemma ctx_pi_close : forall Δ A mp c,
    (ctx_pi Δ A)[close mp c]ᵐ = ctx_pi Δ[close mp c]ᵐ A[ms_close mp c (length Δ)]ᵐ.
Proof.
  intros; rewrite ctx_pi_msub, (exp_msub_ext _ _ _ (ms_qn_close _ _ _ _)), Nat.add_0_r; reflexivity.
Qed.

Lemma ctx_fn_close : forall Δ M mp c,
    (ctx_fn Δ M)[close mp c]ᵐ = ctx_fn Δ[close mp c]ᵐ M[ms_close mp c (length Δ)]ᵐ.
Proof.
  intros; rewrite ctx_fn_msub, (exp_msub_ext _ _ _ (ms_qn_close _ _ _ _)), Nat.add_0_r; reflexivity.
Qed.

(** ** Closing a Frame

    The innermost frame [gu_mk P Φ] of the source is closed along [mp]: its
    parameters become the λ-variables [P] below the local context, a member of
    it becomes the member read out through [mp] and applied to them, and
    everything else is read out through [mp] as it is.  What is supplied is
    where the target resolves what the source did, and that each member of the
    closed frame is well typed there, generalized. *)
Section Close.
  Variables (Θ1 Θ2 : gdeps) (Ξ1 Ξ2 : gstack) (P : ctx) (Φ : gmod) (mp : path).

  #[local] Notation c := (length P).
  #[local] Notation Ξs := (gu_mk P Φ :: Ξ1).

  Hypothesis Hbase : ⊢ Θ2 ⍮ Ξ2 ⍮ P.
  Hypothesis Hsrc : ⊢ Θ1 ⍮ Ξs ⍮ ⋅.
  (** the closed frame's parameters, and those further out *)
  Hypothesis Hhere : forall k T d,
      P ∋ #k : T -> T[↑ₘ 1]ᵐ[sb_params 0][ms_close mp c d]ᵐ = T[wk_shiftn d]ʷ.
  Hypothesis Hout : forall n U k T,
      List.nth_error Ξ1 n = Some U -> gu_params U ∋ #k : T ->
      exists U', List.nth_error Ξ2 n = Some U' /\ gu_params U' = gu_params U /\
        forall d, T[↑ₘ (S (S n))]ᵐ[sb_params (S n)][ms_close mp c d]ᵐ = T[↑ₘ (S n)]ᵐ[sb_params n].
  (** resolution *)
  Hypothesis Hglob_out : forall r Δ b pv A B,
      Θ1 ⍮ Ξs ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> p_qual r <> qu_rel 0 ->
      Θ2 ⍮ Ξ2 ∋ᵍ r[mp]ᵖ ⇒ Δ[close mp c]ᵐ ⍮
        ge_def b pv A[ms_close mp c (length Δ)]ᵐ B[ms_close mp c (length Δ)]ᵐ.
  Hypothesis Hglob_here : forall r Δ b pv A B,
      Θ1 ⍮ Ξs ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> p_qual r = qu_rel 0 ->
      Θ2 ⍮ Ξ2 ∋ᵍ r[mp]ᵖ ⇒ Δ[close mp c]ᵐ ++ P ⍮
        ge_def b pv A[ms_close mp c (length Δ)]ᵐ B[ms_close mp c (length Δ)]ᵐ.
  (** the closed frame's members, generalized *)
  Hypothesis Hhere_typ : forall r Δ b pv A B,
      Θ1 ⍮ Ξs ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> p_qual r = qu_rel 0 ->
      exists i, Θ2 ⍮ Ξ2 ⍮ P ⊢ (ctx_pi Δ A)[close mp c]ᵐ : Type@i.
  Hypothesis Hhere_body : forall r Δ A M pv,
      Θ1 ⍮ Ξs ∋ᵍ r ⇒ Δ ⍮ ge_def true pv A (Some M) -> p_qual r = qu_rel 0 ->
      Θ2 ⍮ Ξ2 ⍮ P ⊢ (ctx_fn Δ M)[close mp c]ᵐ : (ctx_pi Δ A)[close mp c]ᵐ.

  Lemma close_preserves_wf :
    (forall Γ, ⊢ Θ1 ⍮ Ξs ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ[close mp c]ᵐ ++ P) /\
    (forall Γ A M, Θ1 ⍮ Ξs ⍮ Γ ⊢ M : A ->
        Θ2 ⍮ Ξ2 ⍮ Γ[close mp c]ᵐ ++ P ⊢ M[ms_close mp c (length Γ)]ᵐ : A[ms_close mp c (length Γ)]ᵐ) /\
    (forall Γ A M M', Θ1 ⍮ Ξs ⍮ Γ ⊢ M ≈ M' : A ->
        Θ2 ⍮ Ξ2 ⍮ Γ[close mp c]ᵐ ++ P
          ⊢ M[ms_close mp c (length Γ)]ᵐ ≈ M'[ms_close mp c (length Γ)]ᵐ : A[ms_close mp c (length Γ)]ᵐ) /\
    (forall Γ A A', Θ1 ⍮ Ξs ⍮ Γ ⊢ A ⊆ A' ->
        Θ2 ⍮ Ξ2 ⍮ Γ[close mp c]ᵐ ++ P ⊢ A[ms_close mp c (length Γ)]ᵐ ⊆ A'[ms_close mp c (length Γ)]ᵐ).
  Proof.
    assert (Hqn : forall k, ms_eq (ms_qn k (close mp c)) (ms_close mp c k))
      by (intros; rewrite <- (Nat.add_0_r k) at 2; apply ms_qn_close).
    assert (Hg2 : ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅) by (constructor; eapply ctx_wf_gctx; eassumption).
    destruct (msub_preserves_wf Θ1 Θ2 Ξs Ξ2 (close mp c) P) as (Hc & He & Hq & Hs).
    - assumption.
    - (* a parameter of the closed frame is a λ-variable past [Γ]; one further
         out is one frame nearer *)
      intros * Hn Hk HΓ; rewrite !(exp_msub_ext _ _ _ (Hqn _)).
      destruct n as [| n]; cbn in Hn.
      + injection Hn as <-; cbn in Hk.
        rewrite (Hhere _ _ _ Hk); cbn [msubst MSub_exp exp_msub ms_param ms_close lp_mod lp_param].
        pose proof (ctx_lookup_app_r Γ[close mp c]ᵐ P k T Hk) as Hl.
        rewrite ctx_msub_length, Nat.add_comm in Hl.
        split; econstructor; eassumption.
      + destruct (Hout _ _ _ _ Hn Hk) as (U' & Hn' & Hp & Heq).
        rewrite Heq; cbn [msubst MSub_exp exp_msub ms_param ms_close lp_mod lp_param].
        rewrite <- Hp in Hk; split; econstructor; eassumption.
    - (* a global: its type is closed, so closing it is closing at the top *)
      intros * Hl HΓ; rewrite !(exp_msub_ext _ _ _ (Hqn _)).
      pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hsrc Hl) as HscA.
      rewrite <- (exp_msub_close_shiftn _ _ _ _ _ HscA).
      cbn [msubst MSub_exp exp_msub ms_glob ms_close].
      destruct (p_qual r) as [fp | [| m]] eqn:Hr.
      2:{ (* a member of the closed frame, applied to its parameters *)
          pose proof (Hglob_here _ _ _ _ _ _ Hl Hr) as Hl'.
          destruct (Hhere_typ _ _ _ _ _ _ Hl Hr) as [i HY].
          pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hg2 Hl') as HscT.
          rewrite ctx_pi_app, <- ctx_pi_close in HscT.
          assert (HF0 : Θ2 ⍮ Ξ2 ⍮ Γ[close mp c]ᵐ ++ P ⊢ a_glob r[mp]ᵖ
                        : ctx_pi (Δ[close mp c]ᵐ ++ P) A[ms_close mp c (length Δ)]ᵐ)
            by (econstructor; eassumption).
          rewrite ctx_pi_app, <- ctx_pi_close,
            <- (exp_closed_wk _ _ (wk_shiftn (length Γ[close mp c]ᵐ + length P)) HscT) in HF0.
          rewrite <- (ctx_msub_length (close mp c) Γ).
          split; [ eapply app_vars_typed | eapply app_vars_eq ]; eauto using wf_exp_eq_refl. }
      all: pose proof (Hglob_out _ _ _ _ _ _ Hl ltac:(rewrite Hr; discriminate)) as Hl'.
      all: pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hg2 Hl') as HscT.
      all: rewrite ctx_pi_close, (exp_closed_wk _ _ _ HscT); split; econstructor; eassumption.
    - intros * Hl HΓ; rewrite !(exp_msub_ext _ _ _ (Hqn _)).
      pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hsrc Hl) as HscA.
      pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ _ Hsrc Hl) as HscM.
      rewrite <- (exp_msub_close_shiftn _ _ _ _ _ HscA), <- (exp_msub_close_shiftn _ _ _ _ _ HscM).
      cbn [msubst MSub_exp exp_msub ms_glob ms_close].
      destruct (p_qual r) as [fp | [| m]] eqn:Hr.
      2:{ (* unfold, then β once per parameter *)
          pose proof (Hglob_here _ _ _ _ _ _ Hl Hr) as Hl'; cbn [msubst MSub_option option_map] in Hl'.
          destruct (Hhere_typ _ _ _ _ _ _ Hl Hr) as [i HY].
          pose proof (Hhere_body _ _ _ _ _ Hl Hr) as HZ.
          pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hg2 Hl') as HscT.
          pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ _ Hg2 Hl') as HscB.
          rewrite ctx_pi_app, <- ctx_pi_close in HscT.
          rewrite ctx_fn_app, <- ctx_fn_close in HscB.
          assert (HF0 : Θ2 ⍮ Ξ2 ⍮ Γ[close mp c]ᵐ ++ P ⊢ a_glob r[mp]ᵖ
                        ≈ ctx_fn (Δ[close mp c]ᵐ ++ P) M[ms_close mp c (length Δ)]ᵐ
                        : ctx_pi (Δ[close mp c]ᵐ ++ P) A[ms_close mp c (length Δ)]ᵐ)
            by (econstructor; eassumption).
          rewrite ctx_pi_app, <- ctx_pi_close, ctx_fn_app, <- ctx_fn_close,
            <- (exp_closed_wk _ _ (wk_shiftn (length Γ[close mp c]ᵐ + length P)) HscT),
            <- (exp_closed_wk _ _ (wk_shiftn (length Γ[close mp c]ᵐ + length P)) HscB) in HF0.
          rewrite <- (ctx_msub_length (close mp c) Γ).
          eapply wf_exp_eq_trans; [ eapply app_vars_eq; eassumption | eapply app_vars_beta; eassumption ]. }
      all: pose proof (Hglob_out _ _ _ _ _ _ Hl ltac:(rewrite Hr; discriminate)) as Hl';
        cbn [msubst MSub_option option_map] in Hl'.
      all: pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hg2 Hl') as HscT.
      all: pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ _ Hg2 Hl') as HscB.
      all: rewrite ctx_pi_close, ctx_fn_close, (exp_closed_wk _ _ _ HscT), (exp_closed_wk _ _ _ HscB);
        econstructor; eassumption.
    - repeat split; intros * H;
        [ exact (Hc _ _ _ H eq_refl eq_refl)
        | pose proof (He _ _ _ _ _ H eq_refl eq_refl) as H'
        | pose proof (Hq _ _ _ _ _ _ H eq_refl eq_refl) as H'
        | pose proof (Hs _ _ _ _ _ H eq_refl eq_refl) as H' ];
        rewrite !(exp_msub_ext _ _ _ (Hqn _)) in H'; exact H'.
  Qed.
End Close.

(** ** Frames Built One Member at a Time *)

Lemma ctx_msub_shift_zero : forall (Δ : ctx), Δ[↑ₘ 0]ᵐ = Δ.
Proof.
  induction Δ; cbn; [ reflexivity |]; f_equal; [| assumption ].
  rewrite (exp_msub_ext _ _ _ (ms_qn_shift _ _)); apply exp_msub_shift_zero.
Qed.

Lemma opt_msub_shift_zero : forall (B : option exp), B[↑ₘ 0]ᵐ = B.
Proof. intros [X |]; cbn; rewrite ?exp_msub_shift_zero; reflexivity. Qed.

Lemma wf_gmod_gstack : forall Θ Ξ P Φ, Θ ⍮ Ξ ⍮ P ⊢m Φ -> wf_gstack Θ Ξ.
Proof.
  intros * H; pose proof (ctx_wf_gctx _ _ _ (wf_gmod_ctx _ _ _ _ H)) as Hg.
  inversion Hg; assumption.
Qed.

Lemma wf_frame_ctx : forall Θ Ξ P Φ, Θ ⍮ Ξ ⍮ P ⊢m Φ -> ⊢ Θ ⍮ gu_mk P Φ :: Ξ ⍮ ⋅.
Proof.
  intros * H; apply wf_ctx_empty, wf_gctx_intro, wf_gstack_cons;
    [ eapply wf_gmod_gstack; eassumption | constructor; exact H ].
Qed.

Lemma wf_gmod_prefix : forall Φp Φ Θ Ξ P, gm_prefix Φp Φ -> Θ ⍮ Ξ ⍮ P ⊢m Φ -> Θ ⍮ Ξ ⍮ P ⊢m Φp.
Proof.
  intros until 1; revert Θ Ξ P; induction H; intros * Hw; [ assumption | inversion Hw; subst; auto |].
  inversion Hw as [| ? ? ? ? ? ? HΦ HE Hf]; subst.
  inversion HE; subst; econstructor; [ eassumption | constructor; auto | assumption ].
Qed.

(** A frame grown along a prefix: what it resolves carries over. *)
Lemma frame_grow : forall Θ Ξ P Φp Φ,
    gm_prefix Φp Φ ->
    ⊢ Θ ⍮ gu_mk P Φ :: Ξ ⍮ ⋅ ->
    (forall Γ, ⊢ Θ ⍮ gu_mk P Φp :: Ξ ⍮ Γ -> ⊢ Θ ⍮ gu_mk P Φ :: Ξ ⍮ Γ) /\
    (forall Γ A M, Θ ⍮ gu_mk P Φp :: Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ gu_mk P Φ :: Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ ⍮ gu_mk P Φp :: Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ ⍮ gu_mk P Φ :: Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ ⍮ gu_mk P Φp :: Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ gu_mk P Φ :: Ξ ⍮ Γ ⊢ A ⊆ A').
Proof.
  intros * Hp Hb; apply rebase_preserves_wf; [| | assumption ].
  - intros * Hl; inversion Hl as [? ? ? ? ? ? ? ? Hn Hm |]; subst; [| econstructor; eassumption ].
    destruct n as [| n]; cbn in Hn; [ injection Hn as <- |];
      (eapply gcl_rel; [ cbn; first [ reflexivity | eassumption ] | cbn in *; eauto using gm_prefix_lookup ]).
  - intros [| n] U Hn; cbn in *; [ injection Hn as <- |]; eexists; split; eauto.
Qed.

(** ** What Nothing Moves *)

(** Nothing a closed term mentions is moved by a module substitution that
    leaves filed units alone. *)
Definition ms_abs_fix (μ : msub) : Prop :=
  forall fp ip, ms_glob μ (p_abs fp ip) = a_glob (p_abs fp ip).

Lemma ms_qn_abs_fix : forall k μ, ms_abs_fix μ -> ms_abs_fix (ms_qn k μ).
Proof.
  induction k; intros * H; cbn [ms_qn]; [ assumption |].
  intros fp ip; cbn; rewrite IHk by assumption; reflexivity.
Qed.

Lemma ms_close_abs_fix : forall mp c d, ms_abs_fix (ms_close mp c d).
Proof. intros * fp ip; reflexivity. Qed.

Lemma exp_msub_nil : forall (M : exp) n μ, exp_scoped n nil M -> ms_abs_fix μ -> M[μ]ᵐ = M.
Proof.
  induction M; intros * HM Hμ; cbn in *; destruct_all; f_equal;
    eauto using (ms_qn_abs_fix 1 μ), (ms_qn_abs_fix 2 μ).
  - destruct HM as [c [Hc _]]; destruct (lp_mod l); discriminate.
  - destruct p as [[fp | m] ip]; unfold path_ok in *; cbn in *; [ apply Hμ | lia ].
Qed.

Lemma ctx_msub_nil : forall (Δ : ctx) n μ, ctx_scoped n nil Δ -> ms_abs_fix μ -> Δ[μ]ᵐ = Δ.
Proof.
  induction Δ; intros * H Hμ; cbn in *; destruct_all; [ reflexivity |]; f_equal; eauto.
  eapply exp_msub_nil; [ eassumption | apply ms_qn_abs_fix, Hμ ].
Qed.

Lemma opt_msub_nil : forall (B : option exp) n μ, opt_scoped n nil B -> ms_abs_fix μ -> B[μ]ᵐ = B.
Proof. intros [X |] * H Hμ; cbn in *; [ erewrite exp_msub_nil by eassumption |]; reflexivity. Qed.

(** What a filed unit hands back mentions no frame. *)
Lemma gc_lookup_abs_nil : forall Θ Ξ r Δ b pv A B,
    units_scoped Θ ->
    Θ ⍮ Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
    (forall n, p_qual r <> qu_rel n) ->
    ctx_scoped 0 nil Δ /\ exp_scoped (length Δ) nil A /\ opt_scoped (length Δ) nil B.
Proof.
  intros * HΘ Hl Hr; inversion Hl; subst; [ exfalso; eapply Hr; reflexivity |].
  eapply (gc_lookup_scoped Θ nil _ _ b _ _ _ I HΘ); econstructor; eassumption.
Qed.

Lemma ctx_msub_shift_close : forall (Δ : ctx) n x c d,
    Δ[↑ₘ (S n)]ᵐ[ms_close (p_rel 0 (x :: nil)) c d]ᵐ = Δ[↑ₘ n]ᵐ.
Proof.
  induction Δ; intros; cbn; [ reflexivity |]; f_equal; [| apply IHΔ ].
  rewrite ctx_msub_length, !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), (exp_msub_ext _ _ _ (ms_qn_close _ _ _ _)).
  apply exp_msub_shift_close.
Qed.

Lemma opt_msub_shift_close : forall (B : option exp) n x c d,
    B[↑ₘ (S n)]ᵐ[ms_close (p_rel 0 (x :: nil)) c d]ᵐ = B[↑ₘ n]ᵐ.
Proof. intros [X |] *; cbn; rewrite ?exp_msub_shift_close; reflexivity. Qed.

Lemma gcl_rel0 : forall Θ Ξ U ip Δ b pv A B,
    List.nth_error Ξ 0 = Some U -> gu_mod U ∋ ip ⇒ Δ ⍮ ge_def b pv A B ->
    Θ ⍮ Ξ ∋ᵍ p_rel 0 ip ⇒ Δ ⍮ ge_def b pv A B.
Proof.
  intros * Hn Hl; pose proof (gcl_rel Θ Ξ _ _ _ _ _ _ _ _ Hn Hl) as H.
  rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero in H; exact H.
Qed.

(** ** Members, Generalized, at Their Insertion *)

Definition ins_typed (Θ : gdeps) (Ξ : gstack) (P : ctx) (Φ : gmod) : Prop :=
  forall Φq ip Δ b pv A B,
    gm_ins Φ Φq ip Δ (ge_def b pv A B) ->
    (exists i, Θ ⍮ gu_mk P Φq :: Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ gu_mk P Φq :: Ξ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A).

(** ** Closing a Nested Module *)

Section Pop.
  Variables (Θ : gdeps) (Ξ : gstack) (P : ctx) (Φ : gmod) (x : String.string) (Δ' : ctx) (Φ' : gmod).

  #[local] Notation Ξ1 := (gu_mk P Φ :: Ξ).
  #[local] Notation Tgt Φq := (gu_mk P (Φ ⊳ x ↦ ge_mod Δ' Φq) :: Ξ).
  #[local] Notation mx := (p_rel 0 (x :: nil)).

  Hypothesis HΦ : Θ ⍮ Ξ ⍮ P ⊢m Φ ⊳ x ↦ ge_mod Δ' Φ'.
  Hypothesis Hins : ins_typed Θ Ξ1 Δ' Φ'.

  (** Each member of [x], closed, is well typed where [x] stood when it was
      inserted. *)
  Lemma closable_pop : forall n Φq ip Δ b pv A B,
      gm_count Φq < n ->
      gm_ins Φ' Φq ip Δ (ge_def b pv A B) ->
      (exists i, Θ ⍮ Tgt Φq ⍮ Δ' ⊢ (ctx_pi Δ A)[close mx (length Δ')]ᵐ : Type@i) /\
      (forall M, B = Some M ->
         Θ ⍮ Tgt Φq ⍮ Δ' ⊢ (ctx_fn Δ M)[close mx (length Δ')]ᵐ : (ctx_pi Δ A)[close mx (length Δ')]ᵐ).
  Proof.
    induction n as [| n IH]; intros * Hlt Hi; [ lia |].
    inversion HΦ as [| ? ? ? ? ? ? HΦ0 HE Hf]; subst.
    inversion HE as [| | ? ? ? ? HΦ' ]; subst.
    assert (HΞ : wf_gstack Θ Ξ) by (eapply wf_gmod_gstack; eassumption).
    pose proof (gm_ins_prefix _ _ _ _ _ Hi) as Hpq.
    assert (Hwq : Θ ⍮ Ξ1 ⍮ Δ' ⊢m Φq) by (eapply wf_gmod_prefix; eassumption).
    assert (Hsrc : ⊢ Θ ⍮ gu_mk Δ' Φq :: Ξ1 ⍮ ⋅) by (apply wf_frame_ctx; assumption).
    assert (Htgt : ⊢ Θ ⍮ Tgt Φq ⍮ ⋅)
      by (apply wf_frame_ctx; eapply wf_gmod_prefix; [ apply gmp_in; eassumption | eassumption ]).
    assert (Hbase : ⊢ Θ ⍮ Tgt Φq ⍮ Δ')
      by (eapply (frame_grow _ _ _ Φ); [ auto with mctt | assumption | eapply wf_gmod_ctx; eassumption ]).
    assert (HΘ : units_scoped Θ) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hsrc)).
    destruct (Hins _ _ _ _ _ _ _ Hi) as [[i HT] Hb].
    destruct (close_preserves_wf Θ Θ Ξ1 (Tgt Φq) Δ' Φq mx) as (_ & He & _ & _).
    - exact Hbase.
    - exact Hsrc.
    - intros; apply exp_params_close_here.
    - (* the frames outside [x] are those of the target, one nearer *)
      intros [| m] U k T Hn Hk; cbn in Hn; [ injection Hn as <- |];
        eexists; (split; [ cbn; first [ reflexivity | eassumption ]
                         | split; [ reflexivity | intros; apply exp_params_close_out ] ]).
    - (* outside [x]: one frame nearer, or a filed unit, which nothing moves *)
      intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst.
      + destruct n0 as [| m]; [ contradiction |].
        rewrite ctx_msub_shift_close, ctx_msub_length, exp_msub_shift_close, opt_msub_shift_close,
          path_open_in_succ.
        destruct m as [| m]; cbn in Hn; [ injection Hn as <- |];
          (eapply gcl_rel; [ cbn; first [ reflexivity | eassumption ] | cbn in *; eauto with mctt ]).
      + destruct (gc_lookup_abs_nil _ _ _ _ _ _ _ _ HΘ Hl ltac:(intros ? ?; discriminate)) as (HΔ & HA & HB).
        rewrite (ctx_msub_nil _ _ _ HΔ (ms_close_abs_fix _ _ _)),
          (exp_msub_nil _ _ _ HA (ms_close_abs_fix _ _ _)), (opt_msub_nil _ _ _ HB (ms_close_abs_fix _ _ _)).
        cbn; econstructor; eassumption.
    - (* a member of [x] is read out through it *)
      intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero, path_open_in_rel.
      eapply gcl_rel0; [ reflexivity | cbn; eapply gml_in; eassumption ].
    - (* and was inserted before, so is closed already *)
      intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero.
      destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ _ Hir) as Hcr.
      pose proof (gm_ins_prefix _ _ _ _ _ Hir) as Hpr.
      destruct (IH Φr _ _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ _ Hpq Hir)) as [[j HT'] _].
      exists j; eapply (frame_grow _ _ _ (Φ ⊳ x ↦ ge_mod Δ' Φr)); [ auto with mctt | exact Htgt | exact HT' ].
    - intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, !exp_msub_shift_zero.
      match goal with H : _[↑ₘ 0]ᵐ = Some _ |- _ => rewrite opt_msub_shift_zero in H; subst end.
      destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ _ Hir) as Hcr.
      pose proof (gm_ins_prefix _ _ _ _ _ Hir) as Hpr.
      destruct (IH Φr _ _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ _ Hpq Hir)) as [_ HM'].
      eapply (frame_grow _ _ _ (Φ ⊳ x ↦ ge_mod Δ' Φr)); [ auto with mctt | exact Htgt | exact (HM' _ eq_refl) ].
    - split.
      + exists i; exact (He _ _ _ HT).
      + intros M ->; exact (He _ _ _ (Hb _ eq_refl)).
  Qed.
End Pop.

(** ** Closing a Unit as It Is Filed *)

(** More levels: what resolved still does. *)
Lemma levels_grow : forall Θ1 Θ2 Ξ,
    (forall fq V, gds_lookup Θ1 fq = Some V -> gds_lookup Θ2 fq = Some V) ->
    ⊢ Θ2 ⍮ Ξ ⍮ ⋅ ->
    (forall Γ, ⊢ Θ1 ⍮ Ξ ⍮ Γ -> ⊢ Θ2 ⍮ Ξ ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ ⍮ Γ ⊢ A ⊆ A').
Proof.
  intros * Hg Hb; apply rebase_preserves_wf; [| | assumption ].
  - intros * Hl; inversion Hl; subst; econstructor; eauto.
  - intros; eexists; eauto.
Qed.

(** A parameter of a unit mentions no frame, so closing its frame is only
    turning the parameters into the λ-variables past [d]. *)
Lemma exp_params_close_nil : forall (M : exp) n mp c d,
    exp_scoped n nil M ->
    M[↑ₘ 1]ᵐ[sb_params 0][ms_close mp c d]ᵐ = M[wk_shiftn d]ʷ.
Proof.
  intros * HM; rewrite (exp_msub_shift_nil _ _ _ HM).
  rewrite (exp_msub_sub_gen _ (sb_params 0) (ι (wk_shiftn d)) (ms_close mp c 0)).
  - rewrite (exp_msub_nil _ _ _ HM (ms_close_abs_fix _ _ _)), exp_sub_of_wk; reflexivity.
  - repeat split.
    + intros [[| m] k]; cbn; [ f_equal; lia | reflexivity ].
    + intros [[fp | [| m]] ip]; cbn; rewrite ?app_vars_shiftn; reflexivity.
    + intros y; cbn; f_equal; lia.
Qed.

Section File.
  Variables (Θ' Θ2 : gdeps) (fp : list String.string) (PU : ctx) (ΦU : gmod).

  #[local] Notation mf := (p_abs fp nil).

  Hypothesis HU : Θ' ⍮ nil ⍮ PU ⊢m ΦU.
  Hypothesis Hins : ins_typed Θ' nil PU ΦU.
  Hypothesis Hfp : gds_lookup Θ2 fp = Some (gu_mk PU ΦU).
  Hypothesis Hgrow : forall fq V, gds_lookup Θ' fq = Some V -> gds_lookup Θ2 fq = Some V.
  Hypothesis Htgt : ⊢ Θ2 ⍮ nil ⍮ ⋅.

  (** Each member of the unit, closed, is well typed under its parameters
      once the unit is filed. *)
  Lemma closable_file : forall n Φq ip Δ b pv A B,
      gm_count Φq < n ->
      gm_ins ΦU Φq ip Δ (ge_def b pv A B) ->
      (exists i, Θ2 ⍮ nil ⍮ PU ⊢ (ctx_pi Δ A)[close mf (length PU)]ᵐ : Type@i) /\
      (forall M, B = Some M ->
         Θ2 ⍮ nil ⍮ PU ⊢ (ctx_fn Δ M)[close mf (length PU)]ᵐ : (ctx_pi Δ A)[close mf (length PU)]ᵐ).
  Proof.
    induction n as [| n IH]; intros * Hlt Hi; [ lia |].
    pose proof (gm_ins_prefix _ _ _ _ _ Hi) as Hpq.
    assert (Hwq : Θ' ⍮ nil ⍮ PU ⊢m Φq) by (eapply wf_gmod_prefix; eassumption).
    assert (Hsrc : ⊢ Θ' ⍮ gu_mk PU Φq :: nil ⍮ ⋅) by (apply wf_frame_ctx; assumption).
    assert (HP : ⊢ Θ' ⍮ nil ⍮ PU) by (eapply wf_gmod_ctx; eassumption).
    assert (Hbase : ⊢ Θ2 ⍮ nil ⍮ PU) by (eapply levels_grow; eassumption).
    assert (HΘ : units_scoped Θ') by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hsrc)).
    assert (HPs : ctx_scoped 0 nil PU) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ HP)).
    destruct (Hins _ _ _ _ _ _ _ Hi) as [[i HT] Hb].
    destruct (close_preserves_wf Θ' Θ2 nil nil PU Φq mf) as (_ & He & _ & _).
    - exact Hbase.
    - exact Hsrc.
    - intros * Hk; eapply exp_params_close_nil, ctx_scoped_lookup; eassumption.
    - intros [| m] U k T Hn; discriminate.
    - (* no frame outside the unit: only the levels below, which nothing moves *)
      intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst.
      + destruct n0 as [| m]; [ contradiction | destruct m; discriminate ].
      + destruct (gc_lookup_abs_nil _ _ _ _ _ _ _ _ HΘ Hl ltac:(intros ? ?; discriminate)) as (HΔ & HA & HB).
        rewrite (ctx_msub_nil _ _ _ HΔ (ms_close_abs_fix _ _ _)),
          (exp_msub_nil _ _ _ HA (ms_close_abs_fix _ _ _)), (opt_msub_nil _ _ _ HB (ms_close_abs_fix _ _ _)).
        cbn; econstructor; eauto.
    - (* a member of the unit is read out of it, filed *)
      intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero.
      cbn; eapply (gcl_abs _ _ _ (gu_mk PU ΦU)); [ exact Hfp | cbn; eauto using gm_prefix_lookup ].
    - intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero.
      destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ _ Hpq Hir)) as [HT' _]; exact HT'.
    - intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, !exp_msub_shift_zero.
      match goal with H : _[↑ₘ 0]ᵐ = Some _ |- _ => rewrite opt_msub_shift_zero in H; subst end.
      destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ _ Hpq Hir)) as [_ HM'];
        exact (HM' _ eq_refl).
    - split.
      + exists i; exact (He _ _ _ HT).
      + intros M ->; exact (He _ _ _ (Hb _ eq_refl)).
  Qed.
End File.
