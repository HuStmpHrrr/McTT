(** * Transport along a Module Substitution

    A judgment moves to another global context when everything in it is
    substituted by the same module substitution [μ], and the local context is
    extended below by [E] — the parameters of a frame that was closed, which
    became λ-variables.  What has to be supplied is exactly what [μ] puts in: a
    parameter, and a global, each typed at the substituted type.  Pushing a
    frame, growing one, reading out of a nested module, filing a unit and
    adding a level are all instances. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Scoping.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Lemma ctx_lookup_app_left : forall Γ Δ x A, Γ ∋ #x : A -> Γ ++ Δ ∋ #x : A.
Proof. induction 1; cbn; constructor; assumption. Qed.

(** η: the weakening is under the binder the substitution is lifted past. *)
Lemma exp_msub_sub_shift : forall (M : exp) μ, M[Wk][ms_q μ]ᵐ = M[μ]ᵐ[Wk].
Proof. intros; rewrite !exp_sub_of_shift, exp_msub_shift_wk; reflexivity. Qed.

Section MSubTransport.
  Variables (Θ1 Θ2 : gdeps) (Ξ1 Ξ2 : gstack) (μ : msub) (E : ctx).

  (** The context a source context [Γ] becomes, and what a term under [Γ]
      becomes. *)
  #[local] Notation tctx Γ := (Γ[μ]ᵐ ++ E).
  #[local] Notation tm Γ M := (M[ms_qn (length Γ) μ]ᵐ).

  Hypothesis Hbase : ⊢ Θ2 ⍮ Ξ2 ⍮ E.
  Hypothesis Hparam : forall n U k T Γ,
      List.nth_error Ξ1 n = Some U ->
      gu_params U ∋ #k : T ->
      ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ $[n, k] : tm Γ (T[↑ₘ (S n)]ᵐ[sb_params n]) /\
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ $[n, k] ≈ tm Γ $[n, k] : tm Γ (T[↑ₘ (S n)]ᵐ[sb_params n]).
  Hypothesis Hglob : forall r Δ b A B Γ,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
      ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) : tm Γ (ctx_pi Δ A) /\
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) ≈ tm Γ (a_glob r) : tm Γ (ctx_pi Δ A).
  Hypothesis Hunfold : forall r Δ A M Γ,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def true A (Some M) ->
      ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) ≈ tm Γ (ctx_fn Δ M) : tm Γ (ctx_pi Δ A).

  Lemma msub_preserves_wf :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ = Θ1 -> Ξ = Ξ1 -> ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = Θ1 -> Ξ = Ξ1 ->
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ M : tm Γ A) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ = Θ1 -> Ξ = Ξ1 ->
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ M ≈ tm Γ M' : tm Γ A) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ = Θ1 -> Ξ = Ξ1 ->
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ A ⊆ tm Γ A').
  Proof.
    apply syntactic_wf_mut_ind; intros; subst;
      repeat match goal with IH : ?x = ?x -> ?x' = ?x' -> _ |- _ => specialize (IH eq_refl eq_refl) end.
    (* a binder lifts [μ] once more, which is how [exp_msub] goes under it *)
    all: cbn [length ctx_msub msubst MSub_ctx MSub_exp exp_msub ms_qn List.app] in *.
    all: try rewrite !exp_msub_sub1 in *; try rewrite !exp_msub_sub2 in *;
      try rewrite !exp_msub_sub_succ in *; try rewrite !exp_msub_sub_shift in *.
    all: try solve [ econstructor; eauto | exact Hbase ].
    (* what [μ] puts in: a variable is looked up, a parameter and a global are
       supplied *)
    all: try match goal with
      | H : ?Γ ∋ # _ : _ |- _ =>
          econstructor; [ assumption | apply ctx_lookup_app_left, ctx_lookup_msub; exact H ]
      | Hn : List.nth_error Ξ1 _ = Some _, Hk : gu_params _ ∋ # _ : _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _ |- _ =>
          pose proof (Hparam _ _ _ _ _ Hn Hk HΓ) as [Hp1 Hp2];
          first [ exact Hp1 | exact Hp2 ]
      | Hl : Θ1 ⍮ Ξ1 ∋ᵍ _ ⇒ _ ⍮ ge_def true _ (Some _), HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _
        |- _ ⍮ _ ⍮ _ ⊢ _ ≈ _[_]ᵐ : _ =>
          exact (Hunfold _ _ _ _ _ Hl HΓ)
      | Hl : Θ1 ⍮ Ξ1 ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _ |- _ =>
          pose proof (Hglob _ _ _ _ _ _ Hl HΓ) as [Hg1 Hg2];
          first [ exact Hg1 | exact Hg2 ]
      end.
    (* η *)
    rewrite <- exp_msub_shift_wk; econstructor; eauto.
  Qed.
End MSubTransport.

(** ** Module Substitution on Telescopes *)

Lemma ctx_msub_ext : forall (Δ : ctx) μ μ', ms_eq μ μ' -> Δ[μ]ᵐ = Δ[μ']ᵐ.
Proof.
  induction Δ; intros * H; cbn; [ reflexivity |].
  f_equal; [ apply exp_msub_ext, ms_qn_cong, H | apply IHΔ, H ].
Qed.

Lemma ctx_msub_shift_shift : forall (Δ : ctx) a b, Δ[↑ₘ a]ᵐ[↑ₘ b]ᵐ = Δ[↑ₘ (b + a)]ᵐ.
Proof.
  induction Δ; intros; cbn; [ reflexivity |]; f_equal; [| apply IHΔ ].
  rewrite ctx_msub_length, !(exp_msub_ext _ _ _ (ms_qn_shift _ _)).
  apply exp_msub_shift_shift.
Qed.

(** With no frame in scope, there is nothing for a shift to move. *)
Lemma exp_msub_shift_nil : forall (M : exp) n k, exp_scoped n nil M -> M[↑ₘ k]ᵐ = M.
Proof.
  induction M; intros * HM; cbn in *; destruct_all; f_equal.
  all: try rewrite (exp_msub_ext _ _ _ (ms_q_shift _)).
  all: try rewrite (exp_msub_ext _ (ms_q (ms_q (↑ₘ _))) _ (ms_qn_shift 2 _)).
  all: eauto.
  - destruct HM as [c [Hc _]]; destruct (lp_mod l); discriminate.
  - destruct p as [[fp | m] ip]; unfold path_ok in *; cbn in *; [ reflexivity | lia ].
Qed.

Lemma ctx_msub_shift_nil : forall (Δ : ctx) n k, ctx_scoped n nil Δ -> Δ[↑ₘ k]ᵐ = Δ.
Proof.
  induction Δ; intros * H; cbn in *; destruct_all; [ reflexivity |]; f_equal; eauto.
  rewrite (exp_msub_ext _ _ _ (ms_qn_shift _ _)); eauto using exp_msub_shift_nil.
Qed.

Lemma opt_msub_shift_shift : forall (B : option exp) a b, B[↑ₘ a]ᵐ[↑ₘ b]ᵐ = B[↑ₘ (b + a)]ᵐ.
Proof. intros [X |] ? ?; cbn; rewrite ?exp_msub_shift_shift; reflexivity. Qed.

Lemma opt_msub_shift_nil : forall (B : option exp) n k, opt_scoped n nil B -> B[↑ₘ k]ᵐ = B.
Proof. intros [X |] ? ? HX; cbn in *; [ rewrite (exp_msub_shift_nil _ _ _ HX) |]; reflexivity. Qed.

(** ** Pushing a Frame *)

Lemma gc_lookup_push : forall Θ U Ξ r Δ b A B,
    units_scoped Θ ->
    Θ ⍮ Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
    Θ ⍮ U :: Ξ ∋ᵍ r[p_rel 1 nil]ᵖ ⇒ Δ[↑ₘ 1]ᵐ ⍮ ge_def b A[↑ₘ 1]ᵐ B[↑ₘ 1]ᵐ.
Proof.
  intros * HΘ Hlk; inversion Hlk; subst.
  - (* an open frame, one further out *)
    rewrite path_open_shift_rel, ctx_msub_shift_shift, !exp_msub_shift_shift, opt_msub_shift_shift.
    eapply (gcl_rel _ _ (S n) U0); cbn; eassumption.
  - (* a filed unit: closed, so nothing moves *)
    destruct (HΘ _ _ ltac:(eassumption)) as [Hp Hc].
    match goal with H : gu_mod U0 ∋ _ ⇒ _ ⍮ _ |- _ =>
      destruct (Hc _ _ _ _ _ H) as (HΔ & HA & HB) end.
    assert (ctx_scoped 0 nil (Δ0[close (p_abs fp nil) (length (gu_params U0))]ᵐ ++ gu_params U0)) as HR
      by (apply ctx_scoped_app; split;
          [ rewrite Nat.add_0_r; apply ctx_scoped_msub_close; [ apply close_ok_abs | assumption ]
          | assumption ]).
    rewrite (ctx_msub_shift_nil _ _ _ HR),
      (exp_msub_shift_nil _ _ _ (exp_scoped_msub_close _ _ _ _ _ (close_ok_abs _ _) HA)),
      (opt_msub_shift_nil _ _ _ (opt_scoped_msub_close _ _ _ _ _ (close_ok_abs _ _) HB)).
    econstructor; eassumption.
Qed.

Corollary push_preserves_wf : forall Θ U Ξ,
    ⊢g Θ ⍮ U :: Ξ ->
    (forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ U :: Ξ ⍮ Γ[↑ₘ 1]ᵐ) /\
    (forall Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ U :: Ξ ⍮ Γ[↑ₘ 1]ᵐ ⊢ M[↑ₘ 1]ᵐ : A[↑ₘ 1]ᵐ) /\
    (forall Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
        Θ ⍮ U :: Ξ ⍮ Γ[↑ₘ 1]ᵐ ⊢ M[↑ₘ 1]ᵐ ≈ M'[↑ₘ 1]ᵐ : A[↑ₘ 1]ᵐ) /\
    (forall Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ U :: Ξ ⍮ Γ[↑ₘ 1]ᵐ ⊢ A[↑ₘ 1]ᵐ ⊆ A'[↑ₘ 1]ᵐ).
Proof.
  intros * Hg.
  assert (HΘ : units_scoped Θ) by (eapply wf_scoped; eassumption).
  assert (Hb : ⊢ Θ ⍮ U :: Ξ ⍮ ⋅) by (constructor; assumption).
  destruct (msub_preserves_wf Θ Θ Ξ (U :: Ξ) (↑ₘ 1) nil) as (Hc & He & Hq & Hs).
  - assumption.
  - (* a parameter is one frame further out *)
    intros * Hn Hk HΓ.
    rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), exp_params_shift.
    cbn [msubst MSub_exp exp_msub ms_param ms_shift lp_mod lp_param].
    split; econstructor; cbn; eassumption.
  - intros * Hl HΓ.
    rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_pi_msub, (exp_msub_ext _ _ _ (ms_qn_shift _ _)).
    cbn [msubst MSub_exp exp_msub ms_glob ms_shift].
    pose proof (gc_lookup_push _ U _ _ _ _ _ _ HΘ Hl) as Hl'.
    split; econstructor; eassumption.
  - intros * Hl HΓ.
    rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_pi_msub, ctx_fn_msub,
      !(exp_msub_ext _ _ _ (ms_qn_shift _ _)).
    cbn [msubst MSub_exp exp_msub ms_glob ms_shift].
    pose proof (gc_lookup_push _ U _ _ _ _ _ _ HΘ Hl) as Hl'; cbn in Hl'.
    econstructor; eassumption.
  - repeat split; intros * H; rewrite <- (List.app_nil_r Γ[↑ₘ 1]ᵐ);
      [ exact (Hc _ _ _ H eq_refl eq_refl)
      | pose proof (He _ _ _ _ _ H eq_refl eq_refl) as H'
      | pose proof (Hq _ _ _ _ _ _ H eq_refl eq_refl) as H'
      | pose proof (Hs _ _ _ _ _ H eq_refl eq_refl) as H' ];
      rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)) in H'; exact H'.
Qed.

(** ** Transport with Nothing to Substitute

    Growing a frame and adding a level move nothing: resolution carries over as
    it is, and the frames have the same parameters. *)

Lemma ms_q_id : ms_eq (ms_q ms_id) ms_id.
Proof. split; intros; reflexivity. Qed.

Lemma ms_qn_id : forall k, ms_eq (ms_qn k ms_id) ms_id.
Proof.
  induction k; cbn [ms_qn]; [ split; reflexivity |].
  destruct IHk as [H1 H2]; split; intros; cbn; rewrite ?H1, ?H2; reflexivity.
Qed.

Lemma exp_msub_qn_id : forall k (M : exp), M[ms_qn k ms_id]ᵐ = M.
Proof. intros; rewrite (exp_msub_ext _ _ _ (ms_qn_id _)); apply exp_msub_id. Qed.

Lemma ctx_msub_id : forall (Δ : ctx), Δ[ms_id]ᵐ = Δ.
Proof. induction Δ; cbn; [ reflexivity |]; rewrite exp_msub_qn_id; f_equal; assumption. Qed.

Corollary rebase_preserves_wf : forall Θ1 Θ2 Ξ1 Ξ2,
    (forall r Δ b A B, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b A B -> Θ2 ⍮ Ξ2 ∋ᵍ r ⇒ Δ ⍮ ge_def b A B) ->
    (forall n U, List.nth_error Ξ1 n = Some U ->
       exists U', List.nth_error Ξ2 n = Some U' /\ gu_params U' = gu_params U) ->
    ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅ ->
    (forall Γ, ⊢ Θ1 ⍮ Ξ1 ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A').
Proof.
  intros * Hr Hn Hb.
  destruct (msub_preserves_wf Θ1 Θ2 Ξ1 Ξ2 ms_id nil) as (Hc & He & Hq & Hs).
  - assumption.
  - intros * Hn1 Hk HΓ; rewrite !exp_msub_qn_id.
    destruct (Hn _ _ Hn1) as (U' & Hn2 & Hp).
    rewrite <- Hp in Hk; split; econstructor; eassumption.
  - intros * Hl HΓ; rewrite !exp_msub_qn_id; split; econstructor; eauto.
  - intros * Hl HΓ; rewrite !exp_msub_qn_id; econstructor; eauto.
  - repeat split; intros * H;
      [ pose proof (Hc _ _ _ H eq_refl eq_refl) as H'
      | pose proof (He _ _ _ _ _ H eq_refl eq_refl) as H'
      | pose proof (Hq _ _ _ _ _ _ H eq_refl eq_refl) as H'
      | pose proof (Hs _ _ _ _ _ H eq_refl eq_refl) as H' ];
      rewrite ?ctx_msub_id, ?List.app_nil_r, ?exp_msub_qn_id in H'; exact H'.
Qed.
