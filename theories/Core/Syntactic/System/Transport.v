(** * Transport along a Module Substitution

    A judgment moves to another global context when everything in it is
    substituted by the same module substitution [μ], and the local context is
    extended below by [E] — the parameters of a frame that was closed, which
    became λ-variables.  What has to be supplied is exactly what [μ] puts in: a
    parameter, and a global, each typed at the substituted type.  Closing a
    frame is one instance ([Discharge]); the other is the identity, which moves
    a judgment to a global context that resolves at least as much the same way:
    pushing a frame, growing one, adding a level.  Frames are named by level, so
    none of these moves a name. *)

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

  #[local] Notation tctx Γ := (Γ[μ]ᵐ ++ E).
  #[local] Notation tm Γ M := (M[ms_qn (length Γ) μ]ᵐ).

  Hypothesis Hbase : ⊢ Θ2 ⍮ Ξ2 ⍮ E.
  Hypothesis Hparam : forall lp T Γ,
      gs_param Ξ1 lp = Some T ->
      ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
      ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_param lp) : tm Γ T /\
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_param lp) ≈ tm Γ (a_param lp) : tm Γ T.
  Hypothesis Hglob : forall r b pv A B Γ,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ ge_def b pv A B ->
      ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
      ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) : tm Γ A /\
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) ≈ tm Γ (a_glob r) : tm Γ A.
  Hypothesis Hunfold : forall r A M Γ pv,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ ge_def true pv A (Some M) ->
      ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
      ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
      Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) ≈ tm Γ M : tm Γ A.

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
      | Hp : gs_param Ξ1 _ = Some _, H1 : ⊢ Θ1 ⍮ Ξ1 ⍮ _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _ |- _ =>
          pose proof (Hparam _ _ _ Hp H1 HΓ) as [Hp1 Hp2];
          first [ exact Hp1 | exact Hp2 ]
      | Hl : Θ1 ⍮ Ξ1 ∋ᵍ _ ⇒ ge_def true _ _ (Some _), H1 : ⊢ Θ1 ⍮ Ξ1 ⍮ _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _
        |- _ ⍮ _ ⍮ _ ⊢ _ ≈ _[_]ᵐ : _ =>
          exact (Hunfold _ _ _ _ _ Hl H1 HΓ)
      | Hl : Θ1 ⍮ Ξ1 ∋ᵍ _ ⇒ ge_def _ _ _ _, H1 : ⊢ Θ1 ⍮ Ξ1 ⍮ _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _ |- _ =>
          pose proof (Hglob _ _ _ _ _ _ Hl H1 HΓ) as [Hg1 Hg2];
          first [ exact Hg1 | exact Hg2 ]
      end.
    (* η *)
    rewrite <- exp_msub_shift_wk; econstructor; eauto.
  Qed.
End MSubTransport.

(** ** Transport with Nothing to Substitute *)

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

Lemma opt_msub_id : forall (B : option exp), B[ms_id]ᵐ = B.
Proof. intros [X |]; cbn; rewrite ?exp_msub_id; reflexivity. Qed.

(** One global context resolves at least what another does, the same way. *)
Definition gc_ext (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  (forall r E, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ E -> Θ2 ⍮ Ξ2 ∋ᵍ r ⇒ E) /\
  (forall lp T, gs_param Ξ1 lp = Some T -> gs_param Ξ2 lp = Some T).

Lemma gc_ext_refl : forall Θ Ξ, gc_ext Θ Ξ Θ Ξ.
Proof. split; auto. Qed.

Lemma gc_ext_trans : forall Θ1 Ξ1 Θ2 Ξ2 Θ3 Ξ3,
    gc_ext Θ1 Ξ1 Θ2 Ξ2 -> gc_ext Θ2 Ξ2 Θ3 Ξ3 -> gc_ext Θ1 Ξ1 Θ3 Ξ3.
Proof. intros * [H1 H2] [H3 H4]; split; auto. Qed.

Corollary rebase_preserves_wf : forall Θ1 Θ2 Ξ1 Ξ2,
    gc_ext Θ1 Ξ1 Θ2 Ξ2 ->
    ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅ ->
    (forall Γ, ⊢ Θ1 ⍮ Ξ1 ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A').
Proof.
  intros * [Hr Hn] Hb.
  destruct (msub_preserves_wf Θ1 Θ2 Ξ1 Ξ2 ms_id nil) as (Hc & He & Hq & Hs).
  - assumption.
  - intros * Hp _ HΓ; rewrite !exp_msub_qn_id; split; econstructor; eauto.
  - intros * Hl _ HΓ; rewrite !exp_msub_qn_id; split; econstructor; eauto.
  - intros * Hl _ HΓ; rewrite !exp_msub_qn_id; econstructor; eauto.
  - repeat split; intros * H;
      [ pose proof (Hc _ _ _ H eq_refl eq_refl) as H'
      | pose proof (He _ _ _ _ _ H eq_refl eq_refl) as H'
      | pose proof (Hq _ _ _ _ _ _ H eq_refl eq_refl) as H'
      | pose proof (Hs _ _ _ _ _ H eq_refl eq_refl) as H' ];
      rewrite ?ctx_msub_id, ?List.app_nil_r, ?exp_msub_qn_id in H'; exact H'.
Qed.

(** ** Pushing Frames

    Frames are named by level, so a frame pushed inside resolves nothing that
    was resolved before differently. *)

Lemma gc_ext_push : forall Θ Ξa Ξ, gc_ext Θ Ξ Θ (Ξa ++ Ξ).
Proof.
  intros; split.
  - intros * Hl; inversion Hl; subst; econstructor; try eassumption.
    rewrite gs_frame_app; [ assumption | eapply gs_frame_lt; eassumption ].
  - unfold gs_param; intros * Hp.
    destruct (gs_frame Ξ (lp_mod lp)) as [U |] eqn:Hn; [| discriminate ].
    rewrite gs_frame_app, Hn; [ exact Hp | eapply gs_frame_lt; eassumption ].
Qed.

Corollary gc_ext_push1 : forall Θ U Ξ, gc_ext Θ Ξ Θ (U :: Ξ).
Proof. intros; exact (gc_ext_push Θ (U :: nil) Ξ). Qed.

Corollary push_preserves_wf : forall Θ U Ξ,
    ⊢g Θ ⍮ U :: Ξ ->
    (forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ U :: Ξ ⍮ Γ) /\
    (forall Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ U :: Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ ⍮ U :: Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ U :: Ξ ⍮ Γ ⊢ A ⊆ A').
Proof.
  intros * Hg; apply rebase_preserves_wf; [ apply gc_ext_push1 | constructor; assumption ].
Qed.
