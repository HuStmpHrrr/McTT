(** * Induction over the Age of a Global Context

    What the two semantic models share about the global rules.  A judgment of
    [Θ ⍮ Ξ] is moved to another global context along a module substitution
    [μ] that is *syntactically sound* ([syn_msub]: the premises of
    [msub_preserves_wf]); an *embedding* ([Emb]) is the special case that sends
    parameters to parameters and globals to globals, and the ones the
    induction needs (push, grow, truncate a telescope, add a level) compose.

    The induction itself ([global_induction]) is over an abstract model: a
    validity [V Θ Ξ A M] of closed terms, and a notion [Snd] of sound
    substitution with two properties — an embedding whose images are valid is
    sound ([snd_emb]), and a judgment reads off along a sound substitution
    ([vread]).  Every member is then valid at [⋅], by induction on insertion
    order: a member is typed where it was inserted, a context with only older
    members, and embedded from there. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Syntactically sound module substitutions *)

Section MSub.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (μ : msub) (E : ctx).

  #[local] Notation tctx Γ := (Γ[μ]ᵐ ++ E).
  #[local] Notation tm Γ M := (M[ms_qn (length Γ) μ]ᵐ).

  (** The four hypotheses of [msub_preserves_wf], as a record. *)
  Record syn_msub : Prop :=
    { syn_base : ⊢ Θ2 ⍮ Ξ2 ⍮ E
    ; syn_param : forall n U k T Γ,
        List.nth_error Ξ1 n = Some U ->
        gu_params U ∋ #k : T ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ $[n, k] : tm Γ (T[↑ₘ (S n)]ᵐ[sb_params n]) /\
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ $[n, k] ≈ tm Γ $[n, k] : tm Γ (T[↑ₘ (S n)]ᵐ[sb_params n])
    ; syn_glob : forall r Δ b pv A B Γ,
        Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) : tm Γ (ctx_pi Δ A) /\
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) ≈ tm Γ (a_glob r) : tm Γ (ctx_pi Δ A)
    ; syn_unfold : forall r Δ A M Γ pv,
        Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def true pv A (Some M) ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        ⊢ Θ2 ⍮ Ξ2 ⍮ tctx Γ ->
        Θ2 ⍮ Ξ2 ⍮ tctx Γ ⊢ tm Γ (a_glob r) ≈ tm Γ (ctx_fn Δ M) : tm Γ (ctx_pi Δ A)
    }.
End MSub.

(** ** 2. Syntactic transport, with the source context available

    [msub_preserves_wf] with hypotheses that may also use [⊢ Θ1 ⍮ Ξ1 ⍮ Γ]
    (the minimality scheme keeps the premise, so the proof is the same).  This
    weaker demand is what makes [syn_msub] compose. *)

Section MSubTransport'.
  Variables (Θ1 Θ2 : gdeps) (Ξ1 Ξ2 : gstack) (μ : msub) (E : ctx).
  Hypothesis Hsyn : syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E.

  Lemma msub_preserves_wf' :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ = Θ1 -> Ξ = Ξ1 -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ[μ]ᵐ ++ E) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = Θ1 -> Ξ = Ξ1 ->
        Θ2 ⍮ Ξ2 ⍮ Γ[μ]ᵐ ++ E ⊢ M[ms_qn (length Γ) μ]ᵐ : A[ms_qn (length Γ) μ]ᵐ) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ = Θ1 -> Ξ = Ξ1 ->
        Θ2 ⍮ Ξ2 ⍮ Γ[μ]ᵐ ++ E ⊢ M[ms_qn (length Γ) μ]ᵐ ≈ M'[ms_qn (length Γ) μ]ᵐ : A[ms_qn (length Γ) μ]ᵐ) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ = Θ1 -> Ξ = Ξ1 ->
        Θ2 ⍮ Ξ2 ⍮ Γ[μ]ᵐ ++ E ⊢ A[ms_qn (length Γ) μ]ᵐ ⊆ A'[ms_qn (length Γ) μ]ᵐ).
  Proof.
    destruct Hsyn as [Hbase Hparam Hglob Hunfold].
    apply syntactic_wf_mut_ind; intros; subst;
      repeat match goal with IH : ?x = ?x -> ?x' = ?x' -> _ |- _ => specialize (IH eq_refl eq_refl) end.
    all: cbn [length ctx_msub msubst MSub_ctx MSub_exp exp_msub ms_qn List.app] in *.
    all: try rewrite !exp_msub_sub1 in *; try rewrite !exp_msub_sub2 in *;
      try rewrite !exp_msub_sub_succ in *; try rewrite !exp_msub_sub_shift in *.
    all: try solve [ econstructor; eauto | exact Hbase ].
    all: try match goal with
      | H : ?Γ ∋ # _ : _ |- _ =>
          econstructor; [ assumption | apply ctx_lookup_app_left, ctx_lookup_msub; exact H ]
      | Hn : List.nth_error Ξ1 _ = Some _, Hk : gu_params _ ∋ # _ : _,
        H1 : ⊢ Θ1 ⍮ Ξ1 ⍮ _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _ |- _ =>
          pose proof (Hparam _ _ _ _ _ Hn Hk H1 HΓ) as [Hp1 Hp2];
          first [ exact Hp1 | exact Hp2 ]
      | Hl : Θ1 ⍮ Ξ1 ∋ᵍ _ ⇒ _ ⍮ ge_def true _ _ (Some _),
        H1 : ⊢ Θ1 ⍮ Ξ1 ⍮ _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _
        |- _ ⍮ _ ⍮ _ ⊢ _ ≈ _[_]ᵐ : _ =>
          exact (Hunfold _ _ _ _ _ _ Hl H1 HΓ)
      | Hl : Θ1 ⍮ Ξ1 ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ _ _,
        H1 : ⊢ Θ1 ⍮ Ξ1 ⍮ _, HΓ : ⊢ Θ2 ⍮ Ξ2 ⍮ _ |- _ =>
          pose proof (Hglob _ _ _ _ _ _ _ Hl H1 HΓ) as [Hg1 Hg2];
          first [ exact Hg1 | exact Hg2 ]
      end.
    rewrite <- exp_msub_shift_wk; econstructor; eauto.
  Qed.
End MSubTransport'.

(** ** 3. Composition *)

Lemma ms_eq_trans : forall μ1 μ2 μ3, ms_eq μ1 μ2 -> ms_eq μ2 μ3 -> ms_eq μ1 μ3.
Proof. intros * [H1 H2] [H3 H4]; split; intros; rewrite ?H1, ?H2, ?H3, ?H4; reflexivity. Qed.

Lemma ms_eq_sym : forall μ1 μ2, ms_eq μ1 μ2 -> ms_eq μ2 μ1.
Proof. intros * [H1 H2]; split; intros; rewrite ?H1, ?H2; reflexivity. Qed.

Lemma ms_q_comp : forall μ ν, ms_eq (ms_q (ms_comp μ ν)) (ms_comp (ms_q μ) (ms_q ν)).
Proof. intros; split; intros; cbn; apply exp_msub_shift_wk. Qed.

Lemma ms_qn_comp : forall k μ ν, ms_eq (ms_qn k (ms_comp μ ν)) (ms_comp (ms_qn k μ) (ms_qn k ν)).
Proof.
  induction k; intros; cbn [ms_qn]; [ split; reflexivity |].
  eapply ms_eq_trans; [ apply ms_q_cong, IHk | apply ms_q_comp ].
Qed.

Lemma ctx_msub_msub : forall (Δ : ctx) μ ν, Δ[μ]ᵐ[ν]ᵐ = Δ[ms_comp μ ν]ᵐ.
Proof.
  induction Δ as [| A Δ IH]; intros; [ reflexivity |].
  change ((A :: Δ)[μ]ᵐ) with (A[ms_qn (length Δ) μ]ᵐ :: Δ[μ]ᵐ).
  change ((A[ms_qn (length Δ) μ]ᵐ :: Δ[μ]ᵐ)[ν]ᵐ)
    with (A[ms_qn (length Δ) μ]ᵐ[ms_qn (length Δ[μ]ᵐ) ν]ᵐ :: Δ[μ]ᵐ[ν]ᵐ).
  change ((A :: Δ)[ms_comp μ ν]ᵐ) with (A[ms_qn (length Δ) (ms_comp μ ν)]ᵐ :: Δ[ms_comp μ ν]ᵐ).
  rewrite IH, ctx_msub_length, exp_msub_msub; f_equal.
  apply exp_msub_ext, ms_eq_sym, ms_qn_comp.
Qed.

(** First [μ] (out of [Θ1 ⍮ Ξ1], extending by [E]), then [ν] (extending by
    [E']): [ν] is lifted past [E]. *)
Definition ms_then (μ : msub) (E : ctx) (ν : msub) : msub := ms_comp μ (ms_qn (length E) ν).

Lemma tctx_then : forall μ E ν E' Γ,
    (Γ[μ]ᵐ ++ E)[ν]ᵐ ++ E' = Γ[ms_then μ E ν]ᵐ ++ (E[ν]ᵐ ++ E').
Proof.
  intros; unfold ms_then; rewrite ctx_msub_app, ctx_msub_msub, List.app_assoc; reflexivity.
Qed.

Lemma tm_then : forall μ E ν Γ (M : exp),
    M[ms_qn (length Γ) μ]ᵐ[ms_qn (length (Γ[μ]ᵐ ++ E)) ν]ᵐ = M[ms_qn (length Γ) (ms_then μ E ν)]ᵐ.
Proof.
  intros; unfold ms_then; rewrite exp_msub_msub; apply exp_msub_ext.
  rewrite List.length_app, ctx_msub_length, <- ms_qn_add.
  apply ms_eq_sym, ms_qn_comp.
Qed.

(** Syntactic soundness composes. *)
Lemma syn_msub_then : forall Θ1 Ξ1 Θ2 Ξ2 Θ3 Ξ3 μ ν E E',
    syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E -> syn_msub Θ2 Ξ2 Θ3 Ξ3 ν E' ->
    syn_msub Θ1 Ξ1 Θ3 Ξ3 (ms_then μ E ν) (E[ν]ᵐ ++ E').
Proof.
  intros * Hμ Hν.
  destruct (msub_preserves_wf' _ _ _ _ _ _ Hμ) as (Hc1 & He1 & Hq1 & _).
  destruct (msub_preserves_wf' _ _ _ _ _ _ Hν) as (Hc2 & He2 & Hq2 & _).
  pose proof Hμ as [Hb Hp Hg Hu].
  constructor.
  - exact (Hc2 _ _ _ Hb eq_refl eq_refl).
  - intros * Hn Hk HΓ1 _.
    pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
    destruct (Hp _ _ _ _ _ Hn Hk HΓ1 HΓ2) as [D1 D2].
    pose proof (He2 _ _ _ _ _ D1 eq_refl eq_refl) as D1'.
    pose proof (Hq2 _ _ _ _ _ _ D2 eq_refl eq_refl) as D2'.
    rewrite tctx_then, !tm_then in D1', D2'; split; assumption.
  - intros * Hl HΓ1 _.
    pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
    destruct (Hg _ _ _ _ _ _ _ Hl HΓ1 HΓ2) as [D1 D2].
    pose proof (He2 _ _ _ _ _ D1 eq_refl eq_refl) as D1'.
    pose proof (Hq2 _ _ _ _ _ _ D2 eq_refl eq_refl) as D2'.
    rewrite tctx_then, !tm_then in D1', D2'; split; assumption.
  - intros * Hl HΓ1 _.
    pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
    pose proof (Hu _ _ _ _ _ _ Hl HΓ1 HΓ2) as D2.
    pose proof (Hq2 _ _ _ _ _ _ D2 eq_refl eq_refl) as D2'.
    rewrite tctx_then, !tm_then in D2'; assumption.
Qed.

Lemma syn_msub_id : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> syn_msub Θ Ξ Θ Ξ ms_id nil.
Proof.
  intros * Hg; constructor.
  - constructor; assumption.
  - intros * Hn Hk _ HΓ; rewrite !exp_msub_qn_id; split; econstructor; eassumption.
  - intros * Hl _ HΓ; rewrite !exp_msub_qn_id; split; econstructor; eassumption.
  - intros * Hl _ HΓ; rewrite !exp_msub_qn_id; econstructor; eassumption.
Qed.

(** ** 4. Embeddings *)

Record Emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (μ : msub) : Prop :=
  { em_wf : ⊢g Θ2 ⍮ Ξ2
  ; em_qn : forall n, ms_eq (ms_qn n μ) μ
  ; em_param : forall n U k T,
      List.nth_error Ξ1 n = Some U -> gu_params U ∋ #k : T ->
      exists n' U' k' T', $[n, k][μ]ᵐ = $[n', k'] /\ List.nth_error Ξ2 n' = Some U' /\
        gu_params U' ∋ #k' : T' /\ T[↑ₘ (S n)]ᵐ[sb_params n][μ]ᵐ = T'[↑ₘ (S n')]ᵐ[sb_params n']
  ; em_glob : forall r Δ b pv A B,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
      exists r', (a_glob r)[μ]ᵐ = a_glob r' /\ Θ2 ⍮ Ξ2 ∋ᵍ r' ⇒ Δ[μ]ᵐ ⍮ ge_def b pv A[μ]ᵐ B[μ]ᵐ }.

Lemma opt_msub_msub : forall (B : option exp) μ ν, B[μ]ᵐ[ν]ᵐ = B[ms_comp μ ν]ᵐ.
Proof. intros [X |] *; cbn; rewrite ?exp_msub_msub; reflexivity. Qed.

Lemma opt_msub_ext : forall (B : option exp) μ ν, ms_eq μ ν -> B[μ]ᵐ = B[ν]ᵐ.
Proof. intros [X |] * H; [ exact (f_equal Some (exp_msub_ext _ _ _ H)) | reflexivity ]. Qed.

Lemma opt_msub_id : forall (B : option exp), B[ms_id]ᵐ = B.
Proof. intros [X |]; cbn; rewrite ?exp_msub_id; reflexivity. Qed.

Lemma ms_comp_cong : forall ν ν' μ μ', ms_eq ν ν' -> ms_eq μ μ' -> ms_eq (ms_comp ν μ) (ms_comp ν' μ').
Proof.
  intros * [H1 H2] H; split; intros; cbn; rewrite ?H1, ?H2; apply exp_msub_ext; assumption.
Qed.

Lemma ctx_pi_msub_qn : forall μ Δ A, (forall n, ms_eq (ms_qn n μ) μ) ->
    (ctx_pi Δ A)[μ]ᵐ = ctx_pi Δ[μ]ᵐ A[μ]ᵐ.
Proof. intros * H; rewrite ctx_pi_msub, (exp_msub_ext _ _ _ (H _)); reflexivity. Qed.

Lemma ctx_fn_msub_qn : forall μ Δ A, (forall n, ms_eq (ms_qn n μ) μ) ->
    (ctx_fn Δ A)[μ]ᵐ = ctx_fn Δ[μ]ᵐ A[μ]ᵐ.
Proof. intros * H; rewrite ctx_fn_msub, (exp_msub_ext _ _ _ (H _)); reflexivity. Qed.

Lemma ms_qn_shift_all : forall n k, ms_eq (ms_qn n (↑ₘ k)) (↑ₘ k).
Proof. intros; apply ms_qn_shift. Qed.

(** An embedding is syntactically sound. *)
Lemma syn_msub_emb : forall Θ1 Ξ1 Θ2 Ξ2 μ,
    Emb Θ1 Ξ1 Θ2 Ξ2 μ -> syn_msub Θ1 Ξ1 Θ2 Ξ2 μ nil.
Proof.
  intros * [Hg Hq Hp Hl].
  assert (Hb : ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅) by (constructor; assumption).
  assert (Hqe : forall n (X : exp), X[ms_qn n μ]ᵐ = X[μ]ᵐ) by (intros; apply exp_msub_ext, Hq).
  constructor.
  - exact Hb.
  - intros * Hn Hk _ HΓ; rewrite !Hqe.
    destruct (Hp _ _ _ _ Hn Hk) as (n' & U' & k' & T' & Heq & Hn' & Hk' & HT).
    rewrite Heq, HT; split; econstructor; eassumption.
  - intros * Hl0 _ HΓ; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    rewrite Heq, ctx_pi_msub_qn by assumption; split; econstructor; eassumption.
  - intros * Hl0 _ HΓ; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    rewrite Heq, ctx_pi_msub_qn, ctx_fn_msub_qn by assumption; econstructor; eassumption.
Qed.

(** *** Embeddings compose; the basic ones *)

Lemma Emb_comp : forall Θ1 Ξ1 Θ Ξ Θ2 Ξ2 ν μ,
    Emb Θ1 Ξ1 Θ Ξ ν -> Emb Θ Ξ Θ2 Ξ2 μ -> Emb Θ1 Ξ1 Θ2 Ξ2 (ms_comp ν μ).
Proof.
  intros * [_ Hq1 Hp1 Hl1] [Hg Hq2 Hp2 Hl2]; constructor.
  - exact Hg.
  - intros n; eapply ms_eq_trans; [ apply ms_qn_comp | apply ms_comp_cong; auto ].
  - intros * Hn Hk.
    destruct (Hp1 _ _ _ _ Hn Hk) as (n1 & U1 & k1 & T1 & Heq1 & Hn1 & Hk1 & HT1).
    destruct (Hp2 _ _ _ _ Hn1 Hk1) as (n2 & U2 & k2 & T2 & Heq2 & Hn2 & Hk2 & HT2).
    exists n2, U2, k2, T2; rewrite <- !exp_msub_msub, Heq1, HT1; auto.
  - intros * Hl.
    destruct (Hl1 _ _ _ _ _ _ Hl) as (r1 & Heq1 & Hl').
    destruct (Hl2 _ _ _ _ _ _ Hl') as (r2 & Heq2 & Hl'').
    exists r2; rewrite <- exp_msub_msub, Heq1, <- ctx_msub_msub, <- exp_msub_msub, <- opt_msub_msub; auto.
Qed.

(** An embedding preceded by one that moves nothing. *)
Lemma Emb_pre : forall Θ1 Ξ1 Θ Ξ Θ2 Ξ2 μ,
    (forall r Δ b pv A B, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> Θ ⍮ Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B) ->
    (forall n U, List.nth_error Ξ1 n = Some U ->
       exists U', List.nth_error Ξ n = Some U' /\ gu_params U' = gu_params U) ->
    Emb Θ Ξ Θ2 Ξ2 μ -> Emb Θ1 Ξ1 Θ2 Ξ2 μ.
Proof.
  intros * Hr Hn [Hg Hq Hp Hl]; constructor; auto.
  intros * Hn1 Hk; destruct (Hn _ _ Hn1) as (U' & Hn' & HP).
  rewrite <- HP in Hk; eauto.
Qed.

Lemma Emb_id : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> Emb Θ Ξ Θ Ξ ms_id.
Proof.
  intros * Hg; constructor; auto.
  - intros; apply ms_qn_id.
  - intros * Hn Hk; exists n, U, k, T; rewrite !exp_msub_id; repeat split; assumption.
  - intros * Hl; exists r; rewrite ctx_msub_id, !exp_msub_id, opt_msub_id; split; [ reflexivity | assumption ].
Qed.

Lemma Emb_push : forall Θ U Ξ, ⊢g Θ ⍮ U :: Ξ -> Emb Θ Ξ Θ (U :: Ξ) (↑ₘ 1).
Proof.
  intros * Hg.
  assert (HΘ : units_scoped Θ) by (eapply wf_scoped; eassumption).
  constructor; auto.
  - intros; apply ms_qn_shift.
  - intros * Hn Hk; exists (S n), U0, k, T; rewrite exp_params_shift; auto.
  - intros * Hl; exists r[p_rel 1 nil]ᵖ; split; [ reflexivity |].
    apply gc_lookup_push; assumption.
Qed.

(** Popping: a global of a pushed stack not in the new frame is one of the
    smaller stack, pushed. *)
Lemma gc_lookup_pop : forall Θ U Ξ r Δ b pv A B,
    units_scoped Θ ->
    Θ ⍮ U :: Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
    p_qual r <> qu_rel 0 ->
    exists Δ0 A0 B0 r0, Θ ⍮ Ξ ∋ᵍ r0 ⇒ Δ0 ⍮ ge_def b pv A0 B0 /\
        Δ = Δ0[↑ₘ 1]ᵐ /\ A = A0[↑ₘ 1]ᵐ /\ B = B0[↑ₘ 1]ᵐ.
Proof.
  intros * HΘ Hl Hr.
  inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst.
  - destruct n as [| m]; [ contradiction |]; cbn in Hn.
    exists Δ0[↑ₘ m]ᵐ, A0[↑ₘ m]ᵐ, B0[↑ₘ m]ᵐ, (p_rel m ip).
    rewrite ctx_msub_shift_shift, exp_msub_shift_shift, opt_msub_shift_shift.
    repeat split; [ econstructor; eassumption ].
  - destruct (gc_lookup_abs_nil _ _ _ _ _ _ _ _ HΘ Hl ltac:(intros ? ?; discriminate)) as (HΔ & HA & HB).
    do 4 eexists; split; [ econstructor; eassumption |].
    rewrite (ctx_msub_shift_nil _ _ _ HΔ), (exp_msub_shift_nil _ _ _ HA), (opt_msub_shift_nil _ _ _ HB).
    repeat split.
Qed.

(** *** Truncating a frame's telescope

    [ms_off o] moves the parameters of the innermost frame [o] places out and
    leaves everything else alone: it embeds a frame whose parameters are a
    suffix [Pb] of [Pa ++ Pb], [o = length Pa]. *)

Definition ms_off (o : nat) : msub :=
  ms_mk (fun lp => match lp_mod lp with
                   | 0 => a_param (lp_mk 0 (lp_param lp + o))
                   | S _ => a_param lp
                   end) a_glob.

Lemma ms_qn_off : forall n o, ms_eq (ms_qn n (ms_off o)) (ms_off o).
Proof.
  induction n; intros; cbn [ms_qn]; [ split; reflexivity |].
  destruct (IHn o) as [H1 H2]; split; intros; cbn; rewrite ?H1, ?H2;
    [ destruct lp as [[| m] j] |]; reflexivity.
Qed.

Lemma off_shift : forall n o, ms_eq (ms_comp (↑ₘ (S n)) (ms_off o)) (↑ₘ (S n)).
Proof. intros; split; intros; reflexivity. Qed.

Lemma exp_off_shift : forall (X : exp) n o, X[↑ₘ (S n)]ᵐ[ms_off o]ᵐ = X[↑ₘ (S n)]ᵐ.
Proof. intros; rewrite exp_msub_msub; apply exp_msub_ext, off_shift. Qed.

Lemma ctx_off_shift : forall (Δ : ctx) n o, Δ[↑ₘ (S n)]ᵐ[ms_off o]ᵐ = Δ[↑ₘ (S n)]ᵐ.
Proof. intros; rewrite ctx_msub_msub; apply ctx_msub_ext, off_shift. Qed.

Lemma opt_off_shift : forall (B : option exp) n o, B[↑ₘ (S n)]ᵐ[ms_off o]ᵐ = B[↑ₘ (S n)]ᵐ.
Proof. intros; rewrite opt_msub_msub; apply opt_msub_ext, off_shift. Qed.

Lemma params_off_out : forall (X : exp) n o,
    X[↑ₘ (S (S n))]ᵐ[sb_params (S n)][ms_off o]ᵐ = X[↑ₘ (S (S n))]ᵐ[sb_params (S n)].
Proof.
  intros; rewrite (exp_msub_sub_gen _ (sb_params (S n)) (sb_params (S n)) (ms_off o) (ms_off o)),
    exp_off_shift; [ reflexivity |].
  repeat split; intros; try destruct lp as [[| m] j]; reflexivity.
Qed.

Lemma params_off_here : forall (X : exp) o,
    X[↑ₘ 1]ᵐ[sb_params 0][ms_off o]ᵐ = X[wk_shiftn o]ʷ[↑ₘ 1]ᵐ[sb_params 0].
Proof.
  intros.
  rewrite (exp_msub_sub_gen _ (sb_params 0) (fun x => $[0, x + o]) (ms_off o) (ms_off o)),
    (exp_off_shift _ 0).
  - assert (Hw : ms_eq (ms_wk (↑ₘ 1) (wk_shiftn o)) (↑ₘ 1)) by (split; intros; reflexivity).
    rewrite <- (exp_msub_ext (X[wk_shiftn o]ʷ) _ _ Hw), <- exp_msub_wk, exp_sub_wk.
    apply exp_sub_sb_eq; intros x; reflexivity.
  - repeat split; intros; try destruct lp as [[| m] j]; reflexivity.
Qed.

Lemma Emb_trunc : forall Θ Ξ Pa Pb Φ,
    ⊢g Θ ⍮ gu_mk (Pa ++ Pb) Φ :: Ξ ->
    Emb Θ (gu_mk Pb ⋄ :: Ξ) Θ (gu_mk (Pa ++ Pb) Φ :: Ξ) (ms_off (length Pa)).
Proof.
  intros * Hg.
  assert (HΘ : units_scoped Θ) by (eapply wf_scoped; eassumption).
  constructor; auto.
  - intros; apply ms_qn_off.
  - intros [| n] U k T Hn Hk; cbn in Hn.
    + injection Hn as <-; cbn in Hk.
      exists 0, (gu_mk (Pa ++ Pb) Φ), (k + length Pa), T[wk_shiftn (length Pa)]ʷ.
      rewrite params_off_here; repeat split; [ apply ctx_lookup_app_r; exact Hk ].
    + exists (S n), U, k, T; rewrite params_off_out; repeat split; assumption.
  - intros * Hl; exists r; split; [ reflexivity |].
    inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst.
    + destruct n as [| m]; cbn in Hn; [ injection Hn as <-; inversion Hm |].
      rewrite ctx_off_shift, exp_off_shift, opt_off_shift.
      eapply (gcl_rel _ _ (S m)); cbn; eassumption.
    + destruct (gc_lookup_abs_nil _ _ _ _ _ _ _ _ HΘ Hl ltac:(intros ? ?; discriminate)) as (HΔ & HA & HB).
      assert (Hfix : ms_abs_fix (ms_off (length Pa))) by (intros ? ?; reflexivity).
      rewrite (ctx_msub_nil _ _ _ HΔ Hfix), (exp_msub_nil _ _ _ HA Hfix), (opt_msub_nil _ _ _ HB Hfix).
      econstructor; eassumption.
Qed.

(** *** Frames, prefixes and levels *)

Lemma wf_frame_typ : forall Θ U Ξ A i,
    ⊢g Θ ⍮ U :: Ξ ->
    Θ ⍮ Ξ ⍮ gu_params U ⊢ A : Type@i ->
    Θ ⍮ U :: Ξ ⍮ ⋅ ⊢ A[↑ₘ 1]ᵐ[sb_params 0] : Type@i.
Proof.
  intros * Hg HA.
  destruct (push_preserves_wf _ _ _ Hg) as (_ & Hp & _).
  pose proof (Hp _ _ _ HA) as HA'.
  change ((Type@i)[↑ₘ 1]ᵐ) with (Type@i) in HA'.
  change (Type@i) with (Type@i[sb_params 0]).
  eapply sub_preserves_exp; [ exact HA' |].
  econstructor; [ constructor; assumption | eapply presup_exp_ctx; exact HA' |].
  intros x B Hl; destruct (ctx_lookup_msub_inv _ _ _ _ Hl) as (B0 & Hl0 & ->).
  rewrite (exp_msub_ext _ _ _ (ms_qn_shift _ _)).
  econstructor; [ constructor; assumption | reflexivity | eassumption ].
Qed.

(** A frame grown along a prefix resolves what it did. *)
Lemma grow_lookup : forall Θ Ξ P Φq Φ, gm_prefix Φq Φ ->
    forall r Δ b pv A B,
      Θ ⍮ gu_mk P Φq :: Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> Θ ⍮ gu_mk P Φ :: Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B.
Proof.
  intros * Hp * Hl; inversion Hl as [? ? ? ? ? ? ? ? Hn Hm |]; subst; [| econstructor; eassumption ].
  destruct n as [| n]; cbn in Hn; [ injection Hn as <- |];
    (eapply gcl_rel; [ cbn; first [ reflexivity | eassumption ] | cbn in *; eauto using gm_prefix_lookup ]).
Qed.

Lemma wk_shiftn_len : forall (A : exp) (Pa : ctx) (B : exp),
    A[↑]ʷ[wk_shiftn (length Pa)]ʷ = A[wk_shiftn (length (Pa ++ B :: nil))]ʷ.
Proof.
  intros; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app; cbn; lia.
Qed.

(** [closable_file], with a target that files only a prefix [Φt] of the unit:
    a member inserted before [Φt] ends mentions only members of [Φt]. *)
Section FilePrefix.
  Variables (Θ' Θ2 : gdeps) (fp : list String.string) (PU : ctx) (ΦU Φt : gmod).

  #[local] Notation mf := (p_abs fp nil).

  Hypothesis HU : Θ' ⍮ nil ⍮ PU ⊢m ΦU.
  Hypothesis Hins : ins_typed Θ' nil PU ΦU.
  Hypothesis Hfp : gds_lookup Θ2 fp = Some (gu_mk PU Φt).
  Hypothesis Hgrow : forall fq V, gds_lookup Θ' fq = Some V -> gds_lookup Θ2 fq = Some V.
  Hypothesis Htgt : ⊢ Θ2 ⍮ nil ⍮ ⋅.

  Lemma closable_file_prefix : forall n Φq ip Δ b pv A B,
      gm_count Φq < n ->
      gm_ins ΦU Φq ip Δ (ge_def b pv A B) ->
      gm_prefix Φq Φt ->
      (exists i, Θ2 ⍮ nil ⍮ PU ⊢ (ctx_pi Δ A)[close mf (length PU)]ᵐ : Type@i) /\
      (forall M, B = Some M ->
         Θ2 ⍮ nil ⍮ PU ⊢ (ctx_fn Δ M)[close mf (length PU)]ᵐ : (ctx_pi Δ A)[close mf (length PU)]ᵐ).
  Proof.
    induction n as [| n IH]; intros * Hlt Hi Hpt; [ lia |].
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
    - intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst.
      + destruct n0 as [| m]; [ contradiction | destruct m; discriminate ].
      + destruct (gc_lookup_abs_nil _ _ _ _ _ _ _ _ HΘ Hl ltac:(intros ? ?; discriminate)) as (HΔ & HA & HB).
        rewrite (ctx_msub_nil _ _ _ HΔ (ms_close_abs_fix _ _ _)),
          (exp_msub_nil _ _ _ HA (ms_close_abs_fix _ _ _)), (opt_msub_nil _ _ _ HB (ms_close_abs_fix _ _ _)).
        cbn; econstructor; eauto.
    - intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero.
      cbn; eapply (gcl_abs _ _ _ (gu_mk PU Φt)); [ exact Hfp | cbn; eauto using gm_prefix_lookup ].
    - intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero.
      destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ _ Hpq Hir)
                  (gm_prefix_trans _ _ _ (gm_ins_prefix _ _ _ _ _ Hir) Hpt)) as [HT' _]; exact HT'.
    - intros * Hl Hr.
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf' Hm]; subst; cbn in Hr; [| discriminate ].
      injection Hr as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, !exp_msub_shift_zero.
      match goal with H : _[↑ₘ 0]ᵐ = Some _ |- _ => rewrite opt_msub_shift_zero in H; subst end.
      destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ _ Hpq Hir)
                  (gm_prefix_trans _ _ _ (gm_ins_prefix _ _ _ _ _ Hir) Hpt)) as [_ HM'];
        exact (HM' _ eq_refl).
    - split.
      + exists i; exact (He _ _ _ HT).
      + intros M ->; exact (He _ _ _ (Hb _ eq_refl)).
  Qed.
End FilePrefix.

Lemma gds_lookup_single : forall fp V Θ fq W,
    gds_lookup (((fp, V) :: nil) :: Θ) fq = Some W ->
    (fq = fp /\ W = V) \/ gds_lookup Θ fq = Some W.
Proof.
  intros * H; unfold gds_lookup, gd_lookup, path_beq in *; cbn in H.
  destruct (path_eq_dec fq fp) as [-> |]; [ left; injection H as <-; auto | right; exact H ].
Qed.

Lemma gds_lookup_single_here : forall fp V Θ, gds_lookup (((fp, V) :: nil) :: Θ) fp = Some V.
Proof.
  intros; unfold gds_lookup, gd_lookup, path_beq; cbn.
  destruct (path_eq_dec fp fp); [ reflexivity | contradiction ].
Qed.

(** ** 5. The induction, over an abstract model *)

Section Induction.
  (** [V Θ Ξ A M]: [M] is a valid term of type [A] at [⋅] in [Θ ⍮ Ξ]. *)
  Variable V : gdeps -> gstack -> exp -> exp -> Prop.
  (** [Snd Θ1 Ξ1 Θ2 Ξ2 μ]: [μ] is a sound substitution (with no context
      extension). *)
  Variable Snd : gdeps -> gstack -> gdeps -> gstack -> msub -> Prop.

  Definition vtyp (Θ : gdeps) (Ξ : gstack) (X : exp) : Prop := exists i, V Θ Ξ (Type@i) X.

  Definition gent (Θ : gdeps) (Ξ : gstack) (μ : msub) (Δ : ctx) (A : exp) (B : option exp) : Prop :=
    vtyp Θ Ξ ((ctx_pi Δ A)[μ]ᵐ) /\
    (forall M, B = Some M -> V Θ Ξ ((ctx_pi Δ A)[μ]ᵐ) ((ctx_fn Δ M)[μ]ᵐ)).

  (** The images of the globals, and of the parameters' types, are valid. *)
  Definition SG Θ1 Ξ1 Θ2 Ξ2 μ : Prop :=
    forall r Δ b pv A B, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> gent Θ2 Ξ2 μ Δ A B.

  Definition SP (Θ1 : gdeps) (Ξ1 : gstack) Θ2 Ξ2 μ : Prop :=
    forall n U k T, List.nth_error Ξ1 n = Some U -> gu_params U ∋ #k : T ->
      vtyp Θ2 Ξ2 (T[↑ₘ (S n)]ᵐ[sb_params n][μ]ᵐ).

  Hypothesis snd_emb : forall Θ1 Ξ1 Θ2 Ξ2 μ,
      Emb Θ1 Ξ1 Θ2 Ξ2 μ -> SG Θ1 Ξ1 Θ2 Ξ2 μ -> SP Θ1 Ξ1 Θ2 Ξ2 μ -> Snd Θ1 Ξ1 Θ2 Ξ2 μ.
  Hypothesis vread : forall Θ1 Ξ1 Θ2 Ξ2 μ A M,
      Snd Θ1 Ξ1 Θ2 Ξ2 μ -> Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A -> V Θ2 Ξ2 A[μ]ᵐ M[μ]ᵐ.

  Definition Good Θ Ξ : Prop :=
    forall Θ2 Ξ2 μ, Emb Θ Ξ Θ2 Ξ2 μ -> SG Θ Ξ Θ2 Ξ2 μ /\ SP Θ Ξ Θ2 Ξ2 μ.

  Lemma vread_entry : forall Θ1 Ξ1 Θ2 Ξ2 μ Δ A B,
      Snd Θ1 Ξ1 Θ2 Ξ2 μ ->
      (exists i, Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ ctx_pi Δ A : Type@i) ->
      (forall M, B = Some M -> Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A) ->
      gent Θ2 Ξ2 μ Δ A B.
  Proof.
    intros * Hμ [i HT] HM; split.
    - exists i; exact (vread _ _ _ _ _ _ _ Hμ HT).
    - intros M HB; exact (vread _ _ _ _ _ _ _ Hμ (HM _ HB)).
  Qed.

  Lemma frame_outer : forall Θ U Ξ Θ2 Ξ2 μ,
      Good Θ Ξ -> ⊢g Θ ⍮ U :: Ξ -> Emb Θ (U :: Ξ) Θ2 Ξ2 μ ->
      (forall r Δ b pv A B, Θ ⍮ U :: Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> p_qual r <> qu_rel 0 ->
         gent Θ2 Ξ2 μ Δ A B) /\
      (forall n U' k T, List.nth_error Ξ n = Some U' -> gu_params U' ∋ #k : T ->
         vtyp Θ2 Ξ2 T[↑ₘ (S (S n))]ᵐ[sb_params (S n)][μ]ᵐ).
  Proof.
    intros * HG Hg He.
    assert (HΘ : units_scoped Θ) by (eapply wf_scoped; eassumption).
    destruct (HG _ _ _ (Emb_comp _ _ _ _ _ _ _ _ (Emb_push _ _ _ Hg) He)) as [HS HP].
    assert (Hq : forall n, ms_eq (ms_qn n (↑ₘ 1)) (↑ₘ 1)) by (intros; apply ms_qn_shift).
    split.
    - intros * Hl Hr.
      destruct (gc_lookup_pop _ _ _ _ _ _ _ _ _ HΘ Hl Hr) as (Δ0 & A0 & B0 & r0 & Hl0 & -> & -> & ->).
      destruct (HS _ _ _ _ _ _ Hl0) as [HT HM].
      rewrite <- exp_msub_msub, (ctx_pi_msub_qn (↑ₘ 1)) in HT by exact Hq.
      split; [ exact HT |].
      intros M HB; destruct B0 as [M0 |]; cbn in HB; inversion HB; subst.
      specialize (HM _ eq_refl).
      rewrite <- !exp_msub_msub, (ctx_pi_msub_qn (↑ₘ 1)), (ctx_fn_msub_qn (↑ₘ 1)) in HM by exact Hq.
      exact HM.
    - intros * Hn Hk; rewrite <- exp_params_shift, exp_msub_msub; eapply HP; eassumption.
  Qed.

  Lemma good_cons : forall Θ Ξ P Φ,
      wf_gstack Θ Ξ -> Θ ⍮ Ξ ⍮ P ⊢m Φ -> Good Θ Ξ -> Good Θ (gu_mk P Φ :: Ξ).
  Proof.
    intros * HΞ HΦ HG Θ2 Ξ2 μ He.
    assert (Hg : ⊢g Θ ⍮ gu_mk P Φ :: Ξ) by (eapply ctx_wf_gctx, wf_frame_ctx; eassumption).
    assert (HP0 : ⊢ Θ ⍮ Ξ ⍮ P) by (eapply wf_gmod_ctx; eassumption).
    (* the parameters, outermost first *)
    assert (Hpar : forall Pb Pa, P = Pa ++ Pb -> forall k T, Pb ∋ #k : T ->
              vtyp Θ2 Ξ2 T[wk_shiftn (length Pa)]ʷ[↑ₘ 1]ᵐ[sb_params 0][μ]ᵐ).
    { induction Pb as [| A Pb IH]; intros Pa HPe k T Hk; [ inversion Hk |].
      assert (HPe' : P = (Pa ++ A :: nil) ++ Pb) by (rewrite <- List.app_assoc; exact HPe).
      inversion Hk as [| ? ? ? ? Hk0]; subst.
      - assert (HAb : ⊢ Θ ⍮ Ξ ⍮ Pb ▹ A) by (eapply ctx_app_wf_right; exact HP0).
        inversion HAb as [| ? ? ? ? ? HA]; subst.
        assert (HgB : ⊢g Θ ⍮ gu_mk Pb ⋄ :: Ξ)
          by (apply wf_gctx_intro, wf_gstack_cons;
              [ assumption | constructor; constructor; eapply presup_exp_ctx; eassumption ]).
        pose proof (Emb_trunc Θ Ξ (Pa ++ A :: nil) Pb Φ ltac:(rewrite <- HPe'; exact Hg)) as Het.
        rewrite <- HPe' in Het.
        pose proof (Emb_comp _ _ _ _ _ _ _ _ Het He) as He'.
        destruct (frame_outer _ _ _ _ _ _ HG HgB He') as [Ho1 Ho2].
        assert (Hμ : Snd Θ (gu_mk Pb ⋄ :: Ξ) Θ2 Ξ2 (ms_comp (ms_off (length (Pa ++ A :: nil))) μ)).
        { apply snd_emb; [ exact He' | |].
          - intros r * Hl.
            destruct (p_qual r) as [fp | [| m]] eqn:Hq;
              try solve [ eapply Ho1; [ eassumption | rewrite Hq; discriminate ] ].
            inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; cbn in Hq; [| discriminate ].
            injection Hq as ->; cbn in Hn; injection Hn as <-; cbn in Hm; inversion Hm.
          - intros [| m] U k' T' Hn Hk'; cbn in Hn.
            + injection Hn as <-; cbn in Hk'.
              rewrite <- exp_msub_msub, params_off_here.
              exact (IH (Pa ++ A :: nil) HPe' _ _ Hk').
            + exact (Ho2 _ _ _ _ Hn Hk'). }
        pose proof (vread _ _ _ _ _ _ _ Hμ (wf_frame_typ _ (gu_mk Pb ⋄) _ _ _ HgB HA)) as H.
        rewrite <- (exp_msub_msub (A[↑ₘ 1]ᵐ[sb_params 0])), params_off_here in H.
        rewrite (wk_shiftn_len _ _ A); exists i; exact H.
      - rewrite (wk_shiftn_len _ _ A); exact (IH (Pa ++ A :: nil) HPe' _ _ Hk0). }
    assert (HparF : forall k T, P ∋ #k : T -> vtyp Θ2 Ξ2 T[↑ₘ 1]ᵐ[sb_params 0][μ]ᵐ).
    { intros * Hk; pose proof (Hpar P nil eq_refl k T Hk) as H; cbn [length] in H.
      rewrite (exp_wk_wk_eq _ _ _ wk_shiftn_zero), exp_wk_id in H; exact H. }
    destruct (frame_outer _ _ _ _ _ _ HG Hg He) as [Ho1 Ho2].
    (* the members, in insertion order *)
    assert (Hins : ins_typed Θ Ξ P Φ)
      by (destruct presup_global as (_ & _ & _ & _ & _ & Hm & _); exact (Hm _ _ _ _ HΦ)).
    assert (Hmem : forall n Φq ip Δ b pv A B, gm_count Φq < n ->
               gm_ins Φ Φq ip Δ (ge_def b pv A B) -> gent Θ2 Ξ2 μ Δ A B).
    { induction n as [| n IH]; intros * Hlt Hi; [ lia |].
      pose proof (gm_ins_prefix _ _ _ _ _ Hi) as Hpq.
      assert (Hgq : ⊢g Θ ⍮ gu_mk P Φq :: Ξ)
        by (eapply ctx_wf_gctx, wf_frame_ctx, wf_gmod_prefix; eassumption).
      assert (Heq : Emb Θ (gu_mk P Φq :: Ξ) Θ2 Ξ2 μ).
      { eapply Emb_pre; [ apply grow_lookup; exact Hpq | | exact He ].
        intros [| m] U Hn; cbn in *; [ injection Hn as <- |]; eexists; split; eauto. }
      destruct (frame_outer _ _ _ _ _ _ HG Hgq Heq) as [Hq1 Hq2].
      destruct (Hins _ _ _ _ _ _ _ Hi) as [HT HM].
      assert (Hμ : Snd Θ (gu_mk P Φq :: Ξ) Θ2 Ξ2 μ).
      { apply snd_emb; [ exact Heq | |].
        - intros r * Hl.
          destruct (p_qual r) as [fp | [| m]] eqn:Hq;
            try solve [ eapply Hq1; [ eassumption | rewrite Hq; discriminate ] ].
          inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; cbn in Hq; [| discriminate ].
          injection Hq as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
          rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero.
          destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
          pose proof (gm_ins_count _ _ _ _ _ Hir).
          eapply IH; [| exact (gm_prefix_ins _ _ _ _ _ _ Hpq Hir) ]; lia.
        - intros [| m] U k T Hn Hk; cbn in Hn;
            [ injection Hn as <-; cbn in Hk; exact (HparF _ _ Hk) | exact (Hq2 _ _ _ _ Hn Hk) ]. }
      exact (vread_entry _ _ _ _ _ _ _ _ Hμ HT HM). }
    split.
    - intros r * Hl.
      destruct (p_qual r) as [fp | [| m]] eqn:Hq;
        try solve [ eapply Ho1; [ eassumption | rewrite Hq; discriminate ] ].
      inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; cbn in Hq; [| discriminate ].
      injection Hq as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero.
      destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
      eapply (Hmem (S (gm_count Φr)) Φr); [ lia | exact Hir ].
    - intros [| m] U k T Hn Hk; cbn in Hn;
        [ injection Hn as <-; cbn in Hk; exact (HparF _ _ Hk) | exact (Ho2 _ _ _ _ Hn Hk) ].
  Qed.

  Lemma good_level : forall Θ0 d,
      wf_gdeps Θ0 -> wf_gdep Θ0 d -> Good Θ0 nil -> Good (d :: Θ0) nil.
  Proof.
    intros * HΘ Hd HG Θ2 Ξ2 μ He.
    pose proof (wf_gdep_fresh _ _ Hd) as Hfr.
    assert (Hgrow : forall fq V, gds_lookup Θ0 fq = Some V -> gds_lookup (d :: Θ0) fq = Some V)
      by (intros; apply gds_lookup_level; assumption).
    assert (Hlow : forall r Δ b pv A B, Θ0 ⍮ nil ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
                     d :: Θ0 ⍮ nil ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B).
    { intros * Hl; inversion Hl; subst; [ destruct n; discriminate | econstructor; eauto ]. }
    assert (He0 : Emb Θ0 nil Θ2 Ξ2 μ)
      by (eapply Emb_pre; [ exact Hlow | intros [| n] U Hn; discriminate | exact He ]).
    destruct (HG _ _ _ He0) as [HS0 _].
    split; [| intros n U k T Hn; destruct n; discriminate ].
    intros r * Hl.
    inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; [ destruct n; discriminate |].
    pose proof Hf as Hl'; unfold gds_lookup in Hl'; cbn [List.concat] in Hl'.
    apply gd_lookup_app_inv in Hl' as [Hl' | Hl'].
    2: { eapply HS0; econstructor; [ exact Hl' | eassumption ]. }
    apply gd_lookup_in in Hl' as Hin.
    pose proof (wf_gdep_unit _ _ Hd _ _ Hin) as HUw.
    pose proof (Hfr _ _ Hin) as Hfp.
    assert (HinsU : ins_typed Θ0 nil (gu_params U) (gu_mod U))
      by (destruct presup_global as (_ & _ & _ & _ & _ & _ & Hu & _); exact (Hu _ _ _ HUw)).
    inversion HUw as [? ? ? HU]; subst.
    destruct U as [PU ΦU]; cbn [gu_params gu_mod] in *.
    assert (Hmem : forall n Φq ip Δ b pv A B, gm_count Φq < n -> gm_ins ΦU Φq ip Δ (ge_def b pv A B) ->
               gent Θ2 Ξ2 μ (Δ[close (p_abs fp nil) (length PU)]ᵐ ++ PU)
                 A[ms_close (p_abs fp nil) (length PU) (length Δ)]ᵐ
                 B[ms_close (p_abs fp nil) (length PU) (length Δ)]ᵐ).
    { induction n as [| n IH]; intros * Hlt Hi; [ lia |].
      pose proof (gm_ins_prefix _ _ _ _ _ Hi) as Hpq.
      set (Θq := ((fp, gu_mk PU Φq) :: nil) :: Θ0).
      assert (HwUq : Θ0 ⍮ nil ⍮ PU ⊢m Φq) by (eapply wf_gmod_prefix; eassumption).
      assert (Hgq : ⊢g Θq ⍮ nil).
      { apply wf_gctx_intro, wf_gstack_nil, wf_gdeps_cons; [ assumption |].
        apply wf_gdep_cons; [ apply wf_gdep_nil; assumption | constructor; exact HwUq | exact Hfp | unfold gd_fresh; cbn; tauto ]. }
      assert (Hgq' : forall fq V, gds_lookup Θ0 fq = Some V -> gds_lookup Θq fq = Some V).
      { intros; apply gds_lookup_level; [| assumption ].
        intros fq' V' [[= <- <-] | []]; exact Hfp. }
      assert (Hlq : forall r Δ' b' pv' A' B', Θq ⍮ nil ∋ᵍ r ⇒ Δ' ⍮ ge_def b' pv' A' B' ->
                      d :: Θ0 ⍮ nil ∋ᵍ r ⇒ Δ' ⍮ ge_def b' pv' A' B').
      { intros * H; inversion H as [? ? ? ? ? ? ? ? Hn' Hm' | ? ? ? ? ? ? ? ? Hf' Hm']; subst;
          [ destruct n0; discriminate |].
        destruct (gds_lookup_single _ _ _ _ _ Hf') as [[-> ->] | Hb].
        - eapply (gcl_abs _ _ _ (gu_mk PU ΦU)); [ exact Hf | cbn in *; eauto using gm_prefix_lookup ].
        - econstructor; [ apply Hgrow; exact Hb | eassumption ]. }
      assert (Heq : Emb Θq nil Θ2 Ξ2 μ)
        by (eapply Emb_pre; [ exact Hlq | intros [| ?] ? ?; discriminate | exact He ]).
      assert (Hμ : Snd Θq nil Θ2 Ξ2 μ).
      { apply snd_emb; [ exact Heq | | intros [| ?] ? ? ? ?; discriminate ].
        intros r * H; inversion H as [? ? ? ? ? ? ? ? Hn' Hm' | ? ? ? ? ? ? ? ? Hf' Hm']; subst;
          [ destruct n0; discriminate |].
        destruct (gds_lookup_single _ _ _ _ _ Hf') as [[-> ->] | Hb].
        - cbn [gu_params gu_mod] in *.
          destruct (gm_lookup_ins _ _ _ _ Hm') as [Φr Hir].
          pose proof (gm_ins_count _ _ _ _ _ Hir).
          eapply (IH Φr); [ lia | exact (gm_prefix_ins _ _ _ _ _ _ Hpq Hir) ].
        - eapply HS0; econstructor; eassumption. }
      destruct (closable_file_prefix Θ0 Θq fp PU ΦU Φq HU HinsU (gds_lookup_single_here _ _ _) Hgq'
                  ltac:(constructor; exact Hgq) (S (gm_count Φq)) Φq _ _ _ _ _ _ ltac:(lia) Hi
                  (gmp_refl _)) as [[i HT] HM].
      apply (vread_entry _ _ _ _ _ _ _ _ Hμ).
      - rewrite ctx_pi_app, <- ctx_pi_close; eapply ctx_pi_wf0; eassumption.
      - intros M' HB; destruct B as [M0 |]; cbn in HB; inversion HB; subst.
        rewrite ctx_fn_app, <- ctx_fn_close, ctx_pi_app, <- ctx_pi_close.
        eapply ctx_fn_wf0; [ eassumption | apply HM; reflexivity ]. }
    destruct (gm_lookup_ins _ _ _ _ Hm) as [Φq Hi].
    exact (Hmem (S (gm_count Φq)) Φq _ _ _ _ _ _ ltac:(lia) Hi).
  Qed.

  Lemma good_deps : forall Θ, wf_gdeps Θ -> Good Θ nil.
  Proof.
    induction 1 as [| Θ d HΘ IH Hd].
    - intros Θ2 Ξ2 μ He; split.
      + intros r * Hl; inversion Hl; subst; [ destruct n; discriminate | discriminate ].
      + intros [| n] U k T Hn; discriminate.
    - apply good_level; assumption.
  Qed.

  Lemma good_stack : forall Ξ Θ, wf_gstack Θ Ξ -> Good Θ Ξ.
  Proof.
    induction Ξ as [| U Ξ IH]; intros * H; inversion H; subst.
    - apply good_deps; assumption.
    - destruct U as [P Φ]; match goal with Hu : _ ⍮ _ ⊢u _ |- _ => inversion Hu; subst end.
      apply good_cons; auto.
  Qed.

  (** Every resolved global's type and body, and every parameter's type, is
      valid at [⋅] in the context itself. *)
  Theorem global_induction : forall Θ Ξ, ⊢g Θ ⍮ Ξ ->
      (forall p Δ b pv A B, Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
         (exists i, V Θ Ξ (Type@i) (ctx_pi Δ A)) /\
         (forall M, B = Some M -> V Θ Ξ (ctx_pi Δ A) (ctx_fn Δ M))) /\
      (forall n U k T, List.nth_error Ξ n = Some U -> gu_params U ∋ #k : T ->
         exists i, V Θ Ξ (Type@i) (T[↑ₘ (S n)]ᵐ[sb_params n])).
  Proof.
    intros * Hg.
    destruct (good_stack _ _ (wf_gctx_stack _ _ Hg) _ _ _ (Emb_id _ _ Hg)) as [HS HP].
    split.
    - intros p * Hl; destruct (HS _ _ _ _ _ _ Hl) as [HT HM].
      unfold vtyp in HT; rewrite exp_msub_id in HT; split; [ exact HT |].
      intros M HB; specialize (HM _ HB); rewrite !exp_msub_id in HM; exact HM.
    - intros n U k T Hn Hk; pose proof (HP _ _ _ _ Hn Hk) as H; unfold vtyp in H.
      rewrite exp_msub_id in H; exact H.
  Qed.
End Induction.
