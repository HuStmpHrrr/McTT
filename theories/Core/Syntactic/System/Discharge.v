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
Lemma exp_msub_close_wk : forall (X : exp) k cs L mp c d,
    exp_scoped k cs X ->
    X[ms_close L mp c k]ᵐ[wk_qn k (wk_shiftn d)]ʷ = X[ms_close L mp c (k + d)]ᵐ.
Proof.
  induction X; intros * HX; cbn in *; destruct_all; f_equal.
  all: try rewrite !(exp_msub_ext _ _ _ (ms_q_close _ _ _ _)).
  all: try rewrite !(exp_msub_ext _ (ms_q (ms_q (ms_close _ _ _ _))) _ (ms_qn_close 2 _ _ _ _)).
  all: try solve [ eauto ].
  all: try solve [ exact (IHX1 (S k) _ _ _ _ _ ltac:(eassumption))
                 | exact (IHX2 (S k) _ _ _ _ _ ltac:(eassumption))
                 | exact (IHX3 (S (S k)) _ _ _ _ _ ltac:(eassumption)) ].
  - apply wk_qn_lt; assumption.
  - destruct l as [m j]; cbn; destruct (Nat.eqb m L); cbn; [| reflexivity ].
    rewrite wk_qn_ge by lia; unfold wk_shiftn; f_equal; lia.
  - destruct p as [[fp | m] ip]; cbn; try reflexivity.
    destruct (Nat.eqb m L); [| reflexivity ].
    apply app_vars_wk; intros i Hi; rewrite wk_qn_ge by lia; unfold wk_shiftn; lia.
Qed.

Corollary exp_msub_close_shiftn : forall (X : exp) cs L mp c d,
    exp_scoped 0 cs X ->
    X[close L mp c]ᵐ[wk_shiftn d]ʷ = X[ms_close L mp c d]ᵐ.
Proof.
  intros * H; exact (exp_msub_close_wk X 0 cs L mp c d H).
Qed.

(** ** The Closed Frame's Parameters *)

Lemma sb_qn_lt : forall k σ x, x < k -> sb_qn k σ x = #x.
Proof.
  induction k; intros * Hx; [ lia |]; destruct x as [| x]; cbn [sb_qn];
    rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  rewrite IHk by lia; reflexivity.
Qed.

Lemma sb_qn_params_ge : forall k L j x, k <= x -> sb_qn k (sb_params L j) x = $[L, j - S (x - k)].
Proof.
  induction k; intros * Hx; cbn [sb_qn]; [ rewrite Nat.sub_0_r; reflexivity |].
  destruct x as [| x]; [ lia |]; rewrite sb_q_succ, IHk by lia; reflexivity.
Qed.

(** A binding of the closed frame's telescope, read as parameters and closed,
    is the binding weakened past what came to sit above it. *)
Lemma exp_params_close_gen : forall (A : exp) m cs j mp c d,
    exp_scoped (m + j) cs A -> j <= c ->
    A[sb_qn m (sb_params (length cs) j)][ms_close (length cs) mp c (m + d)]ᵐ
    = A[wk_qn m (wk_shiftn (d + (c - j)))]ʷ.
Proof.
  induction A; intros * HA Hj; cbn in *; destruct_all; f_equal.
  all: try rewrite !(exp_msub_ext _ _ _ (ms_q_close _ _ _ _)).
  all: try rewrite !(exp_msub_ext _ (ms_q (ms_q (ms_close _ _ _ _))) _ (ms_qn_close 2 _ _ _ _)).
  all: try solve [ eauto ].
  all: try solve [ apply (IHA1 (S m)); assumption | apply (IHA2 (S m)); assumption
                 | apply (IHA3 (S m)); assumption | apply (IHA3 (S (S m))); assumption ].
  - match goal with |- (sb_qn _ _ ?x)[_]ᵐ = _ => destruct (Nat.lt_ge_cases x m) end.
    + rewrite sb_qn_lt, wk_qn_lt by assumption; reflexivity.
    + rewrite sb_qn_params_ge, wk_qn_ge by assumption; cbn.
      rewrite Nat.eqb_refl; unfold wk_shiftn; f_equal; lia.
  - destruct l as [m' k]; destruct HA as [c' [Hc _]]; cbn in *.
    destruct (Nat.eqb_spec m' (length cs)) as [-> |]; [| reflexivity ].
    exfalso; assert (Hlt : length cs < length cs) by (apply List.nth_error_Some; congruence); lia.
  - destruct p as [[fp | m'] ip]; unfold path_ok in *; cbn in *; [ reflexivity |].
    destruct (Nat.eqb_spec m' (length cs)); [ lia | reflexivity ].
Qed.

Corollary exp_params_close_here : forall (A : exp) cs j mp c d,
    exp_scoped j cs A -> j <= c ->
    A[sb_params (length cs) j][ms_close (length cs) mp c d]ᵐ = A[wk_shiftn (d + (c - j))]ʷ.
Proof. intros; exact (exp_params_close_gen A 0 cs j mp c d ltac:(assumption) ltac:(assumption)). Qed.

(** The [j]-th parameter, as a λ-variable past the context above it. *)
Lemma ctx_lookup_param_var : forall Γ Pa A Pb,
    Γ ++ Pa ++ A :: Pb ∋ #(length Γ + (length (Pa ++ A :: Pb) - S (length Pb)))
      : A[wk_shiftn (length Γ + (length (Pa ++ A :: Pb) - length Pb))]ʷ.
Proof.
  intros.
  pose proof (ctx_lookup_app_mid (Γ ++ Pa) Pb A) as H.
  rewrite <- List.app_assoc in H; cbn in H.
  rewrite List.length_app in *; cbn.
  replace (length Γ + (length Pa + S (length Pb) - S (length Pb))) with (length Γ + length Pa) by lia.
  replace (length Γ + (length Pa + S (length Pb) - length Pb)) with (S (length Γ + length Pa)) by lia.
  exact H.
Qed.

(** ** Resolution in a Frame and below It *)

Lemma gc_lookup_pop : forall Θ U Ξ r E,
    Θ ⍮ U :: Ξ ∋ᵍ r ⇒ E ->
    p_qual r <> qu_rel (length Ξ) ->
    Θ ⍮ Ξ ∋ᵍ r ⇒ E.
Proof.
  intros * Hl Hr; inversion Hl; subst; [| econstructor; eassumption ].
  match goal with H : gs_frame _ _ = Some _ |- _ =>
    destruct (gs_frame_cons_inv _ _ _ _ H) as [[-> ->] | [_ Hn]] end;
    [ contradiction | econstructor; eassumption ].
Qed.

Lemma gc_lookup_top : forall Θ U Ξ ip E,
    Θ ⍮ U :: Ξ ∋ᵍ p_rel (length Ξ) ip ⇒ E -> gu_mod U ∋ ip ⇒ E.
Proof.
  intros * Hl; inversion Hl; subst.
  match goal with H : gs_frame _ _ = Some _ |- _ => rewrite gs_frame_top in H; injection H as <- end.
  assumption.
Qed.

Lemma gs_param_pop : forall U Ξ lp T,
    gs_param (U :: Ξ) lp = Some T -> lp_mod lp <> length Ξ -> gs_param Ξ lp = Some T.
Proof.
  unfold gs_param; intros * Hp Hm.
  destruct (gs_frame (U :: Ξ) (lp_mod lp)) as [V |] eqn:Hn; [| discriminate ].
  destruct (gs_frame_cons_inv _ _ _ _ Hn) as [[? ->] | [_ ->]]; [ contradiction | exact Hp ].
Qed.

Lemma gs_param_top : forall U Ξ j T,
    gs_param (U :: Ξ) (lp_mk (length Ξ) j) = Some T -> List.nth_error (gu_ptys U) j = Some T.
Proof. intros *; unfold gs_param; cbn [lp_mod lp_param]; rewrite gs_frame_top; auto. Qed.

(** ** Closing a Frame

    The frame [P ⍮ Φ] at level [length Ξ1] of the source is closed and filed as
    [mp]: its parameters become the λ-variables [P] below the local context, a
    member of it becomes the member read out of [mp] and applied to them, and
    everything else stays as it is.  What is supplied is where the target
    resolves what the source did, and that each member of the closed frame is
    well typed there. *)
Section Close.
  Variables (Θ1 Θ2 : gdeps) (Ξ1 Ξ2 : gstack) (P : ctx) (Φ : gmod) (mp : path).

  #[local] Notation L := (length Ξ1).
  #[local] Notation c := (length P).
  #[local] Notation Ξs := (gu_mk P (ctx_ptys (length Ξ1) P) Φ :: Ξ1).

  Hypothesis Hbase : ⊢ Θ2 ⍮ Ξ2 ⍮ P.
  Hypothesis Hsrc : ⊢ Θ1 ⍮ Ξs ⍮ ⋅.
  (** the frames outside the closed one *)
  Hypothesis Hpout : forall lp T, gs_param Ξ1 lp = Some T -> gs_param Ξ2 lp = Some T.
  Hypothesis Hglob_out : forall r E, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ E -> Θ2 ⍮ Ξ2 ∋ᵍ r ⇒ E.
  (** the closed frame's members, filed and well typed *)
  Hypothesis Hglob_here : forall ip b pv A B,
      Φ ∋ ip ⇒ ge_def b pv A B -> Θ2 ⍮ Ξ2 ∋ᵍ p_app mp ip ⇒ def_close L mp P b pv A B.
  Hypothesis Hhere_typ : forall ip b pv A B,
      Φ ∋ ip ⇒ ge_def b pv A B -> exists i, Θ2 ⍮ Ξ2 ⍮ P ⊢ A[close L mp c]ᵐ : Type@i.
  Hypothesis Hhere_body : forall ip pv A M,
      Φ ∋ ip ⇒ ge_def true pv A (Some M) -> Θ2 ⍮ Ξ2 ⍮ P ⊢ M[close L mp c]ᵐ : A[close L mp c]ᵐ.

  Lemma close_preserves_wf :
    (forall Γ, ⊢ Θ1 ⍮ Ξs ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ[close L mp c]ᵐ ++ P) /\
    (forall Γ A M, Θ1 ⍮ Ξs ⍮ Γ ⊢ M : A ->
        Θ2 ⍮ Ξ2 ⍮ Γ[close L mp c]ᵐ ++ P ⊢ M[ms_close L mp c (length Γ)]ᵐ : A[ms_close L mp c (length Γ)]ᵐ) /\
    (forall Γ A M M', Θ1 ⍮ Ξs ⍮ Γ ⊢ M ≈ M' : A ->
        Θ2 ⍮ Ξ2 ⍮ Γ[close L mp c]ᵐ ++ P
          ⊢ M[ms_close L mp c (length Γ)]ᵐ ≈ M'[ms_close L mp c (length Γ)]ᵐ : A[ms_close L mp c (length Γ)]ᵐ) /\
    (forall Γ A A', Θ1 ⍮ Ξs ⍮ Γ ⊢ A ⊆ A' ->
        Θ2 ⍮ Ξ2 ⍮ Γ[close L mp c]ᵐ ++ P ⊢ A[ms_close L mp c (length Γ)]ᵐ ⊆ A'[ms_close L mp c (length Γ)]ᵐ).
  Proof.
    assert (Hqn : forall k, ms_eq (ms_qn k (close L mp c)) (ms_close L mp c k))
      by (intros; rewrite <- (Nat.add_0_r k) at 2; apply ms_qn_close).
    destruct wf_scoped as [Hsc _].
    destruct (Hsc _ _ _ Hsrc) as (_ & [(HPs & _ & _ & _) HΞ1s] & HΘs); cbn [gu_params] in HPs.
    assert (HL : length (gs_cs Ξ1) = L) by apply gs_cs_length.
    destruct (msub_preserves_wf Θ1 Θ2 Ξs Ξ2 (close L mp c) P) as (Hc & He & Hq & Hs).
    - assumption.
    - (* a parameter of the closed frame is a λ-variable past [Γ]; one further
         out stays *)
      intros [m j] T Γ Hp _ HΓ; rewrite !(exp_msub_ext _ _ _ (Hqn _)).
      destruct (Nat.eq_dec m L) as [-> |].
      + apply gs_param_top in Hp; cbn [gu_ptys] in Hp.
        destruct (ctx_ptys_nth _ _ _ _ Hp) as (Pa & A & Pb & HP & Hl & ->).
        assert (HAs : exp_scoped j (gs_cs Ξ1) A).
        { rewrite HP in HPs; apply ctx_scoped_app in HPs as [_ [HA _]].
          rewrite Nat.add_0_r, Hl in HA; exact HA. }
        assert (Hjc : j <= c) by (rewrite HP, List.length_app; cbn; lia).
        rewrite <- HL, (exp_params_close_here _ _ _ _ _ _ HAs Hjc), HL.
        cbn [msubst MSub_exp exp_msub ms_param ms_close lp_mod lp_param]; rewrite Nat.eqb_refl.
        pose proof (ctx_lookup_param_var Γ[close L mp c]ᵐ Pa A Pb) as Hv.
        rewrite <- HP, ctx_msub_length, Hl in Hv.
        split; econstructor; [ exact HΓ | exact Hv | exact HΓ | exact Hv ].
      + apply gs_param_pop in Hp; [| cbn; assumption ].
        pose proof (param_type_scoped _ _ _ HΞ1s Hp) as HT.
        rewrite <- HL, (exp_msub_close_fix _ _ _ _ _ _ HT), HL.
        cbn [msubst MSub_exp exp_msub ms_param ms_close lp_mod lp_param].
        destruct (Nat.eqb_spec m L); [ contradiction |].
        split; econstructor; eauto.
    - (* a global: a member of the closed frame is applied to its parameters;
         anything else stays, and so does its type *)
      intros r b pv A B Γ Hl _ HΓ; rewrite !(exp_msub_ext _ _ _ (Hqn _)).
      pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ Hsrc Hl) as HscA.
      destruct r as [[fp | m] ip]; [| destruct (Nat.eq_dec m L) as [-> | Hm] ].
      2:{ apply gc_lookup_top in Hl; cbn [gu_mod] in Hl.
          pose proof (Hglob_here _ _ _ _ _ Hl) as Hl'.
          destruct (Hhere_typ _ _ _ _ _ Hl) as [i HY].
          pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ HΓ Hl') as HscT; cbn in HscT.
          rewrite <- (exp_msub_close_shiftn _ _ _ _ _ _ HscA).
          cbn [msubst MSub_exp exp_msub ms_glob ms_close p_qual p_mems]; rewrite Nat.eqb_refl.
          assert (HF0 : Θ2 ⍮ Ξ2 ⍮ Γ[close L mp c]ᵐ ++ P ⊢ a_glob (p_app mp ip)
                        : ctx_pi P A[close L mp c]ᵐ) by (econstructor; eassumption).
          rewrite <- (exp_closed_wk _ _ (wk_shiftn (length Γ[close L mp c]ᵐ + length P)) HscT) in HF0.
          rewrite <- (ctx_msub_length (close L mp c) Γ).
          split; [ eapply app_vars_typed | eapply app_vars_eq ]; eauto using wf_exp_eq_refl. }
      all: apply gc_lookup_pop in Hl; [| cbn; congruence ].
      all: pose proof (gc_lookup_scoped _ _ _ _ _ _ _ HΞ1s HΘs Hl) as [HA _].
      all: rewrite <- HL, (exp_msub_close_fix _ _ _ _ _ _ HA), HL.
      all: cbn [msubst MSub_exp exp_msub ms_glob ms_close p_qual p_mems].
      all: try (destruct (Nat.eqb_spec m L); [ contradiction |]).
      all: split; econstructor; eauto.
    - (* δ: unfold, then β once per parameter *)
      intros r A M Γ pv Hl _ HΓ; rewrite !(exp_msub_ext _ _ _ (Hqn _)).
      pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ Hsrc Hl) as HscA.
      pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ Hsrc Hl) as HscM.
      destruct r as [[fp | m] ip]; [| destruct (Nat.eq_dec m L) as [-> | Hm] ].
      2:{ apply gc_lookup_top in Hl; cbn [gu_mod] in Hl.
          pose proof (Hglob_here _ _ _ _ _ Hl) as Hl'; cbn [def_close option_map] in Hl'.
          destruct (Hhere_typ _ _ _ _ _ Hl) as [i HY].
          pose proof (Hhere_body _ _ _ _ Hl) as HZ.
          pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ HΓ Hl') as HscT.
          pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ HΓ Hl') as HscB.
          rewrite <- (exp_msub_close_shiftn _ _ _ _ _ _ HscA), <- (exp_msub_close_shiftn _ _ _ _ _ _ HscM).
          cbn [msubst MSub_exp exp_msub ms_glob ms_close p_qual p_mems]; rewrite Nat.eqb_refl.
          assert (HF0 : Θ2 ⍮ Ξ2 ⍮ Γ[close L mp c]ᵐ ++ P ⊢ a_glob (p_app mp ip)
                        ≈ ctx_fn P M[close L mp c]ᵐ : ctx_pi P A[close L mp c]ᵐ)
            by (econstructor; eassumption).
          rewrite <- (exp_closed_wk _ _ (wk_shiftn (length Γ[close L mp c]ᵐ + length P)) HscT),
            <- (exp_closed_wk _ _ (wk_shiftn (length Γ[close L mp c]ᵐ + length P)) HscB) in HF0.
          rewrite <- (ctx_msub_length (close L mp c) Γ).
          eapply wf_exp_eq_trans; [ eapply app_vars_eq; eassumption | eapply app_vars_beta; eassumption ]. }
      all: apply gc_lookup_pop in Hl; [| cbn; congruence ].
      all: pose proof (gc_lookup_scoped _ _ _ _ _ _ _ HΞ1s HΘs Hl) as [HA HB]; cbn in HB.
      all: rewrite <- HL, (exp_msub_close_fix _ _ _ _ _ _ HA), (exp_msub_close_fix _ _ _ _ _ _ HB), HL.
      all: cbn [msubst MSub_exp exp_msub ms_glob ms_close p_qual p_mems].
      all: try (destruct (Nat.eqb_spec m L); [ contradiction |]).
      all: econstructor; eauto.
    - repeat split; intros * H;
        [ exact (Hc _ _ _ H eq_refl eq_refl)
        | pose proof (He _ _ _ _ _ H eq_refl eq_refl) as H'
        | pose proof (Hq _ _ _ _ _ _ H eq_refl eq_refl) as H'
        | pose proof (Hs _ _ _ _ _ H eq_refl eq_refl) as H' ];
        rewrite !(exp_msub_ext _ _ _ (Hqn _)) in H'; exact H'.
  Qed.
End Close.

(** ** Frames Built One Member at a Time *)

(** The frame a module is checked in, at the level of the stack it is pushed
    on. *)
Notation gs_push Ξ P Φ := (gu_mk P (ctx_ptys (List.length Ξ) P) Φ :: Ξ).

Lemma wf_gmod_gstack : forall Θ Ξ P Φ, Θ ⍮ Ξ ⍮ P ⊢m Φ -> wf_gstack Θ Ξ.
Proof.
  intros * H; pose proof (ctx_wf_gctx _ _ _ (wf_gmod_ctx _ _ _ _ H)) as Hg.
  inversion Hg; assumption.
Qed.

Lemma wf_frame_ctx : forall Θ Ξ P Φ, Θ ⍮ Ξ ⍮ P ⊢m Φ -> ⊢ Θ ⍮ gs_push Ξ P Φ ⍮ ⋅.
Proof.
  intros * H; apply wf_ctx_empty, wf_gctx_intro, wf_gstack_cons;
    [ eapply wf_gmod_gstack; eassumption | constructor; [ exact H | reflexivity ] ].
Qed.

(** The number of declarations, nested ones included: what an induction that
    descends through a closed module into the module it closed decreases. *)
Fixpoint ge_size (E : gentry) : nat :=
  match E with
  | ge_def _ _ _ _ => 0
  | ge_mod _ Φ => gm_size Φ
  end
with gm_size (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ' _ E => S (gm_size Φ' + ge_size E)
  end.

Lemma gm_size_close : forall L mp Δ Φ, gm_size (gm_close L mp Δ Φ) = gm_size Φ.
Proof.
  fix IH 4; intros L mp Δ [| Φ x E]; cbn; [ reflexivity |].
  rewrite IH; destruct E; cbn; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma wf_gmod_prefix_n : forall n Φ Φp Θ Ξ P,
    gm_size Φ < n -> gm_prefix Φp Φ -> Θ ⍮ Ξ ⍮ P ⊢m Φ -> Θ ⍮ Ξ ⍮ P ⊢m Φp.
Proof.
  induction n; intros * Hn Hp Hw; [ lia |].
  inversion Hp; subst; [ assumption | |].
  - inversion Hw as [| ? ? ? ? ? ? HΦ HE Hf]; subst.
    eapply IHn; [| eassumption | eassumption ]; cbn in Hn; lia.
  - inversion Hw as [| ? ? ? ? ? ? HΦ HE Hf]; subst.
    inversion HE as [| | ? ? ? ? ? HΦo Heq]; subst.
    match goal with H : gm_prefix _ (gm_close _ _ _ _) |- _ =>
      destruct (gm_close_prefix_inv _ _ _ _ _ H _ eq_refl) as (Φq & -> & Hq) end.
    econstructor; [ eassumption | constructor | assumption ].
    eapply IHn; [| eassumption | eassumption ].
    cbn in Hn; rewrite gm_size_close in Hn; lia.
Qed.

Lemma wf_gmod_prefix : forall Φp Φ Θ Ξ P, gm_prefix Φp Φ -> Θ ⍮ Ξ ⍮ P ⊢m Φ -> Θ ⍮ Ξ ⍮ P ⊢m Φp.
Proof. intros; eapply (wf_gmod_prefix_n (S (gm_size Φ))); eauto. Qed.

(** A frame grown along a prefix: what it resolves carries over. *)
Lemma gc_ext_grow : forall Θ Ξ P X Φp Φ,
    gm_prefix Φp Φ -> gc_ext Θ (gu_mk P X Φp :: Ξ) Θ (gu_mk P X Φ :: Ξ).
Proof.
  intros * Hp; split.
  - intros * Hl; inversion Hl; subst; [| econstructor; eassumption ].
    match goal with H : gs_frame _ _ = Some _ |- _ =>
      destruct (gs_frame_cons_inv _ _ _ _ H) as [[-> ->] | [Hlt Hn]] end.
    + eapply gcl_rel; [ apply gs_frame_top | cbn in *; eauto using gm_prefix_lookup ].
    + eapply gcl_rel; [ rewrite gs_frame_push; eassumption | eassumption ].
  - unfold gs_param; intros * Hp'.
    destruct (gs_frame (gu_mk P X Φp :: Ξ) (lp_mod lp)) as [V |] eqn:Hn; [| discriminate ].
    destruct (gs_frame_cons_inv _ _ _ _ Hn) as [[-> ->] | [Hlt Hn']].
    + rewrite gs_frame_top; exact Hp'.
    + rewrite gs_frame_push, Hn' by assumption; exact Hp'.
Qed.

Lemma frame_grow : forall Θ Ξ P X Φp Φ,
    gm_prefix Φp Φ ->
    ⊢ Θ ⍮ gu_mk P X Φ :: Ξ ⍮ ⋅ ->
    (forall Γ, ⊢ Θ ⍮ gu_mk P X Φp :: Ξ ⍮ Γ -> ⊢ Θ ⍮ gu_mk P X Φ :: Ξ ⍮ Γ) /\
    (forall Γ A M, Θ ⍮ gu_mk P X Φp :: Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ gu_mk P X Φ :: Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ ⍮ gu_mk P X Φp :: Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ ⍮ gu_mk P X Φ :: Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ ⍮ gu_mk P X Φp :: Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ gu_mk P X Φ :: Ξ ⍮ Γ ⊢ A ⊆ A').
Proof. intros * Hp Hb; apply rebase_preserves_wf; [ apply gc_ext_grow; exact Hp | exact Hb ]. Qed.

(** More levels: what resolved still does. *)
Lemma gc_ext_levels : forall Θ1 Θ2 Ξ, Θ1 ⊑ Θ2 -> gc_ext Θ1 Ξ Θ2 Ξ.
Proof.
  intros * Hg; split; [| auto ].
  intros * Hl; inversion Hl; subst; econstructor; eauto.
Qed.

Lemma levels_grow : forall Θ1 Θ2 Ξ,
    Θ1 ⊑ Θ2 ->
    ⊢ Θ2 ⍮ Ξ ⍮ ⋅ ->
    (forall Γ, ⊢ Θ1 ⍮ Ξ ⍮ Γ -> ⊢ Θ2 ⍮ Ξ ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ ⍮ Γ ⊢ A ⊆ A').
Proof. intros * Hg Hb; apply rebase_preserves_wf; [ apply gc_ext_levels; exact Hg | exact Hb ]. Qed.

(** ** Members at Their Insertion *)

(** Each member, typed in the frame it was inserted into: the module as it
    stood just before it. *)
Definition ins_typed (Θ : gdeps) (Ξ : gstack) (P : ctx) (Φ : gmod) : Prop :=
  forall Φq ip b pv A B,
    gm_ins Φ Φq ip (ge_def b pv A B) ->
    (exists i, Θ ⍮ gs_push Ξ P Φq ⍮ ⋅ ⊢ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ gs_push Ξ P Φq ⍮ ⋅ ⊢ M : A).

(** ** Closing a Nested Module *)

Section Pop.
  Variables (Θ : gdeps) (Ξ : gstack) (P : ctx) (Φ : gmod) (x : String.string) (Δ' : ctx) (Φ' : gmod).

  #[local] Notation Ξ1 := (gs_push Ξ P Φ).
  #[local] Notation mx := (p_rel (length Ξ) (x :: nil)).
  #[local] Notation Ln := (S (length Ξ)).
  #[local] Notation Tgt Φc := (gs_push Ξ P (Φ ⊳ x ↦ ge_mod Δ' Φc)).

  Hypothesis HΦ : Θ ⍮ Ξ ⍮ P ⊢m Φ ⊳ x ↦ ge_mod Δ' (gm_close Ln mx Δ' Φ').
  Hypothesis HΦ' : Θ ⍮ Ξ1 ⍮ Δ' ⊢m Φ'.
  Hypothesis Hins : ins_typed Θ Ξ1 Δ' Φ'.

  (** Each member of [x], closed, is well typed where [x] stood when it was
      inserted. *)
  Lemma closable_pop : forall n Φq ip b pv A B,
      gm_count Φq < n ->
      gm_ins Φ' Φq ip (ge_def b pv A B) ->
      (exists i, Θ ⍮ Tgt (gm_close Ln mx Δ' Φq) ⍮ Δ' ⊢ A[close Ln mx (length Δ')]ᵐ : Type@i) /\
      (forall M, B = Some M ->
         Θ ⍮ Tgt (gm_close Ln mx Δ' Φq) ⍮ Δ' ⊢ M[close Ln mx (length Δ')]ᵐ : A[close Ln mx (length Δ')]ᵐ).
  Proof.
    induction n as [| n IH]; intros * Hlt Hi; [ lia |].
    pose proof (gm_ins_prefix _ _ _ _ Hi) as Hpq.
    assert (Hwq : Θ ⍮ Ξ1 ⍮ Δ' ⊢m Φq) by (eapply wf_gmod_prefix; eassumption).
    assert (Hsrc : ⊢ Θ ⍮ gs_push Ξ1 Δ' Φq ⍮ ⋅) by (apply wf_frame_ctx; assumption).
    assert (Htgt : ⊢ Θ ⍮ Tgt (gm_close Ln mx Δ' Φq) ⍮ ⋅)
      by (apply wf_frame_ctx; eapply wf_gmod_prefix;
          [ apply gmp_in, gm_close_prefix; eassumption | eassumption ]).
    assert (Hext : gc_ext Θ Ξ1 Θ (Tgt (gm_close Ln mx Δ' Φq))) by (apply gc_ext_grow; auto with mctt).
    assert (Hbase : ⊢ Θ ⍮ Tgt (gm_close Ln mx Δ' Φq) ⍮ Δ')
      by (eapply rebase_preserves_wf; [ exact Hext | exact Htgt | eapply wf_gmod_ctx; eassumption ]).
    destruct (Hins _ _ _ _ _ _ Hi) as [[i HT] Hb].
    destruct (close_preserves_wf Θ Θ Ξ1 (Tgt (gm_close Ln mx Δ' Φq)) Δ' Φq mx) as (_ & He & _ & _).
    - exact Hbase.
    - exact Hsrc.
    - apply Hext.
    - apply Hext.
    - (* a member of [x] is read out through it *)
      intros * Hl; eapply gcl_rel; [ apply gs_frame_top | cbn; apply gml_in, gm_close_lookup; exact Hl ].
    - (* and was inserted before, so is closed already *)
      intros * Hl.
      destruct (gm_lookup_ins _ _ _ Hl) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ Hpq Hir)) as [[j HT'] _].
      exists j; eapply (frame_grow _ _ _ _ (Φ ⊳ x ↦ ge_mod Δ' (gm_close Ln mx Δ' Φr)));
        [ apply gmp_in, gm_close_prefix, (gm_ins_prefix _ _ _ _ Hir) | exact Htgt | exact HT' ].
    - intros * Hl.
      destruct (gm_lookup_ins _ _ _ Hl) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ Hpq Hir)) as [_ HM'].
      eapply (frame_grow _ _ _ _ (Φ ⊳ x ↦ ge_mod Δ' (gm_close Ln mx Δ' Φr)));
        [ apply gmp_in, gm_close_prefix, (gm_ins_prefix _ _ _ _ Hir) | exact Htgt | exact (HM' _ eq_refl) ].
    - split.
      + exists i; exact (He _ _ _ HT).
      + intros M ->; exact (He _ _ _ (Hb _ eq_refl)).
  Qed.
End Pop.

(** ** Closing a Unit as It Is Filed *)

Section File.
  Variables (Θ' Θ2 : gdeps) (fp : list String.string) (PU : ctx) (ΦU Φt : gmod).

  #[local] Notation mf := (p_abs fp nil).

  Hypothesis HU : Θ' ⍮ nil ⍮ PU ⊢m ΦU.
  Hypothesis Hins : ins_typed Θ' nil PU ΦU.
  Hypothesis Hfp : gds_lookup Θ2 fp = Some (gu_mk PU nil (gm_close 0 mf PU Φt)).
  Hypothesis Hgrow : Θ' ⊑ Θ2.
  Hypothesis Htgt : ⊢ Θ2 ⍮ nil ⍮ ⋅.

  (** Each member of the unit inserted before [Φt] ends, closed, is well typed
      under its parameters once [Φt] is filed. *)
  Lemma closable_file : forall n Φq ip b pv A B,
      gm_count Φq < n ->
      gm_ins ΦU Φq ip (ge_def b pv A B) ->
      gm_prefix Φq Φt ->
      (exists i, Θ2 ⍮ nil ⍮ PU ⊢ A[close 0 mf (length PU)]ᵐ : Type@i) /\
      (forall M, B = Some M ->
         Θ2 ⍮ nil ⍮ PU ⊢ M[close 0 mf (length PU)]ᵐ : A[close 0 mf (length PU)]ᵐ).
  Proof.
    induction n as [| n IH]; intros * Hlt Hi Hpt; [ lia |].
    pose proof (gm_ins_prefix _ _ _ _ Hi) as Hpq.
    assert (Hwq : Θ' ⍮ nil ⍮ PU ⊢m Φq) by (eapply wf_gmod_prefix; eassumption).
    assert (Hsrc : ⊢ Θ' ⍮ gs_push nil PU Φq ⍮ ⋅) by (apply wf_frame_ctx; assumption).
    assert (Hbase : ⊢ Θ2 ⍮ nil ⍮ PU) by (eapply levels_grow; [ eassumption | eassumption | eapply wf_gmod_ctx; eassumption ]).
    destruct (Hins _ _ _ _ _ _ Hi) as [[i HT] Hb].
    destruct (close_preserves_wf Θ' Θ2 nil nil PU Φq mf) as (_ & He & _ & _).
    - exact Hbase.
    - exact Hsrc.
    - unfold gs_param; intros [m j] T Hp; cbn in Hp; destruct m; discriminate.
    - (* no frame outside the unit: only the levels below *)
      apply gc_ext_levels; exact Hgrow.
    - (* a member of the unit is read out of it, filed *)
      intros * Hl; cbn [p_app p_qual p_mems List.app]; cbn [length].
      eapply gcl_abs; [ exact Hfp | cbn; apply gm_close_lookup; eauto using gm_prefix_lookup ].
    - intros * Hl.
      destruct (gm_lookup_ins _ _ _ Hl) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ Hpq Hir)
                  (gm_prefix_trans _ _ _ (gm_ins_prefix _ _ _ _ Hir) Hpt)) as [HT' _]; exact HT'.
    - intros * Hl.
      destruct (gm_lookup_ins _ _ _ Hl) as [Φr Hir].
      pose proof (gm_ins_count _ _ _ _ Hir) as Hcr.
      destruct (IH Φr _ _ _ _ _ ltac:(lia) (gm_prefix_ins _ _ _ _ _ Hpq Hir)
                  (gm_prefix_trans _ _ _ (gm_ins_prefix _ _ _ _ Hir) Hpt)) as [_ HM'];
        exact (HM' _ eq_refl).
    - split.
      + exists i; exact (He _ _ _ HT).
      + intros M ->; exact (He _ _ _ (Hb _ eq_refl)).
  Qed.
End File.
