(** * Scoping

    Every well-formed term is well scoped: its λ-variables are among the local
    binders, and its module parameters and frame references among the frames
    open around it.  What this buys is closedness of globals: an entry is
    stored as a term at [⋅], so in a well-formed context its type and body have
    no free λ-variable, and weakening and substitution leave them alone.  The
    [a_glob] rules rely on exactly that instead of premising it.  The frames
    mentioned matter when a frame is closed: an entry of a frame further out
    does not mention it, so closing it leaves that entry alone.

    A scope is the number [n] of λ-variables and the parameter counts [cs] of
    the frames, *by level* (outermost first), so pushing a frame appends to
    [cs].  Scoping is proved for all eleven judgments at once. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Opening.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Definitions *)

Definition param_ok (cs : list nat) (lp : lpath) : Prop :=
  exists c, List.nth_error cs (lp_mod lp) = Some c /\ lp_param lp < c.

(** A frame reference names one of the frames in scope. *)
Definition path_ok (cs : list nat) (p : path) : Prop :=
  match p_qual p with
  | qu_abs _ => True
  | qu_rel m => m < length cs
  end.

Fixpoint exp_scoped (n : nat) (cs : list nat) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_nat | a_zero => True
  | a_glob p => path_ok cs p
  | a_succ M => exp_scoped n cs M
  | a_natrec A MZ MS M =>
      exp_scoped (S n) cs A /\ exp_scoped n cs MZ /\ exp_scoped (S (S n)) cs MS /\ exp_scoped n cs M
  | a_pi A B | a_fn A B => exp_scoped n cs A /\ exp_scoped (S n) cs B
  | a_app M N => exp_scoped n cs M /\ exp_scoped n cs N
  | a_var x => x < n
  | a_param lp => param_ok cs lp
  end.

(** Each binding is scoped by the bindings below it, and the bottom one by [n]. *)
Fixpoint ctx_scoped (n : nat) (cs : list nat) (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | A :: Γ => exp_scoped (length Γ + n) cs A /\ ctx_scoped n cs Γ
  end.

Definition opt_scoped (n : nat) (cs : list nat) (B : option exp) : Prop :=
  match B with
  | None => True
  | Some M => exp_scoped n cs M
  end.

(** The parameter counts of the frames on a stack, by level. *)
Definition gs_cs (Ξ : gstack) : list nat := List.rev (List.map (fun U => length (gu_ptys U)) Ξ).

Lemma gs_cs_length : forall Ξ, length (gs_cs Ξ) = length Ξ.
Proof. intros; unfold gs_cs; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma gs_cs_cons : forall U Ξ, gs_cs (U :: Ξ) = gs_cs Ξ ++ length (gu_ptys U) :: nil.
Proof. reflexivity. Qed.

Lemma gs_cs_app : forall Ξa Ξb, gs_cs (Ξa ++ Ξb) = gs_cs Ξb ++ gs_cs Ξa.
Proof. intros; unfold gs_cs; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

(** ** Syntactic Facts *)

Lemma exp_scoped_mono : forall M n m cs, n <= m -> exp_scoped n cs M -> exp_scoped m cs M.
Proof.
  induction M; intros * Hle HM; cbn in *; destruct_all; repeat split; try lia; auto;
    match goal with
    | IH : forall _ _ _, _ -> exp_scoped _ _ ?X -> exp_scoped _ _ ?X, H : exp_scoped ?j _ ?X
      |- exp_scoped ?k _ ?X =>
        apply (IH j k); [ lia | exact H ]
    end.
Qed.

(** More frames pushed inside: what was in scope still is, at the same level. *)
Lemma exp_scoped_cs_app : forall M n cs cs', exp_scoped n cs M -> exp_scoped n (cs ++ cs') M.
Proof.
  induction M; intros * HM; cbn in *; destruct_all; repeat split; auto.
  - destruct HM as [c [Hc Hk]]; exists c; split; [| assumption ].
    rewrite List.nth_error_app1 by (apply List.nth_error_Some; congruence); assumption.
  - unfold path_ok in *; destruct (p_qual p); cbn in *; auto; rewrite List.length_app; lia.
Qed.

Corollary exp_scoped_cs_nil : forall M n cs, exp_scoped n nil M -> exp_scoped n cs M.
Proof. intros; apply (exp_scoped_cs_app _ _ nil); assumption. Qed.

Lemma opt_scoped_cs_app : forall B n cs cs', opt_scoped n cs B -> opt_scoped n (cs ++ cs') B.
Proof. intros [M|] *; cbn; eauto using exp_scoped_cs_app. Qed.

Lemma ctx_scoped_cs_app : forall Γ n cs cs', ctx_scoped n cs Γ -> ctx_scoped n (cs ++ cs') Γ.
Proof. induction Γ; intros * H; cbn in *; destruct_all; eauto using exp_scoped_cs_app. Qed.

(** What each operation has to satisfy on the scope, lifted under one binder. *)

Lemma wk_q_bound : forall φ n m,
    (forall x, x < n -> φ x < m) -> forall x, x < S n -> wk_q φ x < S m.
Proof. intros * H [|x] ?; cbn; [ lia |]. specialize (H x ltac:(lia)); lia. Qed.

Lemma wk_q_fix : forall φ n,
    (forall x, x < n -> φ x = x) -> forall x, x < S n -> wk_q φ x = x.
Proof. intros * H [|x] ?; cbn; [ reflexivity |]. rewrite H by lia; reflexivity. Qed.

Lemma sb_q_fix : forall σ n,
    (forall x, x < n -> σ x = #x) -> forall x, x < S n -> (q σ) x = #x.
Proof.
  intros * H [|x] ?; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  rewrite H by lia; reflexivity.
Qed.

Lemma exp_scoped_wk : forall M n m cs φ,
    exp_scoped n cs M ->
    (forall x, x < n -> φ x < m) ->
    exp_scoped m cs M[φ]ʷ.
Proof.
  induction M; intros * HM Hφ; cbn in *; destruct_all; repeat split; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply wk_q_bound; assumption.
Qed.

Corollary exp_scoped_shift : forall M n cs, exp_scoped n cs M -> exp_scoped (S n) cs M[↑]ʷ.
Proof.
  intros; eapply exp_scoped_wk; [ eassumption |]; cbn; lia.
Qed.

Lemma sb_q_bound : forall σ n m cs,
    (forall x, x < n -> exp_scoped m cs (σ x)) ->
    forall x, x < S n -> exp_scoped (S m) cs ((q σ) x).
Proof.
  intros * H [|x] ?; rewrite ?sb_q_zero, ?sb_q_succ; cbn; [ lia |].
  apply exp_scoped_shift, H; lia.
Qed.

Lemma exp_scoped_sub : forall M n m cs σ,
    exp_scoped n cs M ->
    (forall x, x < n -> exp_scoped m cs (σ x)) ->
    exp_scoped m cs M[σ].
Proof.
  induction M; intros * HM Hσ; cbn in *; destruct_all; repeat split; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply sb_q_bound; assumption.
Qed.

Lemma exp_scoped_wk_id : forall M n cs φ,
    exp_scoped n cs M ->
    (forall x, x < n -> φ x = x) ->
    M[φ]ʷ = M.
Proof.
  induction M; intros * HM Hφ; cbn in *; destruct_all; f_equal; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply wk_q_fix; assumption.
Qed.

Lemma exp_scoped_sub_id : forall M n cs σ,
    exp_scoped n cs M ->
    (forall x, x < n -> σ x = #x) ->
    M[σ] = M.
Proof.
  induction M; intros * HM Hσ; cbn in *; destruct_all; f_equal; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply sb_q_fix; assumption.
Qed.

(** A term with no free λ-variable is fixed by every weakening and every
    substitution. *)
Corollary exp_closed_wk : forall M cs φ, exp_scoped 0 cs M -> M[φ]ʷ = M.
Proof.
  intros; eapply exp_scoped_wk_id; [ eassumption | lia ].
Qed.

Corollary exp_closed_sub : forall M cs σ, exp_scoped 0 cs M -> M[σ] = M.
Proof.
  intros; eapply exp_scoped_sub_id; [ eassumption | lia ].
Qed.

(** ** Closing a Frame *)

Lemma app_vars_scoped : forall M N cs d c,
    exp_scoped N cs M -> d + c <= N -> exp_scoped N cs (app_vars M d c).
Proof.
  intros M N cs d c; revert M; induction c; intros * HM Hle; cbn; [ assumption |].
  apply IHc; [ cbn; split; [ assumption | lia ] | lia ].
Qed.

Lemma path_ok_app : forall cs mp ip, path_ok cs mp -> path_ok cs (p_app mp ip).
Proof. intros * H; exact H. Qed.

(** Closing the frame at level [length cs], [n] binders in: its [c]
    parameters become the λ-variables past [n]. *)
Lemma exp_scoped_msub_close : forall M n c cs mp,
    path_ok cs mp ->
    exp_scoped n (cs ++ c :: nil) M -> exp_scoped (n + c) cs M[ms_close (length cs) mp c n]ᵐ.
Proof.
  induction M; intros * Hmp HM; cbn in *; destruct_all; repeat split.
  all: try rewrite (exp_msub_ext _ _ _ (ms_q_close _ _ _ _)).
  all: try rewrite (exp_msub_ext _ (ms_q (ms_q (ms_close _ _ _ _))) _ (ms_qn_close 2 _ _ _ _)).
  all: try (replace (S (n + c)) with (S n + c) by lia; auto).
  all: try (replace (S (S (n + c))) with (2 + n + c) by lia; auto).
  all: auto; try lia.
  - replace (S (S n + c)) with (S (S n) + c) by lia; auto.
  - match goal with l : lpath |- _ => destruct l as [m k] end;
      destruct HM as [c' [Hc Hk]]; cbn in *.
    destruct (Nat.eqb_spec m (length cs)) as [-> |].
    + rewrite List.nth_error_app2, Nat.sub_diag in Hc by lia; injection Hc as <-; cbn; lia.
    + exists c'; split; [| assumption ].
      assert (m < length (cs ++ c :: nil)) by (apply List.nth_error_Some; congruence).
      rewrite List.length_app in *; cbn in *.
      rewrite List.nth_error_app1 in Hc by lia; assumption.
  - destruct p as [[fp | m] ip]; unfold path_ok in *; cbn in *; auto.
    destruct (Nat.eqb_spec m (length cs)) as [-> |].
    + apply app_vars_scoped; cbn; [ exact Hmp | lia ].
    + rewrite List.length_app in HM; cbn in *; lia.
Qed.

Lemma opt_scoped_msub_close : forall B n c cs mp,
    path_ok cs mp ->
    opt_scoped n (cs ++ c :: nil) B -> opt_scoped (n + c) cs B[ms_close (length cs) mp c n]ᵐ.
Proof. intros [M|] *; cbn; eauto using exp_scoped_msub_close. Qed.

(** Closing a frame leaves alone what does not mention it. *)
Lemma exp_msub_close_fix : forall M n cs mp c d,
    exp_scoped n cs M -> M[ms_close (length cs) mp c d]ᵐ = M.
Proof.
  induction M; intros * HM; cbn in *; destruct_all; f_equal.
  all: try rewrite (exp_msub_ext _ _ _ (ms_q_close _ _ _ _)).
  all: try rewrite (exp_msub_ext _ (ms_q (ms_q (ms_close _ _ _ _))) _ (ms_qn_close 2 _ _ _ _)).
  all: eauto.
  - destruct l as [m k]; destruct HM as [c' [Hc _]]; cbn in *.
    destruct (Nat.eqb_spec m (length cs)) as [-> |]; [| reflexivity ].
    exfalso; assert (Hlt : length cs < length cs) by (apply List.nth_error_Some; congruence); lia.
  - destruct p as [[fp | m] ip]; unfold path_ok in *; cbn in *; [ reflexivity |].
    destruct (Nat.eqb_spec m (length cs)); [ lia | reflexivity ].
Qed.

Lemma opt_msub_close_fix : forall B n cs mp c d,
    opt_scoped n cs B -> B[ms_close (length cs) mp c d]ᵐ = B.
Proof. intros [M|] * H; cbn in *; [ erewrite exp_msub_close_fix by eassumption |]; reflexivity. Qed.

Lemma ctx_msub_close_fix : forall Δ n cs mp c,
    ctx_scoped n cs Δ -> Δ[close (length cs) mp c]ᵐ = Δ.
Proof.
  induction Δ; intros * H; cbn in *; destruct_all; [ reflexivity |]; f_equal; eauto.
  rewrite (exp_msub_ext _ _ _ (ms_qn_close _ _ _ _ _)); eapply exp_msub_close_fix; eassumption.
Qed.

Lemma ctx_scoped_app : forall Γ Δ n cs,
    ctx_scoped n cs (Γ ++ Δ) <-> ctx_scoped (length Δ + n) cs Γ /\ ctx_scoped n cs Δ.
Proof.
  induction Γ; intros; cbn; [ tauto |].
  rewrite IHΓ, List.length_app, Nat.add_assoc; tauto.
Qed.

Lemma ctx_scoped_lookup : forall Γ x A n cs,
    ctx_scoped n cs Γ ->
    Γ ∋ #x : A ->
    exp_scoped (length Γ + n) cs A.
Proof.
  intros * HΓ Hlk; induction Hlk; cbn in *; destruct_all;
    apply exp_scoped_shift; auto.
Qed.

Lemma ctx_lookup_length : forall Γ x A, Γ ∋ #x : A -> x < length Γ.
Proof.
  induction 1; cbn; lia.
Qed.

Lemma ctx_pi_scoped : forall Δ A n cs,
    ctx_scoped n cs Δ ->
    exp_scoped (length Δ + n) cs A ->
    exp_scoped n cs (ctx_pi Δ A).
Proof.
  induction Δ; intros * HΔ HA; cbn in *; destruct_all; [ assumption |].
  apply IHΔ; cbn; auto.
Qed.

Lemma ctx_fn_scoped : forall Δ M n cs,
    ctx_scoped n cs Δ ->
    exp_scoped (length Δ + n) cs M ->
    exp_scoped n cs (ctx_fn Δ M).
Proof.
  induction Δ; intros * HΔ HM; cbn in *; destruct_all; [ assumption |].
  apply IHΔ; cbn; auto.
Qed.


(** ** Parameter Types *)

Lemma ctx_ptys_nth : forall L Δ j T,
    List.nth_error (ctx_ptys L Δ) j = Some T ->
    exists Δa A Δb, Δ = Δa ++ A :: Δb /\ length Δb = j /\ T = A[sb_params L j].
Proof.
  induction Δ as [| A Δ IH]; intros * Hj; cbn in Hj; [ destruct j; discriminate |].
  destruct (Nat.lt_ge_cases j (length Δ)).
  - rewrite List.nth_error_app1 in Hj by (rewrite ctx_ptys_length; lia).
    destruct (IH _ _ Hj) as (Δa & B & Δb & -> & Hl & ->).
    exists (A :: Δa), B, Δb; auto.
  - rewrite List.nth_error_app2 in Hj by (rewrite ctx_ptys_length; lia).
    rewrite ctx_ptys_length in Hj.
    destruct (j - length Δ) as [| k] eqn:E; cbn in Hj; [| destruct k; discriminate ].
    injection Hj as <-; exists nil, A, Δ; repeat split; f_equal; f_equal; lia.
Qed.

Lemma ctx_ptys_scoped : forall Δ cs j T,
    ctx_scoped 0 cs Δ ->
    List.nth_error (ctx_ptys (length cs) Δ) j = Some T ->
    exp_scoped 0 (cs ++ length Δ :: nil) T.
Proof.
  intros * HΔ Hj.
  destruct (ctx_ptys_nth _ _ _ _ Hj) as (Δa & A & Δb & -> & Hl & ->).
  apply ctx_scoped_app in HΔ as [_ [HA _]].
  rewrite Nat.add_0_r, Hl in HA.
  eapply exp_scoped_sub; [ apply exp_scoped_cs_app; exact HA |].
  intros x Hx; unfold param_ok; cbn [lp_mod lp_param sb_params]; exists (length (Δa ++ A :: Δb)); split.
  - cbn [lp_mod]; rewrite List.nth_error_app2, Nat.sub_diag by lia; reflexivity.
  - cbn [lp_param]; rewrite List.length_app; cbn [length]; lia.
Qed.

(** ** What a Well-formed Global Context Guarantees *)

(** Every definition [Φ] resolves to is closed, and mentions the frames [cs]. *)
Definition lookups_scoped (Φ : gmod) (cs : list nat) : Prop :=
  forall ip b pv A B,
    Φ ∋ ip ⇒ ge_def b pv A B ->
    exp_scoped 0 cs A /\ opt_scoped 0 cs B.

(** A frame at level [length cs]: its telescope is scoped by the frames
    outside it, and its members and parameter types by those and itself. *)
Definition unit_scoped (U : gunit) (cs : list nat) : Prop :=
  ctx_scoped 0 cs (gu_params U) /\
  length (gu_ptys U) = length (gu_params U) /\
  lookups_scoped (gu_mod U) (cs ++ length (gu_params U) :: nil) /\
  (forall j T, List.nth_error (gu_ptys U) j = Some T -> exp_scoped 0 (cs ++ length (gu_params U) :: nil) T).

(** A filed unit is closed: it mentions no frame. *)
Definition units_scoped (Θ : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> lookups_scoped (gu_mod U) nil.

(** Each frame is scoped by the frames outside it. *)
Fixpoint gs_scoped (Ξ : gstack) : Prop :=
  match Ξ with
  | nil => True
  | U :: Ξ' => unit_scoped U (gs_cs Ξ') /\ gs_scoped Ξ'
  end.

Lemma gs_scoped_app : forall Ξa Ξb, gs_scoped (Ξa ++ Ξb) -> gs_scoped Ξb.
Proof. induction Ξa; intros * H; cbn in *; destruct_all; auto. Qed.

Lemma gs_scoped_frame : forall Ξ n U,
    gs_scoped Ξ ->
    gs_frame Ξ n = Some U ->
    exists Ξa Ξb, Ξ = Ξa ++ U :: Ξb /\ length Ξb = n /\ unit_scoped U (gs_cs Ξb) /\
      gs_cs Ξ = (gs_cs Ξb ++ length (gu_ptys U) :: nil) ++ gs_cs Ξa.
Proof.
  intros * HΞ Hn.
  destruct (gs_frame_split _ _ _ Hn) as (Ξa & Ξb & -> & Hl).
  pose proof (gs_scoped_app _ _ HΞ) as [HU _].
  exists Ξa, Ξb; split; [ reflexivity | split; [ assumption | split; [ assumption |] ] ].
  rewrite gs_cs_app, gs_cs_cons; reflexivity.
Qed.

(** Hence resolution in such a context hands back something closed, and
    scoped by the frames in scope. *)
Lemma gc_lookup_scoped : forall Θ Ξ p b pv A B,
    gs_scoped Ξ ->
    units_scoped Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
    exp_scoped 0 (gs_cs Ξ) A /\ opt_scoped 0 (gs_cs Ξ) B.
Proof.
  intros * HΞ HΘ Hlk; inversion Hlk; subst.
  - destruct (gs_scoped_frame _ _ _ HΞ ltac:(eassumption)) as (Ξa & Ξb & -> & _ & (_ & Hlen & Hc & _) & Hcs).
    match goal with H : gu_mod U ∋ _ ⇒ _ |- _ => destruct (Hc _ _ _ _ _ H) as [HA HB] end.
    rewrite Hcs; rewrite <- Hlen in HA, HB; split; [ apply exp_scoped_cs_app | apply opt_scoped_cs_app ]; assumption.
  - match goal with H : gu_mod U ∋ _ ⇒ _ |- _ => destruct (HΘ _ _ ltac:(eassumption) _ _ _ _ _ H) as [HA HB] end.
    split; [ apply exp_scoped_cs_nil | destruct B; cbn in *; [ apply exp_scoped_cs_nil |] ]; auto.
Qed.

(** A path that resolves names a frame in scope. *)
Lemma gc_lookup_path_ok : forall Θ Ξ p E,
    Θ ⍮ Ξ ∋ᵍ p ⇒ E -> path_ok (gs_cs Ξ) p.
Proof.
  intros * Hlk; inversion Hlk; subst; unfold path_ok; cbn; auto.
  rewrite gs_cs_length; eapply gs_frame_lt; eassumption.
Qed.

(** A parameter's type is closed, and a parameter that has one is in scope. *)
Lemma param_type_scoped : forall Ξ lp T,
    gs_scoped Ξ ->
    gs_param Ξ lp = Some T ->
    exp_scoped 0 (gs_cs Ξ) T.
Proof.
  unfold gs_param; intros * HΞ Hp.
  destruct (gs_frame Ξ (lp_mod lp)) as [U |] eqn:Hn; [| discriminate ].
  destruct (gs_scoped_frame _ _ _ HΞ Hn) as (Ξa & Ξb & -> & _ & (_ & Hlen & _ & Hc) & Hcs).
  rewrite Hcs, Hlen; apply exp_scoped_cs_app, (Hc _ _ Hp).
Qed.

Lemma param_ok_scoped : forall Ξ lp T,
    gs_param Ξ lp = Some T ->
    param_ok (gs_cs Ξ) lp.
Proof.
  unfold gs_param, param_ok; intros * Hp.
  destruct (gs_frame Ξ (lp_mod lp)) as [U |] eqn:Hn; [| discriminate ].
  destruct (gs_frame_split _ _ _ Hn) as (Ξa & Ξb & -> & Hl).
  exists (length (gu_ptys U)); split.
  - rewrite gs_cs_app, gs_cs_cons, <- List.app_assoc, List.nth_error_app2 by (rewrite gs_cs_length; lia).
    rewrite gs_cs_length, Hl, Nat.sub_diag; reflexivity.
  - apply List.nth_error_Some; congruence.
Qed.

(** What a closed module stores is scoped by the frames outside the closed
    one. *)
Lemma gm_close_scoped : forall cs mp Δ Φ,
    path_ok cs mp ->
    ctx_scoped 0 cs Δ ->
    lookups_scoped Φ (cs ++ length Δ :: nil) ->
    lookups_scoped (gm_close (length cs) mp Δ Φ) cs.
Proof.
  intros * Hmp HΔ HΦ ip b pv A B Hl.
  destruct (gm_close_lookup_inv _ _ _ _ _ _ Hl _ eq_refl) as (b0 & pv0 & A0 & B0 & Hl0 & Heq).
  injection Heq as -> -> -> ->.
  destruct (HΦ _ _ _ _ _ Hl0) as [HA HB].
  split.
  - apply ctx_pi_scoped; [ assumption |]; rewrite Nat.add_0_r.
    apply (exp_scoped_msub_close _ 0); assumption.
  - destruct B0; cbn in *; [| exact I ].
    apply ctx_fn_scoped; [ assumption |]; rewrite Nat.add_0_r.
    apply (exp_scoped_msub_close _ 0); assumption.
Qed.

(** The substitutions the rules instantiate with. *)

Lemma exp_scoped_sub1 : forall A M n cs,
    exp_scoped (S n) cs A -> exp_scoped n cs M -> exp_scoped n cs A[Id,,M].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; auto; lia. Qed.

Lemma exp_scoped_sub2 : forall A M N n cs,
    exp_scoped (S (S n)) cs A -> exp_scoped n cs M -> exp_scoped n cs N -> exp_scoped n cs A[Id,,M,,N].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|[|x]] ?; cbn; auto; lia. Qed.

Lemma exp_scoped_sub_succ : forall A n cs,
    exp_scoped (S n) cs A -> exp_scoped (S (S n)) cs A[Wk⨟Wk,,succ #1].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; lia. Qed.

#[local]
Hint Resolve exp_scoped_sub1 exp_scoped_sub2 exp_scoped_sub_succ exp_scoped_shift : mctt.


(** ** Every Judgment is Well Scoped *)

#[local] Arguments units_scoped : simpl never.
#[local] Arguments unit_scoped : simpl never.
#[local] Arguments lookups_scoped : simpl never.
#[local] Arguments gs_cs : simpl never.

(** What a well-formed context carries: its bindings are scoped by the frames
    in scope, and the global context is scoped. *)
Definition ctx_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  ctx_scoped 0 (gs_cs Ξ) Γ /\ gs_scoped Ξ /\ units_scoped Θ.

Definition entry_scoped (cs : list nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ pv A B => exp_scoped 0 cs A /\ opt_scoped 0 cs B
  | ge_mod Δ Φ => lookups_scoped Φ cs
  end.

Theorem wf_scoped :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ctx_ok Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) (gs_cs Ξ) M /\ exp_scoped (length Γ) (gs_cs Ξ) A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) (gs_cs Ξ) M /\ exp_scoped (length Γ) (gs_cs Ξ) M' /\
      exp_scoped (length Γ) (gs_cs Ξ) A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) (gs_cs Ξ) A /\ exp_scoped (length Γ) (gs_cs Ξ) A') /\
  (forall Θ Ξ x E, Θ ⍮ Ξ ⊢e x ↦ E -> Ξ <> nil -> entry_scoped (gs_cs Ξ) E) /\
  (forall Θ Ξ Δ Φ, Θ ⍮ Ξ ⍮ Δ ⊢m Φ ->
      ctx_scoped 0 (gs_cs Ξ) Δ /\ lookups_scoped Φ (gs_cs Ξ ++ length Δ :: nil)) /\
  (forall Θ Ξ U, Θ ⍮ Ξ ⊢u U -> unit_scoped U (gs_cs Ξ)) /\
  (forall Θ d, wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> lookups_scoped (gu_mod U) nil) /\
  (forall Θ, wf_gdeps Θ -> units_scoped Θ) /\
  (forall Θ Ξ, wf_gstack Θ Ξ -> gs_scoped Ξ /\ units_scoped Θ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> gs_scoped Ξ /\ units_scoped Θ).
Proof.
  apply wf_mut_ind_all; intros; unfold ctx_ok in *; cbn in *; destruct_all.
  all: repeat match goal with |- _ /\ _ => split end; try assumption;
    auto using exp_scoped_sub1, exp_scoped_sub2, exp_scoped_sub_succ, exp_scoped_shift.
  (* variables, parameters and globals are in scope, and what a global
     resolves to is closed *)
  all: try match goal with
    | H : _ ⍮ _ ∋ᵍ ?p ⇒ _ |- path_ok _ ?p => eapply gc_lookup_path_ok; exact H
    | H : gs_param _ ?lp = Some _ |- param_ok _ ?lp => eapply param_ok_scoped; exact H
    | |- exp_scoped (length ?Γ + 0) _ _ => rewrite Nat.add_0_r; assumption
    | H : ?Γ ∋ # ?x : ?A |- ?x < _ => apply ctx_lookup_length in H; assumption
    | H : ?Γ ∋ # ?x : ?A, HΓ : ctx_scoped 0 _ ?Γ |- exp_scoped _ _ ?A =>
        pose proof (ctx_scoped_lookup _ _ _ _ _ HΓ H) as Hs; rewrite Nat.add_0_r in Hs; exact Hs
    | H : gs_param ?Ξ _ = Some ?T, HΞ : gs_scoped ?Ξ |- exp_scoped _ _ ?T =>
        eapply exp_scoped_mono; [| exact (param_type_scoped _ _ _ HΞ H) ]; lia
    | H : _ ⍮ _ ∋ᵍ _ ⇒ ge_def _ _ ?A _, HΞ : gs_scoped _, HΘ : units_scoped _
      |- exp_scoped _ _ ?A =>
        eapply exp_scoped_mono; [| apply (gc_lookup_scoped _ _ _ _ _ _ _ HΞ HΘ H) ]; lia
    | H : _ ⍮ _ ∋ᵍ _ ⇒ ge_def _ _ _ (Some ?M), HΞ : gs_scoped _, HΘ : units_scoped _
      |- exp_scoped _ _ ?M =>
        eapply exp_scoped_mono; [| apply (gc_lookup_scoped _ _ _ _ _ _ _ HΞ HΘ H) ]; lia
    end.
  all: try lia.
  - (* [rec], successor *)
    rewrite ?Nat.add_0_r in *.
    eapply exp_scoped_sub2; [ eassumption | eassumption | cbn; repeat split; assumption ].
  - (* a nested module, closed *)
    rewrite <- (gs_cs_length Ξ); apply gm_close_scoped; [| assumption | assumption ].
    unfold path_ok; cbn; rewrite gs_cs_length; destruct Ξ; cbn; [ congruence | lia ].
  - (* the empty module *)
    intros ? * Hlk; inversion Hlk.
  - (* extending a module *)
    match goal with H : _ -> entry_scoped _ ?E |- _ =>
      specialize (H ltac:(discriminate)); rewrite gs_cs_cons in H; cbn [gu_ptys] in H; rewrite ctx_ptys_length in H end.
    unfold lookups_scoped; intros * Hlk; inversion Hlk; subst.
    + match goal with H : entry_scoped _ _ |- _ => cbn in H; destruct H end; cbn; auto.
    + match goal with H : entry_scoped _ _ |- _ => cbn in H; eapply H; eassumption end.
    + match goal with H : lookups_scoped Φ _ |- _ => eapply H; eassumption end.
  - (* a frame: its parameter types are those of its telescope *)
    unfold unit_scoped.
    match goal with Hp : gu_ptys _ = _ |- _ =>
      refine (conj _ (conj _ (conj _ _)));
      [ assumption | rewrite Hp; apply ctx_ptys_length | assumption
      | intros * Hj; rewrite Hp, <- (gs_cs_length Ξ) in Hj; eapply ctx_ptys_scoped; eassumption ]
    end.
  - (* a unit, closed as it is filed *)
    match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end.
    match goal with H : unit_scoped _ _ |- _ => destruct H as (HP & _ & HM & _) end.
    cbn [gu_close gu_mod gu_params].
    apply (gm_close_scoped nil); [ exact I | exact HP | exact HM ].
  - eauto.
  - intros fp U Hl; discriminate.
  - (* a level filed on top: its own units, or the ones below *)
    intros fp U Hl; unfold gds_lookup in Hl; cbn in Hl.
    apply gd_lookup_app_inv in Hl as [Hl | Hl]; [ eapply H2, gd_lookup_in, Hl | eapply H0, Hl ].
Qed.

(** ** Consequences *)

(** In a well-formed context, what a global resolves to has no free
    λ-variable. *)
Corollary wf_gc_lookup_closed : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
    exp_scoped 0 (gs_cs Ξ) A /\ opt_scoped 0 (gs_cs Ξ) B.
Proof.
  intros * HΓ Hlk; destruct wf_scoped as [Hctx _].
  destruct (Hctx _ _ _ HΓ) as (_ & HΞ & HΘ).
  eapply gc_lookup_scoped; eassumption.
Qed.

Corollary wf_gc_lookup_type_closed : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
    exp_scoped 0 (gs_cs Ξ) A.
Proof.
  intros; eapply wf_gc_lookup_closed; eassumption.
Qed.

Corollary wf_gc_lookup_body_closed : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A (Some M) ->
    exp_scoped 0 (gs_cs Ξ) M.
Proof.
  intros * HΓ Hlk; apply (wf_gc_lookup_closed _ _ _ _ _ _ _ _ HΓ Hlk).
Qed.

Corollary wf_param_type_closed : forall Θ Ξ Γ lp T,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gs_param Ξ lp = Some T ->
    exp_scoped 0 (gs_cs Ξ) T.
Proof.
  intros * HΓ Hp; destruct wf_scoped as [Hctx _].
  destruct (Hctx _ _ _ HΓ) as (_ & HΞ & _).
  eapply param_type_scoped; eassumption.
Qed.
