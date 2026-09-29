(** * Scoping

    Every well-formed term is well scoped: its λ-variables are among the local
    binders, and its module parameters among those of the frames open around
    it.  What this buys is closedness of globals.  Resolution hands a definition
    back generalized over the parameters of the modules it is read out of, so in
    a well-formed context its type and body have no free λ-variable, and
    weakening and substitution leave them alone.  The [a_glob] rules rely on
    exactly that instead of premising it.

    A scope is the number [n] of λ-variables and the parameter counts [cs] of
    the frames, innermost first.  Scoping is proved for all eleven judgments at
    once: the term judgments need closedness of what resolution hands back,
    which comes from [⊢g], which is checked by the term judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Opening.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Definitions *)

Definition param_ok (cs : list nat) (lp : lpath) : Prop :=
  exists c, List.nth_error cs (lp_mod lp) = Some c /\ lp_param lp < c.

(** A relative path names one of the frames in scope. *)
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

(** The parameter counts of the frames on a stack. *)
Definition gs_cs (Ξ : gstack) : list nat := List.map (fun U => length (gu_params U)) Ξ.

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

(** With no frames, a well-scoped term has no parameter, so any frames will do. *)
Lemma exp_scoped_cs_nil : forall M n cs, exp_scoped n nil M -> exp_scoped n cs M.
Proof.
  induction M; intros * HM; cbn in *; destruct_all; repeat split; auto.
  - destruct HM as [c [Hc _]]; destruct (lp_mod l); discriminate.
  - unfold path_ok in *; destruct (p_qual p); cbn in *; auto; lia.
Qed.

Lemma opt_scoped_cs_nil : forall B n cs, opt_scoped n nil B -> opt_scoped n cs B.
Proof. intros [M|] *; cbn; eauto using exp_scoped_cs_nil. Qed.

Lemma ctx_scoped_cs_nil : forall Γ n cs, ctx_scoped n nil Γ -> ctx_scoped n cs Γ.
Proof. induction Γ; intros * H; cbn in *; destruct_all; eauto using exp_scoped_cs_nil. Qed.

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

(** ** Module Substitution *)

(** Shifting by [length pre] frames: the frames skipped over are [pre]. *)
Lemma exp_scoped_msub_shift : forall M n cs pre,
    exp_scoped n cs M -> exp_scoped n (pre ++ cs) M[↑ₘ (length pre)]ᵐ.
Proof.
  induction M; intros * HM; cbn in *; destruct_all; repeat split.
  all: try rewrite (exp_msub_ext _ _ _ (ms_q_shift _)).
  all: try rewrite (exp_msub_ext _ (ms_q (ms_q (↑ₘ _))) _ (ms_qn_shift 2 _)).
  all: auto.
  - destruct HM as [c [Hc Hk]]; exists c; cbn; split; [| assumption ].
    rewrite List.nth_error_app2 by lia; rewrite Nat.add_comm, Nat.add_sub; assumption.
  - destruct p as [[fp | m] ip]; unfold path_ok in *; cbn in *; auto.
    rewrite Nat.sub_0_r, List.length_app; lia.
Qed.

Lemma app_vars_scoped : forall M N cs d c,
    exp_scoped N cs M -> d + c <= N -> exp_scoped N cs (app_vars M d c).
Proof.
  intros M N cs d c; revert M; induction c; intros * HM Hle; cbn; [ assumption |].
  apply IHc; [ cbn; split; [ assumption | lia ] | lia ].
Qed.

(** Where the closed frame is read out to: a nested module of the next frame
    out, or a filed unit. *)
Definition close_ok (cs : list nat) (mp : path) : Prop :=
  forall c (r : path), path_ok (c :: cs) r -> path_ok cs r[mp]ᵖ.

Lemma close_ok_in : forall cs x, 0 < length cs -> close_ok cs (p_rel 0 (x :: nil)).
Proof.
  intros * Hlt c [[fp | [| m]] ip]; unfold path_ok; cbn; auto; intros; lia.
Qed.

Lemma close_ok_abs : forall cs fp, close_ok cs (p_abs fp nil).
Proof. intros * c [[fp' | m] ip]; unfold path_ok; cbn; auto. Qed.

(** Closing the innermost frame, [n] binders in: its [c] parameters become the
    λ-variables past [n]. *)
Lemma exp_scoped_msub_close : forall M n c cs mp,
    close_ok cs mp ->
    exp_scoped n (c :: cs) M -> exp_scoped (n + c) cs M[ms_close mp c n]ᵐ.
Proof.
  induction M; intros * Hmp HM; cbn in *; destruct_all; repeat split.
  all: try rewrite (exp_msub_ext _ _ _ (ms_q_close _ _ _)).
  all: try rewrite (exp_msub_ext _ (ms_q (ms_q (ms_close _ _ _))) _ (ms_qn_close 2 _ _ _)).
  all: try (replace (S (n + c)) with (S n + c) by lia; auto).
  all: try (replace (S (S (n + c))) with (2 + n + c) by lia; auto).
  all: auto; try lia.
  - replace (S (S n + c)) with (S (S n) + c) by lia; auto.
  - match goal with l : lpath |- _ => destruct l as [[| m] k] end;
      destruct HM as [c' [Hc Hk]]; cbn in *.
    + injection Hc as <-; lia.
    + exists c'; auto.
  - pose proof (Hmp c p HM) as Hp.
    destruct p as [[fp | [| m]] ip]; cbn; auto.
    apply app_vars_scoped; cbn; auto.
Qed.

(** Reading a frame's telescope as its parameters. *)
Lemma exp_scoped_sb_params : forall M n cs m c,
    exp_scoped n cs M -> List.nth_error cs m = Some c -> n <= c ->
    exp_scoped 0 cs M[sb_params m].
Proof.
  intros * HM Hc Hle; eapply exp_scoped_sub; [ eassumption |].
  intros x Hx; exists c; cbn; split; [ assumption | lia ].
Qed.

Lemma opt_scoped_msub_shift : forall B n cs pre,
    opt_scoped n cs B -> opt_scoped n (pre ++ cs) B[↑ₘ (length pre)]ᵐ.
Proof. intros [M|] *; cbn; eauto using exp_scoped_msub_shift. Qed.

Lemma opt_scoped_msub_close : forall B n c cs mp,
    close_ok cs mp ->
    opt_scoped n (c :: cs) B -> opt_scoped (n + c) cs B[ms_close mp c n]ᵐ.
Proof. intros [M|] *; cbn; eauto using exp_scoped_msub_close. Qed.

(** ** Telescopes *)

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

Lemma ctx_scoped_msub_shift : forall Δ n cs pre,
    ctx_scoped n cs Δ -> ctx_scoped n (pre ++ cs) Δ[↑ₘ (length pre)]ᵐ.
Proof.
  induction Δ; intros * H; cbn in *; destruct_all; [ auto |]; split; [| auto ].
  rewrite ctx_msub_length, (exp_msub_ext _ _ _ (ms_qn_shift _ _)).
  apply exp_scoped_msub_shift; assumption.
Qed.

(** A closed telescope sits on the [c] variables its frame's parameters became. *)
Lemma ctx_scoped_msub_close : forall Δ c cs mp,
    close_ok cs mp ->
    ctx_scoped 0 (c :: cs) Δ -> ctx_scoped c cs Δ[close mp c]ᵐ.
Proof.
  induction Δ; intros * Hmp H; cbn in *; destruct_all; [ auto |]; split; [| auto ].
  rewrite ctx_msub_length, (exp_msub_ext _ _ _ (ms_qn_close _ _ _ _)), !Nat.add_0_r.
  apply exp_scoped_msub_close; rewrite ?Nat.add_0_r in *; assumption.
Qed.

(** ** What a Well-formed Global Context Guarantees *)

(** Every definition [Φ] resolves to is scoped by the frames [cs], the first of
    which is [Φ]'s own, under the parameters on its member chain. *)
Definition lookups_scoped (Φ : gmod) (cs : list nat) : Prop :=
  forall ip Δ b pv A B,
    Φ ∋ ip ⇒ Δ ⍮ ge_def b pv A B ->
    ctx_scoped 0 cs Δ /\ exp_scoped (length Δ) cs A /\ opt_scoped (length Δ) cs B.

(** A unit checked with the frames [cs] outside it. *)
Definition unit_scoped (U : gunit) (cs : list nat) : Prop :=
  ctx_scoped 0 cs (gu_params U) /\ lookups_scoped (gu_mod U) (length (gu_params U) :: cs).

Definition units_scoped (Θ : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> unit_scoped U nil.

(** Each frame is scoped by the frames outside it. *)
Fixpoint gs_scoped (Ξ : gstack) : Prop :=
  match Ξ with
  | nil => True
  | U :: Ξ' => unit_scoped U (gs_cs Ξ') /\ gs_scoped Ξ'
  end.

Lemma gs_scoped_nth : forall Ξ n U,
    gs_scoped Ξ ->
    List.nth_error Ξ n = Some U ->
    unit_scoped U (gs_cs (List.skipn (S n) Ξ)).
Proof.
  induction Ξ as [| V Ξ IH]; intros [|n] U HΞ Hn; cbn in *; try discriminate;
    destruct_all; [ injection Hn as ->; assumption |].
  apply IH; assumption.
Qed.

Lemma gs_cs_split : forall Ξ n U,
    List.nth_error Ξ n = Some U ->
    gs_cs Ξ = List.firstn n (gs_cs Ξ) ++ length (gu_params U) :: gs_cs (List.skipn (S n) Ξ) /\
    length (List.firstn n (gs_cs Ξ)) = n.
Proof.
  induction Ξ as [| V Ξ IH]; intros [|n] U Hn; cbn in *; try discriminate.
  - injection Hn as ->; auto.
  - destruct (IH _ _ Hn) as [H1 H2]; unfold gs_cs in *; cbn; rewrite H1 at 1; cbn; auto.
Qed.

Lemma gs_cs_nth : forall Ξ n U,
    List.nth_error Ξ n = Some U -> List.nth_error (gs_cs Ξ) n = Some (length (gu_params U)).
Proof.
  intros * H; unfold gs_cs; rewrite List.nth_error_map, H; reflexivity.
Qed.

(** Hence resolution in such a context hands back something scoped by the
    frames in scope, with no free λ-variable once generalized. *)
Lemma gc_lookup_scoped : forall Θ Ξ p Δ b pv A B,
    gs_scoped Ξ ->
    units_scoped Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    ctx_scoped 0 (gs_cs Ξ) Δ /\ exp_scoped (length Δ) (gs_cs Ξ) A /\
    opt_scoped (length Δ) (gs_cs Ξ) B.
Proof.
  intros * HΞ HΘ Hlk; inversion Hlk; subst.
  - (* an open frame: its entry shifted past the frames nearer in *)
    pose proof (gs_scoped_nth _ _ _ HΞ ltac:(eassumption)) as [_ Hc].
    destruct (gs_cs_split _ _ _ ltac:(eassumption)) as [Hsp Hlen].
    match goal with H : gu_mod U ∋ _ ⇒ _ ⍮ _ |- _ => destruct (Hc _ _ _ _ _ _ H) as (HΔ & HA & HB) end.
    pose proof (ctx_scoped_msub_shift _ _ _ (List.firstn n (gs_cs Ξ)) HΔ) as HΔ'.
    pose proof (exp_scoped_msub_shift _ _ _ (List.firstn n (gs_cs Ξ)) HA) as HA'.
    pose proof (opt_scoped_msub_shift _ _ _ (List.firstn n (gs_cs Ξ)) HB) as HB'.
    rewrite Hlen, <- Hsp in HΔ', HA', HB'.
    rewrite ctx_msub_length; auto.
  - (* a filed unit: closed, so no parameter is left *)
    destruct (HΘ _ _ ltac:(eassumption)) as [Hp Hc].
    match goal with H : gu_mod U ∋ _ ⇒ _ ⍮ _ |- _ => destruct (Hc _ _ _ _ _ _ H) as (HΔ & HA & HB) end.
    rewrite List.length_app, ctx_msub_length; repeat split.
    + apply ctx_scoped_cs_nil, ctx_scoped_app; split;
        [ rewrite Nat.add_0_r; apply ctx_scoped_msub_close; [ apply close_ok_abs | assumption ]
        | assumption ].
    + apply exp_scoped_cs_nil, exp_scoped_msub_close; [ apply close_ok_abs | assumption ].
    + apply opt_scoped_cs_nil, opt_scoped_msub_close; [ apply close_ok_abs | assumption ].
Qed.

(** A path that resolves names a frame in scope. *)
Lemma gc_lookup_path_ok : forall Θ Ξ p Δ E,
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ E -> path_ok (gs_cs Ξ) p.
Proof.
  intros * Hlk; inversion Hlk; subst; unfold path_ok; cbn; auto.
  unfold gs_cs; rewrite List.length_map; apply List.nth_error_Some; congruence.
Qed.

Corollary gc_lookup_closed : forall Θ Ξ p Δ b pv A B,
    gs_scoped Ξ ->
    units_scoped Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    exp_scoped 0 (gs_cs Ξ) (ctx_pi Δ A) /\ opt_scoped 0 (gs_cs Ξ) (option_map (ctx_fn Δ) B).
Proof.
  intros * HΞ HΘ Hlk; destruct (gc_lookup_scoped _ _ _ _ _ _ _ _ HΞ HΘ Hlk) as (HΔ & HA & HB).
  split; [ apply ctx_pi_scoped; rewrite ?Nat.add_0_r; assumption |].
  destruct B; cbn in *; [ apply ctx_fn_scoped; rewrite ?Nat.add_0_r; assumption | auto ].
Qed.

(** A parameter's type has no λ-variable: the frame's own are read as its
    parameters, and the frames outside are shifted past those nearer in. *)
Lemma param_type_scoped : forall Ξ n U k T,
    gs_scoped Ξ ->
    List.nth_error Ξ n = Some U ->
    gu_params U ∋ #k : T ->
    exp_scoped 0 (gs_cs Ξ) T[↑ₘ (S n)]ᵐ[sb_params n].
Proof.
  intros * HΞ Hn Hk.
  pose proof (gs_scoped_nth _ _ _ HΞ Hn) as [HP _].
  destruct (gs_cs_split _ _ _ Hn) as [Hsp Hlen].
  pose proof (ctx_scoped_lookup _ _ _ _ _ HP Hk) as HT; rewrite Nat.add_0_r in HT.
  pose proof (exp_scoped_msub_shift _ _ _ (List.firstn n (gs_cs Ξ) ++ length (gu_params U) :: nil) HT) as HT'.
  rewrite List.length_app, Hlen, Nat.add_1_r, <- List.app_assoc in HT'; cbn [List.app] in HT'.
  rewrite <- Hsp in HT'.
  eapply exp_scoped_sb_params; [ exact HT' | apply gs_cs_nth; eassumption | lia ].
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
  | ge_mod Δ Φ => ctx_scoped 0 cs Δ /\ lookups_scoped Φ (length Δ :: cs)
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
  (forall Θ Ξ E, Θ ⍮ Ξ ⊢e E -> entry_scoped (gs_cs Ξ) E) /\
  (forall Θ Ξ Δ Φ, Θ ⍮ Ξ ⍮ Δ ⊢m Φ ->
      ctx_scoped 0 (gs_cs Ξ) Δ /\ lookups_scoped Φ (length Δ :: gs_cs Ξ)) /\
  (forall Θ Ξ U, Θ ⍮ Ξ ⊢u U -> unit_scoped U (gs_cs Ξ)) /\
  (forall Θ d, wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> unit_scoped U nil) /\
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
    | H : _ ⍮ _ ∋ᵍ ?p ⇒ _ ⍮ _ |- path_ok _ ?p => eapply gc_lookup_path_ok; exact H
    | |- exp_scoped (length ?Γ + 0) _ _ => rewrite Nat.add_0_r; assumption
    | H : ?Γ ∋ # ?x : ?A |- ?x < _ => apply ctx_lookup_length in H; assumption
    | H : ?Γ ∋ # ?x : ?A, HΓ : ctx_scoped 0 _ ?Γ |- exp_scoped _ _ ?A =>
        pose proof (ctx_scoped_lookup _ _ _ _ _ HΓ H) as Hs; rewrite Nat.add_0_r in Hs; exact Hs
    | Hn : List.nth_error ?Ξ ?n = Some ?U, Hk : gu_params ?U ∋ # ?k : _ |- param_ok _ _ =>
        exists (length (gu_params U)); split;
        [ apply gs_cs_nth; assumption | apply ctx_lookup_length in Hk; assumption ]
    | Hn : List.nth_error ?Ξ ?n = Some ?U, Hk : gu_params ?U ∋ # ?k : _, HΞ : gs_scoped ?Ξ
      |- exp_scoped _ _ _[_]ᵐ[_] =>
        eapply exp_scoped_mono; [| exact (param_type_scoped _ _ _ _ _ HΞ Hn Hk) ]; lia
    | H : _ ⍮ _ ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ _ _, HΞ : gs_scoped _, HΘ : units_scoped _
      |- exp_scoped _ _ (ctx_pi _ _) =>
        eapply exp_scoped_mono; [| apply (gc_lookup_closed _ _ _ _ _ _ _ _ HΞ HΘ H) ]; lia
    | H : _ ⍮ _ ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ _ (Some _), HΞ : gs_scoped _, HΘ : units_scoped _
      |- exp_scoped _ _ (ctx_fn _ _) =>
        eapply exp_scoped_mono; [| apply (gc_lookup_closed _ _ _ _ _ _ _ _ HΞ HΘ H) ]; lia
    end.
  all: try lia.
  - (* [rec], successor *)
    rewrite ?Nat.add_0_r in *.
    eapply exp_scoped_sub2; [ eassumption | eassumption | cbn; repeat split; assumption ].
  - (* the empty module *)
    intros ? * Hlk; inversion Hlk.
  - (* extending a module *)
    unfold lookups_scoped; intros * Hlk; inversion Hlk; subst.
    + match goal with H : entry_scoped _ _ |- _ => cbn in H; destruct H end; cbn; auto.
    + (* a member of the nested module, closed *)
      match goal with H : entry_scoped _ _ |- _ => cbn in H; destruct H as [HΔ' HΦ'] end.
      match goal with
      | Hi : _ ∋ _ ⇒ _ ⍮ ge_def _ _ _ _ |- _ => destruct (HΦ' _ _ _ _ _ _ Hi) as (HΔ2 & HA & HB)
      end.
      rewrite List.length_app, ctx_msub_length; repeat split.
      * apply ctx_scoped_app; split; [ rewrite Nat.add_0_r; apply ctx_scoped_msub_close | ];
          try apply close_ok_in; cbn; auto; lia.
      * apply exp_scoped_msub_close; [ apply close_ok_in; cbn; lia | assumption ].
      * apply opt_scoped_msub_close; [ apply close_ok_in; cbn; lia | assumption ].
    + match goal with H : lookups_scoped Φ _ |- _ => eapply H; eassumption end.
  - split; assumption.
  - match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; assumption.
  - eauto.
  - intros fp U Hl; discriminate.
  - (* a level filed on top: its own units, or the ones below *)
    intros fp U Hl; unfold gds_lookup in Hl; cbn in Hl.
    apply gd_lookup_app_inv in Hl as [Hl | Hl]; [ eapply H2, gd_lookup_in, Hl | eapply H0, Hl ].
Qed.

(** ** Consequences *)

(** In a well-formed context, what a global resolves to has no free
    λ-variable. *)
Corollary wf_gc_lookup_closed : forall Θ Ξ Γ p Δ b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    exp_scoped 0 (gs_cs Ξ) (ctx_pi Δ A) /\ opt_scoped 0 (gs_cs Ξ) (option_map (ctx_fn Δ) B).
Proof.
  intros * HΓ Hlk; destruct wf_scoped as [Hctx _].
  destruct (Hctx _ _ _ HΓ) as (_ & HΞ & HΘ).
  eapply gc_lookup_closed; eassumption.
Qed.

Corollary wf_gc_lookup_type_closed : forall Θ Ξ Γ p Δ b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    exp_scoped 0 (gs_cs Ξ) (ctx_pi Δ A).
Proof.
  intros; eapply wf_gc_lookup_closed; eassumption.
Qed.

Corollary wf_gc_lookup_body_closed : forall Θ Ξ Γ p Δ b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A (Some M) ->
    exp_scoped 0 (gs_cs Ξ) (ctx_fn Δ M).
Proof.
  intros * HΓ Hlk; apply (wf_gc_lookup_closed _ _ _ _ _ _ _ _ _ HΓ Hlk).
Qed.
