(** * Scoping

    Every well-formed term is well scoped: its free variables are among the
    local binders and the parameters of the modules open around it.  What this
    buys is closedness of globals.  A definition is handed back generalized over
    everything that was in scope where it was declared, so in a well-formed
    context its type and body have no free variable at all, and weakening and
    substitution leave them alone.  The [a_glob] rules rely on exactly that
    instead of premising it.

    Scoping is proved for all eleven judgments at once: the term judgments need
    closedness of what resolution hands back, which comes from [⊢g], which is
    checked by the term judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Opening.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

(** ** Definitions *)

Fixpoint exp_scoped (n : nat) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_nat | a_zero | a_glob _ => True
  | a_succ M => exp_scoped n M
  | a_natrec A MZ MS M =>
      exp_scoped (S n) A /\ exp_scoped n MZ /\ exp_scoped (S (S n)) MS /\ exp_scoped n M
  | a_pi A B | a_fn A B => exp_scoped n A /\ exp_scoped (S n) B
  | a_app M N => exp_scoped n M /\ exp_scoped n N
  | a_var x => x < n
  end.

(** Each binding is scoped by the bindings below it, and the bottom one by [n]. *)
Fixpoint ctx_scoped (n : nat) (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | A :: Γ => exp_scoped (length Γ + n) A /\ ctx_scoped n Γ
  end.

Definition opt_scoped (n : nat) (B : option exp) : Prop :=
  match B with
  | None => True
  | Some M => exp_scoped n M
  end.

(** ** Syntactic Facts *)

Lemma exp_scoped_mono : forall M n m, n <= m -> exp_scoped n M -> exp_scoped m M.
Proof.
  induction M; intros * Hle HM; cbn in *; destruct_all; repeat split; try lia; auto;
    match goal with
    | IH : forall _ _, _ -> exp_scoped _ ?X -> exp_scoped _ ?X, H : exp_scoped ?j ?X
      |- exp_scoped ?k ?X =>
        apply (IH j k); [ lia | exact H ]
    end.
Qed.

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

Lemma exp_scoped_wk : forall M n m φ,
    exp_scoped n M ->
    (forall x, x < n -> φ x < m) ->
    exp_scoped m M[φ]w.
Proof.
  induction M; intros * HM Hφ; cbn in *; destruct_all; repeat split; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply wk_q_bound; assumption.
Qed.

Corollary exp_scoped_shift : forall M n, exp_scoped n M -> exp_scoped (S n) M[↑]w.
Proof.
  intros; eapply exp_scoped_wk; [ eassumption |]; cbn; lia.
Qed.

Lemma sb_q_bound : forall σ n m,
    (forall x, x < n -> exp_scoped m (σ x)) ->
    forall x, x < S n -> exp_scoped (S m) ((q σ) x).
Proof.
  intros * H [|x] ?; rewrite ?sb_q_zero, ?sb_q_succ; cbn; [ lia |].
  apply exp_scoped_shift, H; lia.
Qed.

Lemma exp_scoped_sub : forall M n m σ,
    exp_scoped n M ->
    (forall x, x < n -> exp_scoped m (σ x)) ->
    exp_scoped m M[σ].
Proof.
  induction M; intros * HM Hσ; cbn in *; destruct_all; repeat split; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply sb_q_bound; assumption.
Qed.

Lemma exp_scoped_wk_id : forall M n φ,
    exp_scoped n M ->
    (forall x, x < n -> φ x = x) ->
    M[φ]w = M.
Proof.
  induction M; intros * HM Hφ; cbn in *; destruct_all; f_equal; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply wk_q_fix; assumption.
Qed.

Lemma exp_scoped_sub_id : forall M n σ,
    exp_scoped n M ->
    (forall x, x < n -> σ x = #x) ->
    M[σ] = M.
Proof.
  induction M; intros * HM Hσ; cbn in *; destruct_all; f_equal; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply sb_q_fix; assumption.
Qed.

(** A closed expression is fixed by every weakening and every substitution. *)
Corollary exp_closed_wk : forall M φ, exp_scoped 0 M -> M[φ]w = M.
Proof.
  intros; eapply exp_scoped_wk_id; [ eassumption | lia ].
Qed.

Corollary exp_closed_sub : forall M σ, exp_scoped 0 M -> M[σ] = M.
Proof.
  intros; eapply exp_scoped_sub_id; [ eassumption | lia ].
Qed.

Lemma exp_scoped_open : forall a M n, exp_scoped n M -> exp_scoped n M[a]p.
Proof.
  intros a M; induction M; intros; cbn in *; destruct_all; repeat split; eauto.
Qed.

Lemma opt_scoped_open : forall a B n, opt_scoped n B -> opt_scoped n B[a]p.
Proof.
  intros a [M|] n; cbn; eauto using exp_scoped_open.
Qed.

Lemma ctx_scoped_open : forall a Γ n, ctx_scoped n Γ -> ctx_scoped n Γ[a]p.
Proof.
  intros a Γ; induction Γ; intros; cbn in *; destruct_all; [ auto |].
  rewrite list_open_length; eauto using exp_scoped_open.
Qed.

Lemma ctx_scoped_app : forall Γ Δ n,
    ctx_scoped n (Γ ++ Δ) <-> ctx_scoped (length Δ + n) Γ /\ ctx_scoped n Δ.
Proof.
  induction Γ; intros; cbn; [ tauto |].
  rewrite IHΓ, List.length_app, Nat.add_assoc; tauto.
Qed.

Lemma ctx_scoped_lookup : forall Γ x A n,
    ctx_scoped n Γ ->
    Γ ∋ #x : A ->
    exp_scoped (length Γ + n) A.
Proof.
  intros * HΓ Hlk; induction Hlk; cbn in *; destruct_all;
    apply exp_scoped_shift; auto.
Qed.

Lemma ctx_pi_scoped : forall Δ A n,
    ctx_scoped n Δ ->
    exp_scoped (length Δ + n) A ->
    exp_scoped n (ctx_pi Δ A).
Proof.
  induction Δ; intros * HΔ HA; cbn in *; destruct_all; [ assumption |].
  apply IHΔ; cbn; auto.
Qed.

Lemma ctx_fn_scoped : forall Δ M n,
    ctx_scoped n Δ ->
    exp_scoped (length Δ + n) M ->
    exp_scoped n (ctx_fn Δ M).
Proof.
  induction Δ; intros * HΔ HM; cbn in *; destruct_all; [ assumption |].
  apply IHΔ; cbn; auto.
Qed.

Lemma ctx_lookup_length : forall Γ x A, Γ ∋ #x : A -> x < length Γ.
Proof.
  induction 1; cbn; lia.
Qed.

(** ** What a Well-formed Global Context Guarantees *)

(** How many parameters are in scope on a stack. *)
Definition gs_len (Ξ : gstack) : nat := length (gs_tele Ξ).

Lemma gs_len_nil : gs_len nil = 0.
Proof. reflexivity. Qed.

Lemma gs_len_cons : forall U Ξ, gs_len (U :: Ξ) = length (gu_params U) + gs_len Ξ.
Proof.
  intros; unfold gs_len; rewrite gs_tele_cons, list_open_length, List.length_app; reflexivity.
Qed.

(** Every definition [Φ] resolves to is scoped by [n] once generalized over the
    parameters on its member chain. *)
Definition lookups_closed (Φ : gmod) (n : nat) : Prop :=
  forall ip Δ b A B,
    Φ ∋ ip ⇒ Δ ⍮ ge_def b A B ->
    exp_scoped n (ctx_pi Δ A) /\ opt_scoped n (option_map (ctx_fn Δ) B).

(** A unit that is checked with nothing around it is closed. *)
Definition unit_closed (U : gunit) : Prop :=
  ctx_scoped 0 (gu_params U) /\ lookups_closed (gu_mod U) (length (gu_params U)).

Definition units_closed (Θ : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> unit_closed U.

(** Each frame is scoped by the frames outside it. *)
Fixpoint gs_scoped (Ξ : gstack) : Prop :=
  match Ξ with
  | nil => True
  | U :: Ξ' =>
      ctx_scoped (gs_len Ξ') (gu_params U) /\
      lookups_closed (gu_mod U) (length (gu_params U) + gs_len Ξ') /\
      gs_scoped Ξ'
  end.

Lemma gs_scoped_tele : forall Ξ, gs_scoped Ξ -> ctx_scoped 0 (gs_tele Ξ).
Proof.
  induction Ξ as [| U Ξ IH]; intros HΞ; cbn in *; destruct_all; [ auto |].
  apply ctx_scoped_open, ctx_scoped_app; split; [| auto ].
  rewrite Nat.add_0_r; assumption.
Qed.

Lemma gs_scoped_nth : forall Ξ n U,
    gs_scoped Ξ ->
    List.nth_error Ξ n = Some U ->
    List.skipn n Ξ = U :: List.skipn (S n) Ξ /\ gs_scoped (List.skipn n Ξ).
Proof.
  induction Ξ as [| V Ξ IH]; intros [|n] U HΞ Hn; cbn in *; try discriminate;
    destruct_all; [ injection Hn as ->; cbn; auto |].
  apply IH; assumption.
Qed.

(** Generalizing what a frame holds over the telescope in scope there closes it,
    and opening keeps it closed. *)
Lemma generalize_closed : forall Δ T A B a,
    ctx_scoped 0 T ->
    exp_scoped (length T) (ctx_pi Δ A) ->
    opt_scoped (length T) (option_map (ctx_fn Δ) B) ->
    exp_scoped 0 (ctx_pi (Δ ++ T)[a]p A[a]p) /\
    opt_scoped 0 (option_map (ctx_fn (Δ ++ T)[a]p) B[a]p).
Proof.
  intros * HT HA HB.
  rewrite <- ctx_pi_open, ctx_pi_app; split.
  - apply exp_scoped_open, ctx_pi_scoped; [ assumption | rewrite Nat.add_0_r; assumption ].
  - destruct B as [M|]; cbn in *; [| auto ].
    rewrite <- ctx_fn_open, ctx_fn_app.
    apply exp_scoped_open, ctx_fn_scoped; [ assumption | rewrite Nat.add_0_r; assumption ].
Qed.

(** Hence resolution in such a context hands back something closed. *)
Lemma gc_lookup_closed : forall Θ Ξ p Δ b A B,
    gs_scoped Ξ ->
    units_closed Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b A B ->
    exp_scoped 0 (ctx_pi Δ A) /\ opt_scoped 0 (option_map (ctx_fn Δ) B).
Proof.
  intros * HΞ HΘ Hlk; inversion Hlk; subst.
  - destruct (gs_scoped_nth _ _ _ HΞ ltac:(eassumption)) as [Hsk Hsc].
    rewrite Hsk in Hsc |- *; apply gs_scoped_tele in Hsc as Ht.
    cbn [gs_scoped] in Hsc; destruct Hsc as (Hp & Hc & Hrest).
    match goal with H : gu_mod U ∋ _ ⇒ _ ⍮ _ |- _ => destruct (Hc _ _ _ _ _ H) end.
    pose proof (gs_len_cons U (List.skipn (S n) Ξ)) as Hl; unfold gs_len at 1 in Hl.
    apply generalize_closed; rewrite ?Hl; assumption.
  - destruct (HΘ _ _ ltac:(eassumption)) as [Hp Hc].
    match goal with H : gu_mod U ∋ _ ⇒ _ ⍮ _ |- _ => destruct (Hc _ _ _ _ _ H) end.
    assert (ctx_scoped 0 (gs_tele (U :: nil)))
      by (apply gs_scoped_tele; cbn [gs_scoped]; rewrite gs_len_nil, Nat.add_0_r; auto).
    pose proof (gs_len_cons U nil) as Hl; unfold gs_len at 1 in Hl.
    rewrite gs_len_nil, Nat.add_0_r in Hl.
    apply generalize_closed; rewrite ?Hl; assumption.
Qed.

(** The substitutions the rules instantiate with. *)

Lemma exp_scoped_sub1 : forall A M n,
    exp_scoped (S n) A -> exp_scoped n M -> exp_scoped n A[Id,,M].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; auto; lia. Qed.

Lemma exp_scoped_sub2 : forall A M N n,
    exp_scoped (S (S n)) A -> exp_scoped n M -> exp_scoped n N -> exp_scoped n A[Id,,M,,N].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|[|x]] ?; cbn; auto; lia. Qed.

Lemma exp_scoped_sub_succ : forall A n,
    exp_scoped (S n) A -> exp_scoped (S (S n)) A[Wk⨟Wk,,succ #1].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; lia. Qed.

#[local]
Hint Resolve exp_scoped_sub1 exp_scoped_sub2 exp_scoped_sub_succ exp_scoped_shift : mctt.

(** ** Every Judgment is Well Scoped *)

#[local] Arguments units_closed : simpl never.
#[local] Arguments unit_closed : simpl never.
#[local] Arguments lookups_closed : simpl never.
#[local] Arguments gs_len : simpl never.

(** What a well-formed context carries: its local part is scoped by the stack's
    parameters, and the global context resolves only to closed things. *)
Definition ctx_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  ctx_scoped (gs_len Ξ) Γ /\ gs_scoped Ξ /\ units_closed Θ.

Definition entry_scoped (n : nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ A B => exp_scoped n A /\ opt_scoped n B
  | ge_mod Δ Φ => ctx_scoped n Δ /\ lookups_closed Φ (length Δ + n)
  end.

Theorem wf_scoped :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ctx_ok Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ + gs_len Ξ) M /\ exp_scoped (length Γ + gs_len Ξ) A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ + gs_len Ξ) M /\ exp_scoped (length Γ + gs_len Ξ) M' /\
      exp_scoped (length Γ + gs_len Ξ) A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ + gs_len Ξ) A /\ exp_scoped (length Γ + gs_len Ξ) A') /\
  (forall Θ Ξ E, Θ ⍮ Ξ ⊢e E -> entry_scoped (gs_len Ξ) E) /\
  (forall Θ Ξ Δ Φ, Θ ⍮ Ξ ⍮ Δ ⊢m Φ ->
      ctx_scoped (gs_len Ξ) Δ /\ lookups_closed Φ (length Δ + gs_len Ξ)) /\
  (forall Θ Ξ U, Θ ⍮ Ξ ⊢u U ->
      ctx_scoped (gs_len Ξ) (gu_params U) /\ lookups_closed (gu_mod U) (length (gu_params U) + gs_len Ξ)) /\
  (forall Θ d, wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> unit_closed U) /\
  (forall Θ, wf_gdeps Θ -> units_closed Θ) /\
  (forall Θ Ξ, wf_gstack Θ Ξ -> gs_scoped Ξ /\ units_closed Θ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> gs_scoped Ξ /\ units_closed Θ).
Proof.
  apply wf_mut_ind_all; intros; unfold ctx_ok in *; cbn in *; destruct_all.
  all: repeat match goal with |- _ /\ _ => split end; try assumption;
    auto using exp_scoped_sub1, exp_scoped_sub2, exp_scoped_sub_succ, exp_scoped_shift.
  (* variables are among the local binders and the parameters in scope, and a
     global resolves to something closed *)
  all: try match goal with
    | H : ?Γ ++ gs_tele ?Ξ ∋ # ?x : ?A |- ?x < _ =>
        apply ctx_lookup_length in H; rewrite List.length_app in H; unfold gs_len; lia
    | H : ?Γ ++ gs_tele ?Ξ ∋ # ?x : ?A, HΓ : ctx_scoped (gs_len ?Ξ) ?Γ, HΞ : gs_scoped ?Ξ
      |- exp_scoped _ ?A =>
        eapply ctx_scoped_lookup in H;
          [ rewrite List.length_app, Nat.add_0_r in H; exact H
          | apply ctx_scoped_app; split;
            [ rewrite Nat.add_0_r; exact HΓ | apply gs_scoped_tele; exact HΞ ] ]
    | H : _ ⍮ _ ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ _, HΞ : gs_scoped _, HΘ : units_closed _
      |- exp_scoped _ (ctx_pi _ _) =>
        eapply exp_scoped_mono; [| apply (gc_lookup_closed _ _ _ _ _ _ _ HΞ HΘ H) ]; lia
    | H : _ ⍮ _ ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ (Some _), HΞ : gs_scoped _, HΘ : units_closed _
      |- exp_scoped _ (ctx_fn _ _) =>
        eapply exp_scoped_mono; [| apply (gc_lookup_closed _ _ _ _ _ _ _ HΞ HΘ H) ]; lia
    end.
  - (* [rec], successor *)
    eapply exp_scoped_sub2; [ eassumption | eassumption | cbn; repeat split; assumption ].
  - lia.
  - (* the empty module *)
    intros ? * Hlk; inversion Hlk.
  - (* extending a module: what resolves through a nested module is generalized
       over its parameters too *)
    match goal with H : entry_scoped _ _ |- _ => rewrite gs_len_cons in H; rename H into HE end.
    unfold lookups_closed; intros * Hlk; inversion Hlk; subst.
    + cbn in HE; destruct HE as [HA HB]; split; [ exact HA | destruct B; exact HB ].
    + cbn in HE; destruct HE as [HΔ' HΦ'].
      match goal with
      | Hi : _ ∋ _ ⇒ _ ⍮ ge_def _ _ _ |- _ => destruct (HΦ' _ _ _ _ _ Hi) as [HA HB]
      end.
      rewrite ctx_pi_app, <- ctx_pi_open; split.
      * apply ctx_pi_scoped; [ assumption |]. apply exp_scoped_open; assumption.
      * match goal with HB : opt_scoped _ (option_map (ctx_fn _) ?B') |- _ => destruct B' as [M0|] end;
          cbn in *; [| exact I ].
        rewrite ctx_fn_app, <- ctx_fn_open.
        apply ctx_fn_scoped; [ assumption |]. apply exp_scoped_open; assumption.
    + eauto.
  - contradiction.
  - match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end.
    unfold unit_closed; rewrite gs_len_nil, ?Nat.add_0_r in *; split; assumption.
  - eauto.
  - intros fp U Hl; discriminate.
  - (* a level filed on top: its own units, or the ones below *)
    intros fp U Hl; unfold gds_lookup in Hl; cbn in Hl.
    apply gd_lookup_app_inv in Hl as [Hl | Hl]; [ eapply H2, gd_lookup_in, Hl | eapply H0, Hl ].
Qed.

(** ** Consequences *)

(** In a well-formed context, what a global resolves to is closed. *)
Corollary wf_gc_lookup_closed : forall Θ Ξ Γ p Δ b A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b A B ->
    exp_scoped 0 (ctx_pi Δ A) /\ opt_scoped 0 (option_map (ctx_fn Δ) B).
Proof.
  intros * HΓ Hlk; destruct wf_scoped as [Hctx _].
  destruct (Hctx _ _ _ HΓ) as (_ & HΞ & HΘ).
  eapply gc_lookup_closed; eassumption.
Qed.

Corollary wf_gc_lookup_type_closed : forall Θ Ξ Γ p Δ b A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b A B ->
    exp_scoped 0 (ctx_pi Δ A).
Proof.
  intros; eapply wf_gc_lookup_closed; eassumption.
Qed.

Corollary wf_gc_lookup_body_closed : forall Θ Ξ Γ p Δ b A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b A (Some M) ->
    exp_scoped 0 (ctx_fn Δ M).
Proof.
  intros * HΓ Hlk; apply (wf_gc_lookup_closed _ _ _ _ _ _ _ _ HΓ Hlk).
Qed.
