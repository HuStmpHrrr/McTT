(** * Scoping

    Every well-formed term is well scoped: its λ-variables are among the local
    binders.  What this buys is closedness of globals: every entry of a
    well-formed global context is stored generalized over its telescope, so its
    type and body have no free λ-variable, and weakening and substitution leave
    them alone.  The [a_glob] rules rely on exactly that instead of premising
    it.

    Scoping is proved for all eleven judgments at once: the term judgments need
    closedness of what resolution hands back, which comes from [⊢g], which is
    checked by the term judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

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
    exp_scoped m M[φ]ʷ.
Proof.
  induction M; intros * HM Hφ; cbn in *; destruct_all; repeat split; eauto;
    first [ eapply IHM1 | eapply IHM2 | eapply IHM3 ]; try eassumption;
    repeat apply wk_q_bound; assumption.
Qed.

Corollary exp_scoped_shift : forall M n, exp_scoped n M -> exp_scoped (S n) M[↑]ʷ.
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
    M[φ]ʷ = M.
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

(** A term with no free λ-variable is fixed by every weakening and every
    substitution. *)
Corollary exp_closed_wk : forall M φ, exp_scoped 0 M -> M[φ]ʷ = M.
Proof.
  intros; eapply exp_scoped_wk_id; [ eassumption | lia ].
Qed.

Corollary exp_closed_sub : forall M σ, exp_scoped 0 M -> M[σ] = M.
Proof.
  intros; eapply exp_scoped_sub_id; [ eassumption | lia ].
Qed.

(** ** Telescopes *)

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

Lemma ctx_lookup_length : forall Γ x A, Γ ∋ #x : A -> x < length Γ.
Proof.
  induction 1; cbn; lia.
Qed.

Lemma ctx_lookup_app_left : forall Γ Δ x A, Γ ∋ #x : A -> Γ ++ Δ ∋ #x : A.
Proof. induction 1; cbn; constructor; assumption. Qed.

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

(** ** Closed Entries *)

Definition entry_closed (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped 0 A /\ opt_scoped 0 B
  | ge_mod _ _ => True
  end.

(** Every definition a module resolves to is closed. *)
Definition mod_closed (Φ : gmod) : Prop :=
  forall ip E, gm_resolve Φ ip = Some E -> entry_closed E.

Definition units_closed (Θ : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> mod_closed (gu_mod U).

Definition stack_closed (Ξ : gstack) : Prop :=
  forall mp U, List.In (mp, U) Ξ -> mod_closed (gu_mod U).

Definition gctx_closed (Θ : gdeps) (Ξ : gstack) : Prop :=
  units_closed Θ /\ stack_closed Ξ.

Lemma gctx_closed_resolve : forall Θ Ξ p b pv A B,
    gctx_closed Θ Ξ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exp_scoped 0 A /\ opt_scoped 0 B.
Proof.
  intros * [HΘ HΞ] Hr.
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & U & ip & Hin & Hm) | (fp & U & Hl & Hm)].
  - exact (HΞ _ _ Hin _ _ Hm).
  - exact (HΘ _ _ Hl _ _ Hm).
Qed.

Lemma mod_closed_nil : mod_closed ⋄.
Proof. intros ? ? H; discriminate. Qed.

(** What an entry adds is closed if the entry is. *)
Definition entry_ok (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ _ => entry_closed E
  | ge_mod _ Φ => mod_closed Φ
  end.

Lemma mod_closed_ext : forall Φ x E, mod_closed Φ -> entry_ok E -> mod_closed (Φ ⊳ x ↦ E).
Proof.
  intros * HΦ HE ip E0 Hr; cbn in Hr.
  destruct ip as [| y ip']; [ discriminate |].
  destruct (String.eqb y x); [| eapply HΦ; eassumption ].
  destruct ip' as [| z ip''], E as [b pv A B | Δ' Φ']; try discriminate; cbn in HE.
  - injection Hr as <-; exact HE.
  - eapply HE; eassumption.
Qed.

(** ** Every Judgment is Well Scoped *)

#[local] Arguments gctx_closed : simpl never.
#[local] Arguments mod_closed : simpl never.

Definition ctx_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  ctx_scoped 0 Γ /\ gctx_closed Θ Ξ.

Theorem wf_scoped :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ctx_ok Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) M' /\
      exp_scoped (length Γ) A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) A /\ exp_scoped (length Γ) A') /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> entry_ok E) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> mod_closed Φ) /\
  (forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> mod_closed (gu_mod U)) /\
  (forall Θ d, wf_gdep Θ d -> units_closed Θ /\
      forall fp U, List.In (fp, U) d -> mod_closed (gu_mod U)) /\
  (forall Θ, wf_gdeps Θ -> units_closed Θ) /\
  (forall Θ Ξ, wf_gstack Θ Ξ -> gctx_closed Θ Ξ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> gctx_closed Θ Ξ).
Proof.
  apply wf_mut_ind_all; intros; unfold ctx_ok in *; cbn in *; destruct_all.
  all: repeat match goal with |- _ /\ _ => split end; try assumption;
    auto using exp_scoped_sub1, exp_scoped_sub2, exp_scoped_sub_succ, exp_scoped_shift, mod_closed_nil.
  all: try match goal with
    | |- exp_scoped (length ?Γ + 0) _ => rewrite Nat.add_0_r; assumption
    | H : ?Γ ∋ # ?x : ?A |- ?x < _ => apply ctx_lookup_length in H; assumption
    | H : ?Γ ∋ # ?x : ?A, HΓ : ctx_scoped 0 ?Γ |- exp_scoped _ ?A =>
        pose proof (ctx_scoped_lookup _ _ _ _ HΓ H) as Hs; rewrite Nat.add_0_r in Hs; exact Hs
    | H : gc_resolve _ _ _ = Some (ge_def _ _ _ _), Hc : gctx_closed _ _ |- exp_scoped _ _ =>
        destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc H) as [HA HB]; cbn in HB;
        eapply exp_scoped_mono; [| first [ exact HA | exact HB ] ]; lia
    end.
  all: try lia.
  - (* [rec], successor *)
    rewrite ?Nat.add_0_r in *.
    eapply exp_scoped_sub2; [ eassumption | eassumption | cbn; repeat split; assumption ].
  - (* an axiom, generalized *)
    apply ctx_pi_scoped; [ assumption | rewrite Nat.add_0_r; assumption ].
  - apply ctx_pi_scoped; [ assumption | rewrite Nat.add_0_r; assumption ].
  - apply ctx_fn_scoped; [ assumption | rewrite Nat.add_0_r; assumption ].
  - apply mod_closed_ext; assumption.
  - (* a unit filed at the level *)
    intros fq0 V0 [[= <- <-] | Hin]; eauto.
  - intros fq0 V0 Hl; discriminate.
  - (* a level filed on top: its own units, or the ones below *)
    intros fq0 V0 Hl; unfold gds_lookup in Hl; cbn in Hl.
    apply gd_lookup_app_inv in Hl as [Hl | Hl];
      [ match goal with H : forall _ _, List.In _ _ -> _ |- _ => eapply H, gd_lookup_in, Hl end
      | match goal with H : units_closed _ |- _ => eapply H, Hl end ].
  - split; [ assumption | intros ? ? [] ].
  - (* a frame *)
    match goal with H : gctx_closed _ _ |- _ => destruct H as [HΘ HΞ] end.
    split; [ assumption |].
    intros mq V [[= <- <-] | Hin]; eauto.
Qed.

(** ** Consequences *)

Corollary wf_gctx_closed : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> gctx_closed Θ Ξ.
Proof. intros * HΓ; destruct wf_scoped as [Hc _]; apply (Hc _ _ _ HΓ). Qed.

(** In a well-formed context, what a global resolves to has no free
    λ-variable. *)
Corollary wf_gc_resolve_closed : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exp_scoped 0 A /\ opt_scoped 0 B.
Proof.
  intros * HΓ Hr; eapply gctx_closed_resolve; [ eapply wf_gctx_closed | ]; eassumption.
Qed.

Corollary wf_gc_resolve_type_closed : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exp_scoped 0 A.
Proof. intros; eapply wf_gc_resolve_closed; eassumption. Qed.

Corollary wf_gc_resolve_body_closed : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A (Some M)) ->
    exp_scoped 0 M.
Proof. intros * HΓ Hr; apply (wf_gc_resolve_closed _ _ _ _ _ _ _ _ HΓ Hr). Qed.
