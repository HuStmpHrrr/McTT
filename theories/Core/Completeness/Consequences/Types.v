(** * Consequences of Completeness: types are rigid

    Distinct type constructors are never judgmentally equal, and [Type@i ≈ Type@j]
    forces [i = j].  Each proof reads the judgment at the initial environment and
    inverts the resulting [per_univ]; only the variable-against-variable case needs
    work, since there the values are neutrals whose levels must be turned back
    into indices. *)

From Stdlib Require Import Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Completeness.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [x] is bound by an assumption of [Γ], not by a definition. *)
Definition ctx_ass (Γ : ctx) (x : nat) : Prop :=
  exists A, List.nth_error Γ x = Some (ce_ass A).

(** A variable bound by an assumption evaluates, in the initial environment of
    its context, to the neutral at its own level. *)
Lemma eval_var_at_initial_env : forall {Γ x i ρ a},
    ctx_ass Γ x ->
    initial_env_f Γ ρ ->
    ⟦ #x ⟧ ρ ↘ a ->
    Γ ⊢ #x : Type@i ->
    x < length Γ /\ exists b, a = ⇑! b (length Γ - x - 1).
Proof.
  intros * [A Hlookup] Hρ Hev Hx.
  pose proof (initial_env_spec _ _ _ _ Hρ Hlookup) as [b Heq].
  split.
  - apply List.nth_error_Some; congruence.
  - exists b.
    eapply functional_eval_exp; [ exact Hev | apply eval_exp_var_eq; exact Heq ].
Qed.

Lemma exp_eq_typ_implies_eq_level : forall {Γ i j k},
    Γ ⊢ Type@i ≈ Type@j : Type@k ->
    i = j.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = 𝕌@i) as ->
      by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ]).
  assert (a' = 𝕌@j) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  invert_per_univ_elem HR; congruence.
Qed.

Hint Resolve exp_eq_typ_implies_eq_level : mctt.

Inductive is_typ_constr : typ -> Prop :=
| typ_is_typ_constr : forall i, is_typ_constr Type@i
| nat_is_typ_constr : is_typ_constr ℕ
| True_is_typ_constr : is_typ_constr ⊤
| False_is_typ_constr : is_typ_constr ⊥
| pi_is_typ_constr : forall A B, is_typ_constr Π A B
| var_is_typ_constr : forall x, is_typ_constr #x
.
Hint Constructors is_typ_constr : mctt.

(** A type is rigid in [Γ] when it is a type constructor or a variable bound
    by an assumption.  A variable bound by a definition is not rigid, since it
    is equal to its body. *)
Inductive rigid_typ (Γ : ctx) : typ -> Prop :=
| typ_is_rigid : forall i, rigid_typ Γ Type@i
| nat_is_rigid : rigid_typ Γ ℕ
| True_is_rigid : rigid_typ Γ ⊤
| False_is_rigid : rigid_typ Γ ⊥
| pi_is_rigid : forall A B, rigid_typ Γ (Π A B)
| var_is_rigid : forall x, ctx_ass Γ x -> rigid_typ Γ #x
.
Hint Constructors rigid_typ : mctt.

(** A well-formed type constructor is rigid in a context whose variables are
    all bound by assumptions. *)
Lemma rigid_typ_of_is_typ_constr : forall Γ A i,
    (forall x B, Γ ∋ #x : B -> ctx_ass Γ x) ->
    is_typ_constr A ->
    Γ ⊢ A : Type@i ->
    rigid_typ Γ A.
Proof.
  intros * HΓ HA HAi.
  destruct HA; mauto 2.
  destruct (wf_vlookup_inversion HAi) as [B [Hlookup _]].
  constructor; eapply HΓ; eassumption.
Qed.

(** The context of [consistency]. *)
Lemma ctx_ass_of_lookup_typ : forall i x B,
    ⋅ ▹ Type@i ∋ #x : B ->
    ctx_ass (⋅ ▹ Type@i) x.
Proof.
  intros * H.
  dependent destruction H; [ eexists; reflexivity |].
  inversion H.
Qed.

Theorem is_typ_constr_and_exp_eq_var_implies_eq_var : forall Γ A x i,
    rigid_typ Γ A ->
    ctx_ass Γ x ->
    Γ ⊢ A ≈ #x : Type@i ->
    A = #x.
Proof.
  intros * Histyp Hx H.
  assert (Γ ⊢ A : Type@i) by mauto 2.
  assert (Γ ⊢ #x : Type@i) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_var_at_initial_env Hx Hρ Ha' ltac:(eassumption)) as [Hxlt [b ->]].
  (** Only the variable case survives: [⇑! b _] has no other constructor to be
      related to. *)
  destruct Histyp;
    [ assert (a = 𝕌@i0) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = ℕᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
    invert_per_univ_elem HR.
  - (** [Π A B] evaluates to a [Π]-value once its domain does. *)
    match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
  - (** Two neutral variables related in [per_bot]: read both back at
        [length Γ] and compare the indices they produce. *)
    f_equal.
    enough (length Γ - x0 - 1 = length Γ - x - 1) by lia.
    match_by_head1 per_bot ltac:(fun H => destruct (H (length Γ)) as [? []]).
    match_by_head read_ne ltac:(fun H => directed dependent destruction H).
    lia.
Qed.

Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mctt.

Theorem is_typ_constr_and_exp_eq_typ_implies_eq_typ : forall Γ A i j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Type@i : Type@j ->
    A = Type@i.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Type@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = 𝕌@i) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  destruct Histyp;
    [ assert (a = 𝕌@i0) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = ℕᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
    invert_per_univ_elem HR.
  - congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.

Theorem is_typ_constr_and_exp_eq_nat_implies_eq_nat : forall Γ A j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ ℕ : Type@j ->
    A = ℕ.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Type@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = ℕᵈ) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_nat ]).
  destruct Histyp;
    [ assert (a = 𝕌@i) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | reflexivity
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end ];
    invert_per_univ_elem HR.
  match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve exp_eq_typ_implies_eq_level : mctt.
#[export]
Hint Constructors is_typ_constr rigid_typ : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mctt.
