(** * The Extracted Checker Infers the Reference Checker's Types

    The extracted checker ([Extraction.TypeCheck]) infers the type of an
    application along a value-based spine ([Extraction.AppSpine]); the
    reference checker ([Reference.TypeCheck]) normalizes [B[Id,,N]] at each
    argument, as the rule [alg_type_infer_app] reads.  Both decide the
    algorithmic judgment, and it infers one type
    ([functional_alg_type_infer]), so they infer the same types.

    The agreement rests on the algorithmic soundness the extracted
    checker's postconditions rest on: its spine relates values through
    [soundness_ty'] / [soundness], as [alg_type_infer_sound] does. *)
From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Extraction Require Import Lookup.
From Mctt.Extraction Require TypeCheck.
From Mctt.Reference Require TypeCheck.
From Mctt.Extraction Require Import TypeCheckBase.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

(** The type an inference gives, if any *)
Definition inferred_type {G M} (r : { A : nf | G ⊢a M ⟹ A } + { forall A, ~ G ⊢a M ⟹ A }) : option nf :=
  match r with
  | inleft (exist _ A _) => Some A
  | inright _ => None
  end.

(** Two decisions of the inference of one term give one type. *)
Lemma inferred_type_unique : forall G M (HG : ⊢ G) r1 r2, @inferred_type G M r1 = @inferred_type G M r2.
Proof.
  intros * HG [[A1 H1] | N1] [[A2 H2] | N2]; cbn.
  - f_equal; eapply functional_alg_type_infer; [ exact (ctx_wf_gctx _ _ _ HG) | exact H1 | exact H2 ].
  - exfalso; exact (N2 _ H1).
  - exfalso; exact (N1 _ H2).
  - reflexivity.
Qed.

(** Whether a decision accepts *)
Definition decided {Q : Prop} (d : { Q } + { ~ Q }) : bool := if d then true else false.

(** Two decisions of one proposition agree. *)
Lemma decided_unique : forall (Q : Prop) (d1 d2 : { Q } + { ~ Q }), decided d1 = decided d2.
Proof. intros Q [H1 | N1] [H2 | N2]; cbn; first [ reflexivity | contradiction ]. Qed.

(** The elaboration a decision of a body gives, if any *)
Definition elaborated_body {G Φ} (r : { Φx | G ⊢aᵇ Φ ⇝ Φx /\ ⊢ body_ctx Φx ++ G } + { forall Φx, ~ G ⊢aᵇ Φ ⇝ Φx }) :
    option gmod :=
  match r with
  | inleft (exist _ Φx _) => Some Φx
  | inright _ => None
  end.

(** Two decisions of one body give one elaboration. *)
Lemma elaborated_body_unique : forall G Φ r1 r2, @elaborated_body G Φ r1 = @elaborated_body G Φ r2.
Proof.
  intros G Φ [[X1 [H1 HG]] | N1] [[X2 [H2 HG2]] | N2]; cbn.
  - f_equal; eapply alg_body_functional; [ exact (ctx_wf_gctx _ _ _ HG) | exact H1 | exact H2 ].
  - exfalso; exact (N2 _ H1).
  - exfalso; exact (N1 _ H2).
  - reflexivity.
Qed.

Section type_check.
  (** The decision of [levels_abstractable], given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Δ ++ G -> gc_deps ⍮ gc_stack ⍮ Δ ++ G ⊢ᵐ E ≈ E ->
      { levels_abstractable gc_deps gc_stack G Δ E } + { ~ levels_abstractable gc_deps gc_stack G Δ E }.

  (** The extracted checker infers the type the reference checker infers,
      at each environment and order.  Rests on [soundness_ty'] /
      [soundness], through the extracted checker. *)
  Theorem type_infer_in_agrees_with_reference : forall G (HG : ⊢ G) P M H,
      inferred_type (Extraction.TypeCheck.type_infer_in F levels_abstractable_dec G HG P M H) =
      inferred_type (Reference.TypeCheck.type_infer_in F levels_abstractable_dec G HG P M H).
  Proof. intros; apply inferred_type_unique; exact HG. Qed.

  (** The two checkers accept the same terms, parameters, units, module
      expressions, bodies (with the same elaborations) and extensions:
      every judgment the mutual block decides goes through its
      applications.  Rests on [soundness_ty'] / [soundness], through the
      extracted checker. *)
  Theorem type_check_in_agrees_with_reference : forall G A (HA : G ⊢ᵗ A) P M H,
      decided (Extraction.TypeCheck.type_check_in F levels_abstractable_dec G A HA P M H) =
      decided (Reference.TypeCheck.type_check_in F levels_abstractable_dec G A HA P M H).
  Proof. intros; apply decided_unique. Qed.

  Theorem params_check_agrees_with_reference : forall G (HG : ⊢ G) Δ H,
      decided (Extraction.TypeCheck.params_check F levels_abstractable_dec G HG Δ H) =
      decided (Reference.TypeCheck.params_check F levels_abstractable_dec G HG Δ H).
  Proof. intros; apply decided_unique. Qed.

  Theorem unit_check_agrees_with_reference : forall G (HG : ⊢ G) U H,
      decided (Extraction.TypeCheck.unit_check F levels_abstractable_dec G HG U H) =
      decided (Reference.TypeCheck.unit_check F levels_abstractable_dec G HG U H).
  Proof. intros; apply decided_unique. Qed.

  Theorem modexp_check_agrees_with_reference : forall G (HG : ⊢ G) M H,
      decided (Extraction.TypeCheck.modexp_check F levels_abstractable_dec G HG M H) =
      decided (Reference.TypeCheck.modexp_check F levels_abstractable_dec G HG M H).
  Proof. intros; apply decided_unique. Qed.

  Theorem body_check_agrees_with_reference : forall G (HG : ⊢ G) Φ H,
      elaborated_body (Extraction.TypeCheck.body_check F levels_abstractable_dec G HG Φ H) =
      elaborated_body (Reference.TypeCheck.body_check F levels_abstractable_dec G HG Φ H).
  Proof. intros; apply elaborated_body_unique. Qed.

  Theorem ext_check_agrees_with_reference : forall G (HG : ⊢ G) Ψ H,
      decided (Extraction.TypeCheck.ext_check F levels_abstractable_dec G HG Ψ H) =
      decided (Reference.TypeCheck.ext_check F levels_abstractable_dec G HG Ψ H).
  Proof. intros; apply decided_unique. Qed.
End type_check.
End Fixed_GCtx.
