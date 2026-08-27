(** * Contexts

    The two rules of [wf_ctx], plus the two context-subtyping facts that
    [Consequences] needs.  [valid_ctx_empty] is gone: [⊨ Γ] is now the inductive
    [sem_ctx], so the empty case *is* a constructor
    ([sem_ctx_nil]).  What remains is the extension step, and it is the one place
    in the development that has to *build* a context PER rather than take one
    apart.

    Building one means choosing the head relation, and the choice — the
    impredicative [per_head], "whatever every [per_univ_elem] relating the values
    of [A] and [A'] relates" — is made once at the PER layer, by
    [per_ctx_env_extend].  All that is left here is to feed it the premise it
    wants, which is exactly what [rel_exp_of_typ_inversion_simple] delivers. *)

From Stdlib Require Import Morphisms_Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import LogicalRelation UniverseCases.
Import Domain_Notations.

Lemma rel_ctx_extend : forall {Γ Γ' A A' i},
    {{ ⊨ Γ ≈ Γ' }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ ⊨ Γ, A ≈ Γ', A' }}.
Proof.
  intros * [env_relΓΓ' HΓΓ'] H.
  pose proof (rel_exp_of_typ_inversion_simple H) as [env_relΓ [HΓ HA]].
  (** Both witnesses have [Γ] on the left, so they agree up to [<~>].  Naming the
      equivalence rather than calling [handle_per_ctx_env_irrel] keeps
      [env_relΓΓ'] — the only one that witnesses the *tail* of the goal — in
      place. *)
  assert (Hirrel : env_relΓΓ' <~> env_relΓ)
    by (eapply per_ctx_env_right_irrel; [exact HΓΓ' | exact HΓ]).
  eexists.
  eapply per_ctx_env_extend; [ eassumption |].
  intros ρ ρ' Hρ%Hirrel.
  now apply HA.
Qed.

Lemma rel_ctx_extend' : forall {Γ A i},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ A : Type@i }} ->
    {{ ⊨ Γ, A }}.
Proof.
  intros * HΓ HA.
  pose proof (rel_ctx_extend (sem_ctx_per_ctx HΓ) HA) as [env_relΓA HΓA].
  econstructor; eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_extend rel_ctx_extend' : mctt.

Lemma rel_ctx_sub_empty :
  {{ SubE ⋅ <: ⋅ }}.
Proof. mauto. Qed.

Lemma rel_ctx_sub_extend : forall {Γ Δ i A A'},
  {{ SubE Γ <: Δ }} ->
  {{ ⊨ Γ }} ->
  {{ ⊨ Δ }} ->
  {{ Γ ⊨ A : Type@i }} ->
  {{ Δ ⊨ A' : Type@i }} ->
  {{ Γ ⊨ A ⊆ A' }} ->
  {{ SubE Γ , A <: Δ , A' }}.
Proof.
  intros * Hsub HΓ HΔ HA HA' Hsubtyp.
  pose proof (rel_ctx_extend' HΓ HA) as HΓA%sem_ctx_per_ctx_env.
  pose proof (rel_ctx_extend' HΔ HA') as HΔA'%sem_ctx_per_ctx_env.
  destruct HΓA as [env_relΓA HΓA], HΔA' as [env_relΔA' HΔA'].
  pose proof (subtyp_under_ctx_simple Hsubtyp) as [env_relΓ [HΓ' [j Hsub2]]].
  econstructor; try eassumption.
  intros ρ ρ' a a' Hρ Ha Ha'.
  destruct (Hsub2 _ _ Hρ) as [a2 [a2' [Ha2 [Ha2' Hsubaa']]]].
  functional_eval_rewrite_clear.
  eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_sub_empty rel_ctx_sub_extend : mctt.
