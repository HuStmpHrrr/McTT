(** * The Readback of a Kept Proof Is Typed

    A proof is never evaluated: it is kept as the term it was written as,
    together with the environment it was met in ([⋆ᵈ⟨N, ρ⟩]), and reads
    back as [N] copied under local definitions binding the positions of
    [ρ] it reads ([read_proof_kept]).  Nothing in the gluing model types
    that readback: the gluing is closed under the PERs, which relate a
    kept proof to any other proof, so no clause of it can speak of the
    value's own readback.  For example, with
    [Γ = (A : Type@0) (P : Prop) (f : P → A) (h : P)], the real value of
    [f h] and the value [f ⋆ᵈ⟨𝕃@0, nil⟩] are related by [per_bot] — their
    readbacks differ only under [nf_proof], which [nf_eq_upto_proofs]
    ignores — and the readback of the second, [f 𝕃@0], is not typed.

    So the readback of a kept proof is typed under a hypothesis on its
    environment instead, stated here and proved for the environments the
    model builds: the definitions the readback of [ρ] produces are a
    well-formed context extension, and the substitution they ζ-reduce to
    is typed ([env_lets_typed]).  The syntactic work is
    [lets_exp_of_sub]. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Fixed NbE.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System Require Import LetPeeling.
From Mctt.Core.Soundness.Weakening Require Import Definitions.
Import Domain_Notations Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The definitions the readback of the first [k] positions of [ρ]
    produces number [k]: one per position. *)
Lemma read_lets_length : forall k ρ s bs, Rlets ρ at k in gc_deps ⍮ gc_stack ⍮ s ↘ bs ->
    List.length bs = k.
Proof.
  intros k; induction k as [| k IH]; intros * H; inversion H; subst; cbn [List.length]; [ reflexivity |].
  f_equal; eapply IH; eassumption.
Qed.

(** [ρ] stands for the context [Γ] over [Γ0]: at every Kripke weakening of
    [Γ0], the definitions the readback of [ρ]'s first [List.length Γ]
    positions produces bind a well-formed extension whose first entries
    are those of [Γ], and ζ-reduce to a substitution of [Γ].  The two
    conjuncts are the premises [lets_exp_of_sub] asks of a chain of
    definitions, at the substitution [Id] of the bound positions. *)
Definition env_lets_typed (Γ0 Γ : ctx) (ρ : env) : Prop :=
  forall Δ φ bs, Δ ⊢ᵏ φ : Γ0 ->
    Rlets ρ at (List.length Γ) in gc_deps ⍮ gc_stack ⍮ (List.length Δ) ↘ bs ->
    gc_deps ⍮ gc_stack ⍮ ctx_lets Δ bs ⊢ˢ Id : Γ /\
    gc_deps ⍮ gc_stack ⍮ Δ ⊢ˢ lets_sub bs : Γ.

End Fixed_GCtx.
