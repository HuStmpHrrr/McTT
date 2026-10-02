From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export System CtxSub.
From Mctt.Core.Semantic Require Export Domain Evaluation Readback NbE.
Import Domain_Notations.

(** * The Short Forms, for a Fixed Global Context

    The semantic development fixes the global context once per section, with
    [Context `{GCtx}].  These notations write judgments, evaluation and
    readback without [Θ ⍮ Ξ], relative to that fixed context.  Where two
    global contexts meet, the long forms are used. *)

(** The short and long forms do not parse together ([⊢ Γ] against
    [⊢ Θ ⍮ Ξ ⍮ Γ]), so the short forms are a separate module.  Files that
    import it refer to a judgment at another global context by its constant. *)
Module Fixed_Notations.

(** ** Judgments *)
  
  Notation "⊢ Γ" := (wf_ctx gc_deps gc_stack Γ) (at level 70, Γ at level 69) : type_scope.
  Notation "Γ ⊢ M : A" := (wf_exp gc_deps gc_stack Γ A M) (at level 70, M at level 69) : type_scope.
  Notation "Γ ⊢ M ≈ M' : A" := (wf_exp_eq gc_deps gc_stack Γ A M M')
    (at level 70, M at level 69, M' at level 69, A at level 69) : type_scope.
  Notation "Γ ⊢ A ⊆ A'" := (wf_subtyp gc_deps gc_stack Γ A A') (at level 70, A at level 69, A' at level 69) : type_scope.
  Notation "Γ ⊢w φ : Δ" := (wf_wk gc_deps gc_stack Γ Δ φ) (at level 70, φ constr at level 60, Δ at level 69) : type_scope.
  Notation "Γ ⊢s σ : Δ" := (wf_sub gc_deps gc_stack Γ Δ σ) (at level 70, σ at level 69, Δ at level 69) : type_scope.
  Notation "Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq gc_deps gc_stack Γ Δ σ σ')
    (at level 70, σ at level 69, σ' at level 69, Δ at level 69) : type_scope.
  (** Not [⊢ Δ ⊆ Γ], which would not parse alongside [⊢ Γ] and the long forms. *)
  Notation "Δ ⊆ Γ" := (ctx_sub gc_deps gc_stack Δ Γ) (at level 70, Γ at level 69) : type_scope.
  
  (** ** Evaluation and Readback *)
  
  Notation "'⟦' M '⟧' ρ '↘' r" := (eval_exp gc_deps gc_stack M ρ r)
    (at level 70, M at level 69, ρ at level 69, r at level 69).
  Notation "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' ρ '↘' r" :=
    (eval_natrec gc_deps gc_stack A MZ MS m ρ r)
    (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, ρ at level 69, r at level 69).
  Notation "'$|' m '&' n '|↘' r" := (eval_app gc_deps gc_stack m n r)
    (at level 70, m at level 69, n at level 69, r at level 69).
  Notation "'⟦' σ '⟧s' ρ '↘' ρσ" := (eval_sub gc_deps gc_stack σ ρ ρσ)
    (at level 70, σ at level 69, ρ at level 69, ρσ at level 69) : mctt_scope.
  Notation "'Rnf' m 'in' s ↘ M" := (read_nf gc_deps gc_stack s m M) (at level 70, m at level 69, s at level 69, M at level 69).
  Notation "'Rne' m 'in' s ↘ M" := (read_ne gc_deps gc_stack s m M) (at level 70, m at level 69, s at level 69, M at level 69).
  Notation "'Rtyp' m 'in' s ↘ M" := (read_typ gc_deps gc_stack s m M) (at level 70, m at level 69, s at level 69, M at level 69).
  
  Abbreviation initial_env_f := (initial_env gc_deps gc_stack).
  Abbreviation nbe_f := (nbe gc_deps gc_stack).
  Abbreviation nbe_ty_f := (nbe_ty gc_deps gc_stack).

End Fixed_Notations.
