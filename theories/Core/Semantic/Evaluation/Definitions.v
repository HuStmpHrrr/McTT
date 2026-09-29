From Stdlib Require Import List Morphisms String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution GlobalCtx.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'⟦' M '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" (at level 70, σ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρσ at level 69).

Generalizable All Variables.

(** * Evaluation of Expressions

    Three mutually defined relations: evaluation proper, its
    [ℕ]-eliminator case, and semantic application.  All three are relative to
    the global context [Θ ⍮ Ξ], which does not change during NbE.  A global is
    resolved there: a transparent definition unfolds to its body — generalized
    and opened into this context by resolution, hence closed, and evaluated in
    the empty environment — and anything else is a neutral at its type. *)
Inductive eval_exp (Θ : gdeps) (Ξ : gstack) : exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( ⟦ Type@i ⟧ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌@i )
| eval_exp_var :
  `( env_var ρ x = Some m ->
     ⟦ #x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m )
| eval_exp_nat :
  `( ⟦ ℕ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ℕᵈ )
| eval_exp_zero :
  `( ⟦ zero ⟧ Θ ⍮ Ξ ⍮ ρ ↘ zeroᵈ )
| eval_exp_succ :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ succᵈ m )
| eval_exp_natrec :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
| eval_exp_pi :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ Π A B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ a ρ B )
| eval_exp_fn :
  `( ⟦ λ A M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ λᵈ ρ M )
| eval_exp_app :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $| m & n | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** δ: a transparent definition is its body. *)
| eval_exp_glob_delta :
  `( gc_resolve Θ Ξ p = Some (Δ, ge_def true A (Some M)) ->
     ⟦ ctx_fn Δ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ m ->
     ⟦ a_glob p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m )
(** An opaque definition or an axiom stays a neutral at its type. *)
| eval_exp_glob_neut :
  `( gc_resolve Θ Ξ p = Some (Δ, ge_def b A B) ->
     b = false \/ B = None ->
     ⟦ ctx_pi Δ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a ->
     ⟦ a_glob p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_glob p) )
where "'⟦' e '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_exp Θ Ξ e ρ r)
with eval_natrec (Θ : gdeps) (Ξ : gstack) : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦rec zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz )
| eval_natrec_succ :
  `( ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ MS ⟧ Θ ⍮ Ξ ⍮ ρ ↦ b ↦ r ↘ ms ->
     ⟦rec succᵈ b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ms )
| eval_natrec_neut :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦rec ⇑ b m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a recᵈ m under ρ return A | zero -> mz | succ -> MS end )
where "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_natrec Θ Ξ A MZ MS m ρ r)
with eval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ m ->
     $| λᵈ ρ M & n | Θ ⍮ Ξ ↘ m )
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
where "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" := (eval_app Θ Ξ m n r)
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_natrec_mut_ind,
  eval_app_mut_ind.

#[export]
Hint Constructors eval_exp eval_natrec eval_app : mctt.

(** * Evaluation of Substitutions

    Pointwise on the variables the target environment has: each of its values is
    what the substitution computes from [ρ].  The number of variables is the
    context's business, which [per_ctx] fixes. *)
Definition eval_sub (Θ : gdeps) (Ξ : gstack) (σ : sub) (ρ ρσ : env) : Prop :=
  forall x m, env_var ρσ x = Some m -> ⟦ σ x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m.
Arguments eval_sub : simpl never.

Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" := (eval_sub Θ Ξ σ ρ ρσ) : mctt_scope.

Lemma eval_sub_id : forall Θ Ξ ρ, ⟦ Id ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ.
Proof. intros * x m H; constructor; assumption. Qed.

Lemma eval_sub_shift : forall Θ Ξ ρ, ⟦ Wk ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ↯.
Proof.
  intros Θ Ξ [| d ρ] x m H; cbn in *; [ destruct x; discriminate |].
  constructor; assumption.
Qed.

Lemma eval_sub_extend : forall Θ Ξ σ ρ ρσ M m,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ σ,,M ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H HM [| x] n Hx; cbn in Hx; [ injection Hx as <-; assumption | apply H, Hx ].
Qed.

Corollary eval_sub_single : forall Θ Ξ ρ M m,
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ Id,,M ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ m.
Proof.
  intros; apply eval_sub_extend; [ apply eval_sub_id | assumption ].
Qed.

#[export]
Hint Resolve eval_sub_id eval_sub_shift eval_sub_extend eval_sub_single : mctt.
