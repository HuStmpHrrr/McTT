From Equations Require Import Equations.
From Stdlib Require Import Morphisms Relation_Definitions RelationClasses.

From Mctt.Core.Syntactic Require Export Syntax.

Reserved Notation "'env'".

Inductive domain : Set :=
| d_nat : domain
| d_pi : domain -> env -> exp -> domain
| d_univ : nat -> domain
| d_zero : domain
| d_succ : domain -> domain
| d_fn : env -> exp -> domain
| d_neut : domain -> domain_ne -> domain
with domain_ne : Set :=
(** Notice that the number x here is not a de Bruijn index but an absolute
    representation of names.  That is, this number does not change relative to the
    binding structure it currently exists in.
 *)
| d_var : forall (x : nat), domain_ne
| d_app : domain_ne -> domain_nf -> domain_ne
| d_natrec : env -> typ -> domain -> exp -> domain_ne -> domain_ne
with domain_nf : Set :=
| d_dom : domain -> domain -> domain_nf
where "'env'" := (nat -> domain).

Derive NoConfusion for domain domain_ne domain_nf.

Definition empty_env : env := fun x => d_zero.
Arguments empty_env _ /.

Definition extend_env (ρ : env) (d : domain) : env :=
  fun n =>
    match n with
    | 0 => d
    | S n' => ρ n'
    end.
Arguments extend_env _ _ _ /.
Transparent extend_env.

Definition drop_env (ρ : env) : env := fun n => ρ (S n).
Arguments drop_env _ _ /.
Transparent drop_env.

(** ** Equality of Environments

    Environments are functions, and this development is axiom-free, so
    "the same environment" means pointwise equality — exactly as [wk_eq] and
    [sb_eq] do for weakenings and substitutions in [Syntax.v].  This matters as
    soon as substitutions are evaluated: their evaluation is defined pointwise,
    so determinism can only deliver [env_eq], never [eq].

    Note that [env_eq] is *not* a congruence for [eval_exp]: a closure
    [λ ρ M] carries its environment, so [env_eq ρ ρ'] makes [λ ρ M] and
    [λ ρ' M] distinct values.  Relating those is the job of the PER model, not
    of [eq].
 *)
Definition env_eq : relation env := pointwise_relation nat eq.

#[export]
Instance env_eq_Equivalence : Equivalence env_eq := _.

#[export]
Instance extend_env_Proper : Proper (env_eq ==> eq ==> env_eq) extend_env.
Proof.
  intros ρ ρ' Hρ d d' <- [| n]; [ reflexivity | apply Hρ ].
Qed.

#[export]
Instance drop_env_Proper : Proper (env_eq ==> env_eq) drop_env.
Proof.
  intros ρ ρ' Hρ n. apply Hρ.
Qed.

#[global] Declare Custom Entry domain.
#[global] Bind Scope mctt_scope with domain.

Module Domain_Notations.
  Export Syntax_Notations.

  Notation "'d{{{' x '}}}'" := x (at level 0, x custom domain at level 99, format "'d{{{'  x  '}}}'") : mctt_scope.
  (** Declared before the value constructors so that level 1 is left
      associative, as [e[s]] does for the [exp] entry. *)
  Notation "ρ '↯'" := (drop_env ρ) (in custom domain at level 1, ρ custom domain, left associativity) : mctt_scope.
  Notation "( x )" := x (in custom domain at level 0, x custom domain at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom domain at level 1, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom domain at level 0, x ident) : mctt_scope.
  Notation "'λ' ρ M" := (d_fn ρ M) (in custom domain at level 2, ρ custom domain at level 30, M custom exp at level 30) : mctt_scope.
  Notation "f x .. y" := (d_app .. (d_app f x) .. y) (in custom domain at level 40, f custom domain, x custom domain at next level, y custom domain at next level) : mctt_scope.
  Notation "'ℕ'" := d_nat (in custom domain) : mctt_scope.
  Notation "'𝕌' @ n" := (d_univ n) (in custom domain at level 2, n constr at level 0) : mctt_scope.
  Notation "'Π' a ρ B" := (d_pi a ρ B) (in custom domain at level 2, a custom domain at level 30, ρ custom domain at level 0, B custom exp at level 30) : mctt_scope.
  Notation "'zero'" := d_zero (in custom domain at level 0) : mctt_scope.
  (** At the level just below [ρ ↦ m], which is what [↦] admits as its right
      operand, so that [ρ ↦ succ m] needs no parentheses. *)
  Notation "'succ' m" := (d_succ m) (in custom domain at level 19, m custom domain at level 2) : mctt_scope.
  Notation "'rec' m 'under' ρ 'return' P | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec ρ P mz MS m) (in custom domain at level 0, P custom exp at level 60, mz custom domain at level 60, MS custom exp at level 60, ρ custom domain at level 60, m custom domain at level 60) : mctt_scope.
  Notation "'!' n" := (d_var n) (in custom domain at level 2, n constr at level 0) : mctt_scope.
  Notation "'⇑' a m" := (d_neut a m) (in custom domain at level 2, a custom domain at level 30, m custom domain at level 30) : mctt_scope.
  Notation "'⇓' a m" := (d_dom a m) (in custom domain at level 2, a custom domain at level 30, m custom domain at level 30) : mctt_scope.
  Notation "'⇑!' a n" := (d_neut a (d_var n)) (in custom domain at level 2, a custom domain at level 30, n constr at level 0) : mctt_scope.

  Notation "ρ ↦ m" := (extend_env ρ m) (in custom domain at level 20, left associativity) : mctt_scope.
End Domain_Notations.

Import Domain_Notations.

(** The two projections of an extended environment.  Both hold by conversion,
    but they are still worth stating: the tactics that drive the PER model
    ([functional_eval_rewrite_clear], [handle_per_univ_elem_irrel]) match
    hypotheses against goals *syntactically*, so a goal phrased over
    [(ρ ↦ a) ↯] or [(ρ ↦ a) 0] has to be rewritten before it can meet a
    hypothesis phrased over [ρ] or [a]. *)
Proposition drop_env_extend_env_cancel : forall ρ a,
    d{{{ (ρ ↦ a) ↯ }}} = ρ.
Proof.
  reflexivity.
Qed.

Proposition extend_env_zero_cancel : forall ρ a,
    d{{{ ρ ↦ a }}} 0 = a.
Proof.
  reflexivity.
Qed.
