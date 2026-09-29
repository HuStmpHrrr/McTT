From Equations Require Import Equations.
From Stdlib Require Import List String Morphisms Relation_Definitions RelationClasses.

From Mctt.Core.Syntactic Require Export Syntax.

(** * The Semantic Domain

    An environment is the list of the values of the variables in scope, indexed
    by de Bruijn index; for [Θ ⍮ Ξ ⍮ Γ] those are [Γ ++ gs_tele Ξ].  The global
    context is not part of it: it does not change during NbE, so evaluation
    takes it as a separate argument. *)

Inductive domain : Set :=
| d_nat : domain
| d_pi : domain -> list domain -> exp -> domain
| d_univ : nat -> domain
| d_zero : domain
| d_succ : domain -> domain
| d_fn : list domain -> exp -> domain
| d_neut : domain -> domain_ne -> domain
with domain_ne : Set :=
(** Notice that the number x here is not a de Bruijn index but an absolute
    representation of names.  That is, this number does not change relative to the
    binding structure it currently exists in.
 *)
| d_var : forall (x : nat), domain_ne
| d_app : domain_ne -> domain_nf -> domain_ne
| d_natrec : list domain -> typ -> domain -> exp -> domain_ne -> domain_ne
(** An opaque definition or an axiom. *)
| d_glob : path -> domain_ne
with domain_nf : Set :=
| d_dom : domain -> domain -> domain_nf.

Notation env := (list domain).

Derive NoConfusion for domain domain_ne domain_nf.

(** The value of the variable [#x]. *)
Definition env_var (ρ : env) (x : nat) : option domain := List.nth_error ρ x.

Definition extend_env (ρ : env) (d : domain) : env := d :: ρ.
Arguments extend_env _ _ /.

Definition drop_env (ρ : env) : env := List.tl ρ.
Arguments drop_env _ /.

#[global] Bind Scope mctt_scope with domain.

(** ** Semantic Notations

    Values live in ordinary [constr] alongside the expressions, so the four
    spellings the two sorts would otherwise share — [ℕ], [zero], [succ], [Π]
    and the closure's [λ] — carry a superscript [ᵈ] here.  Everything that is
    specific to values ([↦], [↯], [𝕌@n], [⇑], [⇓], [⇑!], [#ᵈ n]) keeps the
    spelling of the paper. *)
Module Domain_Notations.
  Export Syntax_Notations.

  (** Declared before the value constructors so that level 1 is left
      associative, as [M[σ]] does in [Syntax_Notations]. *)
  Notation "ρ '↯'" := (drop_env ρ) (at level 1, left associativity) : mctt_scope.
  Notation "'𝕌' @ n" := (d_univ n) (at level 1, n at level 0, format "'𝕌' @ n") : mctt_scope.
  Notation "'#ᵈ' n" := (d_var n) (at level 1, n at level 0, format "'#ᵈ' n") : mctt_scope.
  Notation "'ℕᵈ'" := d_nat : mctt_scope.
  Notation "'zeroᵈ'" := d_zero : mctt_scope.
  Notation "'succᵈ' m" := (d_succ m) (at level 2, m at level 1) : mctt_scope.
  Notation "'λᵈ' ρ M" := (d_fn ρ M) (at level 2, ρ at level 1, M at level 9) : mctt_scope.
  Notation "'Πᵈ' a ρ B" := (d_pi a ρ B) (at level 2, a at level 1, ρ at level 0, B at level 9) : mctt_scope.
  Notation "'⇑' a m" := (d_neut a m) (at level 2, a at level 1, m at level 1) : mctt_scope.
  Notation "'⇓' a m" := (d_dom a m) (at level 2, a at level 1, m at level 1) : mctt_scope.
  Notation "'⇑!' a n" := (d_neut a (d_var n)) (at level 2, a at level 1, n at level 0) : mctt_scope.
  Notation "m '$ᵈ' n" := (d_app m n) (at level 10, left associativity, format "m  $ᵈ  n") : mctt_scope.
  Notation "'recᵈ' m 'under' ρ 'return' P | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec ρ P mz MS m) (at level 0, m at level 60, ρ at level 60, P at level 60, mz at level 60, MS at level 60) : mctt_scope.

  Notation "ρ ↦ m" := (extend_env ρ m) (at level 20, left associativity) : mctt_scope.
End Domain_Notations.

Import Domain_Notations.

(** The two projections of an extended environment. *)
Proposition drop_env_extend_env_cancel : forall ρ a,
    (ρ ↦ a)↯ = ρ.
Proof. reflexivity. Qed.

Proposition extend_env_zero_cancel : forall ρ a,
    env_var (ρ ↦ a) 0 = Some a.
Proof. reflexivity. Qed.

Proposition extend_env_succ : forall ρ a x,
    env_var (ρ ↦ a) (S x) = env_var ρ x.
Proof. reflexivity. Qed.
