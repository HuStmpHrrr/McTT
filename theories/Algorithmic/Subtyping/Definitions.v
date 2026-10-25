From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Semantic Require Export NbE Fixed.
Import Syntax_Notations Fixed_Notations.

Reserved Notation "Γ ⊢a A ⊆ A'" (at level 70, A at level 69, A' at level 69).
Reserved Notation "⊢anf A ⊆ A'" (at level 70, A at level 69, A' at level 69).

(** The normal forms whose subtyping is not syntactic equality: the
    universes, the types of levels and [Π]. *)
Definition not_univ_pi (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_univ _ _ | nf_level _ | nf_pi _ _ => False
  | _ => True
  end.

(** Subtyping of normal forms is purely syntactic: it neither evaluates nor
    refers to a judgment, so it is defined outside the fixed global context. *)
Inductive alg_subtyping_nf : nf -> nf -> Prop :=
| alg_subtyping_nf_refl_case : forall A A',
    not_univ_pi A ->
    A = A' ->
    ⊢anf A ⊆ A'
| alg_subtyping_nf_univ : forall i j,
    i <= j ->
    ⊢anf Typeωⁿ@i ⊆ Typeωⁿ@j
(** A small universe below one at a larger level: the decidable order on
    canonical levels ([Core.Syntactic.Levels.Levels.lvl_le]), which is the order on
    every assignment to the atoms, never the order on realisers. *)
| alg_subtyping_nf_suniv : forall c xs d ys,
    lvl_le (c, xs) (d, ys) ->
    ⊢anf univⁿ c xs ⊆ univⁿ d ys
(** A small universe below every large one. *)
| alg_subtyping_nf_small_large : forall c xs i,
    ⊢anf univⁿ c xs ⊆ Typeωⁿ@i
(** The types of levels, by the order on sorts. *)
| alg_subtyping_nf_level : forall m n,
    m <= n ->
    ⊢anf Levelⁿ@m ⊆ Levelⁿ@n
| alg_subtyping_nf_pi : forall A B A' B',
    A = A' ->
    ⊢anf B ⊆ B' ->
    ⊢anf Πⁿ A B ⊆ Πⁿ A' B'
where "⊢anf A ⊆ A'" := (alg_subtyping_nf A A') : type_scope.

#[export]
Hint Constructors alg_subtyping_nf : mctt.

Section Fixed_GCtx.
  Context {GC : GCtx}.

#[warnings="-cannot-define-projection"]
Record alg_subtyping (Γ : ctx) (A B : typ) : Prop := alg_subtyp_run
  { A' : nf
  ; B' : nf
  ; alg_subtyping_nbe : nbe_ty_f Γ A A'
  ; alg_subtyping_nbe' : nbe_ty_f Γ B B'
  ; alg_subtyping_sub : ⊢anf A' ⊆ B' }.

Notation "Γ ⊢a A ⊆ B" := (alg_subtyping Γ A B) : type_scope.

Hint Constructors alg_subtyping : mctt.

End Fixed_GCtx.

Notation "Γ ⊢a A ⊆ B" := (alg_subtyping Γ A B) : type_scope.

#[export]
Hint Constructors alg_subtyping : mctt.
