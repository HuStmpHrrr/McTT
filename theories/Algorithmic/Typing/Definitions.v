From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Subtyping Require Export Definitions.
From Mctt.Core Require Import Base.
Import Domain_Notations Fixed_Notations.

Reserved Notation "Γ '⊢a' M ⟹ A" (at level 70, M at level 69, A at level 69).
Reserved Notation "Γ '⊢a' M ⟸ A" (at level 70, M at level 69, A at level 69).

Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Inductive alg_type_check : ctx -> typ -> exp -> Prop :=
| atc_ati :
  `( Γ ⊢a M ⟹ A ->
     Γ ⊢a A ⊆ B ->
     Γ ⊢a M ⟸ B )
where "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) : type_scope
with alg_type_infer : ctx -> nf -> exp -> Prop :=
| ati_typ :
  `( Γ ⊢a Type@i ⟹ Typeⁿ@(S i) )
| ati_nat :
  `( Γ ⊢a ℕ ⟹ Typeⁿ@0 )
| ati_zero :
  `( Γ ⊢a zero ⟹ ℕⁿ )
| ati_succ :
  `( Γ ⊢a M ⟸ ℕ ->
     Γ ⊢a succ M ⟹ ℕⁿ )
| ati_natrec :
  `( Γ ▹ ℕ ⊢a A ⟹ Typeⁿ@i ->
     Γ ⊢a MZ ⟸ A[Id,,zero] ->
     Γ ▹ ℕ ▹ A ⊢a MS ⟸ A[Wk ⨟ Wk,,succ #1] ->
     Γ ⊢a M ⟸ ℕ ->
     nbe_ty_f Γ A[Id,,M] B ->
     Γ ⊢a rec M return A | zero -> MZ | succ -> MS end ⟹ B )
| ati_pi :
  `( Γ ⊢a A ⟹ Typeⁿ@i ->
     Γ ▹ A ⊢a B ⟹ Typeⁿ@j ->
     Γ ⊢a Π A B ⟹ Typeⁿ@(max i j) )
| ati_fn :
  `( Γ ⊢a A ⟹ Typeⁿ@i ->
     Γ ▹ A ⊢a M ⟹ B ->
     nbe_ty_f Γ A C ->
     Γ ⊢a λ A M ⟹ Πⁿ C B )
| ati_app :
  `( Γ ⊢a M ⟹ Πⁿ A B ->
     Γ ⊢a N ⟸ A ->
     nbe_ty_f Γ B[Id,,N] C ->
     Γ ⊢a M $ N ⟹ C )
| ati_vlookup :
  `( Γ ∋ #x : A ->
     nbe_ty_f Γ A B ->
     Γ ⊢a #x ⟹ B )
(** A global infers the normal form of the closed type that resolution
    returns for it. *)
| ati_glob :
  `( gc_resolve gc_deps gc_stack p = Some (ge_def b pv A B) ->
     nbe_ty_f Γ A C ->
     Γ ⊢a a_glob p ⟹ C )
where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) : type_scope.

Hint Constructors alg_type_check alg_type_infer : mctt.

End Fixed_GCtx.

Notation "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) : type_scope.
Notation "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) : type_scope.

#[export]
Hint Constructors alg_type_check alg_type_infer : mctt.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.

(** ** User Expressions

    The expressions the type checker accepts.  Every [exp] is one
    ([user_exp_all]); the predicate exists because [type_check_closed] is
    indexed by it. *)
Generalizable All Variables.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp (a_typ i) )
| user_exp_nat :
  `( user_exp a_nat )
| user_exp_zero :
  `( user_exp a_zero )
| user_exp_succ :
  `( user_exp M ->
     user_exp (a_succ M) )
| user_exp_natrec :
  `( user_exp A ->
     user_exp MZ ->
     user_exp MS ->
     user_exp M ->
     user_exp (a_natrec A MZ MS M) )
| user_exp_pi :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_pi A B) )
| user_exp_fn :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_fn A M) )
| user_exp_app :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_app M N) )
| user_exp_vlookup :
  `( user_exp (a_var x) )
| user_exp_glob :
  `( user_exp (a_glob p) ).

#[export]
Hint Constructors user_exp : mctt.

Lemma user_exp_all : forall M, user_exp M.
Proof.
  induction M; mauto 3.
Qed.

#[export]
Hint Resolve user_exp_all : mctt.

Lemma user_exp_nf : forall M, user_exp (nf_to_exp M)
with user_exp_ne : forall M, user_exp (ne_to_exp M).
Proof.
  - clear user_exp_nf; induction M; mauto 3.
  - clear user_exp_ne; induction M; mauto 3.
Qed.
