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
(** A parameter of an open frame, at the type [wf_param] gives it.  The two
    premises of that rule are a lookup in a list and a lookup in a telescope, so
    they are one call of [gs_param] here: a function, which keeps the inferred
    type determined by the term without appealing to canonicity of the global
    context, and keeps the extracted checker a table lookup. *)
| ati_param :
  `( gs_param gc_stack lp = Some T ->
     nbe_ty_f Γ T C ->
     Γ ⊢a a_param lp ⟹ C )
(** A global, at the type it is stored with.  [gc_resolve] is [gc_lookup] as a
    function, for the same two reasons. *)
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
