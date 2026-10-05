From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
From Mctt.Core.Syntactic Require Import GlobalCtx.

Reserved Notation "'Rnf' m 'in' Θ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, s constr, M at level 69).
Reserved Notation "'Rne' m 'in' Θ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, s constr, M at level 69).
Reserved Notation "'Rtyp' m 'in' Θ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, s constr, M at level 69).

Generalizable All Variables.

(** Readback of values into normal and neutral forms in a context with [s]
    variables.  The global context is needed to evaluate closures. *)
Inductive read_nf (Θ : gctx) : nat -> domain_nf -> nf -> Prop :=
| read_nf_type :
  `( Rtyp a in Θ ⍮ s ↘ A ->
     Rnf ⇓ 𝕌@i a in Θ ⍮ s ↘ A )
| read_nf_zero :
  `( Rnf ⇓ ℕᵈ zeroᵈ in Θ ⍮ s ↘ zeroⁿ )
| read_nf_succ :
  `( Rnf ⇓ ℕᵈ m in Θ ⍮ s ↘ M ->
     Rnf ⇓ ℕᵈ (succᵈ m) in Θ ⍮ s ↘ succⁿ M )
| read_nf_nat_neut :
  `( Rne m in Θ ⍮ s ↘ M ->
     Rnf ⇓ ℕᵈ (⇑ a m) in Θ ⍮ s ↘ ⇑ⁿ M )
(** η for [⊤]: every value of type [⊤] reads back as [⋆]. *)
| read_nf_true :
  `( Rnf ⇓ ⊤ᵈ m in Θ ⍮ s ↘ ⋆ⁿ )
| read_nf_False_neut :
  `( Rne m in Θ ⍮ s ↘ M ->
     Rnf ⇓ ⊥ᵈ (⇑ a m) in Θ ⍮ s ↘ ⇑ⁿ M )
| read_nf_fn :
  `( (** The normal form of the argument type. *)
     Rtyp a in Θ ⍮ s ↘ A ->
     (** The normal form of the η-expanded body. *)
     $| m & ⇑! a s | Θ ↘ m' ->
     ⟦ B ⟧ Θ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rnf ⇓ b m' in Θ ⍮ S s ↘ M ->

     Rnf ⇓ (Πᵈ a ρ B) m in Θ ⍮ s ↘ λⁿ A M )
| read_nf_neut :
  `( Rne m in Θ ⍮ s ↘ M ->
     Rnf ⇓ (⇑ a b) (⇑ c m) in Θ ⍮ s ↘ ⇑ⁿ M )
where "'Rnf' m 'in' Θ '⍮' s ↘ M" := (read_nf Θ s m M) : type_scope
with read_ne (Θ : gctx) : nat -> domain_ne -> ne -> Prop :=
| read_ne_var :
  `( Rne #ᵈ x in Θ ⍮ s ↘ #ⁿ (s - x - 1) )
| read_ne_app :
  `( Rne m in Θ ⍮ s ↘ M ->
     Rnf n in Θ ⍮ s ↘ N ->
     Rne m $ᵈ n in Θ ⍮ s ↘ M $ⁿ N )
| read_ne_natrec :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ Θ ⍮ ρ ↦ ⇑! ℕᵈ s ↘ b ->
     Rtyp b in Θ ⍮ S s ↘ B' ->

     (** The normal form of the zero case. *)
     ⟦ B ⟧ Θ ⍮ ρ ↦ zeroᵈ ↘ bz ->
     Rnf ⇓ bz mz in Θ ⍮ s ↘ MZ ->

     (** The normal form of the successor case. *)
     ⟦ B ⟧ Θ ⍮ ρ ↦ succᵈ (⇑! ℕᵈ s) ↘ bs ->
     ⟦ MS ⟧ Θ ⍮ ρ ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s) ↘ ms ->
     Rnf ⇓ bs ms in Θ ⍮ S (S s) ↘ MS' ->

     (** The neutral form of the scrutinee. *)
     Rne m in Θ ⍮ s ↘ M ->

     Rne recᵈ m under ρ return B | zero -> mz | succ -> MS end in Θ ⍮ s ↘ recⁿ M return B' | zero -> MZ | succ -> MS' end )
| read_ne_exfalso :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ Θ ⍮ ρ ↦ ⇑! ⊥ᵈ s ↘ b ->
     Rtyp b in Θ ⍮ S s ↘ B' ->

     (** The neutral form of the scrutinee. *)
     Rne m in Θ ⍮ s ↘ M ->

     Rne efqᵈ m under ρ return B in Θ ⍮ s ↘ efqⁿ M return B' )
| read_ne_glob :
  `( Rne d_glob p in Θ ⍮ s ↘ ne_glob p )
where "'Rne' m 'in' Θ '⍮' s ↘ M" := (read_ne Θ s m M) : type_scope
with read_typ (Θ : gctx) : nat -> domain -> nf -> Prop :=
| read_typ_univ :
  `( Rtyp 𝕌@i in Θ ⍮ s ↘ Typeⁿ@i )
| read_typ_nat :
  `( Rtyp ℕᵈ in Θ ⍮ s ↘ ℕⁿ )
| read_typ_True :
  `( Rtyp ⊤ᵈ in Θ ⍮ s ↘ ⊤ⁿ )
| read_typ_False :
  `( Rtyp ⊥ᵈ in Θ ⍮ s ↘ ⊥ⁿ )
| read_typ_pi :
  `( (** The normal form of the argument type. *)
     Rtyp a in Θ ⍮ s ↘ A ->

     (** The normal form of the return type. *)
     ⟦ B ⟧ Θ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rtyp b in Θ ⍮ S s ↘ B' ->

     Rtyp Πᵈ a ρ B in Θ ⍮ s ↘ Πⁿ A B')
| read_typ_neut :
  `( Rne b in Θ ⍮ s ↘ B ->
     Rtyp ⇑ a b in Θ ⍮ s ↘ ⇑ⁿ B)
where "'Rtyp' m 'in' Θ '⍮' s ↘ M" := (read_typ Θ s m M) : type_scope
.

Scheme read_nf_mut_ind := Induction for read_nf Sort Prop
with read_ne_mut_ind := Induction for read_ne Sort Prop
with read_typ_mut_ind := Induction for read_typ Sort Prop.
Combined Scheme read_mut_ind from
  read_nf_mut_ind,
  read_ne_mut_ind,
  read_typ_mut_ind.

#[export]
Hint Constructors read_nf read_ne read_typ : mctt.
