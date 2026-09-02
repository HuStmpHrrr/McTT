From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.

Reserved Notation "'Rnf' m 'in' s ↘ M" (at level 70, m at level 69, s constr, M at level 69).
Reserved Notation "'Rne' m 'in' s ↘ M" (at level 70, m at level 69, s constr, M at level 69).
Reserved Notation "'Rtyp' m 'in' s ↘ M" (at level 70, m at level 69, s constr, M at level 69).

Generalizable All Variables.

Inductive read_nf : nat -> domain_nf -> nf -> Prop :=
| read_nf_type :
  `( Rtyp a in s ↘ A ->
     Rnf ⇓ 𝕌@i a in s ↘ A )
| read_nf_zero :
  `( Rnf ⇓ ℕᵈ zeroᵈ in s ↘ zeroⁿ )
| read_nf_succ :
  `( Rnf ⇓ ℕᵈ m in s ↘ M ->
     Rnf ⇓ ℕᵈ (succᵈ m) in s ↘ succⁿ M )
| read_nf_nat_neut :
  `( Rne m in s ↘ M ->
     Rnf ⇓ ℕᵈ (⇑ a m) in s ↘ ⇑ⁿ M )
| read_nf_fn :
  `( (** Normal form of arg type *)
     Rtyp a in s ↘ A ->
     (** Normal form of eta-expanded body *)
     $| m & ⇑! a s |↘ m' ->
     ⟦ B ⟧ ρ ↦ ⇑! a s ↘ b ->
     Rnf ⇓ b m' in S s ↘ M ->

     Rnf ⇓ (Πᵈ a ρ B) m in s ↘ λⁿ A M )
| read_nf_neut :
  `( Rne m in s ↘ M ->
     Rnf ⇓ (⇑ a b) (⇑ c m) in s ↘ ⇑ⁿ M )
where "'Rnf' m 'in' s ↘ M" := (read_nf s m M) : type_scope
with read_ne : nat -> domain_ne -> ne -> Prop :=
| read_ne_var :
  `( Rne #ᵈ x in s ↘ #ⁿ (s - x - 1) )
| read_ne_app :
  `( Rne m in s ↘ M ->
     Rnf n in s ↘ N ->
     Rne m $ᵈ n in s ↘ M $ⁿ N )
| read_ne_natrec :
  `( (** Normal form of motive *)
     ⟦ B ⟧ ρ ↦ ⇑! ℕᵈ s ↘ b ->
     Rtyp b in S s ↘ B' ->

     (** Normal form of mz *)
     ⟦ B ⟧ ρ ↦ zeroᵈ ↘ bz ->
     Rnf ⇓ bz mz in s ↘ MZ ->

     (** Normal form of MS *)
     ⟦ B ⟧ ρ ↦ succᵈ (⇑! ℕᵈ s) ↘ bs ->
     ⟦ MS ⟧ ρ ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s) ↘ ms ->
     Rnf ⇓ bs ms in S (S s) ↘ MS' ->

     (** Neutral form of m *)
     Rne m in s ↘ M ->

     Rne recᵈ m under ρ return B | zero -> mz | succ -> MS end in s ↘ recⁿ M return B' | zero -> MZ | succ -> MS' end )
where "'Rne' m 'in' s ↘ M" := (read_ne s m M) : type_scope
with read_typ : nat -> domain -> nf -> Prop :=
| read_typ_univ :
  `( Rtyp 𝕌@i in s ↘ Typeⁿ@i )
| read_typ_nat :
  `( Rtyp ℕᵈ in s ↘ ℕⁿ )
| read_typ_pi :
  `( (** Normal form of arg type *)
     Rtyp a in s ↘ A ->

     (** Normal form of ret type *)
     ⟦ B ⟧ ρ ↦ ⇑! a s ↘ b ->
     Rtyp b in S s ↘ B' ->

     Rtyp Πᵈ a ρ B in s ↘ Πⁿ A B')
| read_typ_neut :
  `( Rne b in s ↘ B ->
     Rtyp ⇑ a b in s ↘ ⇑ⁿ B)
where "'Rtyp' m 'in' s ↘ M" := (read_typ s m M) : type_scope
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
