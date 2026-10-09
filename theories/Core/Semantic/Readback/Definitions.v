From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
From Mctt.Core.Syntactic Require Import Members.

Reserved Notation "'Rnf' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rne' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rtyp' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rla' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" (at level 70, xs at level 69, Θ at level 69, Ξ at level 69, s constr, ys at level 69).

Generalizable All Variables.

(** Readback of values into normal and neutral forms in a context with [s]
    variables.  The global context is needed to evaluate closures. *)
Inductive read_nf (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> nf -> Prop :=
| read_nf_type :
  `( Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ 𝕌ω@i a in Θ ⍮ Ξ ⍮ s ↘ A )
| read_nf_stype :
  `( Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ 𝕌@n a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A level reads back canonically: its atoms are read, then sorted and
    merged, and a dominated constant is dropped ([lvl_canon]).  Evaluation
    flattens only, so this is where levels equal by the level equations become
    the same normal form.  A neutral level is the single atom at offset [0],
    which is already canonical. *)
| read_nf_lvl :
  `( Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rnf ⇓ (Levelᵈ@n) (lvᵈ c xs) in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of (lvl_canon (c, ys)) )
| read_nf_lvl_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ (Levelᵈ@n) (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ lvⁿ oz (la_cons 0 M la_nil) )
| read_nf_zero :
  `( Rnf ⇓ ℕᵈ zeroᵈ in Θ ⍮ Ξ ⍮ s ↘ zeroⁿ )
| read_nf_succ :
  `( Rnf ⇓ ℕᵈ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ ℕᵈ (succᵈ m) in Θ ⍮ Ξ ⍮ s ↘ succⁿ M )
| read_nf_nat_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ ℕᵈ (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
(** η for [⊤]: every value of type [⊤] reads back as [⋆]. *)
| read_nf_true :
  `( Rnf ⇓ ⊤ᵈ m in Θ ⍮ Ξ ⍮ s ↘ ⋆ⁿ )
| read_nf_False_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ ⊥ᵈ (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
| read_nf_fn :
  `( (** The normal form of the argument type. *)
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     (** The normal form of the η-expanded body. *)
     $| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rnf ⇓ b m' in Θ ⍮ Ξ ⍮ S s ↘ M ->

     Rnf ⇓ (Πᵈ a ρ B) m in Θ ⍮ Ξ ⍮ s ↘ λⁿ A M )
| read_nf_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ (⇑ a b) (⇑ c m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
where "'Rnf' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_nf Θ Ξ s m M) : type_scope
with read_ne (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> ne -> Prop :=
| read_ne_var :
  `( Rne #ᵈ x in Θ ⍮ Ξ ⍮ s ↘ #ⁿ (s - x - 1) )
| read_ne_app :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf n in Θ ⍮ Ξ ⍮ s ↘ N ->
     Rne m $ᵈ n in Θ ⍮ Ξ ⍮ s ↘ M $ⁿ N )
| read_ne_natrec :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ℕᵈ s ↘ b ->
     Rtyp b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     (** The normal form of the zero case. *)
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ zeroᵈ ↘ bz ->
     Rnf ⇓ bz mz in Θ ⍮ Ξ ⍮ s ↘ MZ ->

     (** The normal form of the successor case. *)
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ succᵈ (⇑! ℕᵈ s) ↘ bs ->
     ⟦ MS ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s) ↘ ms ->
     Rnf ⇓ bs ms in Θ ⍮ Ξ ⍮ S (S s) ↘ MS' ->

     (** The neutral form of the scrutinee. *)
     Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->

     Rne recᵈ m under ρ return B | zero -> mz | succ -> MS end in Θ ⍮ Ξ ⍮ s ↘ recⁿ M return B' | zero -> MZ | succ -> MS' end )
| read_ne_exfalso :
  `( (** The normal form of the motive. *)
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! ⊥ᵈ s ↘ b ->
     Rtyp b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     (** The neutral form of the scrutinee. *)
     Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->

     Rne efqᵈ m under ρ return B in Θ ⍮ Ξ ⍮ s ↘ efqⁿ M return B' )
| read_ne_glob :
  `( Rne d_glob p in Θ ⍮ Ξ ⍮ s ↘ ne_glob p )
where "'Rne' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_ne Θ Ξ s m M) : type_scope
with read_typ (Θ : gdeps) (Ξ : gstack) : nat -> domain -> nf -> Prop :=
| read_typ_univ :
  `( Rtyp 𝕌ω@i in Θ ⍮ Ξ ⍮ s ↘ Typeωⁿ@i )
(** A small universe reads back as the universe at the canonical form its
    level reads back as: that readback is always of the shape [nf_lvl_of L]
    (see [Core.Semantic.Levels.dlvl_canon_of_read]), and the universe takes
    the same canonical level. *)
| read_typ_suniv :
  `( Rnf ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of L ->
     Rtyp 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of L )
| read_typ_level :
  `( Rtyp Levelᵈ@n in Θ ⍮ Ξ ⍮ s ↘ Levelⁿ@n )
| read_typ_nat :
  `( Rtyp ℕᵈ in Θ ⍮ Ξ ⍮ s ↘ ℕⁿ )
| read_typ_True :
  `( Rtyp ⊤ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊤ⁿ )
| read_typ_False :
  `( Rtyp ⊥ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊥ⁿ )
| read_typ_pi :
  `( (** The normal form of the argument type. *)
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->

     (** The normal form of the return type. *)
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ↘ b ->
     Rtyp b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     Rtyp Πᵈ a ρ B in Θ ⍮ Ξ ⍮ s ↘ Πⁿ A B')
| read_typ_neut :
  `( Rne b in Θ ⍮ Ξ ⍮ s ↘ B ->
     Rtyp ⇑ a b in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ B)
where "'Rtyp' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_typ Θ Ξ s m M) : type_scope
(** The atoms of a level, read one by one. *)
with read_la (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * domain_ne) -> lvl_atoms -> Prop :=
| read_la_nil :
  `( Rla nil in Θ ⍮ Ξ ⍮ s ↘ la_nil )
| read_la_cons :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rla (k, m) :: xs in Θ ⍮ Ξ ⍮ s ↘ la_cons k M ys )
where "'Rla' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" := (read_la Θ Ξ s xs ys) : type_scope
.

Scheme read_nf_mut_ind := Induction for read_nf Sort Prop
with read_ne_mut_ind := Induction for read_ne Sort Prop
with read_typ_mut_ind := Induction for read_typ Sort Prop
with read_la_mut_ind := Induction for read_la Sort Prop.
Combined Scheme read_mut_ind from
  read_nf_mut_ind,
  read_ne_mut_ind,
  read_typ_mut_ind,
  read_la_mut_ind.

#[export]
Hint Constructors read_nf read_ne read_typ read_la : mctt.
