From Stdlib Require Import String.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
#[local] Open Scope list_scope.
From Mctt.Core.Syntactic Require Import Members Inductives.

Reserved Notation "'Rnf' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rne' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rtyp' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rla' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" (at level 70, xs at level 69, Θ at level 69, Ξ at level 69, s constr, ys at level 69).

Reserved Notation "'Rps' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).

Generalizable All Variables.

(** ** Fresh Variables of the Telescopes of an Inductive Type

    The readback of a stuck eliminator reads its motive and its branches
    under fresh variables, of the types the declaration gives: the
    non-uniform parameters, the arguments of a constructor, and the
    recursive results.  Each type is evaluated in the environment of the
    variables before it; nothing is built. *)

(** A telescope, outermost first: [fresh_tele ρ T s vs] gives the variables
    from [s] on, the type of each evaluated in [ρ] extended by those
    before it. *)
Inductive fresh_tele (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> list domain -> Prop :=
| fresh_tele_nil :
  `( fresh_tele Θ Ξ ρ nil s nil )
| fresh_tele_cons :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     fresh_tele Θ Ξ (ρ ↦ ⇑! a s) T (S s) vs ->
     fresh_tele Θ Ξ ρ (ce_ass A :: T) s (⇑! a s :: vs) ).

(** The arguments of a constructor of [p] at the uniform parameters [ups]:
    a non-recursive one of the type its declaration gives, in the
    environment of the parameters and the non-recursive arguments before
    it; a recursive one of the type of its shape there. *)
Inductive fresh_cargs (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> list domain -> Prop :=
| fresh_cargs_nil :
  `( fresh_cargs Θ Ξ p ups ρ nil s nil )
| fresh_cargs_arg :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     fresh_cargs Θ Ξ p ups (ρ ↦ ⇑! a s) gs (S s) vs ->
     fresh_cargs Θ Ξ p ups ρ (ca_arg A :: gs) s (⇑! a s :: vs) )
| fresh_cargs_rec :
  `( eval_shty Θ Ξ p ups ρ t a ->
     fresh_cargs Θ Ξ p ups ρ gs (S s) vs ->
     fresh_cargs Θ Ξ p ups ρ (ca_rec t :: gs) s (⇑! a s :: vs) ).

(** The recursive results of the arguments [vs]: one per recursive argument,
    of the type of its recursive result, the motive [A] in [ρ], the shape's
    components in the environment [ρa] of the parameters and the
    non-recursive arguments before it. *)
Inductive fresh_ihs (Θ : gdeps) (Ξ : gstack) (ρ : env) (A : exp) :
  env -> list carg -> list domain -> nat -> list domain -> Prop :=
| fresh_ihs_nil :
  `( fresh_ihs Θ Ξ ρ A ρa nil nil s nil )
| fresh_ihs_arg :
  `( fresh_ihs Θ Ξ ρ A (ρa ↦ v) gs vs s ihs ->
     fresh_ihs Θ Ξ ρ A ρa (ca_arg T :: gs) (v :: vs) s ihs )
| fresh_ihs_rec :
  `( eval_ihty Θ Ξ ρ A ρa t v a ->
     fresh_ihs Θ Ξ ρ A ρa gs vs (S s) ihs ->
     fresh_ihs Θ Ξ ρ A ρa (ca_rec t :: gs) (v :: vs) s (⇑! a s :: ihs) ).

#[export]
Hint Constructors fresh_tele fresh_cargs fresh_ihs : mctt.

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
    of the sort of its type ([dsort]), which is already canonical: the sort
    is read off the neutral's type, not off the type it is read back at. *)
| read_nf_lvl :
  `( Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rnf ⇓ (Levelᵈ@n) (lvᵈ c xs) in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of (lvl_canon (c, ys)) )
| read_nf_lvl_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ (Levelᵈ@n) (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ lvⁿ oz (la_cons 0 (dsort a) M la_nil) )
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
(** A constructor at all its parameters and arguments: the parameters are
    read off the type, at the types the declaration gives them, and the
    arguments at theirs. *)
| read_nf_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length as' = ind_np D ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     Rps as' at List.rev (ind_params D) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     read_cargs Θ Ξ s p (List.firstn (ind_nu D) as') (env_args nil as') gs (List.skipn (ind_np D) vs) Args ->
     Rnf ⇓ (d_ind p as') (d_con p c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p c (nfs_app Ps Args) )
| read_nf_ind_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ (d_ind p as') (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ M )
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
(** A stuck eliminator: the motive under its non-uniform parameters and the
    scrutinee, each branch under its own variables. *)
| read_ne_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     nm = S (ind_nn D) ->
     fresh_tele Θ Ξ (env_args nil (List.firstn (ind_nu D) as')) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as' ++ ns)) ((s + ind_nn D)%nat) :: nil) ↘ a ->
     Rtyp a in Θ ⍮ Ξ ⍮ S (s + ind_nn D)%nat ↘ A' ->
     read_brs Θ Ξ s ρ A p D (List.firstn (ind_nu D) as') (ind_cons D) Bs Bs' ->
     Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rne d_elim ρ nm A Bs p as' m in Θ ⍮ Ξ ⍮ s ↘ ne_elim nm A' Bs' M )
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
(** An inductive type at all its parameters, each read at its type. *)
| read_typ_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     Rps as' at List.rev (ind_params D) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtyp d_ind p as' in Θ ⍮ Ξ ⍮ s ↘ nf_indty p Ps )
where "'Rtyp' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_typ Θ Ξ s m M) : type_scope
(** The atoms of a level, read one by one. *)
with read_la (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> lvl_atoms -> Prop :=
| read_la_nil :
  `( Rla nil in Θ ⍮ Ξ ⍮ s ↘ la_nil )
| read_la_cons :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rla (k, n, m) :: xs in Θ ⍮ Ξ ⍮ s ↘ la_cons k n M ys )
where "'Rla' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" := (read_la Θ Ξ s xs ys) : type_scope
(** Values at a telescope, outermost first, each at its type in the
    environment of the values before it. *)
with read_ps (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> nfs -> Prop :=
| read_ps_nil :
  `( Rps nil at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nfs_nil )
| read_ps_cons :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rps vs at T in Θ ⍮ Ξ ⍮ ρ ↦ v ⍮ s ↘ Vs ->
     Rps v :: vs at ce_ass A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nfs_cons V Vs )
where "'Rps' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (read_ps Θ Ξ s ρ T vs Ms) : type_scope
(** The arguments of a constructor of [p] at the uniform parameters [ups],
    each at its type: a non-recursive one at the type its declaration gives,
    a recursive one at the type itself. *)
with read_cargs (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> nfs -> Prop :=
| read_cargs_nil :
  `( read_cargs Θ Ξ s p ups ρ nil nil nfs_nil )
| read_cargs_arg :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     read_cargs Θ Ξ s p ups (ρ ↦ v) gs vs Vs ->
     read_cargs Θ Ξ s p ups ρ (ca_arg A :: gs) (v :: vs) (nfs_cons V Vs) )
| read_cargs_rec :
  `( eval_shty Θ Ξ p ups ρ t a ->
     Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     read_cargs Θ Ξ s p ups ρ gs vs Vs ->
     read_cargs Θ Ξ s p ups ρ (ca_rec t :: gs) (v :: vs) (nfs_cons V Vs) )
(** The branches of a stuck eliminator, one per constructor in order: each
    under the non-uniform parameters, the arguments and the recursive
    results, at the motive's instance at the constructor. *)
with read_brs (Θ : gdeps) (Ξ : gstack) : nat -> env -> exp -> qname -> ind_decl -> list domain ->
                                    list (string * list carg) -> list (string * nat * exp) -> nbrs -> Prop :=
| read_brs_nil :
  `( read_brs Θ Ξ s ρ A p D ups nil nil nbrs_nil )
| read_brs_cons :
  `( n = (ind_nn D + List.length gs + cargs_nrec gs)%nat ->
     cargs_plen (ind_nn D) gs ->
     fresh_tele Θ Ξ (env_args nil ups) (List.rev (List.firstn (ind_nn D) (ind_params D))) s ns ->
     fresh_cargs Θ Ξ p ups (env_args nil (ups ++ ns)) gs (s + ind_nn D)%nat vs ->
     fresh_ihs Θ Ξ ρ A (env_args nil (ups ++ ns)) gs vs (s + ind_nn D + List.length gs)%nat ihs ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ vs ++ ihs) ↘ b ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (ns ++ d_con p c (ups ++ ns ++ vs) :: nil) ↘ t ->
     Rnf ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
     read_brs Θ Ξ s ρ A p D ups cs Bs Bs' ->
     read_brs Θ Ξ s ρ A p D ups ((c, gs) :: cs) ((c, n, B) :: Bs) (nbrs_cons c n B' Bs') )
.

Scheme read_nf_mut_ind := Induction for read_nf Sort Prop
with read_ne_mut_ind := Induction for read_ne Sort Prop
with read_typ_mut_ind := Induction for read_typ Sort Prop
with read_la_mut_ind := Induction for read_la Sort Prop
with read_ps_mut_ind := Induction for read_ps Sort Prop
with read_cargs_mut_ind := Induction for read_cargs Sort Prop
with read_brs_mut_ind := Induction for read_brs Sort Prop.
Combined Scheme read_mut_ind from
  read_nf_mut_ind,
  read_ne_mut_ind,
  read_typ_mut_ind,
  read_la_mut_ind,
  read_ps_mut_ind,
  read_cargs_mut_ind,
  read_brs_mut_ind.

#[export]
Hint Constructors read_nf read_ne read_typ read_la read_ps read_cargs read_brs : mctt.
