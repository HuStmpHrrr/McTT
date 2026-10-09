From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Subtyping Require Export Definitions.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Fresh.
Import Domain_Notations Fixed_Notations.

Reserved Notation "Γ '⊢a' M ⟹ A" (at level 70, M at level 69, A at level 69).
Reserved Notation "Γ '⊢a' M ⟸ A" (at level 70, M at level 69, A at level 69).
Reserved Notation "Γ '⊢aˣ' Ψ" (at level 70, Ψ at level 69).
Reserved Notation "Γ '⊢aᵘ' U" (at level 70, U at level 69).
Reserved Notation "Γ '⊢aᵐ' H" (at level 70, H at level 69).

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
(** The universes of both tiers infer the universe above.  A small universe's
    level infers a type of levels, and the universe above is the normal form
    of [Type⟨succl M⟩], as the type of an application is the normal form of
    the instantiated codomain: the side condition is a normalisation, not an
    index computed in the conclusion. *)
| ati_typ :
  `( Γ ⊢a Typeω@i ⟹ Typeωⁿ@(S i) )
| ati_suniv :
  `( Γ ⊢a M ⟹ Levelⁿ@n ->
     nbe_ty_f Γ Type⟨succl M⟩ W ->
     Γ ⊢a Type⟨M⟩ ⟹ W )
(** The closed small types infer the least universe. *)
| ati_level :
  `( Γ ⊢a Level@n ⟹ Typeⁿ@0 )
(** A level literal is of the least type of levels; the two operations
    infer the types of levels of their arguments, and are of the larger. *)
| ati_llit :
  `( Γ ⊢a 𝕃ᵒ o ⟹ Levelⁿ@0 )
| ati_succl :
  `( Γ ⊢a M ⟹ Levelⁿ@n ->
     Γ ⊢a succl M ⟹ Levelⁿ@n )
| ati_maxl :
  `( Γ ⊢a M ⟹ Levelⁿ@m ->
     Γ ⊢a N ⟹ Levelⁿ@n ->
     Γ ⊢a maxl M N ⟹ Levelⁿ@(Nat.max m n) )
| ati_nat :
  `( Γ ⊢a ℕ ⟹ Typeⁿ@0 )
| ati_zero :
  `( Γ ⊢a zero ⟹ ℕⁿ )
| ati_succ :
  `( Γ ⊢a M ⟸ ℕ ->
     Γ ⊢a succ M ⟹ ℕⁿ )
| ati_natrec :
  `( Γ ▹ ℕ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ⊢a MZ ⟸ A[Id,,zero] ->
     Γ ▹ ℕ ▹ A ⊢a MS ⟸ A[Wk ⨟ Wk,,succ #1] ->
     Γ ⊢a M ⟸ ℕ ->
     nbe_ty_f Γ A[Id,,M] B ->
     Γ ⊢a rec M return A | zero -> MZ | succ -> MS end ⟹ B )
| ati_True :
  `( Γ ⊢a ⊤ ⟹ Typeⁿ@0 )
| ati_true :
  `( Γ ⊢a ⋆ ⟹ ⊤ⁿ )
| ati_False :
  `( Γ ⊢a ⊥ ⟹ Typeⁿ@0 )
| ati_exfalso :
  `( Γ ▹ ⊥ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ⊢a M ⟸ ⊥ ->
     nbe_ty_f Γ A[Id,,M] B ->
     Γ ⊢a efq M return A ⟹ B )
(** A [Π] is at the join of the universes of its parts ([unf_pi_tm]): a
    large universe absorbs a small one, and two small ones join on levels when
    the codomain's level does not mention the bound variable.  The join is
    the normal form of that universe, a side condition rather than the
    conclusion's index: an index computed from the premises makes the
    judgment's inversion non-terminating.  The side conditions on the parts
    are [is_univ_nf] rather than equations on [univ_nf_idx], for the reason
    given there. *)
| ati_pi :
  `( Γ ⊢a A ⟹ UA ->
     Γ ▹ A ⊢a B ⟹ UB ->
     is_univ_nf UA u ->
     is_univ_nf UB v ->
     nbe_ty_f Γ (unf_pi_tm u v) W ->
     Γ ⊢a Π A B ⟹ W )
| ati_fn :
  `( Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ▹ A ⊢a M ⟹ B ->
     nbe_ty_f Γ A C ->
     Γ ⊢a λ A M ⟹ Πⁿ C B )
| ati_app :
  `( Γ ⊢a M ⟹ Πⁿ A B ->
     Γ ⊢a N ⟸ A ->
     nbe_ty_f Γ B[Id,,N] C ->
     Γ ⊢a M $ N ⟹ C )
| ati_let :
  `( Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ⊢a M ⟸ A ->
     Γ ▸ A ≔ M ⊢a B ⟹ C ->
     nbe_ty_f Γ C[Id,,M] D ->
     Γ ⊢a ℓ A ≔ M in B ⟹ D )
(** An unannotated definition is of the type its body infers. *)
| ati_let_infer :
  `( Γ ⊢a M ⟹ A ->
     Γ ▸ (A : exp) ≔ M ⊢a B ⟹ C ->
     nbe_ty_f Γ C[Id,,M] D ->
     Γ ⊢a ℓ ≔ M in B ⟹ D )
| ati_let_mod :
  `( Γ ⊢aᵘ U ->
     Γ ▹ₘ U ⊢a B ⟹ C ->
     nbe_ty_f Γ C[Id ,,ₘ me_lit U] D ->
     Γ ⊢a ℓₘ U in B ⟹ D )
(** A member infers the normal form of its canonical type.  Neither that
    type nor the member's δ-reduct is checked: of a well-formed module, the
    one is a type and the other inhabits it ([member_wf]). *)
| ati_mem :
  `( me_noargs H ->
     Γ ⊢aᵐ H ->
     member_type gc_deps gc_stack Γ H (x :: nil) (mr_term A) ->
     nbe_ty_f Γ A B ->
     Γ ⊢a a_mem H x ⟹ B )
(** A member of an applied module infers as its root's member applied. *)
| ati_mem_app :
  `( Γ ⊢aᵐ H ->
     modexp_spine H = (R, args, pre) ->
     args <> nil ->
     Γ ⊢a apps (member_ref R (pre ++ x :: nil)) args ⟹ A ->
     Γ ⊢a a_mem H x ⟹ A )
| ati_vlookup :
  `( Γ ∋ #x : A ->
     nbe_ty_f Γ A B ->
     Γ ⊢a #x ⟹ B )
(** A member of a chain from a unit, a global, infers the normal form of the
    closed type that resolution returns for it. *)
| ati_mem_glob :
  `( mod_qname H = Some mp ->
     gc_resolve gc_deps gc_stack (qname_app mp (x :: nil)) = Some (ge_def b pv A B) ->
     nbe_ty_f Γ A C ->
     Γ ⊢a a_mem H x ⟹ C )
where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) : type_scope
(** The well-formedness of extensions, units and module expressions, entry by
    entry, part by part. *)
with alg_ext : ctx -> ctx -> Prop :=
| aext_nil :
  `( Γ ⊢aˣ ⋅ )
| aext_ass :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Γ ⊢aˣ Ψ ▹ A )
| aext_def :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢a A ⟹ UA ->
     is_univ_nf UA u ->
     Ψ ++ Γ ⊢a M ⟸ A ->
     Γ ⊢aˣ Ψ ▸ A ≔ M )
| aext_mod :
  `( Γ ⊢aˣ Ψ ->
     Ψ ++ Γ ⊢aᵘ U ->
     Γ ⊢aˣ Ψ ▹ₘ U )
where "Γ '⊢aˣ' Ψ" := (alg_ext Γ Ψ) : type_scope
with alg_unit : ctx -> gunit -> Prop :=
| aunit_body :
  `( Γ ⊢aˣ body_ctx Φ ++ Δ ->
     tele_ass Δ ->
     body_shape Φ Φ ->
     List.NoDup (gm_names Φ) ->
     Γ ⊢aᵘ gu_body Δ Φ )
| aunit_alias :
  `( Γ ⊢aˣ Δ ->
     tele_ass Δ ->
     Δ ++ Γ ⊢aᵐ E ->
     Γ ⊢aᵘ gu_mk Δ (md_alias E) )
where "Γ '⊢aᵘ' U" := (alg_unit Γ U) : type_scope
with alg_modexp : ctx -> modexp -> Prop :=
| amod_glob :
  `( mod_qname H = Some mp ->
     member_type gc_deps gc_stack Γ H nil (mr_mod T) ->
     Γ ⊢aᵐ H )
| amod_var :
  `( Γ ∋ #x ⇒ₘ U ->
     Γ ⊢aᵐ me_var x )
| amod_lit :
  `( Γ ⊢aᵘ U ->
     Γ ⊢aᵐ me_lit U )
| amod_mem :
  `( Γ ⊢aᵐ H ->
     member_type gc_deps gc_stack Γ H (y :: nil) (mr_mod T) ->
     Γ ⊢aᵐ me_mem H y )
(** An argument is checked against the outermost parameter of the arity. *)
| amod_app :
  `( Γ ⊢aᵐ H ->
     member_type gc_deps gc_stack Γ H nil (mr_mod T) ->
     tele_view T = Some (B, T1) ->
     Γ ⊢a N ⟸ B ->
     Γ ⊢aᵐ me_app H N )
where "Γ '⊢aᵐ' H" := (alg_modexp Γ H) : type_scope.

Hint Constructors alg_type_check alg_type_infer alg_ext alg_unit alg_modexp : mctt.

End Fixed_GCtx.

Notation "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) : type_scope.
Notation "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) : type_scope.
Notation "Γ '⊢aˣ' Ψ" := (alg_ext Γ Ψ) : type_scope.
Notation "Γ '⊢aᵘ' U" := (alg_unit Γ U) : type_scope.
Notation "Γ '⊢aᵐ' H" := (alg_modexp Γ H) : type_scope.

#[export]
Hint Constructors alg_type_check alg_type_infer alg_ext alg_unit alg_modexp : mctt.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop
with alg_ext_mut_ind := Induction for alg_ext Sort Prop
with alg_unit_mut_ind := Induction for alg_unit Sort Prop
with alg_modexp_mut_ind := Induction for alg_modexp Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind,
  alg_ext_mut_ind,
  alg_unit_mut_ind,
  alg_modexp_mut_ind.

(** ** User Expressions

    The expressions the type checker accepts.  Every [exp] is one
    ([user_exp_all]); the predicate exists because [type_check_closed] is
    indexed by it. *)
Generalizable All Variables.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp (a_typ i) )
| user_exp_univ :
  `( user_exp M ->
     user_exp (a_univ M) )
| user_exp_level :
  `( user_exp (a_level n) )
| user_exp_llit :
  `( user_exp (a_llit n) )
| user_exp_succl :
  `( user_exp M ->
     user_exp (a_succl M) )
| user_exp_maxl :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_maxl M N) )
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
| user_exp_True :
  `( user_exp a_True )
| user_exp_true :
  `( user_exp a_true )
| user_exp_False :
  `( user_exp a_False )
| user_exp_exfalso :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_exfalso A M) )
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
| user_exp_let :
  `( user_exp A ->
     user_exp M ->
     user_exp B ->
     user_exp (ℓ A ≔ M in B) )
| user_exp_let_infer :
  `( user_exp M ->
     user_exp B ->
     user_exp (ℓ ≔ M in B) )
| user_exp_let_mod :
  `( user_exp B ->
     user_exp (ℓₘ U in B) )
| user_exp_mem :
  `( user_exp (a_mem H x) )
| user_exp_vlookup :
  `( user_exp (a_var x) ).

#[export]
Hint Constructors user_exp : mctt.

Lemma user_exp_all : forall M, user_exp M.
Proof.
  eapply proj1, (syn_mut_ind user_exp (fun _ => True)
    (fun b => match b with b_def oA M => (forall A, oA = Some A -> user_exp A) /\ user_exp M | b_mod _ => True end)
    (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True));
    intros; try destruct_conjs; try match goal with b : bnd |- _ => destruct b as [[] |]; destruct_conjs end;
    mauto 3.
Qed.

#[export]
Hint Resolve user_exp_all : mctt.

Lemma user_exp_nf : forall M, user_exp (nf_to_exp M)
with user_exp_ne : forall M, user_exp (ne_to_exp M).
Proof.
  - clear user_exp_nf; induction M; mauto 3.
  - clear user_exp_ne; induction M; mauto 3.
Qed.

#[export]
Hint Constructors is_univ_nf : mctt.
#[export]
Hint Resolve is_univ_nf_univ_nf : mctt.

(** The universes as normal forms, for the rewriting the universe cases need:
    the coercion [nf_to_exp] does not unfold by [rewrite] on its own. *)
Lemma nf_to_exp_typ : forall i, nf_to_exp Typeωⁿ@i = Typeω@i.
Proof. reflexivity. Qed.

Lemma nf_to_exp_univ : forall n, nf_to_exp Typeⁿ@n = Type@n.
Proof. reflexivity. Qed.

Lemma nf_to_exp_univ_of : forall L,
    nf_to_exp (nf_univ_of L) = Type⟨nf_to_exp (nf_lvl_of L)⟩.
Proof. reflexivity. Qed.

(** Normalises the universes a derivation reads back, whichever of the three
    spellings they are in. *)
Ltac simpl_univ_nf := rewrite ?nf_to_exp_univ_nf, ?nf_to_exp_typ, ?nf_to_exp_univ in *.
