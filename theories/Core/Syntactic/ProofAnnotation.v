(** * Normal Forms with Annotated Proofs

    A normal form keeps a proof as the term it was written as
    ([nf_proof P M]), and [nf_to_exp] drops the proposition [P]: as a
    term, the normal form says nothing of which positions hold proofs.
    Normal forms are compared up to their proofs ([nf_eq_upto_proofs]), so
    two typed normal forms equal up to their proofs need not be equal
    terms: [nf_proof nf_True (𝕃@0)] and [nf_proof nf_True (𝕃@1)] are
    related, and as terms they are [𝕃@0] and [𝕃@1], both of type
    [Level@1], and not equal.

    [nf_annotate_proofs] writes each proof [M] of a normal form at its
    proposition [P] as [proof_ascription P M], whose typing says that [P]
    is a proposition, [M] a proof of it, and the position of type [P] or
    above.  Two normal forms equal up to their proofs whose annotations
    are typed are then equal ([nf_annotate_proofs_upto] in
    [Core.Completeness.Consequences.AnnotatedUpto]): at a proof position the
    two proofs prove one proposition, and are equal by proof irrelevance.
    The gluing model of soundness states its readback equations at
    annotated normal forms, and the annotation is itself a normal form
    equal to the original up to proofs ([nf_annotate_proofs_upto_proofs]). *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** A proof [M] of the proposition [P], ascribed it:
    [ℓ x : P ≔ a_left (a_conj P ⊤ M a_tt) in x].  Its typing says that [P]
    is a proposition and [M] a proof of it (the pair at [Σₚ P ⊤]), and
    that its type is [P] or above it (the local definition at [P]). *)
Definition proof_ascription (P M : exp) : exp := a_let (b_def P (a_left (a_conj P a_True M a_tt))) (a_var 0).

(** A normal form with each proof ascribed its proposition, itself
    annotated; every other part is kept. *)
Fixpoint nf_annotate_proofs (W : nf) : nf :=
  match W with
  | nf_typ i => nf_typ i
  | nf_univ c xs =>
      nf_univ c (List.map (fun a => mk_level_atom (atom_offset a) (atom_sort a) (ne_annotate_proofs (atom_level a))) xs)
  | nf_level n => nf_level n
  | nf_level_sort => nf_level_sort
  | nf_lvl c xs =>
      nf_lvl c (List.map (fun a => mk_level_atom (atom_offset a) (atom_sort a) (ne_annotate_proofs (atom_level a))) xs)
  | nf_prop => nf_prop
  | nf_True => nf_True
  | nf_proof P M => nf_proof (nf_annotate_proofs P) (proof_ascription (nf_to_exp (nf_annotate_proofs P)) M)
  | nf_False => nf_False
  | nf_and P Q => nf_and (nf_annotate_proofs P) (nf_annotate_proofs Q)
  | nf_pi κd κc A B => nf_pi κd κc (nf_annotate_proofs A) (nf_annotate_proofs B)
  | nf_fn A M => nf_fn (nf_annotate_proofs A) (nf_annotate_proofs M)
  | nf_indty p k Ms => nf_indty p k (List.map nf_annotate_proofs Ms)
  | nf_con p k c Ms => nf_con p k c (List.map nf_annotate_proofs Ms)
  | nf_neut κ M => nf_neut κ (ne_annotate_proofs M)
  | nf_record p Ms => nf_record p (List.map nf_annotate_proofs Ms)
  | nf_tuple p Ms fs Ns => nf_tuple p (List.map nf_annotate_proofs Ms) fs (List.map nf_annotate_proofs Ns)
  end
(** The same for neutrals. *)
with ne_annotate_proofs (M : ne) : ne :=
  match M with
  | ne_absurd A M => ne_absurd (nf_annotate_proofs A) M
  | ne_elim p Us m Bks M =>
      ne_elim p (List.map nf_annotate_proofs Us) m
        (List.map (fun b => mk_normal_block (block_arity b) (nf_annotate_proofs (block_scrutinee_type b))
                              (nf_annotate_proofs (block_motive b))
                              (List.map (fun br => mk_normal_branch (branch_constructor br) (branch_arity br)
                                                    (nf_annotate_proofs (branch_body br)))
                                 (block_branches b))) Bks)
        (ne_annotate_proofs M)
  | ne_app M N => ne_app (ne_annotate_proofs M) (nf_annotate_proofs N)
  | ne_var x => ne_var x
  | ne_glob p => ne_glob p
  | ne_proj f M => ne_proj f (ne_annotate_proofs M)
  end.

(** The annotation changes only proofs: a normal form is equal to its
    annotation up to proofs. *)
Lemma nf_ne_annotate_proofs_upto_proofs :
  (forall W, nf_eqb_upto_proofs W (nf_annotate_proofs W) = true) /\
  (forall M, ne_eqb_upto_proofs M (ne_annotate_proofs M) = true).
Proof.
  apply nf_ne_ind; intros; cbn [nf_annotate_proofs ne_annotate_proofs nf_eqb_upto_proofs ne_eqb_upto_proofs]; eqb_split;
    rewrite ?PeanoNat.Nat.eqb_refl, ?dec_eqb_refl; try assumption; try reflexivity.
  all: lazymatch goal with Hl : list_all _ _ ?l |- list_eqb _ ?l (map _ ?l) = true =>
         clear - Hl; induction Hl as [| x Hx l' Hl' IH]; cbn; [ reflexivity |]; rewrite IH; rewrite ?Bool.andb_true_r
       end.
  all: try (destruct Hx; cbn; rewrite ?PeanoNat.Nat.eqb_refl; cbn; assumption).
  all: try assumption.
  (** A block of a stuck eliminator: its scrutinee type, its motive, and
      its branches one by one *)
  destruct Hx as [n' Z HZ A' HA brs Hbrs]; cbn; rewrite PeanoNat.Nat.eqb_refl, HZ, HA; cbn.
  clear - Hbrs; induction Hbrs as [| br Hbr brs' Hbrs' IH]; cbn; [ reflexivity |]; rewrite IH, Bool.andb_true_r.
  destruct Hbr; cbn; rewrite dec_eqb_refl, PeanoNat.Nat.eqb_refl; assumption.
Qed.

Lemma nf_annotate_proofs_upto_proofs : forall W, nf_eq_upto_proofs W (nf_annotate_proofs W).
Proof. intros; exact (proj1 nf_ne_annotate_proofs_upto_proofs W). Qed.
