(** * The Group of an Eliminator

    An eliminator as written carries no group and no uniform parameters
    ([a_elim None nil m Bks M]).  The typed fill ([TypedElab.Fill]) reads
    both off its scrutinee's inferred, normalised type [nf_indty pc k Rs]:
    [elim_target] lists every reading of the eliminator that fits its
    blocks as written (their number, the block marked [at], each block's
    constructor names), and the eliminator is filled when exactly one
    reading fits.

    - The own reading: the eliminator of the group [pc] of the scrutinee's
      type, at its declared member [k], the uniform parameters the first
      [ind_nu] of [Rs].
    - A view reading: for a group [q] other than [pc] with a type former
      in the uniform arguments of the scrutinee's type (its first
      occurrence, in pre-order), whose member [m] (the block marked [at])
      is a view of [(pc, k)]: the eliminator of [q], the uniform
      parameters the first [ind_nu] arguments of that occurrence,
      strengthened past the binders it is under.

    For [ts : List (Rose ℕ)], one block with branches [nil] and [cons] is
    List's own eliminator at [Us = [Rose ℕ]]; two blocks with branches
    [node], then [nil] and [cons] at the second, are Rose's eliminator at
    its view [List (Rose A)], at [Us = [ℕ]].  Two readings that both fit
    are rejected ([elim_target_ambiguous]); none is [elim_target_none].  Nothing is chosen
    by precedence or by an annotation: an annotation is checked against
    the reading by typing, by conversion. *)

From Stdlib Require Import List String Bool Arith.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.Inductives Require Import Group.
Import ListNotations.
Import Syntax_Notations.

(** The type formers occurring in a normal form, in pre-order (leftmost,
    outermost first), each with the number of binders it is under and its
    arguments. *)
Fixpoint nf_formers (d : nat) (W : nf) {struct W} : list (qname * nat * list exp) :=
  match W with
  | nf_pi A B => nf_formers d A ++ nf_formers (S d) B
  | nf_fn A M => nf_formers d A ++ nf_formers (S d) M
  | nf_indty p _ Ms => (p, d, List.map nf_to_exp Ms) :: List.flat_map (nf_formers d) Ms
  | nf_con _ _ _ Ms | nf_record _ Ms => List.flat_map (nf_formers d) Ms
  | nf_tuple _ Ms _ Ns => List.flat_map (nf_formers d) Ms ++ List.flat_map (nf_formers d) Ns
  | _ => nil
  end.

(** What [elim_target] finds. *)
Inductive elim_target_result : Set :=
(** Exactly one reading fits: its group and its uniform parameters *)
| elim_target_one : qname -> list exp -> elim_target_result
(** Several readings fit, each its group and its uniform parameters; the
    eliminator is rejected, naming them *)
| elim_target_ambiguous : list (qname * list exp) -> elim_target_result
(** No reading fits *)
| elim_target_none : elim_target_result.

Section ElimTarget.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** Whether the blocks as written are those of the group [D]: one per
      member before the record views ([ind_nblk]), each with one branch
      per constructor of its member, by name, in order. *)
  Definition blocks_fit (D : ind_decl) (Bks : list eblock) : bool :=
    Nat.eqb (List.length Bks) (ind_nblk D) &&
    List.forallb (fun Mb : prod imember eblock =>
      if list_eq_dec string_dec (List.map fst (im_cons (fst Mb))) (List.map (fun b => fst (fst b)) (eb_brs (snd Mb)))
      then true else false)
      (List.combine (ind_members D) Bks).

  (** The own reading: the eliminator of the scrutinee type's own group
      [pc], at its declared member [k], which is the block marked [at]
      ([m]); its uniform parameters are the first [ind_nu] arguments. *)
  Definition own_target (pc : qname) (k : nat) (Rs : list nf) (m : nat) (Bks : list eblock) : option (qname * list exp) :=
    match ind_lookup Θ Ξ pc with
    | Some D =>
        if Nat.eqb m k && Nat.ltb k (ind_ndecl D) && blocks_fit D Bks
        then Some (pc, List.firstn (ind_nu D) (List.map nf_to_exp Rs))
        else None
    | None => None
    end.

  (** Whether the member [m] of [D] is a view of the declared member [k]
      of the group at [pc]. *)
  Definition view_of (D : ind_decl) (m : nat) (pc : qname) (k : nat) : bool :=
    match ind_member D m with
    | Some Mm =>
        match im_head Mm with
        | mh_view qc k' _ _ => (if qname_eq_dec qc pc then true else false) && Nat.eqb k' k
        | mh_decl _ | mh_record _ _ _ => false
        end
    | None => false
    end.

  (** The view readings, from the type formers [os] met in the uniform
      arguments of the scrutinee's type: for each group [q] other than
      [pc], at its first occurrence only, whose member [m] is a view of
      [(pc, k)] and whose blocks fit, [q] and the first [ind_nu] arguments
      of that occurrence, strengthened past the binders they are under.
      [seen] lists the groups met already.  The first occurrence
      suffices: a view's type has the group's uniform arguments the same
      at every occurrence, so if any occurrence gives a reading that
      type-checks, the first one gives the same [Us]. *)
  Fixpoint view_targets (pc : qname) (k m : nat) (Bks : list eblock) (seen : list qname)
      (os : list (qname * nat * list exp)) : list (qname * list exp) :=
    match os with
    | nil => nil
    | (pq, d, As) :: os' =>
        if qname_eq_dec pq pc then view_targets pc k m Bks seen os' else
        if List.existsb (fun s => if qname_eq_dec s pq then true else false) seen
        then view_targets pc k m Bks seen os' else
        let rest := view_targets pc k m Bks (pq :: seen) os' in
        match ind_lookup Θ Ξ pq with
        | Some D =>
            if view_of D m pc k && blocks_fit D Bks
            then match img_pats (List.repeat true d) (List.firstn (ind_nu D) As) with
                 | Some Us => (pq, Us) :: rest
                 | None => rest
                 end
            else rest
        | None => rest
        end
    end.

  (** Every reading that fits the blocks [Bks], the block [m] marked
      [at], of an eliminator whose scrutinee's type normalises to
      [nf_indty pc k Rs]: the own one, then the view ones. *)
  Definition elim_readings (pc : qname) (k : nat) (Rs : list nf) (m : nat) (Bks : list eblock) : list (qname * list exp) :=
    let own := match own_target pc k Rs m Bks with Some r => r :: nil | None => nil end in
    match ind_lookup Θ Ξ pc with
    | Some Dc => own ++ view_targets pc k m Bks nil (List.flat_map (nf_formers 0) (List.firstn (ind_nu Dc) Rs))
    | None => own
    end.

  (** The group and the uniform parameters of the eliminator: exactly one
      reading fits, several do, or none does. *)
  Definition elim_target (pc : qname) (k : nat) (Rs : list nf) (m : nat) (Bks : list eblock) : elim_target_result :=
    match elim_readings pc k Rs m Bks with
    | nil => elim_target_none
    | (p, Us) :: nil => elim_target_one p Us
    | rs => elim_target_ambiguous rs
    end.

  (** One reading at most is the eliminator's. *)
  Lemma elim_target_functional : forall pc k Rs m Bks p1 Us1 p2 Us2,
      elim_target pc k Rs m Bks = elim_target_one p1 Us1 -> elim_target pc k Rs m Bks = elim_target_one p2 Us2 ->
      p1 = p2 /\ Us1 = Us2.
  Proof. intros * H1 H2; rewrite H1 in H2; injection H2; auto. Qed.
End ElimTarget.

(** [elim_target] reads the global context through [ind_lookup] alone. *)
Lemma elim_target_lookup_ext : forall Θ Ξ Θ' Ξ', (forall p, ind_lookup Θ Ξ p = ind_lookup Θ' Ξ' p) ->
    forall pc k Rs m Bks, elim_target Θ Ξ pc k Rs m Bks = elim_target Θ' Ξ' pc k Rs m Bks.
Proof.
  intros * He pc k Rs m Bks.
  assert (Hv : forall seen os, view_targets Θ Ξ pc k m Bks seen os = view_targets Θ' Ξ' pc k m Bks seen os).
  { intros seen os; revert seen; induction os as [| [[pq d] As] os IH]; intros seen; cbn; [ reflexivity |].
    rewrite !IH, He; reflexivity. }
  unfold elim_target, elim_readings, own_target; rewrite !He.
  destruct (ind_lookup Θ' Ξ' pc); [ rewrite Hv |]; reflexivity.
Qed.
