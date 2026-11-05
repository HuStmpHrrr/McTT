From Stdlib Require Import Ascii Lia List PeanoNat String.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** * Canonical Levels

    A level is flat: [max (c, k₁ + a₁, …, kₙ + aₙ)], a constant and a finite
    multiset of atoms under offsets, where an atom is a neutral normal form.
    Evaluation only flattens, so the same level has many flat forms; readback
    canonicalises, and the canonical form is unique:

    - the atoms are strictly sorted by [ne_cmp] and so without repetition,
      duplicates having been merged at the larger offset;
    - the constant is [0] unless it exceeds every offset, a smaller one being
      dominated.

    [lvl_canon_iff]: two levels have the same canonical form exactly when they
    agree under every assignment of ordinals below ω² to atoms.  That is the
    uniqueness-of-normal-forms theorem for levels, and with it the level
    equations ([maxl] is a semilattice, [succl] distributes over it, and a
    level is below its successor) hold on canonical forms.  [lvl_le] is the
    decidable order the universe subtyping rule uses. *)

(** ** A Total Order on Normal Forms

    The order is structural, with variables first by de Bruijn index; it is
    obtained by coding a normal form into a tree of naturals, and ordering
    those lexicographically.  Only the three properties of a strict total
    order are needed, so they are proved once for the trees and transported
    along the coding, which is injective.

    A tree node is [code_tree_node lbl child sibling]: the coding is first child,
    next sibling, so the children of a node are its [sibling]-chain. *)
Inductive code_tree : Set :=
| code_tree_nil : code_tree
| code_tree_node : nat -> code_tree -> code_tree -> code_tree.

Fixpoint lt_cmp (s t : code_tree) : comparison :=
  match s, t with
  | code_tree_nil, code_tree_nil => Eq
  | code_tree_nil, _ => Lt
  | _, code_tree_nil => Gt
  | code_tree_node a c r, code_tree_node b c' r' =>
      match Nat.compare a b with
      | Eq => match lt_cmp c c' with
             | Eq => lt_cmp r r'
             | x => x
             end
      | x => x
      end
  end.

Lemma lt_cmp_eq : forall s t, lt_cmp s t = Eq <-> s = t.
Proof.
  induction s as [| a c IHc r IHr]; intros [| b c' r']; cbn; split; intros H;
    try discriminate; try reflexivity.
  - destruct (Nat.compare_spec a b); try discriminate.
    destruct (lt_cmp c c') eqn:E; try discriminate.
    apply IHc in E; apply IHr in H; subst; reflexivity.
  - injection H as -> -> ->.
    rewrite Nat.compare_refl.
    assert (lt_cmp c' c' = Eq) as -> by (apply IHc; reflexivity).
    apply IHr; reflexivity.
Qed.

Lemma lt_cmp_refl : forall s, lt_cmp s s = Eq.
Proof. intros; apply lt_cmp_eq; reflexivity. Qed.

Lemma lt_cmp_opp : forall s t, lt_cmp t s = CompOpp (lt_cmp s t).
Proof.
  induction s as [| a c IHc r IHr]; intros [| b c' r']; cbn; try reflexivity.
  rewrite (Nat.compare_antisym a b), IHc.
  destruct (Nat.compare a b); cbn; try reflexivity.
  destruct (lt_cmp c c'); cbn; auto.
Qed.

Lemma lt_cmp_trans : forall s t u, lt_cmp s t = Lt -> lt_cmp t u = Lt -> lt_cmp s u = Lt.
Proof.
  induction s as [| a c IHc r IHr]; intros [| b c' r'] [| d c'' r'']; cbn;
    intros H1 H2; try discriminate; try reflexivity.
  destruct (Nat.compare_spec a b), (Nat.compare_spec b d), (Nat.compare_spec a d);
    subst; try lia; try discriminate; try reflexivity.
  destruct (lt_cmp c c') eqn:E1, (lt_cmp c' c'') eqn:E2; try discriminate.
  - apply lt_cmp_eq in E1, E2; subst.
    rewrite lt_cmp_refl; eapply IHr; eassumption.
  - apply lt_cmp_eq in E1; subst; rewrite E2; reflexivity.
  - apply lt_cmp_eq in E2; subst; rewrite E1; reflexivity.
  - rewrite (IHc _ _ E1 E2); reflexivity.
Qed.

(** The coding of strings and qualified names, which a global's neutral
    carries. *)
Fixpoint str_code (x : string) (t : code_tree) : code_tree :=
  match x with
  | EmptyString => code_tree_node 0 code_tree_nil t
  | String ch r => code_tree_node (S (nat_of_ascii ch)) code_tree_nil (str_code r t)
  end.

Fixpoint strings_code (l : list string) (t : code_tree) : code_tree :=
  match l with
  | nil => code_tree_node 0 code_tree_nil t
  | x :: r => code_tree_node 1 (str_code x code_tree_nil) (strings_code r t)
  end.

(** A qualified name is coded by its two lists.  Both codings are stuck
    fixpoints on a projection, so [injection] stops there and
    [qname_code_inj] takes the hypothesis apart. *)
#[global] Arguments str_code : simpl never.
#[global] Arguments strings_code : simpl never.

Lemma str_code_inj : forall x y t t', str_code x t = str_code y t' -> x = y /\ t = t'.
Proof.
  induction x as [| ch x IH]; intros [| ch' y] t t' H; cbn in H; injection H as; subst;
    try discriminate; try (split; reflexivity).
  match goal with Hs : str_code _ _ = str_code _ _ |- _ => apply IH in Hs as [-> ->] end.
  split; [| reflexivity].
  f_equal.
  rewrite <- (ascii_nat_embedding ch), <- (ascii_nat_embedding ch'); congruence.
Qed.

Lemma strings_code_inj : forall l l' t t', strings_code l t = strings_code l' t' -> l = l' /\ t = t'.
Proof.
  induction l as [| x l IH]; intros [| y l'] t t' H; cbn in H; injection H as; subst;
    try discriminate; try (split; reflexivity).
  match goal with H : str_code _ _ = str_code _ _ |- _ => apply str_code_inj in H as [-> _] end.
  match goal with H : strings_code _ _ = strings_code _ _ |- _ => apply IH in H as [-> ->] end.
  split; reflexivity.
Qed.

Lemma qname_code_inj : forall p p',
    strings_code (q_unit p) (strings_code (q_chain p) code_tree_nil)
    = strings_code (q_unit p') (strings_code (q_chain p') code_tree_nil) -> p = p'.
Proof.
  intros [u ch] [u' ch'] H; cbn in H.
  apply strings_code_inj in H as [-> H]; apply strings_code_inj in H as [-> _]; reflexivity.
Qed.

(** The coding of a list, each element by [f]: the elements are the
    children of [1]-nodes, and the list ends in a [0]-node continuing with
    [t]. *)
Fixpoint list_code {A : Set} (f : A -> code_tree) (l : list A) (t : code_tree) : code_tree :=
  match l with
  | nil => code_tree_node 0 code_tree_nil t
  | x :: r => code_tree_node 1 (f x) (list_code f r t)
  end.

(** The coding of a kind. *)
Definition abs_kind_code (κ : abs_kind) : nat :=
  match κ with ak_relevant => 0 | ak_propositional => 1 | ak_level => 2 end.

(** The coding of the records normal forms hold, given that of what they
    hold.  An atom: its offset, the neutral, then its sort. *)
Definition atom_code {E : Set} (f : E -> code_tree) (a : level_atom_g E) : code_tree :=
  code_tree_node (atom_offset a) (f (atom_level a)) (code_tree_node (atom_sort a) code_tree_nil code_tree_nil).

(** A branch: its arity, its constructor, then its body. *)
Definition branch_code {E : Set} (f : E -> code_tree) (br : normal_branch_g E) : code_tree :=
  code_tree_node (branch_arity br) (str_code (branch_constructor br) code_tree_nil) (f (branch_body br)).

(** A block: its arity, its motive, then its branches. *)
Definition block_code {E : Set} (f : E -> code_tree) (b : normal_block_g E) : code_tree :=
  code_tree_node (block_arity b) (code_tree_node 0 (f (block_scrutinee_type b)) (f (block_motive b)))
    (list_code (branch_code f) (block_branches b) code_tree_nil).

(** The coding of normal forms.  The tags order the constructors; in a
    neutral, [ne_var] comes first, so variables precede every other atom and
    are ordered by their index. *)
Fixpoint nf_code (M : nf) (t : code_tree) : code_tree :=
  match M with
  | nf_typ i => code_tree_node 0 (code_tree_node i code_tree_nil code_tree_nil) t
  | nf_univ (a, b) xs =>
      code_tree_node 1 (code_tree_node a (code_tree_node b (list_code (atom_code (fun m => ne_code m code_tree_nil)) xs code_tree_nil) code_tree_nil) code_tree_nil) t
  | nf_level n => code_tree_node 2 (code_tree_node n code_tree_nil code_tree_nil) t
  | nf_level_sort => code_tree_node 22 code_tree_nil t
  | nf_lvl (a, b) xs =>
      code_tree_node 3 (code_tree_node a (code_tree_node b (list_code (atom_code (fun m => ne_code m code_tree_nil)) xs code_tree_nil) code_tree_nil) code_tree_nil) t
  | nf_True => code_tree_node 7 code_tree_nil t
  | nf_proof _ => code_tree_node 8 code_tree_nil t
  | nf_False => code_tree_node 9 code_tree_nil t
  | nf_prop => code_tree_node 17 code_tree_nil t
  | nf_and P Q => code_tree_node 19 (nf_code P (nf_code Q code_tree_nil)) t
  | nf_pi κd κc A B =>
      code_tree_node 10 (code_tree_node (abs_kind_code κd) (code_tree_node (abs_kind_code κc) code_tree_nil code_tree_nil)
                           (nf_code A (nf_code B code_tree_nil))) t
  | nf_fn A M' => code_tree_node 11 (nf_code A (nf_code M' code_tree_nil)) t
  | nf_neut m => code_tree_node 12 (ne_code m code_tree_nil) t
  | nf_indty p k Ms =>
      code_tree_node 13 (code_tree_node k (strings_code (q_unit p) (strings_code (q_chain p) code_tree_nil))
                    (list_code (fun M => nf_code M code_tree_nil) Ms code_tree_nil)) t
  | nf_con p k c Ms =>
      code_tree_node 14 (code_tree_node k (strings_code (q_unit p) (strings_code (q_chain p) code_tree_nil))
                    (code_tree_node 0 (str_code c code_tree_nil) (list_code (fun M => nf_code M code_tree_nil) Ms code_tree_nil))) t
  | nf_record p Ms =>
      code_tree_node 15 (code_tree_node 0 (strings_code (q_unit p) (strings_code (q_chain p) code_tree_nil))
                    (list_code (fun M => nf_code M code_tree_nil) Ms code_tree_nil)) t
  | nf_tuple p Ms fs Ns =>
      code_tree_node 16 (code_tree_node 0 (strings_code (q_unit p) (strings_code (q_chain p) code_tree_nil))
                    (code_tree_node 0 (strings_code fs code_tree_nil)
                       (code_tree_node 0 (list_code (fun M => nf_code M code_tree_nil) Ms code_tree_nil)
                          (list_code (fun M => nf_code M code_tree_nil) Ns code_tree_nil)))) t
  end
with ne_code (m : ne) (t : code_tree) : code_tree :=
  match m with
  | ne_var x => code_tree_node 0 (code_tree_node x code_tree_nil code_tree_nil) t
  | ne_glob p => code_tree_node 1 (strings_code (q_unit p) (strings_code (q_chain p) code_tree_nil)) t
  | ne_app m' N => code_tree_node 2 (ne_code m' (nf_code N code_tree_nil)) t
  | ne_absurd A _ => code_tree_node 4 (nf_code A code_tree_nil) t
  | ne_elim p Us m Bks m' =>
      code_tree_node 5 (code_tree_node m (strings_code (q_unit p) (strings_code (q_chain p) code_tree_nil))
                   (list_code (block_code (fun A => nf_code A code_tree_nil)) Bks
                      (ne_code m' (list_code (fun M => nf_code M code_tree_nil) Us code_tree_nil)))) t
  | ne_proj f m' => code_tree_node 6 (code_tree_node 0 (str_code f code_tree_nil) (ne_code m' code_tree_nil)) t
  end.

#[global] Arguments atom_code : simpl never.
#[global] Arguments block_code : simpl never.

(** The coding of a list determines the list up to [r] where the coding of
    its elements does: on the elements of which [P] holds, [P] saying that
    [f] determines [r] there.  The coding of a normal form ignores its
    proofs, so it determines the normal form up to them ([r] the
    comparison up to proofs). *)
Lemma list_code_inj {A : Set} (P : A -> Set) (f : A -> code_tree) (r : A -> A -> bool) : forall l,
    list_all A P l -> (forall x, P x -> forall y, f x = f y -> r x y = true) ->
    forall l' t t', list_code f l t = list_code f l' t' -> list_eqb r l l' = true /\ t = t'.
Proof.
  intros l Hl Hf; induction Hl as [| x Hx l Hl IH]; intros [| y l'] t t' H; cbn in H;
    injection H as; subst; try discriminate; [ split; reflexivity |].
  match goal with H : list_code _ _ _ = list_code _ _ _ |- _ => apply IH in H as [E ->] end.
  match goal with H : f _ = f _ |- _ => apply (Hf _ Hx) in H end.
  cbn; split; [ apply Bool.andb_true_iff; split; assumption | reflexivity ].
Qed.

Lemma atom_code_inj {E : Set} (P : E -> Set) (f : E -> code_tree) (r : E -> E -> bool) : forall a,
    level_atom_g_all E P a -> (forall x, P x -> forall y, f x = f y -> r x y = true) ->
    forall a', atom_code f a = atom_code f a' ->
    (Nat.eqb (atom_offset a) (atom_offset a') && Nat.eqb (atom_sort a) (atom_sort a') && r (atom_level a) (atom_level a'))%bool = true.
Proof.
  intros a [k s x Hx] Hf [k' s' y] H; unfold atom_code in H; cbn in H; injection H as -> H ->.
  apply (Hf _ Hx) in H; cbn; rewrite !Nat.eqb_refl, H; reflexivity.
Qed.

Lemma branch_code_inj {E : Set} (P : E -> Set) (f : E -> code_tree) (r : E -> E -> bool) : forall br,
    normal_branch_g_all E P br -> (forall x, P x -> forall y, f x = f y -> r x y = true) ->
    forall br', branch_code f br = branch_code f br' ->
    (dec_eqb String.string_dec (branch_constructor br) (branch_constructor br') &&
     Nat.eqb (branch_arity br) (branch_arity br') && r (branch_body br) (branch_body br'))%bool = true.
Proof.
  intros br [c n x Hx] Hf [c' n' y] H; unfold branch_code in H; cbn in H; injection H as -> H H'.
  apply str_code_inj in H as [-> _]; apply (Hf _ Hx) in H'; cbn; rewrite dec_eqb_refl, Nat.eqb_refl, H'; reflexivity.
Qed.

Lemma block_code_inj {E : Set} (P : E -> Set) (f : E -> code_tree) (r : E -> E -> bool) : forall b,
    normal_block_g_all E P b -> (forall x, P x -> forall y, f x = f y -> r x y = true) ->
    forall b', block_code f b = block_code f b' ->
    (Nat.eqb (block_arity b) (block_arity b') && r (block_scrutinee_type b) (block_scrutinee_type b') &&
     r (block_motive b) (block_motive b') &&
     list_eqb (fun br br' => dec_eqb String.string_dec (branch_constructor br) (branch_constructor br') &&
                             Nat.eqb (branch_arity br) (branch_arity br') && r (branch_body br) (branch_body br'))
       (block_branches b) (block_branches b'))%bool = true.
Proof.
  intros b [n z Hz x Hx brs Hbrs] Hf [n' z' y brs'] H; unfold block_code in H; cbn in H; injection H as -> Hzz H H'.
  apply (Hf _ Hz) in Hzz; apply (Hf _ Hx) in H.
  eapply list_code_inj in H' as [Ebrs _]; [| exact Hbrs |].
  - cbn; rewrite Nat.eqb_refl, Hzz, H, Ebrs; reflexivity.
  - intros br Hbr br'; eapply branch_code_inj; eassumption.
Qed.

(** The side condition of [list_code_inj] and the record lemmas at the
    elements of a normal form: an element is coded at [code_tree_nil], and the
    induction hypothesis at it says its coding is injective. *)
#[local] Ltac code_elem_inj :=
  let x := fresh "x" in let Hx := fresh "Hx" in let y := fresh "y" in let Hy := fresh "Hy" in
  intros x Hx y Hy; cbv beta in Hy;
  first [ apply Hx in Hy as [? _]; assumption
        | eapply atom_code_inj; [ exact Hx | code_elem_inj | exact Hy ]
        | eapply block_code_inj; [ exact Hx | code_elem_inj | exact Hy ] ].

(** The coding determines a normal form up to its proofs. *)
Lemma nf_ne_code_inj :
  (forall M N t t', nf_code M t = nf_code N t' -> nf_eq_upto_proofs M N /\ t = t') /\
  (forall m m' t t', ne_code m t = ne_code m' t' -> ne_eq_upto_proofs m m' /\ t = t').
Proof.
  apply nf_ne_ind.
  all: intros; match goal with
               | H : nf_code _ _ = nf_code ?N _ |- _ => destruct N
               | H : ne_code _ _ = ne_code ?N _ |- _ => destruct N
               end.
  all: repeat match goal with p : o2 |- _ => destruct p | κ : abs_kind |- _ => destruct κ end.
  all: match goal with
       | H : nf_code _ _ = nf_code _ _ |- _ => cbn in H; injection H as; subst; try discriminate
       | H : ne_code _ _ = ne_code _ _ |- _ => cbn in H; injection H as; subst; try discriminate
       end.
  all: repeat match goal with
         | H : nf_code ?M _ = nf_code _ _, IH : forall N t t', nf_code ?M t = nf_code N t' -> _ |- _ =>
             apply IH in H as [?E H]
         | H : ne_code ?M _ = ne_code _ _, IH : forall N t t', ne_code ?M t = ne_code N t' -> _ |- _ =>
             apply IH in H as [?E H]
         | H : list_code (atom_code _) _ _ = list_code _ _ _ |- _ =>
             eapply (list_code_inj _ _ (fun a a' => Nat.eqb (atom_offset a) (atom_offset a') && Nat.eqb (atom_sort a) (atom_sort a') &&
                                                     ne_eqb_upto_proofs (atom_level a) (atom_level a'))%bool) in H as [?E H];
               [| eassumption | code_elem_inj ]
         | H : list_code (block_code _) _ _ = list_code _ _ _ |- _ =>
             eapply (list_code_inj _ _ (fun b b' =>
                       Nat.eqb (block_arity b) (block_arity b') &&
                       nf_eqb_upto_proofs (block_scrutinee_type b) (block_scrutinee_type b') &&
                       nf_eqb_upto_proofs (block_motive b) (block_motive b') &&
                       list_eqb (fun br br' => dec_eqb String.string_dec (branch_constructor br) (branch_constructor br') &&
                                               Nat.eqb (branch_arity br) (branch_arity br') &&
                                               nf_eqb_upto_proofs (branch_body br) (branch_body br'))
                         (block_branches b) (block_branches b'))%bool) in H as [?E H];
               [| eassumption | code_elem_inj ]
         | H : list_code _ _ _ = list_code _ _ _ |- _ =>
             eapply (list_code_inj _ _ nf_eqb_upto_proofs) in H as [?E H]; [| eassumption | code_elem_inj ]
         | H : str_code _ _ = str_code _ _ |- _ => apply str_code_inj in H as [-> H]
         | H : strings_code _ _ = strings_code _ _ |- _ => apply qname_code_inj in H as ->
         | H : strings_code _ _ = strings_code _ _ |- _ => apply strings_code_inj in H as [-> H]
         | H : code_tree_node _ _ _ = code_tree_node _ _ _ |- _ => injection H as; subst
       end.
  all: try discriminate.
  all: unfold nf_eq_upto_proofs, ne_eq_upto_proofs in *; cbn [nf_eqb_upto_proofs ne_eqb_upto_proofs];
    split; [ eqb_split; rewrite ?Nat.eqb_refl, ?dec_eqb_refl; try reflexivity; try assumption | congruence ].
Qed.

Lemma nf_code_inj : forall M N t t', nf_code M t = nf_code N t' -> nf_eq_upto_proofs M N /\ t = t'.
Proof. apply nf_ne_code_inj. Qed.

Lemma ne_code_inj : forall m m' t t', ne_code m t = ne_code m' t' -> ne_eq_upto_proofs m m' /\ t = t'.
Proof. apply nf_ne_code_inj. Qed.

(** Normal forms equal up to their proofs have one coding: the coding
    ignores proofs. *)
Lemma list_code_eqb {A : Set} (P : A -> Set) (f : A -> code_tree) (r : A -> A -> bool) : forall l,
    list_all A P l -> (forall x, P x -> forall y, r x y = true -> f x = f y) ->
    forall l' t, list_eqb r l l' = true -> list_code f l t = list_code f l' t.
Proof.
  intros l Hl Hf; induction Hl as [| x Hx l Hl IH]; intros [| y l'] t H; cbn in *; try discriminate; [ reflexivity |].
  apply Bool.andb_true_iff in H as [H1 H2]; rewrite (Hf _ Hx _ H1), (IH _ _ H2); reflexivity.
Qed.

Lemma nf_ne_code_upto :
  (forall M N t, nf_eq_upto_proofs M N -> nf_code M t = nf_code N t) /\
  (forall m m' t, ne_eq_upto_proofs m m' -> ne_code m t = ne_code m' t).
Proof.
  unfold nf_eq_upto_proofs, ne_eq_upto_proofs.
  apply nf_ne_ind; intros;
    lazymatch goal with
    | H : nf_eqb_upto_proofs _ ?N = true |- _ => destruct N
    | H : ne_eqb_upto_proofs _ ?N = true |- _ => destruct N
    end;
    cbn [nf_eqb_upto_proofs ne_eqb_upto_proofs] in *; try discriminate; eqb_split; eqb_leaves; subst;
    repeat match goal with p : o2 |- _ => destruct p | κ : abs_kind |- _ => destruct κ end;
    cbn [nf_code ne_code]; try reflexivity.
  all: repeat match goal with
         | IH : forall N t, nf_eqb_upto_proofs ?M N = true -> _, H : nf_eqb_upto_proofs ?M ?N = true |- _ =>
             rewrite (IH N _ H); clear H
         | IH : forall N t, ne_eqb_upto_proofs ?M N = true -> _, H : ne_eqb_upto_proofs ?M ?N = true |- _ =>
             rewrite (IH N _ H); clear H
         | Hl : list_all _ _ ?l, H : list_eqb _ ?l ?l' = true |- _ =>
             erewrite (list_code_eqb _ _ _ l Hl _ l' _ H); clear H
         end; try reflexivity.
  Unshelve.
  all: first
    [ intros x Hx y Hxy; apply Hx; exact Hxy
    | intros a Ha b Hab; destruct Ha as [k s x Hx]; destruct b as [k' s' y]; unfold atom_code; cbn in *;
      eqb_split; eqb_leaves; subst; rewrite (Hx _ _ ltac:(eassumption)); reflexivity
    | intros b0 Hb b1 Hbb; destruct Hb as [n' z Hz x Hx brs Hbrs]; destruct b1 as [n'' z' x' brs']; unfold block_code; cbn in *;
      eqb_split; eqb_leaves; subst; rewrite (Hz _ _ ltac:(eassumption)), (Hx _ _ ltac:(eassumption));
      f_equal; eapply list_code_eqb; [ exact Hbrs | | eassumption ];
      intros br Hbr br' Hbr'; destruct Hbr as [c n3 y Hy]; destruct br' as [c' n4 y']; unfold branch_code; cbn in *;
      eqb_split; eqb_leaves; subst; rewrite (Hy _ _ ltac:(eassumption)); reflexivity ].
Qed.

Lemma ne_code_upto : forall m m' t, ne_eq_upto_proofs m m' -> ne_code m t = ne_code m' t.
Proof. apply nf_ne_code_upto. Qed.

(** The order on the atoms of a level.  It ignores their proofs. *)
Definition ne_cmp (m m' : ne) : comparison := lt_cmp (ne_code m code_tree_nil) (ne_code m' code_tree_nil).

(** Two neutrals are equal in the order exactly when they are equal up to
    their proofs. *)
Lemma ne_cmp_eq : forall m m', ne_cmp m m' = Eq <-> ne_eq_upto_proofs m m'.
Proof.
  intros; unfold ne_cmp; rewrite lt_cmp_eq; split.
  - intros H; apply ne_code_inj in H as [? _]; assumption.
  - intros H; apply ne_code_upto; exact H.
Qed.

Lemma ne_cmp_refl : forall m, ne_cmp m m = Eq.
Proof. intros; apply ne_cmp_eq; reflexivity. Qed.

(** Neutrals equal in the order compare alike to every other. *)
Lemma ne_cmp_eq_compat : forall m m' n, ne_cmp m m' = Eq -> ne_cmp m n = ne_cmp m' n.
Proof. intros * H; unfold ne_cmp in *; apply lt_cmp_eq in H; rewrite H; reflexivity. Qed.

Lemma ne_cmp_eq_compat_r : forall m n n', ne_cmp n n' = Eq -> ne_cmp m n = ne_cmp m n'.
Proof. intros * H; unfold ne_cmp in *; apply lt_cmp_eq in H; rewrite H; reflexivity. Qed.

Lemma ne_cmp_opp : forall m m', ne_cmp m' m = CompOpp (ne_cmp m m').
Proof. intros; apply lt_cmp_opp. Qed.

Lemma ne_cmp_trans : forall m m' m'', ne_cmp m m' = Lt -> ne_cmp m' m'' = Lt -> ne_cmp m m'' = Lt.
Proof. intros; eapply lt_cmp_trans; eassumption. Qed.

(** ** Levels and Their Canonical Forms

    A level is a constant, an ordinal below ω², and a list of atoms under
    finite offsets, each atom with its sort.  An atom of sort [s] is a level
    of type [Level@s], so it ranges over the ordinals below ω·(s+1):
    [lvl_eval ν] evaluates a level at an assignment [ν] of ordinals to atoms,
    and the assignments that matter are the admissible ones ([lvl_adm]),
    which respect the sorts.  Two levels are equal exactly when they agree at
    every admissible assignment.  A constant [c] absorbs every atom of a sort
    below [fst c] ([max (ω, u + 5)] is [ω] for [u : Level@0]), and no other:
    an atom of sort [s ≥ fst c] can be [ω·s + N] for any [N].  The type
    [lvl] itself is in [Core.Syntactic.Syntax], with the normal forms it
    indexes. *)

(** The order on the atoms: by the neutral, then by the sort. *)
Definition at_cmp (a : ne) (s : nat) (b : ne) (t : nat) : comparison :=
  match ne_cmp a b with Eq => Nat.compare s t | c => c end.

Lemma at_cmp_eq : forall a s b t, at_cmp a s b t = Eq <-> ne_eq_upto_proofs a b /\ s = t.
Proof.
  intros; unfold at_cmp; destruct (ne_cmp a b) eqn:E.
  - apply ne_cmp_eq in E; rewrite Nat.compare_eq_iff; intuition.
  - split; [ discriminate | intros [H _]; apply ne_cmp_eq in H; congruence ].
  - split; [ discriminate | intros [H _]; apply ne_cmp_eq in H; congruence ].
Qed.

(** Atoms equal in the order compare alike to every other. *)
Lemma at_cmp_eq_compat : forall a s b t c u, at_cmp a s b t = Eq -> at_cmp a s c u = at_cmp b t c u.
Proof.
  intros * H; unfold at_cmp in *; destruct (ne_cmp a b) eqn:E; try discriminate.
  apply Nat.compare_eq_iff in H as ->; rewrite (ne_cmp_eq_compat _ _ _ E); reflexivity.
Qed.

Lemma at_cmp_refl : forall a s, at_cmp a s a s = Eq.
Proof. intros; apply at_cmp_eq; split; reflexivity. Qed.

Lemma at_cmp_opp : forall a s b t, at_cmp b t a s = CompOpp (at_cmp a s b t).
Proof.
  intros; unfold at_cmp; rewrite (ne_cmp_opp a b).
  destruct (ne_cmp a b); cbn; [ apply Nat.compare_antisym | reflexivity .. ].
Qed.

Lemma at_cmp_trans : forall a s b t c u,
    at_cmp a s b t = Lt -> at_cmp b t c u = Lt -> at_cmp a s c u = Lt.
Proof.
  intros * H1 H2; unfold at_cmp in *.
  destruct (ne_cmp a b) eqn:E1, (ne_cmp b c) eqn:E2; try discriminate.
  - rewrite (ne_cmp_eq_compat _ _ _ E1), E2.
    apply Nat.compare_lt_iff in H1, H2; apply Nat.compare_lt_iff; lia.
  - rewrite (ne_cmp_eq_compat _ _ _ E1), E2; reflexivity.
  - rewrite <- (ne_cmp_eq_compat_r a _ _ E2), E1; reflexivity.
  - rewrite (ne_cmp_trans _ _ _ E1 E2); reflexivity.
Qed.

Fixpoint level_atoms_eval (ν : ne -> nat -> o2) (xs : list level_atom) : o2 :=
  match xs with
  | nil => ordinal_zero
  | mk_level_atom k s a :: r => ordinal_max (ordinal_add_nat k (ν a s)) (level_atoms_eval ν r)
  end.

Definition lvl_eval (ν : ne -> nat -> o2) (l : lvl) : o2 := ordinal_max (fst l) (level_atoms_eval ν (snd l)).

(** An assignment is admissible when it respects the sorts and the
    irrelevance of proofs. *)
Record lvl_adm (ν : ne -> nat -> o2) : Prop := mk_lvl_adm
  { (** An atom of sort [s] is below [ω·(s+1)] *)
    lvl_adm_sort : forall a s, fst (ν a s) <= s
    (** Atoms equal up to their proofs have the same value *)
  ; lvl_adm_upto_proofs : forall a b s, ne_eq_upto_proofs a b -> ν a s = ν b s }.

Lemma lvl_adm_zero : lvl_adm (fun _ _ => ordinal_zero).
Proof. constructor; intros; cbn; [ lia | reflexivity ]. Qed.

Definition lvl_zero : lvl := (ordinal_zero, nil).

Fixpoint level_atoms_suc (xs : list level_atom) : list level_atom :=
  match xs with
  | nil => nil
  | mk_level_atom k s a :: r => mk_level_atom (S k) s a :: level_atoms_suc r
  end.

Definition lvl_suc (l : lvl) : lvl := (ordinal_succ (fst l), level_atoms_suc (snd l)).

Definition lvl_max (l l' : lvl) : lvl := (ordinal_max (fst l) (fst l'), snd l ++ snd l').

(** Insertion into a sorted list of atoms, merging at the larger offset.
    The atom is inserted as it is.  The order ignores proofs, so of the
    atoms equal up to them a canonical level keeps the one already there. *)
Fixpoint level_atoms_insert (k s : nat) (a : ne) (ys : list level_atom) : list level_atom :=
  match ys with
  | nil => mk_level_atom k s a :: nil
  | mk_level_atom k' t b :: r =>
      match at_cmp a s b t with
      | Lt => mk_level_atom k s a :: ys
      | Eq => mk_level_atom (Nat.max k k') t b :: r
      | Gt => mk_level_atom k' t b :: level_atoms_insert k s a r
      end
  end.

Fixpoint level_atoms_sort (xs : list level_atom) : list level_atom :=
  match xs with
  | nil => nil
  | mk_level_atom k s a :: r => level_atoms_insert k s a (level_atoms_sort r)
  end.

Fixpoint level_atoms_max_offset (xs : list level_atom) : nat :=
  match xs with
  | nil => 0
  | mk_level_atom k _ _ :: r => Nat.max k (level_atoms_max_offset r)
  end.

(** The atoms a constant does not absorb: those of a sort at least its
    tier. *)
Fixpoint level_atoms_keep (c : o2) (xs : list level_atom) : list level_atom :=
  match xs with
  | nil => nil
  | mk_level_atom k s a :: r => if fst c <=? s then mk_level_atom k s a :: level_atoms_keep c r else level_atoms_keep c r
  end.

(** A constant is dominated by atoms whose largest offset is [m] when it is
    at most [m]: that is the least value of the atoms, at the assignment of
    [0] to every atom.  A constant [≥ ω] is never dominated. *)
Definition o2_dominated (c : o2) (m : nat) : bool := (fst c =? 0) && (snd c <=? m).

Lemma o2_dominated_spec : forall c m, o2_dominated c m = true <-> ordinal_le c (ordinal_of_nat m).
Proof.
  intros [a b] m; unfold o2_dominated; cbn.
  rewrite Bool.andb_true_iff, Nat.eqb_eq, Nat.leb_le; ordinal_solve.
Qed.

(** The canonical form: sort and merge the atoms, drop the atoms the constant
    absorbs, then drop the constant if the atoms dominate it. *)
Definition lvl_canon (l : lvl) : lvl :=
  let ys := level_atoms_keep (fst l) (level_atoms_sort (snd l)) in
  (if o2_dominated (fst l) (level_atoms_max_offset ys) then ordinal_zero else fst l, ys).

Lemma level_atoms_eval_insert : forall ν k s a ys, lvl_adm ν ->
    level_atoms_eval ν (level_atoms_insert k s a ys) = ordinal_max (ordinal_add_nat k (ν a s)) (level_atoms_eval ν ys).
Proof.
  intros ν k s a ys Hadm.
  induction ys as [| [k' t b] r IH]; cbn; [ reflexivity |].
  destruct (at_cmp a s b t) eqn:E; cbn.
  - apply at_cmp_eq in E as [Eab ->]; rewrite (lvl_adm_upto_proofs _ Hadm _ _ t Eab).
    generalize (ν b t) (level_atoms_eval ν r); intros; ordinal_solve.
  - reflexivity.
  - rewrite IH; generalize (ν a s) (ν b t) (level_atoms_eval ν r); intros; ordinal_solve.
Qed.

Lemma level_atoms_eval_sort : forall ν xs, lvl_adm ν -> level_atoms_eval ν (level_atoms_sort xs) = level_atoms_eval ν xs.
Proof.
  intros ν xs Hadm; induction xs as [| [k s a] r IH]; cbn; [ reflexivity | rewrite level_atoms_eval_insert, IH by exact Hadm; reflexivity ].
Qed.

(** The dropped atoms are absorbed by the constant. *)
Lemma level_atoms_eval_keep : forall ν c ys, lvl_adm ν -> ordinal_max c (level_atoms_eval ν (level_atoms_keep c ys)) = ordinal_max c (level_atoms_eval ν ys).
Proof.
  intros ν c ys Hadm; induction ys as [| [k s a] r IH]; cbn [level_atoms_keep level_atoms_eval]; [ reflexivity |].
  pose proof (lvl_adm_sort _ Hadm a s) as Hs.
  destruct (Nat.leb_spec (fst c) s); cbn [level_atoms_eval].
  - revert IH; generalize (level_atoms_eval ν (level_atoms_keep c r)) (level_atoms_eval ν r); intros; ordinal_solve.
  - revert IH Hs; generalize (level_atoms_eval ν (level_atoms_keep c r)) (level_atoms_eval ν r) (ν a s); intros; ordinal_solve.
Qed.

Lemma level_atoms_max_offset_le_eval : forall ν xs, ordinal_le (ordinal_of_nat (level_atoms_max_offset xs)) (level_atoms_eval ν xs).
Proof.
  induction xs as [| [k s a] r IH]; cbn; [ ordinal_solve |].
  revert IH; generalize (ν a s) (level_atoms_eval ν r) (level_atoms_max_offset r); intros; ordinal_solve.
Qed.

Lemma lvl_canon_eval : forall ν l, lvl_adm ν -> lvl_eval ν (lvl_canon l) = lvl_eval ν l.
Proof.
  intros ν [c xs] Hadm; unfold lvl_canon, lvl_eval; cbn [fst snd].
  rewrite <- (level_atoms_eval_sort ν xs Hadm), <- (level_atoms_eval_keep ν c _ Hadm).
  pose proof (level_atoms_max_offset_le_eval ν (level_atoms_keep c (level_atoms_sort xs))) as H.
  destruct (o2_dominated c (level_atoms_max_offset (level_atoms_keep c (level_atoms_sort xs)))) eqn:E; [| reflexivity ].
  apply o2_dominated_spec in E.
  revert H E; generalize (level_atoms_eval ν (level_atoms_keep c (level_atoms_sort xs))) (level_atoms_max_offset (level_atoms_keep c (level_atoms_sort xs))); intros; ordinal_solve.
Qed.

(** Strictly sorted: every later atom is greater. *)
Fixpoint level_atoms_In (k s : nat) (a : ne) (xs : list level_atom) : Prop :=
  match xs with
  | nil => False
  | mk_level_atom k' t b :: r => (k = k' /\ s = t /\ ne_eq_upto_proofs a b) \/ level_atoms_In k s a r
  end.

(** The first atom of a list is in it. *)
Lemma level_atoms_In_head : forall k s a r, level_atoms_In k s a (mk_level_atom k s a :: r).
Proof. intros; left; split; [ reflexivity | split; [ reflexivity | apply nf_ne_eqb_upto_proofs_refl ] ]. Qed.

Fixpoint level_atoms_sorted (ys : list level_atom) : Prop :=
  match ys with
  | nil => True
  | mk_level_atom _ s a :: r => (forall k t b, level_atoms_In k t b r -> at_cmp a s b t = Lt) /\ level_atoms_sorted r
  end.

Lemma level_atoms_insert_atoms : forall k s a ys k' t b,
    level_atoms_In k' t b (level_atoms_insert k s a ys) -> (t = s /\ ne_eq_upto_proofs b a) \/ exists k'', level_atoms_In k'' t b ys.
Proof.
  induction ys as [| [k0 u c] r IH]; cbn; intros k' t b H.
  - destruct H as [(_ & -> & Eb) | []]; auto.
  - destruct (at_cmp a s c u) eqn:E; cbn in H.
    + destruct H as [(_ & -> & Eb) | H]; [ right; exists k0; left; auto | right; eauto ].
    + destruct H as [(_ & -> & Eb) | H]; [ auto | right; eauto ].
    + destruct H as [(_ & -> & Eb) | H]; [ right; exists k0; left; auto |].
      destruct (IH _ _ _ H) as [[-> Eb] | [k'' Hin]]; [ auto | right; eauto ].
Qed.

(** The order sees an atom up to its proofs. *)
Lemma at_cmp_upto_l : forall a a' s b t, ne_eq_upto_proofs a a' -> at_cmp a s b t = at_cmp a' s b t.
Proof. intros * E; unfold at_cmp, ne_cmp; rewrite (ne_code_upto _ _ _ E); reflexivity. Qed.

Lemma at_cmp_upto_r : forall a s b b' t, ne_eq_upto_proofs b b' -> at_cmp a s b t = at_cmp a s b' t.
Proof. intros * E; unfold at_cmp, ne_cmp; rewrite (ne_code_upto _ _ _ E); reflexivity. Qed.

Lemma level_atoms_insert_sorted : forall k s a ys, level_atoms_sorted ys -> level_atoms_sorted (level_atoms_insert k s a ys).
Proof.
  induction ys as [| [k0 u c] r IH]; cbn; intros Hs.
  - split; [ intros ? ? ? [] | exact I ].
  - destruct Hs as [Hc Hr].
    destruct (at_cmp a s c u) eqn:E; cbn.
    + split; assumption.
    + split; [| split; auto ].
      intros k' t b [(_ & -> & Eb) | H];
        [ rewrite (at_cmp_upto_r _ _ _ _ _ Eb); exact E | eapply at_cmp_trans; eauto ].
    + split; [| auto ].
      intros k' t b H; destruct (level_atoms_insert_atoms _ _ _ _ _ _ _ H) as [[-> Eb] | [k'' Hin]]; eauto.
      rewrite (at_cmp_upto_r _ _ _ _ _ Eb), at_cmp_opp, E; reflexivity.
Qed.

Lemma level_atoms_sort_sorted : forall xs, level_atoms_sorted (level_atoms_sort xs).
Proof. induction xs as [| [k s a] r IH]; cbn; [ exact I | apply level_atoms_insert_sorted; exact IH ]. Qed.

Lemma level_atoms_keep_In : forall c ys k s a, level_atoms_In k s a (level_atoms_keep c ys) -> level_atoms_In k s a ys /\ fst c <= s.
Proof.
  intros c; induction ys as [| [k0 t b] r IH]; cbn [level_atoms_keep]; intros k s a H; [ destruct H |].
  destruct (Nat.leb_spec (fst c) t); cbn in H |- *.
  - destruct H as [(-> & -> & Hab) | H]; [ split; [ left; auto | auto ] |].
    apply IH in H as [? ?]; auto.
  - apply IH in H as [? ?]; auto.
Qed.

Lemma level_atoms_keep_sorted : forall c ys, level_atoms_sorted ys -> level_atoms_sorted (level_atoms_keep c ys).
Proof.
  intros c; induction ys as [| [k t b] r IH]; cbn [level_atoms_keep]; intros Hs; [ exact I |].
  destruct Hs as [Hb Hr].
  destruct (Nat.leb_spec (fst c) t); [| apply IH; exact Hr ].
  cbn [level_atoms_sorted]; split; [| apply IH; exact Hr ].
  intros k' t' b' Hin; apply level_atoms_keep_In in Hin as [Hin _]; eapply Hb; eauto.
Qed.

(** A canonical level: its atoms sorted, each of a sort the constant's tier
    does not exceed, and its constant zero or above every offset. *)
Record lvl_canonical (l : lvl) : Prop := mk_lvl_canonical
  { (** The atoms are strictly sorted *)
    lvl_canonical_sorted : level_atoms_sorted (snd l)
    (** No atom is of a sort below the constant's tier *)
  ; lvl_canonical_sorts : forall k s a, level_atoms_In k s a (snd l) -> fst (fst l) <= s
    (** The constant is zero or above every offset *)
  ; lvl_canonical_const : fst l = ordinal_zero \/ ordinal_lt (ordinal_of_nat (level_atoms_max_offset (snd l))) (fst l) }.

Lemma lvl_canon_canonical : forall l, lvl_canonical (lvl_canon l).
Proof.
  intros [c xs]; unfold lvl_canon; constructor; cbn [fst snd];
    [ apply level_atoms_keep_sorted, level_atoms_sort_sorted | | ];
  destruct (o2_dominated c (level_atoms_max_offset (level_atoms_keep c (level_atoms_sort xs)))) eqn:E; cbn [fst].
  - intros; cbn; lia.
  - intros k s a H; apply level_atoms_keep_In in H as [_ H]; exact H.
  - left; reflexivity.
  - right.
    assert (~ ordinal_le c (ordinal_of_nat (level_atoms_max_offset (level_atoms_keep c (level_atoms_sort xs))))) as Hn
      by (rewrite <- o2_dominated_spec, E; discriminate).
    revert Hn; generalize (level_atoms_max_offset (level_atoms_keep c (level_atoms_sort xs))); intros; ordinal_solve.
Qed.

Fixpoint level_atoms_lookup (a : ne) (s : nat) (ys : list level_atom) : option nat :=
  match ys with
  | nil => None
  | mk_level_atom k t b :: r => match at_cmp a s b t with Eq => Some k | _ => level_atoms_lookup a s r end
  end.

Lemma level_atoms_lookup_In : forall a s ys k, level_atoms_lookup a s ys = Some k -> level_atoms_In k s a ys.
Proof.
  induction ys as [| [k0 t b] r IH]; cbn; intros k H; [ discriminate |].
  destruct (at_cmp a s b t) eqn:E;
    [ apply at_cmp_eq in E as [Eab ->]; injection H as <-; left; auto | right; auto | right; auto ].
Qed.

(** Lookup sees an atom up to its proofs. *)
Lemma level_atoms_lookup_upto : forall a a' s ys, ne_eq_upto_proofs a a' ->
    level_atoms_lookup a s ys = level_atoms_lookup a' s ys.
Proof.
  intros * E; induction ys as [| [k t b] r IH]; cbn; [ reflexivity |].
  rewrite (at_cmp_upto_l _ _ _ _ _ E), IH; reflexivity.
Qed.

(** [nf_proof_free W]: the normal form [W] holds no kept proof
    ([nf_proof]) and no ex falso; mutually, [ne_proof_free u] for the
    neutral [u].  A well-typed level atom is so, a level being made of
    levels only ("levels only from levels"), and on such normal forms
    equality up to proofs is equality ([nf_ne_proof_free_eq]).  The normal
    forms that are strengthened ([Algorithmic.Strengthening.nf_strengthen])
    and the classification of an argument by its normal form
    ([classify_in_nf]) ask for proof-free ones too (see
    [Core.Syntactic.Fresh]). *)
Fixpoint nf_proof_free (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_False => True
  | nf_proof _ => False
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_proof_free (atom_level a)) xs
  | nf_pi _ _ A B | nf_fn A B | nf_and A B => nf_proof_free A /\ nf_proof_free B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms | nf_record _ Ms => all_list nf_proof_free Ms
  | nf_neut M => ne_proof_free M
  | nf_tuple _ Ms _ Ns => all_list nf_proof_free Ms /\ all_list nf_proof_free Ns
  end
with ne_proof_free (M : ne) : Prop :=
  match M with
  | ne_absurd _ _ => False
  | ne_elim _ Us _ Bks M =>
      all_list nf_proof_free Us /\ all_list (normal_block_forall (fun _ => nf_proof_free)) Bks /\ ne_proof_free M
  | ne_app M N => ne_proof_free M /\ nf_proof_free N
  | ne_var _ | ne_glob _ => True
  | ne_proj _ M => ne_proof_free M
  end.

(** The list case of [nf_ne_proof_free_eq]: a list of proof-free
    elements is the only list related to it. *)
Lemma list_eqb_proof_free_eq : forall {A : Set} (Q : A -> Type) (pf : A -> Prop) (f : A -> A -> bool) l,
    list_all A Q l -> (forall x, Q x -> pf x -> forall y, f x y = true -> x = y) ->
    all_list pf l -> forall l', list_eqb f l l' = true -> l = l'.
Proof.
  intros * Hl Hf; induction Hl as [| x Hx l Hl IH]; intros Hp [| y l'] H; cbn in *; try discriminate; [ reflexivity |].
  destruct Hp as [Hpx Hpl]; apply Bool.andb_true_iff in H as [H1 H2].
  rewrite (Hf _ Hx Hpx _ H1), (IH Hpl _ H2); reflexivity.
Qed.

(** A normal form without proofs is the only normal form equal to it up to
    proofs: a related normal form has the same shape, and a proof or an ex
    falso can only be related to a proof or an ex falso. *)
Lemma nf_ne_proof_free_eq :
  (forall W, nf_proof_free W -> forall W', nf_eq_upto_proofs W W' -> W = W') /\
  (forall M, ne_proof_free M -> forall M', ne_eq_upto_proofs M M' -> M = M').
Proof.
  unfold nf_eq_upto_proofs, ne_eq_upto_proofs.
  apply nf_ne_ind; intros;
    lazymatch goal with
    | H : nf_eqb_upto_proofs _ ?N = true |- _ => destruct N
    | H : ne_eqb_upto_proofs _ ?N = true |- _ => destruct N
    end;
    cbn [nf_eqb_upto_proofs ne_eqb_upto_proofs nf_proof_free ne_proof_free] in *; try discriminate; try contradiction;
    eqb_split; eqb_leaves; subst; try reflexivity;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: f_equal; try solve [ eauto ].
  all: eapply list_eqb_proof_free_eq; [ eassumption | | eassumption | eassumption ];
    intros x Hx Hpx y Hxy; try solve [ apply Hx; assumption ].
  all: destruct Hx; destruct y; unfold normal_block_forall in *; cbn in *;
    eqb_split; eqb_leaves; subst; repeat match goal with H : _ /\ _ |- _ => destruct H end; f_equal; auto.
  all: eapply list_eqb_proof_free_eq; [ eassumption | | eassumption | eassumption ];
    intros br Hbr Hpbr br' Hbb; destruct Hbr; destruct br'; cbn in *;
    eqb_split; eqb_leaves; subst; f_equal; auto.
Qed.

(** The neutral case of [nf_ne_proof_free_eq]. *)
Lemma ne_proof_free_eq : forall M M', ne_proof_free M -> ne_eq_upto_proofs M M' -> M = M'.
Proof. intros * H E; exact (proj2 nf_ne_proof_free_eq _ H _ E). Qed.

(** Two lists of atoms equal up to the proofs in their neutrals. *)
Definition level_atoms_eq_upto_proofs (ys ys' : list level_atom) : Prop :=
  list_eqb (fun a a' => Nat.eqb (atom_offset a) (atom_offset a') && Nat.eqb (atom_sort a) (atom_sort a') &&
                        ne_eqb_upto_proofs (atom_level a) (atom_level a'))%bool ys ys' = true.

Definition level_atoms_eq_upto_proofs_dec (ys ys' : list level_atom) :
    {level_atoms_eq_upto_proofs ys ys'} + {~ level_atoms_eq_upto_proofs ys ys'} :=
  Bool.bool_dec _ true.

Lemma level_atoms_eq_upto_proofs_refl : forall ys, level_atoms_eq_upto_proofs ys ys.
Proof.
  unfold level_atoms_eq_upto_proofs; induction ys as [| [k s a] r IH]; cbn; [ reflexivity |].
  rewrite !Nat.eqb_refl, (proj2 nf_ne_eqb_upto_proofs_refl), IH; reflexivity.
Qed.

Lemma level_atoms_eq_upto_proofs_cons : forall k s a a' r r',
    ne_eq_upto_proofs a a' -> level_atoms_eq_upto_proofs r r' ->
    level_atoms_eq_upto_proofs (mk_level_atom k s a :: r) (mk_level_atom k s a' :: r').
Proof.
  unfold level_atoms_eq_upto_proofs, ne_eq_upto_proofs; intros * Ha Hr; cbn.
  rewrite !Nat.eqb_refl, Ha, Hr; reflexivity.
Qed.

Lemma level_atoms_sorted_unique : forall ys1 ys2, level_atoms_sorted ys1 -> level_atoms_sorted ys2 ->
    (forall a s, level_atoms_lookup a s ys1 = level_atoms_lookup a s ys2) -> level_atoms_eq_upto_proofs ys1 ys2.
Proof.
  induction ys1 as [| [k s a] r1 IH]; intros [| [k' t b] r2] H1 H2 Hl.
  - reflexivity.
  - specialize (Hl b t); cbn in Hl; rewrite at_cmp_refl in Hl; discriminate.
  - specialize (Hl a s); cbn in Hl; rewrite at_cmp_refl in Hl; discriminate.
  - destruct H1 as [Ha1 Hr1], H2 as [Hb2 Hr2].
    destruct (at_cmp a s b t) eqn:E.
    + apply at_cmp_eq in E as [Eab <-].
      pose proof (Hl a s) as Hk; cbn in Hk; rewrite at_cmp_refl, (at_cmp_upto_l _ _ _ _ _ Eab), at_cmp_refl in Hk;
        injection Hk as <-.
      apply level_atoms_eq_upto_proofs_cons; [ exact Eab |]; apply IH; auto.
      intros x u; specialize (Hl x u); cbn in Hl.
      rewrite <- (at_cmp_upto_r _ _ _ _ _ Eab) in Hl.
      destruct (at_cmp x u a s) eqn:Ex; auto.
      apply at_cmp_eq in Ex as [Ex ->]; rewrite !(level_atoms_lookup_upto _ _ _ _ Ex).
      destruct (level_atoms_lookup a s r1) eqn:L1;
        [ apply level_atoms_lookup_In in L1; specialize (Ha1 _ _ _ L1); rewrite at_cmp_refl in Ha1; discriminate |].
      destruct (level_atoms_lookup a s r2) eqn:L2;
        [ apply level_atoms_lookup_In in L2; specialize (Hb2 _ _ _ L2);
          rewrite <- (at_cmp_upto_l _ _ _ _ _ Eab), at_cmp_refl in Hb2; discriminate |].
      reflexivity.
    + pose proof (Hl a s) as Hk; cbn in Hk; rewrite at_cmp_refl, E in Hk.
      symmetry in Hk; apply level_atoms_lookup_In in Hk; specialize (Hb2 _ _ _ Hk).
      rewrite at_cmp_opp, E in Hb2; discriminate.
    + pose proof (Hl b t) as Hk; cbn in Hk; rewrite at_cmp_refl in Hk.
      assert (Eba : at_cmp b t a s = Lt) by (rewrite at_cmp_opp, E; reflexivity).
      rewrite Eba in Hk; apply level_atoms_lookup_In in Hk; specialize (Ha1 _ _ _ Hk).
      rewrite at_cmp_opp, Eba in Ha1; discriminate.
Qed.

(** The assignment that separates one atom: it alone is large, at [ω·s + N],
    the largest region its sort [s] allows. *)
Definition ν_at (a : ne) (s N : nat) : ne -> nat -> o2 :=
  fun b t => match at_cmp a s b t with Eq => (s, N) | _ => ordinal_zero end.

Lemma ν_at_adm : forall a s N, lvl_adm (ν_at a s N).
Proof.
  intros a s N; constructor.
  - intros b t; unfold ν_at; destruct (at_cmp a s b t) eqn:E; cbn; [| lia | lia ].
    apply at_cmp_eq in E as [_ ->]; lia.
  - intros b b' t E; unfold ν_at; rewrite (at_cmp_upto_r _ _ _ _ _ E); reflexivity.
Qed.

Lemma level_atoms_eval_zero : forall ys, level_atoms_eval (fun _ _ => ordinal_zero) ys = ordinal_of_nat (level_atoms_max_offset ys).
Proof. induction ys as [| [k s a] r IH]; cbn; [ reflexivity | rewrite IH; ordinal_solve ]. Qed.

Lemma level_atoms_eval_at_none : forall a s N ys, level_atoms_lookup a s ys = None -> level_atoms_eval (ν_at a s N) ys = ordinal_of_nat (level_atoms_max_offset ys).
Proof.
  induction ys as [| [k t b] r IH]; cbn; intros H; [ reflexivity |].
  unfold ν_at at 1; destruct (at_cmp a s b t); try discriminate; rewrite IH by auto; ordinal_solve.
Qed.

Lemma level_atoms_eval_at_some : forall a s N ys k, level_atoms_max_offset ys < N -> level_atoms_sorted ys -> level_atoms_lookup a s ys = Some k ->
    level_atoms_eval (ν_at a s N) ys = (s, k + N).
Proof.
  induction ys as [| [k0 t b] r IH]; cbn; intros k HN Hs H; [ discriminate |].
  destruct Hs as [Hb Hr]; unfold ν_at at 1.
  destruct (at_cmp a s b t) eqn:E.
  - apply at_cmp_eq in E as [Eab <-]; injection H as <-.
    rewrite level_atoms_eval_at_none; [ revert HN; ordinal_solve |].
    destruct (level_atoms_lookup a s r) eqn:L; auto.
    apply level_atoms_lookup_In in L; specialize (Hb _ _ _ L).
    rewrite (at_cmp_upto_r _ _ _ _ _ Eab), at_cmp_refl in Hb; discriminate.
  - rewrite (IH k ltac:(lia) Hr H); revert HN; ordinal_solve.
  - rewrite (IH k ltac:(lia) Hr H); revert HN; ordinal_solve.
Qed.

(** Two levels equal up to the proofs in their atoms. *)
Definition lvl_eq_upto_proofs (l l' : lvl) : Prop := fst l = fst l' /\ level_atoms_eq_upto_proofs (snd l) (snd l').

(** The normal forms of levels, and of their universes, equal up to proofs
    are so as normal forms. *)
Lemma nf_lvl_of_upto_proofs : forall l l', lvl_eq_upto_proofs l l' -> nf_eq_upto_proofs (nf_lvl_of l) (nf_lvl_of l').
Proof.
  intros [c ys] [c' ys'] [Hc Hys]; cbn in *; subst c'; unfold nf_eq_upto_proofs; cbn.
  rewrite dec_eqb_refl; exact Hys.
Qed.

Lemma nf_univ_of_upto_proofs : forall l l', lvl_eq_upto_proofs l l' -> nf_eq_upto_proofs (nf_univ_of l) (nf_univ_of l').
Proof.
  intros [c ys] [c' ys'] [Hc Hys]; cbn in *; subst c'; unfold nf_eq_upto_proofs; cbn.
  rewrite dec_eqb_refl; exact Hys.
Qed.

Lemma level_atoms_eq_upto_proofs_max_offset : forall ys ys', level_atoms_eq_upto_proofs ys ys' ->
    level_atoms_max_offset ys = level_atoms_max_offset ys'.
Proof.
  unfold level_atoms_eq_upto_proofs; induction ys as [| [k s a] r IH]; intros [| [k' s' a'] r'] H; cbn in *;
    try discriminate; [ reflexivity |].
  eqb_split; eqb_leaves; subst; rewrite (IH _ ltac:(eassumption)); reflexivity.
Qed.

(** Levels equal up to proofs have the same value at an admissible
    assignment. *)
Lemma level_atoms_eval_upto : forall ν ys ys', lvl_adm ν -> level_atoms_eq_upto_proofs ys ys' ->
    level_atoms_eval ν ys = level_atoms_eval ν ys'.
Proof.
  unfold level_atoms_eq_upto_proofs; intros ν ys; induction ys as [| [k s a] r IH]; intros [| [k' s' a'] r'] Hadm H; cbn in *;
    try discriminate; [ reflexivity |].
  eqb_split; eqb_leaves; subst.
  rewrite (lvl_adm_upto_proofs _ Hadm a a' s' ltac:(eassumption)), (IH _ Hadm ltac:(eassumption)); reflexivity.
Qed.

Lemma lvl_eval_upto : forall ν l l', lvl_adm ν -> lvl_eq_upto_proofs l l' -> lvl_eval ν l = lvl_eval ν l'.
Proof. intros ν [c ys] [c' ys'] Hadm [Hc Hys]; unfold lvl_eval; cbn in *; rewrite Hc, (level_atoms_eval_upto _ _ _ Hadm Hys); reflexivity. Qed.

Theorem lvl_canonical_unique : forall l1 l2, lvl_canonical l1 -> lvl_canonical l2 ->
    (forall ν, lvl_adm ν -> lvl_eval ν l1 = lvl_eval ν l2) -> lvl_eq_upto_proofs l1 l2.
Proof.
  intros [c1 ys1] [c2 ys2] [S1 K1 C1] [S2 K2 C2] Hev; unfold lvl_eq_upto_proofs; cbn [fst snd] in *.
  assert (Hys : level_atoms_eq_upto_proofs ys1 ys2).
  { apply level_atoms_sorted_unique; auto; intros a s.
    set (N := S (snd c1 + snd c2 + level_atoms_max_offset ys1 + level_atoms_max_offset ys2)).
    assert (HN1 : level_atoms_max_offset ys1 < N) by (subst N; lia).
    assert (HN2 : level_atoms_max_offset ys2 < N) by (subst N; lia).
    assert (Hc1 : snd c1 < N) by (subst N; lia).
    assert (Hc2 : snd c2 < N) by (subst N; lia).
    specialize (Hev (ν_at a s N) (ν_at_adm a s N)); unfold lvl_eval in Hev; cbn [fst snd] in Hev.
    destruct (level_atoms_lookup a s ys1) as [k1 |] eqn:L1, (level_atoms_lookup a s ys2) as [k2 |] eqn:L2.
    - pose proof (K1 _ _ _ (level_atoms_lookup_In _ _ _ _ L1)); pose proof (K2 _ _ _ (level_atoms_lookup_In _ _ _ _ L2)).
      rewrite (level_atoms_eval_at_some _ _ _ _ _ HN1 S1 L1), (level_atoms_eval_at_some _ _ _ _ _ HN2 S2 L2) in Hev.
      f_equal; clearbody N; revert Hc1 Hc2 H H0 Hev; ordinal_solve.
    - pose proof (K1 _ _ _ (level_atoms_lookup_In _ _ _ _ L1)).
      rewrite (level_atoms_eval_at_some _ _ _ _ _ HN1 S1 L1), (level_atoms_eval_at_none _ _ _ _ L2) in Hev.
      exfalso; clearbody N; revert Hc1 Hc2 HN2 H Hev; ordinal_solve.
    - pose proof (K2 _ _ _ (level_atoms_lookup_In _ _ _ _ L2)).
      rewrite (level_atoms_eval_at_none _ _ _ _ L1), (level_atoms_eval_at_some _ _ _ _ _ HN2 S2 L2) in Hev.
      exfalso; clearbody N; revert Hc1 Hc2 HN1 H Hev; ordinal_solve.
    - reflexivity. }
  split; [| exact Hys ].
  specialize (Hev _ lvl_adm_zero); unfold lvl_eval in Hev; cbn [fst snd] in Hev; rewrite !level_atoms_eval_zero in Hev.
  rewrite <- (level_atoms_eq_upto_proofs_max_offset _ _ Hys) in Hev, C2.
  revert Hev C1 C2; generalize (level_atoms_max_offset ys1); intros; ordinal_solve.
Qed.

(** Two levels have canonical forms equal up to proofs exactly when they
    agree at every admissible assignment.  On well-typed levels the
    relation is equality: level atoms carry no proofs ("levels only from
    levels"), though no proof needs that. *)
Theorem lvl_canon_iff : forall l l',
    lvl_eq_upto_proofs (lvl_canon l) (lvl_canon l') <-> (forall ν, lvl_adm ν -> lvl_eval ν l = lvl_eval ν l').
Proof.
  split.
  - intros H ν Hν; rewrite <- (lvl_canon_eval ν l Hν), <- (lvl_canon_eval ν l' Hν); exact (lvl_eval_upto _ _ _ Hν H).
  - intros H; apply lvl_canonical_unique; try apply lvl_canon_canonical.
    intros ν Hν; rewrite !lvl_canon_eval by exact Hν; apply H, Hν.
Qed.

(** Sorting a sorted list of atoms changes nothing. *)
Lemma level_atoms_sort_sorted_id : forall ys, level_atoms_sorted ys -> level_atoms_sort ys = ys.
Proof.
  induction ys as [| [k s a] r IH]; cbn; intros Hs; [ reflexivity |]; destruct Hs as [Ha Hr].
  rewrite (IH Hr); destruct r as [| [k' t b] r']; cbn; [ reflexivity |].
  rewrite (Ha k' t b ltac:(left; split; [ reflexivity | split; [ reflexivity | apply nf_ne_eqb_upto_proofs_refl ] ])); reflexivity.
Qed.

(** Keeping the atoms of a sort at least the constant's tier keeps them
    all when they are all of such a sort. *)
Lemma level_atoms_keep_all : forall c ys, (forall k s a, level_atoms_In k s a ys -> fst c <= s) -> level_atoms_keep c ys = ys.
Proof.
  intros c; induction ys as [| [k s a] r IH]; cbn; intros H; [ reflexivity |].
  rewrite (proj2 (Nat.leb_le _ _) (H k s a ltac:(left; split; [ reflexivity | split; [ reflexivity | apply nf_ne_eqb_upto_proofs_refl ] ]))).
  f_equal; apply IH; intros; eapply H; right; eassumption.
Qed.

(** A canonical level is its canonical form. *)
Lemma lvl_canonical_canon : forall l, lvl_canonical l -> lvl_canon l = l.
Proof.
  intros [c ys] [S K C]; unfold lvl_canon; cbn [fst snd] in *.
  rewrite (level_atoms_sort_sorted_id _ S), (level_atoms_keep_all _ _ K).
  destruct (o2_dominated c (level_atoms_max_offset ys)) eqn:E; f_equal.
  apply o2_dominated_spec in E; destruct C as [-> | C]; [ reflexivity |].
  exfalso; revert E C; generalize (level_atoms_max_offset ys); intros; ordinal_solve.
Qed.

Lemma lvl_canon_idem : forall l, lvl_canon (lvl_canon l) = lvl_canon l.
Proof. intros; apply lvl_canonical_canon, lvl_canon_canonical. Qed.

(** The level operations evaluate as the successor and the join. *)
Lemma level_atoms_eval_suc : forall ν xs,
    level_atoms_eval ν (level_atoms_suc xs) = match xs with nil => ordinal_zero | _ => ordinal_succ (level_atoms_eval ν xs) end.
Proof.
  intros ν; induction xs as [| [k s a] r IH]; cbn; [ reflexivity |]; rewrite IH.
  destruct r as [| x r]; cbn; [| generalize (level_atoms_eval ν (x :: r)) ]; generalize (ν a s); intros; ordinal_solve.
Qed.

Lemma lvl_eval_suc : forall ν l, lvl_eval ν (lvl_suc l) = ordinal_succ (lvl_eval ν l).
Proof.
  intros ν [c xs]; unfold lvl_eval, lvl_suc; cbn; rewrite level_atoms_eval_suc.
  destruct xs as [| x xs]; cbn; [| generalize (level_atoms_eval ν (x :: xs)) ]; intros; ordinal_solve.
Qed.

Lemma level_atoms_eval_app : forall ν xs ys, level_atoms_eval ν (xs ++ ys) = ordinal_max (level_atoms_eval ν xs) (level_atoms_eval ν ys).
Proof.
  induction xs as [| [k s a] r IH]; intros; cbn; [ symmetry; apply ordinal_max_zero_l |].
  rewrite IH; symmetry; apply ordinal_max_assoc.
Qed.

Lemma lvl_eval_max : forall ν l l', lvl_eval ν (lvl_max l l') = ordinal_max (lvl_eval ν l) (lvl_eval ν l').
Proof.
  intros ν [c xs] [d ys]; unfold lvl_eval, lvl_max; cbn; rewrite level_atoms_eval_app.
  generalize (level_atoms_eval ν xs) (level_atoms_eval ν ys); intros; ordinal_solve.
Qed.

(** Canonicalising a part of a level does not change its canonical form: this
    is what makes readback compositional, since the atoms of a level read back
    already canonical (up to the proofs of their atoms). *)
Lemma lvl_canon_max_l : forall l l', lvl_eq_upto_proofs (lvl_canon (lvl_max (lvl_canon l) l')) (lvl_canon (lvl_max l l')).
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_eval_max, !lvl_canon_eval by assumption; reflexivity. Qed.

Lemma lvl_canon_max_r : forall l l', lvl_eq_upto_proofs (lvl_canon (lvl_max l (lvl_canon l'))) (lvl_canon (lvl_max l l')).
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_eval_max, !lvl_canon_eval by assumption; reflexivity. Qed.

Lemma lvl_canon_suc : forall l, lvl_eq_upto_proofs (lvl_canon (lvl_suc (lvl_canon l))) (lvl_canon (lvl_suc l)).
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_eval_suc, !lvl_canon_eval by assumption; reflexivity. Qed.

Lemma lvl_canon_max_cong : forall l1 l1' l2 l2',
    lvl_eq_upto_proofs (lvl_canon l1) (lvl_canon l1') -> lvl_eq_upto_proofs (lvl_canon l2) (lvl_canon l2') ->
    lvl_eq_upto_proofs (lvl_canon (lvl_max l1 l2)) (lvl_canon (lvl_max l1' l2')).
Proof.
  intros * H1 H2; rewrite lvl_canon_iff in H1, H2 |- *.
  intros; rewrite !lvl_eval_max, H1, H2 by assumption; reflexivity.
Qed.

Lemma lvl_canon_suc_cong : forall l l',
    lvl_eq_upto_proofs (lvl_canon l) (lvl_canon l') -> lvl_eq_upto_proofs (lvl_canon (lvl_suc l)) (lvl_canon (lvl_suc l')).
Proof.
  intros * H; rewrite lvl_canon_iff in H |- *.
  intros; rewrite !lvl_eval_suc, H by assumption; reflexivity.
Qed.

(** ** Properties of Every Atom

    Canonicalisation only reorders, merges and drops atoms, so a property of
    all the atoms of a level survives it.  Cleanness, stuckness and
    freshness of the atoms are instances, through [level_atoms_all_all_list]. *)
Fixpoint level_atoms_all (P : ne -> Prop) (xs : list level_atom) : Prop :=
  match xs with
  | nil => True
  | mk_level_atom _ _ a :: r => P a /\ level_atoms_all P r
  end.

Lemma level_atoms_all_insert : forall P k s a ys, P a -> level_atoms_all P ys -> level_atoms_all P (level_atoms_insert k s a ys).
Proof.
  induction ys as [| [k' t b] r IH]; cbn; intros Ha Hys; [ auto |].
  destruct Hys as [Hb Hr]; destruct (at_cmp a s b t) eqn:E; cbn; auto.
Qed.

Lemma level_atoms_all_sort : forall (P : ne -> Prop) xs,
    level_atoms_all P xs -> level_atoms_all P (level_atoms_sort xs).
Proof.
  intros P xs; induction xs as [| [k s a] r IH]; cbn; intros H; [ exact I |].
  destruct H; apply level_atoms_all_insert; auto.
Qed.

Lemma level_atoms_all_keep : forall P c xs, level_atoms_all P xs -> level_atoms_all P (level_atoms_keep c xs).
Proof.
  intros P c; induction xs as [| [k s a] r IH]; cbn [level_atoms_keep]; intros H; [ exact I |].
  destruct H as [Ha Hr]; destruct (fst c <=? s); cbn; auto.
Qed.

Lemma level_atoms_all_canon : forall (P : ne -> Prop) c xs,
    level_atoms_all P xs -> level_atoms_all P (snd (lvl_canon (c, xs))).
Proof. intros; unfold lvl_canon; cbn; apply level_atoms_all_keep, level_atoms_all_sort; assumption. Qed.

Lemma level_atoms_all_app : forall P xs ys, level_atoms_all P xs -> level_atoms_all P ys -> level_atoms_all P (xs ++ ys).
Proof.
  intros P xs ys; induction xs as [| [k s a] r IH]; cbn; [ intros _ H; exact H |].
  intros [Ha Hr] Hy; split; auto.
Qed.

Lemma level_atoms_all_suc : forall P xs, level_atoms_all P xs -> level_atoms_all P (level_atoms_suc xs).
Proof.
  intros P xs; induction xs as [| [k s a] r IH]; cbn; [ intros; exact I |].
  intros [Ha Hr]; split; auto.
Qed.

(** [level_atoms_all P] is [all_list] at the atoms' neutrals, the form the
    properties of normal forms take at a level. *)
Lemma level_atoms_all_all_list : forall P xs, all_list (fun a => P (atom_level a)) xs <-> level_atoms_all P xs.
Proof. induction xs as [| [k s a] r IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** A level whose atoms hold no proof is the only level equal to it up to
    proofs ([nf_ne_proof_free_eq] at each atom). *)
Lemma lvl_proof_free_eq : forall l l', level_atoms_all ne_proof_free (snd l) -> lvl_eq_upto_proofs l l' -> l = l'.
Proof.
  intros [c xs] [c' ys] Hp [Hc Hxs]; cbn in *; subst c'; f_equal.
  revert ys Hxs; induction xs as [| [k s a] r IH]; intros [| [k' s' a'] r'] H;
    unfold level_atoms_eq_upto_proofs in H; cbn in *; try discriminate; [ reflexivity |].
  destruct Hp as [Ha Hr]; eqb_split; eqb_leaves; subst.
  f_equal; [ f_equal; apply ne_proof_free_eq; assumption | apply IH; assumption ].
Qed.

(** The generated induction hypothesis at the atoms of a level is [level_atoms_all]
    of the motive. *)
Lemma list_all_level_atoms_all : forall (P : ne -> Prop) xs, list_all level_atom (level_atom_g_all ne P) xs -> level_atoms_all P xs.
Proof. intros P xs H; induction H as [| [k s a] Ha r Hr IH]; cbn; [ exact I | inversion Ha; subst; auto ]. Qed.

(** The atoms of a level are clean, as [nf_clean] asks of a level, when
    every atom's neutral is. *)
Lemma level_atoms_clean_all : forall xs, all_list (fun a => ne_clean (atom_level a)) xs <-> level_atoms_all ne_clean xs.
Proof. intros; apply level_atoms_all_all_list. Qed.

Lemma level_atoms_clean_canon : forall c xs, all_list (fun a => ne_clean (atom_level a)) xs ->
    all_list (fun a => ne_clean (atom_level a)) (snd (lvl_canon (c, xs))).
Proof. intros * H; apply level_atoms_clean_all, level_atoms_all_canon, level_atoms_clean_all; assumption. Qed.

Lemma level_atoms_clean_sort : forall xs, all_list (fun a => ne_clean (atom_level a)) xs ->
    all_list (fun a => ne_clean (atom_level a)) (level_atoms_sort xs).
Proof. intros * H; apply level_atoms_clean_all, level_atoms_all_sort, level_atoms_clean_all; assumption. Qed.

(** ** The Order on Levels

    [lvl_le l l'] is the decidable order [l ⊔ l' = l'], which is the pointwise
    order at every admissible assignment. *)
Definition lvl_le (l l' : lvl) : Prop := lvl_eq_upto_proofs (lvl_canon (lvl_max l l')) (lvl_canon l').

Theorem lvl_le_correct : forall l l',
    lvl_le l l' <-> (forall ν, lvl_adm ν -> ordinal_le (lvl_eval ν l) (lvl_eval ν l')).
Proof.
  intros l l'; unfold lvl_le; rewrite lvl_canon_iff; split; intros H ν Hν; specialize (H ν Hν);
    rewrite lvl_eval_max in *; revert H; generalize (lvl_eval ν l) (lvl_eval ν l'); intros; ordinal_solve.
Qed.

Definition lvl_eq_dec : forall (l l' : lvl), ({l = l'} + {l <> l'})%type.
Proof.
  intros [c xs] [c' ys]; destruct (o2_eq_dec c c') as [-> |]; [| right; congruence ].
  destruct (List.list_eq_dec (level_atom_eq_dec_g ne_eq_dec) xs ys) as [-> |]; [ left; reflexivity | right; congruence ].
Defined.

(** Equality up to proofs of levels is decidable. *)
Definition lvl_eq_upto_proofs_dec : forall l l', ({lvl_eq_upto_proofs l l'} + {~ lvl_eq_upto_proofs l l'})%type.
Proof.
  intros [c xs] [c' ys]; unfold lvl_eq_upto_proofs; cbn [fst snd].
  destruct (o2_eq_dec c c') as [-> |]; [| right; intros [? _]; congruence ].
  destruct (level_atoms_eq_upto_proofs_dec xs ys); [ left; split; auto | right; intros [_ ?]; contradiction ].
Defined.

Definition lvl_le_dec : forall l l', ({lvl_le l l'} + {~ lvl_le l l'})%type.
Proof. intros; unfold lvl_le; apply lvl_eq_upto_proofs_dec. Defined.

Lemma lvl_le_refl : forall l, lvl_le l l.
Proof. intros; apply lvl_le_correct; intros; apply ordinal_le_refl. Qed.

Lemma lvl_le_trans : forall l1 l2 l3, lvl_le l1 l2 -> lvl_le l2 l3 -> lvl_le l1 l3.
Proof.
  intros * H1 H2; rewrite lvl_le_correct in H1, H2; apply lvl_le_correct; intros ν Hν.
  eapply ordinal_le_trans; [ apply H1, Hν | apply H2, Hν ].
Qed.

Lemma lvl_le_canon : forall l l', lvl_eq_upto_proofs (lvl_canon l) (lvl_canon l') -> lvl_le l l'.
Proof.
  intros * H; rewrite lvl_canon_iff in H; apply lvl_le_correct; intros ν Hν; rewrite (H ν Hν); apply ordinal_le_refl.
Qed.

Lemma lvl_le_antisym : forall l l', lvl_le l l' -> lvl_le l' l -> lvl_eq_upto_proofs (lvl_canon l) (lvl_canon l').
Proof.
  intros * H H'; rewrite lvl_le_correct in H, H'; apply lvl_canon_iff; intros ν Hν.
  apply ordinal_le_antisym; [ apply H, Hν | apply H', Hν ].
Qed.

Lemma lvl_le_max_left : forall l l', lvl_le l (lvl_max l l').
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_eval_max; apply ordinal_le_ordinal_max_l. Qed.

Lemma lvl_le_max_right : forall l l', lvl_le l' (lvl_max l l').
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_eval_max; apply ordinal_le_ordinal_max_r. Qed.

Lemma lvl_le_max_lub : forall l l' l'', lvl_le l l'' -> lvl_le l' l'' -> lvl_le (lvl_max l l') l''.
Proof.
  intros * H H'; rewrite lvl_le_correct in H, H'; apply lvl_le_correct; intros ν Hν.
  rewrite lvl_eval_max; apply ordinal_max_lub; [ apply H, Hν | apply H', Hν ].
Qed.

Lemma lvl_le_suc : forall l, lvl_le l (lvl_suc l).
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_eval_suc; apply ordinal_le_ordinal_succ. Qed.

(** The least level, and the literals. *)
Definition lvl_lit (o : o2) : lvl := (o, nil).

Lemma lvl_eval_lit : forall ν o, lvl_eval ν (lvl_lit o) = o.
Proof. intros; unfold lvl_eval, lvl_lit; cbn; apply ordinal_max_zero_r. Qed.

Lemma lvl_canon_lit : forall o, lvl_canon (lvl_lit o) = lvl_lit o.
Proof.
  intros; apply lvl_canonical_canon; constructor; [ exact I | intros ? ? ? [] | ].
  cbn; destruct o as [[|] [|]]; [ left | right .. ]; ordinal_solve.
Qed.

Lemma lvl_le_lit : forall o o', ordinal_le o o' -> lvl_le (lvl_lit o) (lvl_lit o').
Proof. intros; apply lvl_le_correct; intros; rewrite !lvl_eval_lit; assumption. Qed.

Lemma lvl_le_zero : forall l, lvl_le lvl_zero l.
Proof. intros; apply lvl_le_correct; intros; unfold lvl_eval, lvl_zero; cbn; rewrite ordinal_max_zero_l; apply ordinal_le_zero. Qed.

(** ** Levels of a Sort

    A level of sort [n] has a constant of a tier at most [n] and atoms of
    sorts at most [n]: at every admissible assignment it is below ω·(n+1),
    so the limit [ω·(n+1)] absorbs it. *)
Definition lvl_sort_bounded (n : nat) (l : lvl) : Prop :=
  fst (fst l) <= n /\ forall k s a, level_atoms_In k s a (snd l) -> s <= n.

Lemma level_atoms_sort_In : forall xs k s a, level_atoms_In k s a (level_atoms_sort xs) -> exists k', level_atoms_In k' s a xs.
Proof.
  induction xs as [| [j t b] r IH]; cbn; intros k s a H; [ contradiction |].
  destruct (level_atoms_insert_atoms _ _ _ _ _ _ _ H) as [[-> Hab] | [k'' Hin]]; [ exists j; left; auto |].
  destruct (IH _ _ _ Hin) as [k' ?]; eauto.
Qed.

Lemma lvl_sort_bounded_canon : forall n l, lvl_sort_bounded n l -> lvl_sort_bounded n (lvl_canon l).
Proof.
  intros n [c xs] [Hc Hxs]; unfold lvl_canon, lvl_sort_bounded in *; cbn [fst snd] in *; split.
  - destruct (o2_dominated _ _); cbn; lia.
  - intros k s a Hin; apply level_atoms_keep_In in Hin as [Hin _].
    apply level_atoms_sort_In in Hin as [k' Hin]; eapply Hxs; exact Hin.
Qed.

Lemma level_atoms_suc_In : forall xs k s a, level_atoms_In k s a (level_atoms_suc xs) -> exists k', level_atoms_In k' s a xs.
Proof.
  induction xs as [| [j t b] r IH]; cbn; intros k s a H; [ contradiction |].
  destruct H as [(_ & -> & Hab) | H]; [ exists j; left; auto |].
  destruct (IH _ _ _ H) as [k' ?]; eauto.
Qed.

Lemma level_atoms_app_In : forall xs ys k s a, level_atoms_In k s a (xs ++ ys) -> level_atoms_In k s a xs \/ level_atoms_In k s a ys.
Proof.
  induction xs as [| [j t b] r IH]; cbn; intros ys k s a H; [ auto |].
  destruct H as [H | H]; [ auto |].
  destruct (IH _ _ _ _ H); auto.
Qed.

Lemma lvl_sort_bounded_lit : forall n o, fst o <= n -> lvl_sort_bounded n (lvl_lit o).
Proof. intros; split; [ assumption | intros ? ? ? [] ]. Qed.

Lemma lvl_sort_bounded_suc : forall n l, lvl_sort_bounded n l -> lvl_sort_bounded n (lvl_suc l).
Proof.
  intros n [c xs] [Hc Ha]; split; [ exact Hc |].
  intros k s a Hin; apply level_atoms_suc_In in Hin as [k' Hin]; eapply Ha; exact Hin.
Qed.

Lemma lvl_sort_bounded_max : forall n l l', lvl_sort_bounded n l -> lvl_sort_bounded n l' -> lvl_sort_bounded n (lvl_max l l').
Proof.
  intros n [c xs] [d ys] [Hc Ha] [Hd Hb]; split; [ apply ordinal_max_fst_le; assumption |].
  intros k s a Hin; apply level_atoms_app_In in Hin as [Hin | Hin]; [ eapply Ha | eapply Hb ]; exact Hin.
Qed.

Lemma lvl_eval_sort_bounded : forall ν n l, lvl_adm ν -> lvl_sort_bounded n l -> fst (lvl_eval ν l) <= n.
Proof.
  intros ν n [c xs] Hν [Hc Hxs]; unfold lvl_eval; cbn [fst snd] in *.
  enough (fst (level_atoms_eval ν xs) <= n) by (revert Hc H; generalize (level_atoms_eval ν xs); intros; ordinal_solve).
  induction xs as [| [k s a] r IH]; cbn; [ lia |].
  assert (Hs : s <= n) by (eapply Hxs; apply level_atoms_In_head).
  assert (IH' : fst (level_atoms_eval ν r) <= n) by (apply IH; intros; eapply Hxs; right; eassumption).
  pose proof (lvl_adm_sort _ Hν a s) as Ha; revert IH' Hs Ha; generalize (level_atoms_eval ν r) (ν a s); intros; ordinal_solve.
Qed.

Lemma lvl_canon_absorb : forall n l, lvl_sort_bounded n l ->
    lvl_canon (lvl_max l (lvl_lit (S n, 0))) = lvl_lit (S n, 0).
Proof.
  intros n l Hl.
  assert (H : lvl_eq_upto_proofs (lvl_canon (lvl_max l (lvl_lit (S n, 0)))) (lvl_canon (lvl_lit (S n, 0)))).
  { apply lvl_canon_iff; intros ν Hν.
    rewrite lvl_eval_max, lvl_eval_lit; pose proof (lvl_eval_sort_bounded _ _ _ Hν Hl) as H.
    revert H; generalize (lvl_eval ν l); intros; ordinal_solve. }
  (** The literal has no atoms, so the relation is equality here. *)
  rewrite lvl_canon_lit in H; destruct (lvl_canon (lvl_max l (lvl_lit (S n, 0)))) as [c ys];
    destruct H as [Hc Hys]; unfold level_atoms_eq_upto_proofs in Hys; cbn in Hc, Hys.
  destruct ys; [ subst; reflexivity | discriminate ].
Qed.

(** ** The Realiser

    The realiser of a level is its value when every atom is [0].  It is the
    index of a small universe in the PER and gluing models: those are indexed
    by ordinals, and a level's canonical form depends on the length of the
    context, so no finer index would be stable.  The order on levels refines
    the order on realisers ([lvl_le_real]), which is what makes a subtyping
    between small universes hold in the model. *)
(** The constant is the base of the fold rather than an [ordinal_max] on top of it,
    so that the realiser of a literal level is that literal by computation. *)
Fixpoint level_atoms_max (c : o2) (xs : list level_atom) : o2 :=
  match xs with
  | nil => c
  | mk_level_atom k _ _ :: r => ordinal_max (ordinal_of_nat k) (level_atoms_max c r)
  end.

Definition lvl_real (l : lvl) : o2 := level_atoms_max (fst l) (snd l).

Lemma lvl_real_eval : forall l, lvl_real l = lvl_eval (fun _ _ => ordinal_zero) l.
Proof.
  intros [c xs]; unfold lvl_real, lvl_eval; cbn.
  induction xs as [| [k s a] r IH]; cbn; [ symmetry; apply ordinal_max_zero_r |].
  rewrite IH; generalize (level_atoms_eval (fun _ _ => ordinal_zero) r); intros; ordinal_solve.
Qed.

Lemma lvl_real_canon : forall l, lvl_real (lvl_canon l) = lvl_real l.
Proof. intros; rewrite !lvl_real_eval; apply lvl_canon_eval, lvl_adm_zero. Qed.

Lemma lvl_le_real : forall l l', lvl_le l l' -> ordinal_le (lvl_real l) (lvl_real l').
Proof. intros * H; rewrite lvl_le_correct in H; rewrite !lvl_real_eval; apply H, lvl_adm_zero. Qed.

Lemma lvl_real_lit : forall o, lvl_real (lvl_lit o) = o.
Proof. reflexivity. Qed.

Lemma lvl_real_suc : forall l, lvl_real (lvl_suc l) = ordinal_succ (lvl_real l).
Proof. intros; rewrite !lvl_real_eval; apply lvl_eval_suc. Qed.

Lemma lvl_real_max : forall l l', lvl_real (lvl_max l l') = ordinal_max (lvl_real l) (lvl_real l').
Proof. intros; rewrite !lvl_real_eval; apply lvl_eval_max. Qed.

(** ** Levels Equal up to Proofs

    Two related levels are interchangeable for everything the semantics
    reads off a level: the realiser, the order, the sorts. *)
#[export] Instance lvl_eq_upto_proofs_Equivalence : RelationClasses.Equivalence lvl_eq_upto_proofs.
Proof.
  unfold lvl_eq_upto_proofs, level_atoms_eq_upto_proofs; split.
  - intros [c xs]; split; [ reflexivity | apply level_atoms_eq_upto_proofs_refl ].
  - intros [c xs] [d ys] [Hc H]; cbn in *; split; [ congruence |]; revert ys H.
    induction xs as [| [k s a] r IH]; intros [| [k' s' a'] r'] H; cbn in *; try discriminate; [ reflexivity |].
    eqb_split; eqb_leaves; subst; try solve [ auto ].
    rewrite (proj2 nf_ne_eqb_upto_proofs_sym); assumption.
  - intros [c xs] [d ys] [e zs] [Hc H] [Hd H']; cbn in *; split; [ congruence |]; revert ys zs H H'.
    induction xs as [| [k s a] r IH]; intros [| [k' s' a'] r'] [| [k'' s'' a''] r''] H H'; cbn in *; try discriminate;
      [ reflexivity |].
    eqb_split; eqb_leaves; subst; try solve [ eauto ].
    eapply (proj2 nf_ne_eqb_upto_proofs_trans); eassumption.
Qed.

(** The normal forms of two levels are related exactly when the levels
    are. *)
Lemma nf_lvl_of_upto_proofs_iff : forall l l', nf_eq_upto_proofs (nf_lvl_of l) (nf_lvl_of l') <-> lvl_eq_upto_proofs l l'.
Proof.
  intros [c xs] [d ys]; split; [| apply nf_lvl_of_upto_proofs ].
  unfold nf_eq_upto_proofs, lvl_eq_upto_proofs; cbn; intros H; eqb_split; eqb_leaves; split; assumption.
Qed.

Lemma lvl_real_upto_proofs : forall l l', lvl_eq_upto_proofs l l' -> lvl_real l = lvl_real l'.
Proof. intros * H; rewrite !lvl_real_eval; apply lvl_eval_upto; [ apply lvl_adm_zero | exact H ]. Qed.

Lemma lvl_le_of_upto_proofs : forall l l', lvl_eq_upto_proofs l l' -> lvl_le l l'.
Proof.
  intros * H; apply lvl_le_correct; intros ν Hν; rewrite (lvl_eval_upto _ _ _ Hν H); apply ordinal_le_refl.
Qed.

(** An atom of a related list is an atom of the list, at its offset and
    sort. *)
Lemma level_atoms_In_upto_proofs : forall ys ys', level_atoms_eq_upto_proofs ys ys' ->
    forall k s a, level_atoms_In k s a ys' -> level_atoms_In k s a ys.
Proof.
  unfold level_atoms_eq_upto_proofs; induction ys as [| [k0 t b] r IH]; intros [| [k0' t' b'] r'] H k s a Hin;
    cbn in *; try discriminate; [ contradiction |].
  eqb_split; eqb_leaves; subst.
  destruct Hin as [(-> & -> & Ha) | Hin]; [ left; split; [ reflexivity | split; [ reflexivity |] ] | right; eapply IH; eassumption ].
  unfold ne_eq_upto_proofs in *; eapply (proj2 nf_ne_eqb_upto_proofs_trans); [ exact Ha |].
  rewrite (proj2 nf_ne_eqb_upto_proofs_sym); assumption.
Qed.

Lemma lvl_sort_bounded_upto_proofs : forall n l l', lvl_eq_upto_proofs l l' -> lvl_sort_bounded n l -> lvl_sort_bounded n l'.
Proof.
  intros n [c xs] [d ys] [Hc H] [Hn Ha]; cbn in *; subst d; split; [ exact Hn |].
  intros k s a Hin; eapply Ha, level_atoms_In_upto_proofs; eassumption.
Qed.

(** ** The Order on Universe Normal Forms

    The checker compares two universes by the canonical order of their levels
    in the small tier, by the order on levels in the large one, and a small
    universe is below every large one. *)
Definition universe_nf_le (u v : universe_nf) : Prop :=
  match u, v with
  | universe_small L, universe_small L' => lvl_le L L'
  | universe_small _, universe_large _ => True
  | universe_large _, universe_small _ => False
  | universe_large i, universe_large j => i <= j
  end.

Lemma universe_nf_le_refl : forall u, universe_nf_le u u.
Proof. intros []; cbn; [ apply lvl_le_refl | lia ]. Qed.

Lemma universe_nf_le_trans : forall u v w, universe_nf_le u v -> universe_nf_le v w -> universe_nf_le u w.
Proof.
  intros [] [] []; cbn; try contradiction; intros;
    first [ eapply lvl_le_trans; eassumption | exact I | lia ].
Qed.

(** The large universe a type at [u] also lives in. *)
Definition universe_nf_large_index (u : universe_nf) : nat := match u with universe_small _ => 0 | universe_large n => n end.

Lemma universe_nf_le_large : forall u, universe_nf_le u (universe_large (universe_nf_large_index u)).
Proof. intros []; cbn; [ exact I | lia ]. Qed.

(** The semantic index of a universe normal form. *)
Definition universe_nf_idx (u : universe_nf) : universe_index :=
  match u with universe_small L => us (lvl_real L) | universe_large i => ul i end.

Lemma universe_nf_le_idx : forall u v, universe_nf_le u v -> universe_index_le (universe_nf_idx u) (universe_nf_idx v).
Proof. intros [] []; cbn; try contradiction; intros; [ apply lvl_le_real | exact I |]; assumption. Qed.

(** ** The Join of Two Universe Normal Forms

    Two small universes join at the canonical join of their levels, a small
    and a large one at the large one, and two large ones at the larger.  (The
    universe a [Π] is inferred at is [Core.Syntactic.Fresh.universe_nf_pi_tm]: its
    codomain's level lives under the domain, and is bounded first.) *)
Definition universe_nf_max (u v : universe_nf) : universe_nf :=
  match u, v with
  | universe_small l, universe_small l' => universe_small (lvl_canon (lvl_max l l'))
  | universe_small _, universe_large j => universe_large j
  | universe_large i, universe_small _ => universe_large i
  | universe_large i, universe_large j => universe_large (Nat.max i j)
  end.

Lemma universe_nf_le_max_left : forall u v, universe_nf_le u (universe_nf_max u v).
Proof.
  intros [l |] [l' |]; cbn [universe_nf_max universe_nf_le]; try solve [ exact I | lia ].
  apply lvl_le_correct; intros ν Hν; rewrite lvl_canon_eval, lvl_eval_max by exact Hν; apply ordinal_le_ordinal_max_l.
Qed.

Lemma universe_nf_le_max_right : forall u v, universe_nf_le v (universe_nf_max u v).
Proof.
  intros [l |] [l' |]; cbn [universe_nf_max universe_nf_le]; try solve [ exact I | lia ].
  apply lvl_le_correct; intros ν Hν; rewrite lvl_canon_eval, lvl_eval_max by exact Hν; apply ordinal_le_ordinal_max_r.
Qed.

(** A level below a literal has no atom of a sort at least the literal's
    tier: such an atom can be assigned [ω·s + N] for any [N].  Below a finite
    literal, then, a level has no atom at all. *)
Lemma lvl_le_lit_sorts : forall l o, lvl_le l (lvl_lit o) ->
    forall k s a, level_atoms_In k s a (snd l) -> s < fst o.
Proof.
  intros [c xs] o H k s a Hin; rewrite lvl_le_correct in H; cbn [snd] in Hin.
  destruct (Nat.lt_ge_cases s (fst o)) as [| Hs]; [ assumption | exfalso ].
  specialize (H (ν_at a s (S (snd o))) (ν_at_adm _ _ _)); rewrite lvl_eval_lit in H.
  unfold lvl_eval in H; cbn [fst snd] in H.
  assert (Hge : ordinal_le (s, S (snd o)) (level_atoms_eval (ν_at a s (S (snd o))) xs)).
  { clear H; induction xs as [| [k0 t b] r IH]; cbn in Hin |- *; [ contradiction |].
    destruct Hin as [(<- & <- & Eab) | Hin].
    - unfold ν_at at 1; rewrite <- (at_cmp_upto_r _ _ _ _ _ Eab), at_cmp_refl.
      generalize (level_atoms_eval (ν_at a s (S (snd o))) r); intros; ordinal_solve.
    - specialize (IH Hin); revert IH; generalize (level_atoms_eval (ν_at a s (S (snd o))) r) (ν_at a s (S (snd o)) b t); intros; ordinal_solve. }
  revert H Hge Hs; generalize (level_atoms_eval (ν_at a s (S (snd o))) xs); intros; ordinal_solve.
Qed.

Lemma lvl_le_lit_closed : forall l n, lvl_le l (lvl_lit (ordinal_of_nat n)) -> snd l = nil.
Proof.
  intros [c xs] n H; destruct xs as [| [k s a] r]; [ reflexivity | exfalso ].
  pose proof (lvl_le_lit_sorts _ _ H k s a (level_atoms_In_head _ _ _ _)) as Hs; cbn in Hs; lia.
Qed.

(** The literal small universes. *)
Definition universe_nf_lit (o : o2) : universe_nf := universe_small (lvl_lit o).

Lemma universe_nf_le_lit : forall o o', ordinal_le o o' -> universe_nf_le (universe_nf_lit o) (universe_nf_lit o').
Proof. intros; apply lvl_le_lit; assumption. Qed.

(** Decides an identity between ordinals built from the values of levels:
    each value [lvl_eval ν l] is an opaque ordinal, and [ordinal_solve] does the rest. *)
Ltac lvl_ordinal :=
  repeat match goal with
         | |- context [lvl_eval ?ν ?l] => let x := fresh "x" in generalize (lvl_eval ν l) as x
         end;
  ordinal_solve.
