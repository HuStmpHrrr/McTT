From Stdlib Require Import Lia List PeanoNat Relation_Operators String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax.

Import Syntax_Notations Wk_Notations.

(** * Names in Scope

    Core commands do not name a frame's parameters, so for each open frame the
    elaborator keeps an [eframe]: its members, without their types, and its
    named parameters.

    A private member can be named from its own frame and the frames nested in
    it.  Through a module that is not open, only public members are reachable.
    Of an imported unit only the path is known. *)

(** ** Frames *)

(** A member without its type: whether a definition is private, or the
    number of parameters and the members of a nested module. *)
Inductive ename : Set :=
| en_def : bool -> ename
| en_mod : nat -> emod -> ename
with emod : Set :=
| em_nil : emod
| em_ext : emod -> string -> ename -> emod.

(** An open frame: [ef_params] names its parameters, innermost first, and
    [ef_mod] holds its members so far. *)
Record eframe : Set := ef_mk
  { ef_params : list string
  ; ef_mod : emod }.

Fixpoint em_lookup (x : string) (Φ : emod) : option ename :=
  match Φ with
  | em_nil => None
  | em_ext Φ' y E => if String.eqb x y then Some E else em_lookup x Φ'
  end.

Fixpoint index_of (x : string) (xs : list string) : option nat :=
  match xs with
  | nil => None
  | y :: xs' => if String.eqb x y then Some 0 else option_map S (index_of x xs')
  end.

(** ** What a Name Denotes

    A module reached by a dotted prefix: its unit and member chain, its
    members, whether only public members may be named, and the arguments
    given so far.  The members are [None] for a path into an imported unit,
    which is _opaque_: typing decides what it names. *)
Record mref : Set := mr_mk
  { mr_unit : list string
  ; mr_mems : list string
  ; mr_mod : option emod
  ; mr_public : bool
  ; mr_args : list exp }.

(** What an alias names: a module, or a definition of one. *)
Inductive target : Set :=
| tg_mod : mref -> target
| tg_mem : mref -> string -> target.


(** ** The Local Scope

    Bindings made inside a term, each recorded with the depth it was
    elaborated at and weakened to the use site. *)
Inductive lent : Set :=
| le_term : exp -> nat -> lent
| le_mod : mref -> nat -> lent.

Definition lscope : Set := list (string * lent).

Definition ls_push (x : string) (d : nat) (ls : lscope) : lscope := (x, le_term #0 (S d)) :: ls.

Definition sc_shift (d n : nat) (M : exp) : exp := M[wk_shiftn (d - n)]ʷ.

Definition sc_apply (M : exp) (args : list exp) : exp := List.fold_left a_app args M.

Definition mr_weaken (d n : nat) (mr : mref) : mref :=
  {| mr_unit := mr_unit mr; mr_mems := mr_mems mr; mr_mod := mr_mod mr;
     mr_public := mr_public mr;
     mr_args := List.map (sc_shift d n) (mr_args mr) |}.

(** * Import Depths

    Starting at [0] and replacing the depth [n] by [max(n, m + 1)] for each
    import of depth [m] assigns every module the length of the longest import
    chain below it.  Such a ranking exists exactly when the import graph is
    acyclic: [depth_acyclic] and [depths_ranks] are the two directions. *)
Section ImportDepth.

  (** A finite import graph in declaration order: node [i] imports the nodes
      listed in [nth i g nil]. *)
  Definition graph : Set := list (list nat).

  Definition edge (g : graph) (i j : nat) : Prop :=
    i < List.length g /\ List.In j (List.nth i g nil).

  Definition ranks (g : graph) (d : list nat) : Prop :=
    forall i j, edge g i j -> List.nth j d 0 < List.nth i d 0.

  Lemma ranks_clos_trans : forall g d,
      ranks g d ->
      forall i j, clos_trans nat (edge g) i j -> List.nth j d 0 < List.nth i d 0.
  Proof.
    induction 2; [ eauto | lia ].
  Qed.

  (** A ranked graph has no import cycles. *)
  Theorem depth_acyclic : forall g d,
      ranks g d ->
      forall i, ~ clos_trans nat (edge g) i i.
  Proof.
    intros * Hr * Hc.
    pose proof (ranks_clos_trans _ _ Hr _ _ Hc). lia.
  Qed.

  (** Conversely, depths exist for a graph in declaration order, which is
      every acyclic graph up to a topological sort. *)
  Definition ordered (g : graph) : Prop := forall i j, edge g i j -> j < i.

  Definition rank_of (d : list nat) (is : list nat) : nat :=
    List.fold_left (fun n j => Nat.max n (S (List.nth j d 0))) is 0.

  Fixpoint depths_from (d : list nat) (g : graph) : list nat :=
    match g with
    | nil => d
    | is :: g' => depths_from (d ++ cons (rank_of d is) nil) g'
    end.

  Definition depths (g : graph) : list nat := depths_from nil g.

  Lemma rank_of_acc : forall is d n,
      n <= List.fold_left (fun n j => Nat.max n (S (List.nth j d 0))) is n.
  Proof.
    induction is; intros; simpl; [ lia |].
    transitivity (Nat.max n (S (List.nth a d 0))); [ lia | auto ].
  Qed.

  Lemma rank_of_gt : forall is d j,
      List.In j is ->
      List.nth j d 0 < rank_of d is.
  Proof.
    unfold rank_of. intros * Hin.
    enough (forall n, List.nth j d 0 < List.fold_left (fun n j => Nat.max n (S (List.nth j d 0))) is n) by auto.
    induction is; intros; simpl in *; [ contradiction |].
    destruct Hin as [-> |]; [| auto ].
    pose proof (rank_of_acc is d (Nat.max n (S (List.nth j d 0)))). lia.
  Qed.

  Lemma depths_from_prefix : forall g d, exists e, depths_from d g = d ++ e.
  Proof.
    induction g; intros; simpl.
    - exists nil. rewrite app_nil_r. reflexivity.
    - destruct (IHg (d ++ cons (rank_of d a) nil)) as [e ->].
      exists (rank_of d a :: e). rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma depths_from_nth_low : forall g d j,
      j < List.length d ->
      List.nth j (depths_from d g) 0 = List.nth j d 0.
  Proof.
    intros * ?.
    destruct (depths_from_prefix g d) as [e ->].
    rewrite app_nth1; auto.
  Qed.

  Lemma depths_from_ranks : forall g d,
      (forall i j, i < List.length g -> List.In j (List.nth i g nil) -> j < List.length d + i) ->
      forall i j, i < List.length g ->
             List.In j (List.nth i g nil) ->
             List.nth j (depths_from d g) 0 < List.nth (List.length d + i) (depths_from d g) 0.
  Proof.
    induction g as [| is g IHg]; intros * Hlt * Hi Hin; simpl in *; [ lia |].
    destruct i as [| i]; simpl in *.
    - pose proof (Hlt 0 j Hi Hin) as Hj. rewrite Nat.add_0_r in *.
      rewrite depths_from_nth_low by (rewrite length_app; simpl; lia).
      destruct (depths_from_prefix g (d ++ cons (rank_of d is) nil)) as [e Heq].
      rewrite Heq, <- app_assoc, app_nth1 by lia.
      rewrite app_nth2, Nat.sub_diag by lia.
      simpl. apply rank_of_gt. assumption.
    - replace (List.length d + S i) with (List.length (d ++ cons (rank_of d is) nil) + i)
        by (rewrite length_app; simpl; lia).
      apply IHg; auto with arith.
      intros i' j' Hi' Hin'. rewrite length_app. simpl.
      specialize (Hlt (S i') j' (proj1 (Nat.succ_lt_mono _ _) Hi') Hin'). lia.
  Qed.

  Theorem depths_ranks : forall g, ordered g -> ranks g (depths g).
  Proof.
    unfold ranks, depths, ordered, edge. intros * Hord * [? ?].
    replace i with (List.length (@nil nat) + i) by (simpl; lia).
    apply depths_from_ranks; simpl; auto.
  Qed.

  (** The depth rule rules out cycles. *)
  Corollary ordered_acyclic : forall g,
      ordered g ->
      forall i, ~ clos_trans nat (edge g) i i.
  Proof.
    intros. eapply depth_acyclic, depths_ranks. assumption.
  Qed.

End ImportDepth.
