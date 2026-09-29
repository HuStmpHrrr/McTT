From Stdlib Require Import Lia List PeanoNat Relation_Operators String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax GlobalCtx.

Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

(** * Names in Scope

    The elaborator emits into the global context: a unit becomes a [gunit], a
    definition a [ge_def], a nested module a [ge_mod], and a name one of
    [$[n, k]], [a_glob] or a λ-variable.  What the global context does not
    record is names that are not members: a frame's parameters are a nameless
    [ctx].  So the elaborator keeps, per open frame, a copy of the frame with
    the types stripped and the parameters named: an [eframe].

    Visibility: a private member can be named from the frame it is declared
    in and from the frames nested inside it, i.e. when it is reached as a
    member of a frame on the stack.  Through a module that is not open — a
    sibling, a module nested in one, a filed unit — only public members are
    reachable. *)

(** ** Frames *)

(** A member, types stripped: whether a definition is private; how many
    parameters a nested module has, and its members. *)
Inductive ename : Set :=
| en_def : bool -> ename
| en_mod : nat -> emod -> ename
with emod : Set :=
| em_nil : emod
| em_ext : emod -> string -> ename -> emod.

(** An open frame: [ef_params] names its parameters, the [k]th one being
    [$[_, k]], i.e. innermost first; [ef_mod] its members so far. *)
Record eframe : Set := ef_mk
  { ef_params : list string
  ; ef_mod : emod }.

Fixpoint em_lookup (x : string) (Φ : emod) : option ename :=
  match Φ with
  | em_nil => None
  | em_ext Φ' y E => if String.eqb x y then Some E else em_lookup x Φ'
  end.

(** What a module filed in [Θ] looks like to the elaborator. *)
Fixpoint ge_erase (E : gentry) : ename :=
  match E with
  | ge_def _ pv _ _ => en_def pv
  | ge_mod Δ Φ => en_mod (List.length Δ) (gm_erase Φ)
  end
with gm_erase (Φ : gmod) : emod :=
  match Φ with
  | gm_nil => em_nil
  | gm_ext Φ' x E => em_ext (gm_erase Φ') x (ge_erase E)
  end.

Fixpoint index_of (x : string) (xs : list string) : option nat :=
  match xs with
  | nil => None
  | y :: xs' => if String.eqb x y then Some 0 else option_map S (index_of x xs')
  end.

(** ** What a Name Denotes

    A module reached by a dotted prefix: where it is ([mr_qual], [mr_mems]),
    its members, whether only its public members may be named, how many
    arguments a use of a member has to supply ([mr_arity]: the parameters of
    the closed modules crossed, which resolution generalizes over), and the
    arguments given so far. *)
Record mref : Set := mr_mk
  { mr_qual : qual
  ; mr_mems : list string
  ; mr_mod : emod
  ; mr_public : bool
  ; mr_arity : nat
  ; mr_args : list exp }.

(** What an alias names: a module, or a definition of one. *)
Inductive target : Set :=
| tg_mod : mref -> target
| tg_mem : mref -> string -> target.

(** An alias recorded in frame [j] is used from [i] frames further in: its
    relative qualifier and its arguments move out by [i]. *)
Definition qual_shift (i : nat) (ql : qual) : qual :=
  match ql with
  | qu_rel m => qu_rel (i + m)
  | qu_abs fp => qu_abs fp
  end.

Definition mr_shift (i : nat) (mr : mref) : mref :=
  {| mr_qual := qual_shift i (mr_qual mr); mr_mems := mr_mems mr; mr_mod := mr_mod mr;
     mr_public := mr_public mr; mr_arity := mr_arity mr;
     mr_args := List.map (fun M => M[↑ₘ i]ᵐ) (mr_args mr) |}.

Definition tg_shift (i : nat) (t : target) : target :=
  match t with
  | tg_mod mr => tg_mod (mr_shift i mr)
  | tg_mem mr x => tg_mem (mr_shift i mr) x
  end.

(** ** The Local Scope

    Bindings made inside a term: a λ-variable, or a [let], each recorded with
    the depth it was elaborated at and moved to the use site by weakening. *)
Inductive lent : Set :=
| le_term : exp -> nat -> lent
| le_mod : mref -> nat -> lent.

Definition lscope : Set := list (string * lent).

Definition ls_push (x : string) (d : nat) (ls : lscope) : lscope := (x, le_term #0 (S d)) :: ls.

Definition sc_shift (d n : nat) (M : exp) : exp := M[wk_shiftn (d - n)]ʷ.

Definition sc_apply (M : exp) (args : list exp) : exp := List.fold_left a_app args M.

Definition mr_weaken (d n : nat) (mr : mref) : mref :=
  {| mr_qual := mr_qual mr; mr_mems := mr_mems mr; mr_mod := mr_mod mr;
     mr_public := mr_public mr; mr_arity := mr_arity mr;
     mr_args := List.map (sc_shift d n) (mr_args mr) |}.

(** * Import Depths

    The rule of the design document — start at [0] and replace the current
    depth [n] by [max(n, m + 1)] for an import of depth [m] — assigns each
    module the length of the longest import chain below it.  Such an assignment
    is a *ranking* of the import graph, and ranking and acyclicity are two views
    of the same property: [depth_acyclic] is one direction, [depths_ranks] the
    other. *)
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

  (** Conversely, depths always exist.  A unit can only import what it has
      already declared, so its import graph comes in declaration order; this is
      the general acyclic case up to a topological sort. *)
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

  (** So the depth rule really does rule out cycles. *)
  Corollary ordered_acyclic : forall g,
      ordered g ->
      forall i, ~ clos_trans nat (edge g) i i.
  Proof.
    intros. eapply depth_acyclic, depths_ranks. assumption.
  Qed.

End ImportDepth.
