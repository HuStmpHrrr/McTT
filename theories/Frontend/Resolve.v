From Stdlib Require Import Lia List PeanoNat Relation_Operators String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax.

Import Syntax_Notations Wk_Notations.

(** * Scopes and Name Resolution

    Modules, global definitions and local bindings live entirely in the
    front end: a compilation unit is compiled down to one *closed* [exp], so
    the core calculus, its metatheory and [nbe] are untouched.

    Every definition [x : A := M] becomes one entry of a *definition telescope*,
    emitted as the nest [(λ A body) $ M].  This is what makes [A] checked and [M]
    checked against it.  What the [abstract] modifier changes is only what the
    name [x] resolves to inside [body]:

    - [abstract]: the variable the [λ] just bound.  Type checking [body] then
      never sees [M] — which is precisely opacity — while the trailing
      application restores the value, so evaluation is unaffected.
    - transparent: [M] itself, substituted at every use site.  Delta reduction
      by inlining is the only form of transparency available, the core having no
      [let]; the cost is that [M] is duplicated, and re-checked, per use.

    Consequently the only thing a name has to resolve to is either a term
    together with the depth at which that term was elaborated, or a module. *)

(** ** Entries

    [v_arity] is the number of module parameters that a use of the member still
    has to supply: the parameters of every enclosing module are prepended to a
    member's type and body as ordinary binders, so [(X.Y.Z a b).foo] is just
    [foo] applied to [a] and [b].  Since dot binds tighter than application,
    module arguments must be parenthesised, as in the design document. *)
Record val : Set :=
  { v_depth : nat
  ; v_term : exp
  ; v_arity : nat
  ; v_private : bool }.

Inductive entry : Set :=
| e_val : val -> entry
(** [e_mod n ms] has import depth [n]; see [ImportDepth] below. *)
| e_mod : nat -> scope -> entry

(** The global and the local scope have the same shape: a tree whose leaves are
    terms, so that every prefix of a dotted name denotes either a module or a
    term.  Innermost binding first, so shadowing is "first match wins".

    This is an association list spelled out as an inductive rather than a
    [list (string * entry)]: the guard condition does not see through the pair,
    so with a [list] none of the mutual recursions below would be accepted. *)
with scope : Set :=
| sc_nil : scope
| sc_cons : string -> entry -> scope -> scope.

Fixpoint sc_app (s t : scope) : scope :=
  match s with
  | sc_nil => t
  | sc_cons x e s' => sc_cons x e (sc_app s' t)
  end.

Fixpoint sc_lookup (x : string) (s : scope) : option entry :=
  match s with
  | sc_nil => None
  | sc_cons y e s' => if string_dec y x then Some e else sc_lookup x s'
  end.

Fixpoint sc_lookup_path (p : list string) (s : scope) : option entry :=
  match p with
  | nil => None
  | x :: nil => sc_lookup x s
  | x :: p' =>
      match sc_lookup x s with
      | Some (e_mod _ ms) => sc_lookup_path p' ms
      | _ => None
      end
  end.

(** Insertion merges with the modules already there, so that [module X.A] and
    [module X.B] end up as two members of one [X]. *)
Fixpoint sc_insert (p : list string) (e : entry) (s : scope) : scope :=
  match p with
  | nil => s
  | x :: nil => sc_cons x e s
  | x :: p' =>
      match sc_lookup x s with
      | Some (e_mod n ms) => sc_cons x (e_mod n (sc_insert p' e ms)) s
      | _ => sc_cons x (e_mod 0 (sc_insert p' e sc_nil)) s
      end
  end.

(** Hiding what [private] hides.  This is the *only* effect of [private], and it
    happens only at [import]: within the declaring unit a private member is an
    ordinary one. *)
Fixpoint ent_public (e : entry) : option entry :=
  match e with
  | e_val v => if v_private v then None else Some (e_val v)
  | e_mod n ms => Some (e_mod n (sc_public ms))
  end
with sc_public (s : scope) : scope :=
  match s with
  | sc_nil => sc_nil
  | sc_cons x e s' =>
      match ent_public e with
      | Some e' => sc_cons x e' (sc_public s')
      | None => sc_public s'
      end
  end.

(** ** Using an Entry *)

(** A term elaborated at depth [n], moved to the deeper depth [d]. *)
Definition sc_shift (d n : nat) (M : exp) : exp := M⟨wk_shiftn (d - n)⟩.

Definition sc_apply (M : exp) (args : list exp) : exp := List.fold_left a_app args M.

(** A member may not be used before all of its module parameters are given. *)
Definition sc_use (d : nat) (v : val) (args : list exp) : option exp :=
  if Nat.leb (v_arity v) (List.length args)
  then Some (sc_apply (sc_shift d (v_depth v) (v_term v)) args)
  else None.

(** The two ways of binding a name at depth [d]: to the variable a binder just
    introduced, or to an already elaborated term. *)
Definition v_bound (d ar : nat) (priv : bool) : val :=
  {| v_depth := S d; v_term := #0; v_arity := ar; v_private := priv |}.

Definition v_inline (d ar : nat) (priv : bool) (M : exp) : val :=
  {| v_depth := d; v_term := M; v_arity := ar; v_private := priv |}.

(** Which of the two a definition binds its name to, given [abstract]. *)
Definition v_bind (ab : bool) (d ar : nat) (priv : bool) (M : exp) : val :=
  if ab then v_bound d ar priv else v_inline d ar priv M.

Definition sc_push (x : string) (d : nat) (s : scope) : scope :=
  sc_cons x (e_val (v_bound d 0 false)) s.

(** Baking module arguments into every member of a module.  This is what
    [let module M := X.Y.Z a b] and [import X.Y.Z as N] do: no term is emitted,
    the arguments are merely recorded. *)
Fixpoint ent_fix (d : nat) (args : list exp) (e : entry) : option entry :=
  match e with
  | e_val v =>
      if Nat.leb (List.length args) (v_arity v)
      then Some (e_val (v_inline d (v_arity v - List.length args) (v_private v)
                                 (sc_apply (sc_shift d (v_depth v) (v_term v)) args)))
      else None
  | e_mod n ms =>
      match sc_fix d args ms with
      | Some ms' => Some (e_mod n ms')
      | None => None
      end
  end
with sc_fix (d : nat) (args : list exp) (s : scope) : option scope :=
  match s with
  | sc_nil => Some sc_nil
  | sc_cons x e s' =>
      match ent_fix d args e, sc_fix d args s' with
      | Some e', Some s'' => Some (sc_cons x e' s'')
      | _, _ => None
      end
  end.

(** Binding the members named by [import ... use (f; g)]. *)
Fixpoint sc_take (ns : list string) (ms s : scope) : option scope :=
  match ns with
  | nil => Some s
  | x :: ns' =>
      match sc_lookup x ms with
      | Some e => sc_take ns' ms (sc_cons x e s)
      | None => None
      end
  end.

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
