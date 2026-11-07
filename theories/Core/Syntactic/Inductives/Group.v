(** * Groups of Inductive Types: Members, and the Classification of Arguments

    A group ([ind_decl], in [Syntax]) has members: the types it declares,
    then its views, the instances of types of earlier groups its
    constructors nest through.  This file reads a member off a group (its
    type former, its uniform arguments, its constructors) and states the
    classification of an argument type in normal form, which decides
    whether an argument is recursive, and in which member: the one rule of
    positivity (the command, [Core.Syntactic.System.Command], normalizes an
    argument type and classifies its normal form). *)

From Stdlib Require Import List String PeanoNat Bool Sorting.Sorted Lia RelationClasses.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations Sub_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Lists of Variables and Pattern Weakenings *)

(** The variables [#(k + n - 1)], …, [#k], outermost first. *)
Definition vars_from (k n : nat) : list exp := List.map (fun i => a_var (k + i)) (List.rev (List.seq 0 n)).

(** [wk_pat pat] sends a context into the one with more binders, where
    [pat] tells, innermost first, which binders of the bigger context are
    new ([true]). *)
Fixpoint wk_pat (pat : list bool) : wk :=
  match pat with
  | nil => fun x => x
  | false :: pat' => wk_q (wk_pat pat')
  | true :: pat' => wk_compose (wk_pat pat') wk_shift
  end.

(** Its left inverse. *)
Fixpoint unwk_pat (pat : list bool) : wk :=
  match pat with
  | nil => fun x => x
  | false :: pat' => wk_q (unwk_pat pat')
  | true :: pat' => wk_compose pred (unwk_pat pat')
  end.

(** The pattern of the arguments [gs] of a constructor, innermost first:
    [true] at a recursive one. *)
Definition cargs_pat (gs : list carg) : list bool :=
  List.rev (List.map (fun g => match g with ca_rec _ => true | ca_arg _ _ => false end) gs).

(** The arguments of the constructor [c]. *)
Fixpoint cons_lookup (cs : list (string * list carg)) (c : string) : option (list carg) :=
  match cs with
  | nil => None
  | (c', gs) :: cs' => if String.eqb c c' then Some gs else cons_lookup cs' c
  end.

(** ** Members

    The member [M] at position [k] of the group at path [pq]: its type
    former, the uniform arguments of its type at the group's uniform
    parameters [Us], and its type at [Us] and its non-uniform parameters
    [Ns].  A declared member is [a_ind pq k] at [Us]; a view of the
    declared member [k'] of the group at [q] at [Is] is [a_ind q k'] at
    [Is] instantiated by [Us]; a record view of the record at [q] at [Is]
    is the record type [a_record q] at [Is] instantiated by [Us]. *)

(** The type former a member's type is headed by: its own at a declared
    member, its container's member at a view.  A record view's type is a
    record type ([im_ty_at]); its constructor, before it is saturated, is
    the member's own ([pq], [k]). *)
Definition im_ref (pq : qname) (k : nat) (M : imember) : (qname * nat)%type :=
  match im_head M with
  | mh_decl _ => (pq, k)
  | mh_view qc k' _ _ => (qc, k')
  | mh_record _ _ _ => (pq, k)
  end.

(** The uniform arguments of a member's type at the group's uniform
    parameters [Us]: [Us] at a declared member, the view's instance [Is]
    at [Us] at a view, the record view's [Is] at [Us] at a record view.
    At a declared member and at a view this is also what the member's
    constructors are applied to; at a record view it is only the prefix
    of its type, the record type: its constructor [rview_con] is the
    group's own, applied to [Us] ([wf_exp_eq_con_rview]).  A record view
    has no block, so no branch's type applies its constructor to
    [im_pre]. *)
Definition im_pre (M : imember) (Us : list exp) : list exp :=
  match im_head M with
  | mh_decl _ => Us
  | mh_view _ _ Is _ => List.map (fun I => I[sb_of_list sb_id Us]) Is
  | mh_record _ Is _ => List.map (fun I => I[sb_of_list sb_id Us]) Is
  end.

(** A member's type at the uniform parameters [Us] and the non-uniform
    ones [Ns]: the record type at the instance at a record view (which has
    no non-uniform parameters). *)
Definition im_ty_at (pq : qname) (k : nat) (M : imember) (Us Ns : list exp) : typ :=
  match im_head M with
  | mh_record qr _ _ => apps_exp (a_record qr) (im_pre M Us ++ Ns)
  | _ => apps_exp (a_ind (fst (im_ref pq k M)) (snd (im_ref pq k M))) (im_pre M Us ++ Ns)
  end.

(** The arguments of a member's constructor [c], if it has one. *)
Definition im_con (M : imember) (c : string) : option (list carg) := cons_lookup (im_cons M) c.

(** Whether a member is a declared type (rather than a view or a record
    view). *)
Definition im_is_decl (M : imember) : bool :=
  match im_head M with mh_decl _ => true | _ => false end.

(** Whether a member is a record view. *)
Definition im_is_rview (M : imember) : bool :=
  match im_head M with mh_record _ _ _ => true | _ => false end.

(** The members that have a block in an eliminator: all but the record
    views, which come last ([rview_suffix_ok]). *)
Definition ind_nblk (D : ind_decl) : nat := List.length (List.filter (fun M => negb (im_is_rview M)) (ind_members D)).

(** The record views come after every other member: a member is a record
    view exactly when its position is not below [ind_nblk D]. *)
Definition rview_suffix_ok (D : ind_decl) : Prop :=
  forall k M, ind_member D k = Some M -> (im_is_rview M = true <-> ind_nblk D <= k).

(** A constructor of the member [M] is a value of its own before any
    argument: always at a declared member, and at a view when the group has
    uniform parameters (with none, it is at once the container's). *)
Definition im_starts (D : ind_decl) (M : imember) : bool := im_is_decl M || (0 <? ind_nu D).

(** The declared members come first: [ind_ndecl D] of them, then the
    views. *)
Definition ind_ndecl (D : ind_decl) : nat := List.length (List.filter im_is_decl (ind_members D)).

(** A group has views when some member is not declared: its eliminator
    then carries the group's uniform parameters. *)
Definition ind_has_views (D : ind_decl) : bool := negb (List.forallb im_is_decl (ind_members D)).

Lemma no_views_decl : forall D j Mj, ind_has_views D = false -> ind_member D j = Some Mj -> im_is_decl Mj = true.
Proof.
  intros * Hv Hj; unfold ind_has_views in Hv; apply Bool.negb_false_iff in Hv.
  rewrite List.forallb_forall in Hv; exact (Hv _ (List.nth_error_In _ _ Hj)).
Qed.

(** A group with a view member has views. *)
Lemma view_has_views : forall D j Mj qc k Is vm, ind_member D j = Some Mj -> im_head Mj = mh_view qc k Is vm ->
    ind_has_views D = true.
Proof.
  intros * Hj Hh; destruct (ind_has_views D) eqn:Hv; [ reflexivity |].
  pose proof (no_views_decl _ _ _ Hv Hj) as Hd; unfold im_is_decl in Hd; rewrite Hh in Hd; discriminate.
Qed.

(** The declared members come before the views: a member is declared
    exactly when its position is below [ind_ndecl D]. *)
Definition ind_order_ok (D : ind_decl) : Prop :=
  forall k M, ind_member D k = Some M -> (im_is_decl M = true <-> k < ind_ndecl D).

(** ** Classification of an Argument Type in Normal Form

    The command classifies each argument of each constructor of each
    member, declared or view, as the normal form [W] of its type, in the
    context of the arguments before it (all of them binders), the member's
    parameters ([np] of them, the group's own [nu] uniform ones outermost),
    the variables [Self_0], …, [Self_(n-1)] of the [n] declared members
    (bound outside the parameters, [Self_0] outermost, of type
    [Π (params). S]), and the frames' parameters.  Under [d] domains of a
    function shape the context has [d] more binders.

    [Vs] is the list of views of the group, the instances in order: a view
    [(q, k, Cs)] is the declared member [k] of the filed group at [q] at
    the uniform arguments [Cs], normal, over the group's own uniform
    parameters, the [Self]s and the frames' parameters.  The view [v] is
    the member [n + v].

    [classify_pat d np n pat] is the pattern of the weakening that sends the
    context of the domains, the non-recursive arguments before ([pat] tells,
    innermost first, which arguments before are recursive), the parameters
    and the frames into the full one: a term in its image mentions no
    recursive argument and no [Self].

    The classification is a function, written as a recognizer: a term is in
    the image of a pattern weakening exactly when it is the image of its own
    preimage candidate ([image_pat]).  A nested occurrence is classified with
    its instance, not yet numbered ([classified_ptyp]); the command numbers the views
    once it has found them all ([classified_ptyp_num]). *)

(** The key of a view: an instance met, its arguments in normal form,
    which the group files as one of its members.  Two keys are of one
    view when they are equal up to their proofs ([view_key_eqb]): an
    instance normalized holds its proofs as kept, and two proofs of one
    proposition make one type. *)
Inductive view_key : Set :=
(** An inductive view: the declared member [k] of the filed group at [qc],
    at the uniform arguments [Cs] *)
| vk_ind (qc : qname) (k : nat) (Cs : list nf)
(** A record view: the record at [qr], at the instance [Is] (all its
    parameters) *)
| vk_record (qr : qname) (Is : list nf).

(** An instance met, as the classification reads it off a type: its
    arguments as they are there, which the command normalizes into the
    key of its view. *)
Inductive view_inst : Set :=
(** The declared member [k] of the filed group at [qc], at the uniform
    arguments [Cs] *)
| vi_ind (qc : qname) (k : nat) (Cs : list exp)
(** The record at [qr], at the instance [Is] *)
| vi_record (qr : qname) (Is : list exp).

(** Whether two keys are of one view: the same container's member, or
    the same record, at arguments equal up to their proofs. *)
Definition view_key_eqb (x y : view_key) : bool :=
  match x, y with
  | vk_ind qc k Cs, vk_ind qc' k' Cs' => dec_eqb qname_eq_dec qc qc' && Nat.eqb k k' && list_eqb nf_eqb_upto_proofs Cs Cs'
  | vk_record qr Is, vk_record qr' Is' => dec_eqb qname_eq_dec qr qr' && list_eqb nf_eqb_upto_proofs Is Is'
  | _, _ => false
  end.

(** Two keys of one view: the relation of statements, decided by
    [view_key_eqb]. *)
Definition view_key_eq (x y : view_key) : Prop := view_key_eqb x y = true.

#[export] Instance view_key_eq_Equivalence : Equivalence view_key_eq.
Proof.
  unfold view_key_eq; split.
  - intros [qc k Cs | qr Is]; cbn; rewrite dec_eqb_refl; [ rewrite Nat.eqb_refl |]; cbn;
      exact (Equivalence_Reflexive (Equivalence := nfs_eq_upto_proofs_Equivalence) _).
  - intros [qc k Cs | qr Is] [qc' k' Cs' | qr' Is'] H; cbn in *; try discriminate;
      repeat (apply andb_prop in H as [H ?]).
    + apply dec_eqb_true in H; apply Nat.eqb_eq in H1; subst qc' k'; rewrite dec_eqb_refl, Nat.eqb_refl; cbn.
      exact (Equivalence_Symmetric (Equivalence := nfs_eq_upto_proofs_Equivalence) _ _ H0).
    + apply dec_eqb_true in H; subst qr'; rewrite dec_eqb_refl; cbn.
      exact (Equivalence_Symmetric (Equivalence := nfs_eq_upto_proofs_Equivalence) _ _ H0).
  - intros [qc k Cs | qr Is] [qc' k' Cs' | qr' Is'] [qc'' k'' Cs'' | qr'' Is''] H H'; cbn in *; try discriminate;
      repeat (apply andb_prop in H as [H ?]); repeat (apply andb_prop in H' as [H' ?]).
    + apply dec_eqb_true in H, H'; apply Nat.eqb_eq in H1, H3; subst qc' qc'' k' k''; rewrite dec_eqb_refl, Nat.eqb_refl; cbn.
      exact (Equivalence_Transitive (Equivalence := nfs_eq_upto_proofs_Equivalence) _ _ _ H0 H2).
    + apply dec_eqb_true in H, H'; subst qr' qr''; rewrite dec_eqb_refl; cbn.
      exact (Equivalence_Transitive (Equivalence := nfs_eq_upto_proofs_Equivalence) _ _ _ H0 H1).
Qed.

(** A key among keys, up to the views they are of. *)
Definition key_in (x : view_key) (Vs : list view_key) : Prop := exists y, In y Vs /\ view_key_eq x y.

(** A key in a list is a key among it. *)
Lemma key_in_of_in : forall x Vs, In x Vs -> key_in x Vs.
Proof. intros x Vs H; exists x; split; [ exact H | reflexivity ]. Qed.

(** Whether a key is a record view's. *)
Definition vk_is_record (x : view_key) : bool := match x with vk_record _ _ => true | vk_ind _ _ _ => false end.

(** The type former a view's type is headed by: the container's member
    at an inductive view, the record type at a record view. *)
Definition view_key_head (x : view_key) : exp :=
  match x with vk_ind qc k _ => a_ind qc k | vk_record qr _ => a_record qr end.

(** The arguments a view's key fixes: the uniform arguments at an
    inductive view, the instance at a record view. *)
Definition view_key_args (x : view_key) : list nf :=
  match x with vk_ind _ _ Cs => Cs | vk_record _ Is => Is end.

(** Keys of one view have one head and, as many arguments, equal up to
    their proofs. *)
Lemma view_key_eq_parts : forall x y, view_key_eq x y ->
    view_key_head x = view_key_head y /\ vk_is_record x = vk_is_record y /\ nfs_eq_upto_proofs (view_key_args x) (view_key_args y).
Proof.
  unfold view_key_eq; intros [qc k Cs | qr Is] [qc' k' Cs' | qr' Is'] H; cbn in *; try discriminate;
    repeat (apply andb_prop in H as [H ?]).
  - apply dec_eqb_true in H; apply Nat.eqb_eq in H1; subst qc' k'; split; [ reflexivity | split; [ reflexivity | exact H0 ] ].
  - apply dec_eqb_true in H; subst qr'; split; [ reflexivity | split; [ reflexivity | exact H0 ] ].
Qed.

(** The pattern of the weakening from the context of an argument's
    [Self]-free parts into the context the argument is written in: [d]
    domains, the arguments before ([pat]), [np] parameters, then the [n]
    [Self]s, which the image avoids. *)
Definition classify_pat (d np n : nat) (pat : list bool) : list bool :=
  List.repeat false d ++ pat ++ List.repeat false np ++ List.repeat true n.

(** The preimage of a term under a pattern weakening, if it has one. *)
Definition image_pat (pat : list bool) (T : exp) : option exp :=
  if exp_eq_dec T T[unwk_pat pat]ʷ[wk_pat pat]ʷ then Some T[unwk_pat pat]ʷ else None.

(** The preimages of a list of terms, if each has one. *)
Fixpoint image_pats (pat : list bool) (Ts : list exp) : option (list exp) :=
  match Ts with
  | nil => Some nil
  | T :: Ts' =>
      match image_pat pat T, image_pats pat Ts' with
      | Some A, Some As => Some (A :: As)
      | _, _ => None
      end
  end.

(** The head and the arguments of an application spine. *)
Fixpoint app_head (M : exp) : exp :=
  match M with
  | a_app M _ => app_head M
  | _ => M
  end.

(** The arguments of an application spine, outermost first. *)
Fixpoint app_args (M : exp) : list exp :=
  match M with
  | a_app M N => app_args M ++ N :: nil
  | _ => nil
  end.

(** The position of the view of a key among the views: the first key of
    its view. *)
Fixpoint view_key_index (x : view_key) (Vs : list view_key) : option nat :=
  match Vs with
  | nil => None
  | y :: Vs' => if view_key_eqb x y then Some 0 else option_map S (view_key_index x Vs')
  end.

(** Whether the view of a key is among the views. *)
Definition view_key_mem (x : view_key) (Vs : list view_key) : bool :=
  match view_key_index x Vs with Some _ => true | None => false end.

(** Syntactic equality of keys is decidable. *)
Definition view_key_eq_dec (x y : view_key) : {x = y} + {x <> y}.
Proof.
  destruct x as [qc k Cs | qr Is], y as [qc' k' Cs' | qr' Is']; try (right; discriminate).
  - destruct (qname_eq_dec qc qc') as [<- |]; [| right; congruence ].
    destruct (Nat.eq_dec k k') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec nf_eq_dec Cs Cs') as [<- |]; [ left; reflexivity | right; congruence ].
  - destruct (qname_eq_dec qr qr') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec nf_eq_dec Is Is') as [<- |]; [ left; reflexivity | right; congruence ].
Defined.

(** The position of a key itself among the keys, syntactically: the tables
    aligned with the views found are read at the key found, its arguments
    as met, not at another key of its view. *)
Fixpoint view_key_pos (x : view_key) (Vs : list view_key) : option nat :=
  match Vs with
  | nil => None
  | y :: Vs' => if view_key_eq_dec x y then Some 0 else option_map S (view_key_pos x Vs')
  end.

(** A shape as classified, a nested occurrence at its instance, of the
    kind [K] of its instances: [view_inst] as the classification reads
    them, [view_key] once normalized; an argument as classified. *)
Inductive classified_ptyp_of (K : Set) : Set :=
(** The declared member [j] at the non-uniform parameters [Ps]. *)
| classified_ptyp_self : nat -> list exp -> classified_ptyp_of K
(** A nested occurrence: the view of the instance [x], not yet numbered,
    at the non-uniform parameters [Ns]. *)
| classified_ptyp_nest : K -> list exp -> classified_ptyp_of K
(** A function from a [Self]-free domain into a shape. *)
| classified_ptyp_pi : exp -> classified_ptyp_of K -> classified_ptyp_of K.
Arguments classified_ptyp_self {K}.
Arguments classified_ptyp_nest {K}.
Arguments classified_ptyp_pi {K}.

(** An argument as classified, its views not yet numbered. *)
Inductive classified_carg_of (K : Set) : Set :=
(** A non-recursive argument, of a [Self]-free type, of the kind the
    tag says. *)
| classified_carg_arg : abs_kind -> exp -> classified_carg_of K
(** A recursive argument, of a shape. *)
| classified_carg_rec_case : classified_ptyp_of K -> classified_carg_of K.
Arguments classified_carg_arg {K}.
Arguments classified_carg_rec_case {K}.

(** A shape and an argument as the classification reads them off a
    type, their instances as there *)
Notation written_ptyp := (classified_ptyp_of view_inst).
Notation written_carg := (classified_carg_of view_inst).

(** A shape and an argument classified, their instances normalized into
    the keys of their views *)
Notation classified_ptyp := (classified_ptyp_of view_key).
Notation classified_carg := (classified_carg_of view_key).

(** Whether a classified argument is recursive: its bit in the pattern of
    the arguments before the next one. *)
Definition classified_carg_bit {K} (g : classified_carg_of K) : bool :=
  match g with classified_carg_rec_case _ => true | classified_carg_arg _ _ => false end.

(** A classified argument at the kind [κ]: a non-recursive one takes it,
    a recursive one keeps its shape.  The syntactic classification
    ([classify_arg]) cannot see sorts; the command tags the non-recursive
    arguments by the sort their types infer to. *)
Definition classified_carg_tag {K} (κ : abs_kind) (g : classified_carg_of K) : classified_carg_of K :=
  match g with classified_carg_arg _ A => classified_carg_arg κ A | classified_carg_rec_case t => classified_carg_rec_case t end.

Lemma classified_carg_bit_tag : forall {K} κ (g : classified_carg_of K), classified_carg_bit (classified_carg_tag κ g) = classified_carg_bit g.
Proof. intros K κ [] ; reflexivity. Qed.

(** The views numbered: the view [v] is the member [n + v]. *)
Fixpoint classified_ptyp_num (n : nat) (Vs : list view_key) (t : classified_ptyp) : option ptyp :=
  match t with
  | classified_ptyp_self j Ps => Some (pt_self j Ps)
  | classified_ptyp_nest x Ns => option_map (fun v => pt_self (n + v) Ns) (view_key_index x Vs)
  | classified_ptyp_pi B t' => option_map (pt_pi B) (classified_ptyp_num n Vs t')
  end.

(** A classified argument with its views numbered. *)
Definition classified_carg_num (n : nat) (Vs : list view_key) (g : classified_carg) : option carg :=
  match g with
  | classified_carg_arg κ A => Some (ca_arg κ A)
  | classified_carg_rec_case t => option_map ca_rec (classified_ptyp_num n Vs t)
  end.

(** A constructor's classified arguments with their views numbered. *)
Fixpoint classified_cargs_num (n : nat) (Vs : list view_key) (gs : list classified_carg) : option (list carg) :=
  match gs with
  | nil => Some nil
  | g :: gs' =>
      match classified_carg_num n Vs g, classified_cargs_num n Vs gs' with
      | Some g', Some gs'' => Some (g' :: gs'')
      | _, _ => None
      end
  end.

(** A member's classified constructors with their views numbered. *)
Fixpoint classified_cons_num (n : nat) (Vs : list view_key) (cs : list (string * list classified_carg)) : option (list (string * list carg)) :=
  match cs with
  | nil => Some nil
  | (c, gs) :: cs' =>
      match classified_cargs_num n Vs gs, classified_cons_num n Vs cs' with
      | Some gs', Some cs'' => Some ((c, gs') :: cs'')
      | _, _ => None
      end
  end.

(** A [Self] occurs in the uniform arguments [Cs] of a nested occurrence,
    terms over the group's [nu] own uniform parameters, the [n] [Self]s and
    the frames' parameters: they are not in the image of the weakening past
    the [Self]s. *)
Definition selfs_occur (nu n : nat) (Cs : list exp) : bool :=
  let pat := List.repeat false nu ++ List.repeat true n in
  if list_eq_dec exp_eq_dec (List.map (fun C => C[unwk_pat pat]ʷ[wk_pat pat]ʷ) Cs) Cs then false else true.

(** ** The Guard of a Record Instance

    A record view's instance may mention the [Self]s only where a type
    former or a [Π] takes them: as an argument of a neutral head (a
    variable, a module member or an opaque global, a stuck elimination),
    which may compute with it, a [Self] would be read through a term the
    group cannot see.  [selfs_neutral_head lo n I]: the first neutral head
    of [I] an argument of which mentions a [Self] (the variables [lo] to
    [lo + n - 1], under the binders crossed), if any. *)

(** Whether a term mentions one of the variables [lo] to [lo + n - 1]. *)
Definition mentions_vars (lo n : nat) (M : exp) : bool :=
  match image_pat (List.repeat false lo ++ List.repeat true n) M with Some _ => false | None => true end.

(** Whether the head [h] of an application may take a [Self]: a type
    former, a record type, or a [Self] itself. *)
Definition head_takes_selfs (lo n : nat) (h : exp) : bool :=
  match h with
  | a_ind _ _ | a_record _ => true
  | a_var x => (lo <=? x) && (x <? lo + n)
  | _ => false
  end.

(** The first neutral head of [M] an argument of which mentions a [Self]
    (the variables [lo] to [lo + n - 1], shifted under the binders
    crossed), if any. *)
Fixpoint selfs_neutral_head (lo n : nat) (M : exp) {struct M} : option exp :=
  match M with
  | a_pi _ _ A B =>
      match selfs_neutral_head lo n A with
      | Some h => Some h
      | None => selfs_neutral_head (S lo) n B
      end
  | a_app M1 M2 =>
      if head_takes_selfs lo n (app_head M1) then
        match selfs_neutral_spine lo n M1 with
        | Some h => Some h
        | None => selfs_neutral_head lo n M2
        end
      else if existsb (mentions_vars lo n) (app_args M) then Some (app_head M1) else None
  | _ => None
  end
(** The arguments of an application spine whose head may take a [Self],
    each checked. *)
with selfs_neutral_spine (lo n : nat) (M : exp) {struct M} : option exp :=
  match M with
  | a_app M1 M2 =>
      match selfs_neutral_spine lo n M1 with
      | Some h => Some h
      | None => selfs_neutral_head lo n M2
      end
  | _ => None
  end.

(** No [Self] occurs as an argument of a neutral head in the instance
    [Is], over the group's [nu] uniform parameters, then its [n] [Self]s. *)
Definition selfs_guarded (nu n : nat) (Is : list exp) : bool :=
  forallb (fun I => match selfs_neutral_head nu n I with Some _ => false | None => true end) Is.

Section Classify.
  (** The number of uniform parameters of the filed group at [q], if its
      member [k] is a declared one. *)
  Variable (grp_nu : qname -> nat -> option nat).
  (** The number of parameters of the record at [q], if it is one. *)
  Variable (rec_np : qname -> option nat).
  Variables (nu np n : nat) (pat : list bool).

  (** A [Self_j] at the uniform parameters and Self-free non-uniform ones,
      under [d] domains: the variable [x] at [args]. *)
  Definition classify_self (d x : nat) (args : list exp) : option written_ptyp :=
    let b := (d + List.length pat + np)%nat in
    if (b <=? x) && (x <? b + n) then
      if list_eq_dec exp_eq_dec (List.firstn nu args) (vars_from (d + List.length pat + (np - nu)) nu)
      then option_map (classified_ptyp_self (n - 1 - (x - b))) (image_pats (classify_pat d np n pat) (List.skipn nu args))
      else None
    else None.

  (** A declared member [k] of a filed group at uniform arguments [Cs] in
      which a [Self] occurs, and no argument, domain or non-uniform
      parameter, and at Self-free non-uniform ones: the view [(qc, k, Cs)]. *)
  Definition classify_nest (d : nat) (qc : qname) (k : nat) (args : list exp) : option written_ptyp :=
    match grp_nu qc k with
    | Some m =>
        if m <=? List.length args then
          match image_pats (List.repeat true (d + List.length pat + (np - nu))) (List.firstn m args),
                image_pats (classify_pat d np n pat) (List.skipn m args) with
          | Some Cs, Some Ns => if selfs_occur nu n Cs then Some (classified_ptyp_nest (vi_ind qc k Cs) Ns) else None
          | _, _ => None
          end
        else None
    | None => None
    end.

  (** A record at all its parameters [args], an instance in which a [Self]
      occurs, and no argument, domain or non-uniform parameter, and only
      where a type former or a [Π] takes it ([selfs_guarded]): the record
      view [(qr, Is)], of no non-uniform parameter. *)
  Definition classify_record_view (d : nat) (qr : qname) (args : list exp) : option written_ptyp :=
    match rec_np qr with
    | Some m =>
        if Nat.eqb m (List.length args) then
          match image_pats (List.repeat true (d + List.length pat + (np - nu))) args with
          | Some Is => if selfs_occur nu n Is && selfs_guarded nu n Is then Some (classified_ptyp_nest (vi_record qr Is) nil) else None
          | None => None
          end
        else None
    | None => None
    end.

  (** A shape under [d] of its domains: [classify_self], [classify_nest],
      [classify_record_view], or a [Π] over a Self-free domain into a shape.  A
      [Self] thus occurs only strictly positively, and in a nested
      occurrence only in its uniform arguments, or in a record's
      instance. *)
  Fixpoint classify_shape (d : nat) (T : exp) : option written_ptyp :=
    match T with
    | a_pi ak_relevant ak_relevant B T' =>
        match image_pat (classify_pat d np n pat) B with
        | Some B0 => option_map (classified_ptyp_pi B0) (classify_shape (S d) T')
        | None => None
        end
    | _ =>
        match app_head T with
        | a_var x => classify_self d x (app_args T)
        | a_ind qc k => classify_nest d qc k (app_args T)
        | a_record qr => classify_record_view d qr (app_args T)
        | _ => None
        end
    end.

  (** An argument: Self-free (and free of the recursive arguments before
      it), or recursive of a shape. *)
  Definition classify_arg (T : exp) : option written_carg :=
    match image_pat (classify_pat 0 np n pat) T with
    | Some A => Some (classified_carg_arg ak_relevant A)
    | None => option_map classified_carg_rec_case (classify_shape 0 T)
    end.
End Classify.

(** No filed group: the classification as written finds no nested
    occurrence. *)
Definition grp_none : qname -> nat -> option nat := fun _ _ => None.

(** No filed record: the classification as written finds no record
    view. *)
Definition rec_none : qname -> option nat := fun _ => None.

(** The classification reads the records' parameter counts pointwise: any
    function equal to [rec_np] at every record classifies alike. *)
Lemma classify_shape_rec_ext : forall grp_nu rec_np rec_np', (forall qr, rec_np qr = rec_np' qr) ->
    forall nu np n pat T d, classify_shape grp_nu rec_np nu np n pat d T = classify_shape grp_nu rec_np' nu np n pat d T.
Proof.
  intros * Hr nu np n pat T; induction T; intros d; cbn [classify_shape];
    try (destruct (app_head _); try reflexivity; unfold classify_record_view; rewrite Hr; reflexivity).
  destruct (image_pat _ T1); [ rewrite IHT2 |]; reflexivity.
Qed.

Lemma classify_arg_rec_ext : forall grp_nu rec_np rec_np', (forall qr, rec_np qr = rec_np' qr) ->
    forall nu np n pat T, classify_arg grp_nu rec_np nu np n pat T = classify_arg grp_nu rec_np' nu np n pat T.
Proof. intros * Hr *; unfold classify_arg; rewrite (classify_shape_rec_ext _ _ _ Hr); reflexivity. Qed.

(** The instances a classified argument meets, in order: the one its
    shape ends in, if it ends in a nested occurrence. *)
Fixpoint classified_ptyp_view (t : classified_ptyp) : list view_key :=
  match t with
  | classified_ptyp_nest x _ => x :: nil
  | classified_ptyp_pi _ t' => classified_ptyp_view t'
  | classified_ptyp_self _ _ => nil
  end.

(** The instance a classified argument meets, if it is a nested
    occurrence. *)
Definition classified_carg_view (g : classified_carg) : list view_key :=
  match g with classified_carg_rec_case t => classified_ptyp_view t | classified_carg_arg _ _ => nil end.

(** The instances the constructors [cs] meet, constructors in order,
    arguments left to right. *)
Definition classified_cons_views (cs : list (string * list classified_carg)) : list view_key :=
  List.concat (List.map (fun c => List.concat (List.map classified_carg_view (snd c))) cs).

(** ** The Views of a Group

    The views are found, in order, from the instances the constructors meet:
    the declared members' constructors, then those of the views, in order
    (constructors in order, arguments left to right).  An instance met for
    the first time adds, at that point, the members of its own group at
    its arguments, in that group's order ([sibs x], normal; [x] is among
    them): the eliminator at a view reads back as the eliminator of the
    view's group, which needs a block for each of them.  An argument nested
    twice, as [List 0l (List 0l (Rose A))], meets the outer instance only;
    the inner one is met by the outer view's constructors: the outer
    instance comes first.  The search is depth first: the instances a
    view's constructors meet are met before the instances still queued, so
    the views come in reading order, as the recursive results do: for
    [node (xs : List (List T)) (o : Option T)] the members are [T],
    [List (List T)], [List T], [Option T].  [views_dfs sibs meets acc tr
    Vs]: from the views found so far, [acc], and the instances still to
    meet, [tr], in order, the views are [Vs]; a view found has the
    instances its constructors meet ([meets]) queued before the others.
    The command gives [sibs] and [meets] as tables of the instances it
    meets. *)

(** Those of [ss] not in [acc], in order, each once. *)
Fixpoint views_new (acc ss : list view_key) : list view_key :=
  match ss with
  | nil => nil
  | s :: ss' => if view_key_mem s acc then views_new acc ss' else s :: views_new (acc ++ s :: nil) ss'
  end.

(** The views an instance met for the first time adds: its siblings, and
    itself if they do not list it. *)
Definition views_met (sibs : view_key -> list view_key) (acc : list view_key) (x : view_key) : list view_key :=
  if view_key_mem x acc then nil else views_new acc (sibs x ++ x :: nil).

(** The views of a group, found depth first from the instances still to
    meet. *)
Inductive views_dfs (sibs meets : view_key -> list view_key) : list view_key -> list view_key -> list view_key -> Prop :=
(** No instance left to meet: the views are those found. *)
| views_dfs_done : forall acc, views_dfs sibs meets acc nil acc
(** The next instance adds its new views, and their instances are queued
    before the others. *)
| views_dfs_step : forall acc x tr Vs,
    views_dfs sibs meets (acc ++ views_met sibs acc x)
      (List.concat (List.map meets (views_met sibs acc x)) ++ tr) Vs ->
    views_dfs sibs meets acc (x :: tr) Vs.

(** The view at the index of a key is that key's view. *)
Lemma view_key_index_in : forall x Vs v, view_key_index x Vs = Some v ->
    exists y, List.nth_error Vs v = Some y /\ view_key_eq x y.
Proof.
  induction Vs as [| y Vs IH]; cbn; intros v H; [ discriminate |].
  destruct (view_key_eqb x y) eqn:Exy; [ injection H as <-; exists y; split; [ reflexivity | exact Exy ] |].
  destruct (view_key_index x Vs) as [v' |] eqn:E; cbn in H; [ injection H as <-; cbn; apply IH; reflexivity | discriminate ].
Qed.

(** The index is the first view of the key's view. *)
Lemma view_key_index_first : forall x Vs v, view_key_index x Vs = Some v ->
    forall w y, w < v -> List.nth_error Vs w = Some y -> ~ view_key_eq x y.
Proof.
  induction Vs as [| z Vs IH]; cbn; intros v H; [ discriminate |].
  destruct (view_key_eqb x z) eqn:Exz; [ injection H as <-; intros w y Hw; lia |].
  destruct (view_key_index x Vs) as [v' |] eqn:E; cbn in H; [ injection H as <- | discriminate ].
  intros [| w] y Hw Hy; cbn in Hy; [ injection Hy as <-; unfold view_key_eq; congruence |].
  exact (IH _ eq_refl w y ltac:(lia) Hy).
Qed.

(** A key has an index exactly when its view is among the views. *)
Lemma view_key_mem_spec : forall x Vs, view_key_mem x Vs = true <-> key_in x Vs.
Proof.
  unfold view_key_mem, key_in; induction Vs as [| y Vs IH]; cbn.
  - split; [ discriminate | intros (? & [] & _) ].
  - destruct (view_key_eqb x y) eqn:Exy; [ split; [ intros _; exists y; split; [ left; reflexivity | exact Exy ] | reflexivity ] |].
    assert (E : (match option_map S (view_key_index x Vs) with Some _ => true | None => false end) =
                (match view_key_index x Vs with Some _ => true | None => false end))
      by (destruct (view_key_index x Vs); reflexivity).
    rewrite E, IH; split.
    + intros (z & Hz & Hxz); exists z; split; [ right; exact Hz | exact Hxz ].
    + intros (z & [<- | Hz] & Hxz); [ unfold view_key_eq in Hxz; congruence | exists z; split; assumption ].
Qed.

(** A key among the views has an index. *)
Lemma view_key_index_in_some : forall x Vs, key_in x Vs -> exists v, view_key_index x Vs = Some v.
Proof.
  intros x Vs H; apply view_key_mem_spec in H; unfold view_key_mem in H.
  destruct (view_key_index x Vs) as [v |]; [ exists v; reflexivity | discriminate ].
Qed.

(** Among keys one more key: among the first, or of its view. *)
Lemma key_in_snoc : forall x acc s, key_in x (acc ++ s :: nil) -> key_in x acc \/ view_key_eq x s.
Proof.
  intros x acc s (y & Hy & Hxy); apply List.in_app_or in Hy as [Hy | [<- | []]];
    [ left; exists y; split; assumption | right; exact Hxy ].
Qed.

(** A key of [ss] is of a view found before or among the new ones. *)
Lemma views_new_in : forall acc ss x, In x ss -> key_in x acc \/ key_in x (views_new acc ss).
Proof.
  intros acc ss; revert acc; induction ss as [| s ss IH]; cbn; intros acc x H; [ destruct H |].
  destruct (view_key_mem s acc) eqn:Es.
  - destruct H as [<- | H]; [ left; apply view_key_mem_spec; exact Es | exact (IH _ _ H) ].
  - destruct H as [<- | H]; [ right; apply key_in_of_in; left; reflexivity |].
    destruct (IH (acc ++ s :: nil) x H) as [H' | (y & Hy & Hxy)]; [| right; exists y; split; [ right; exact Hy | exact Hxy ] ].
    destruct (key_in_snoc _ _ _ H') as [H'' | H'']; [ left; exact H'' | right; exists s; split; [ left; reflexivity | exact H'' ] ].
Qed.

Lemma views_dfs_incl : forall sibs meets acc tr Vs, views_dfs sibs meets acc tr Vs -> forall y, In y acc -> In y Vs.
Proof. induction 1; intros y Hy; [ exact Hy | apply IHviews_dfs, List.in_or_app; left; exact Hy ]. Qed.

(** Two runs from the same state whose tables agree at the views both find,
    and give an instance not found no sibling but itself, find the same
    views.  An instance met first is then found itself, not another
    instance of its view: the view's first instance met is its key. *)
Lemma views_dfs_functional : forall sibs1 meets1 acc tr Vs1, views_dfs sibs1 meets1 acc tr Vs1 ->
    forall sibs2 meets2 Vs2, views_dfs sibs2 meets2 acc tr Vs2 ->
    (forall x, In x Vs1 -> In x Vs2 -> sibs1 x = sibs2 x /\ meets1 x = meets2 x) ->
    (forall x, ~ In x Vs1 -> sibs1 x = x :: nil) -> (forall x, ~ In x Vs2 -> sibs2 x = x :: nil) -> Vs1 = Vs2.
Proof.
  induction 1 as [acc | acc x tr Vs1 H1 IH]; intros sibs2 meets2 Vs2 H2 Hag Hd1 Hd2; inversion H2; subst; [ reflexivity |].
  match goal with H : views_dfs sibs2 meets2 _ _ Vs2 |- _ => rename H into H5 end.
  assert (Hm : views_met sibs1 acc x = views_met sibs2 acc x).
  { destruct (view_key_mem x acc) eqn:Ex; [ unfold views_met; rewrite Ex; reflexivity |].
    (* An instance met first is a view found itself: else it has no
       siblings, and is the one view it adds. *)
    assert (Hx : forall sibs meets tr' Vs, views_dfs sibs meets (acc ++ views_met sibs acc x) tr' Vs ->
                 (~ In x Vs -> sibs x = x :: nil) -> In x Vs).
    { intros * Hb Hd; destruct (in_dec view_key_eq_dec x Vs) as [Hi | Hi]; [ exact Hi |].
      apply (views_dfs_incl _ _ _ _ _ Hb), List.in_or_app; right.
      unfold views_met; rewrite Ex, (Hd Hi); cbn; rewrite Ex; left; reflexivity. }
    pose proof (proj1 (Hag x (Hx _ _ _ _ H1 (Hd1 x)) (Hx _ _ _ _ H5 (Hd2 x)))) as Es.
    unfold views_met; rewrite Ex, Es; reflexivity. }
  assert (Hms : List.map meets1 (views_met sibs1 acc x) = List.map meets2 (views_met sibs1 acc x)).
  { apply List.map_ext_in; intros y Hy.
    assert (Hy1 : In y Vs1) by (apply (views_dfs_incl _ _ _ _ _ H1), List.in_or_app; right; exact Hy).
    assert (Hy2 : In y Vs2) by (rewrite Hm in Hy; apply (views_dfs_incl _ _ _ _ _ H5), List.in_or_app; right; exact Hy).
    exact (proj2 (Hag y Hy1 Hy2)). }
  apply (IH sibs2 meets2); [| exact Hag | exact Hd1 | exact Hd2 ].
  rewrite Hms, Hm; exact H5.
Qed.

(** The siblings and the instances met of an instance, read off tables
    aligned with the views; an instance not among them is alone and meets
    nothing. *)
Definition siblings_table (Vs : list view_key) (Ss : list (list view_key)) (x : view_key) : list view_key :=
  match view_key_pos x Vs with Some v => List.nth v Ss (x :: nil) | None => x :: nil end.

(** The instances the constructors of a view meet, read off a table
    aligned with the views. *)
Definition meets_table (Vs : list view_key) (Cs : list (list (string * list classified_carg))) (x : view_key) : list view_key :=
  match view_key_pos x Vs with Some v => classified_cons_views (List.nth v Cs nil) | None => nil end.

(** A key not among the views has no siblings but itself. *)
Lemma siblings_table_absent : forall Vs Ss x, ~ In x Vs -> siblings_table Vs Ss x = x :: nil.
Proof.
  intros * Hx; unfold siblings_table.
  enough (E : view_key_pos x Vs = None) by (rewrite E; reflexivity).
  induction Vs as [| y Vs IH]; cbn; [ reflexivity |].
  destruct (view_key_eq_dec x y) as [-> | _]; [ exfalso; apply Hx; left; reflexivity |].
  rewrite IH; [ reflexivity | intros H; apply Hx; right; exact H ].
Qed.

(** The position of a key is at that key. *)
Lemma view_key_pos_in : forall x Vs v, view_key_pos x Vs = Some v -> List.nth_error Vs v = Some x.
Proof.
  induction Vs as [| y Vs IH]; cbn; intros v H; [ discriminate |].
  destruct (view_key_eq_dec x y) as [-> | _]; [ injection H as <-; reflexivity |].
  destruct (view_key_pos x Vs) as [v' |] eqn:E; cbn in H; [ injection H as <-; cbn; apply IH; reflexivity | discriminate ].
Qed.

(** A key among the keys has a position. *)
Lemma view_key_pos_in_some : forall x Vs, In x Vs -> exists v, view_key_pos x Vs = Some v.
Proof.
  induction Vs as [| y Vs IH]; cbn; intros H; [ destruct H |].
  destruct (view_key_eq_dec x y) as [-> | Hne]; [ exists 0; reflexivity |].
  destruct H as [-> | H]; [ congruence |].
  destruct (IH H) as [v ->]; exists (S v); reflexivity.
Qed.

(** ** The Order of the Filed Views

    The inductive views are filed in the order found ([views_dfs]: depth
    first, pre-order).  The record views come after them, by record height:
    [0] for one none of whose fields meets a record view, else one more
    than the highest record view its fields meet, the views met through an
    inductive view not counted (a leaf path stops there).  Ties keep the
    order found.  A record view's fields then end only in record views
    before it ([rview_order_ok]): the height drops along each field
    ([record_height_drop]), and the sort puts lower heights first
    ([sort_by_height_lt]).  The heights are computed in as many rounds as
    there are record views, as the rank of the views is ([grp_rank]). *)

(** The record views among the keys [xs], in order. *)
Definition record_keys (xs : list view_key) : list view_key := List.filter vk_is_record xs.

(** The inductive views among the keys [xs], in order. *)
Definition ind_keys (xs : list view_key) : list view_key := List.filter (fun x => negb (vk_is_record x)) xs.

(** The record height of [x] after [m] rounds, its fields meeting
    [meets x]. *)
Fixpoint record_height_iter (meets : view_key -> list view_key) (m : nat) (x : view_key) : nat :=
  match m with
  | 0 => 0
  | S m' =>
      match record_keys (meets x) with
      | nil => 0
      | ys => S (List.fold_right Nat.max 0 (List.map (record_height_iter meets m') ys))
      end
  end.

(** The record height of [x], in as many rounds as the views [Vs] have
    record views. *)
Definition record_height (meets : view_key -> list view_key) (Vs : list view_key) (x : view_key) : nat :=
  record_height_iter meets (List.length (record_keys Vs)) x.

(** [x] inserted into [l] after every key of [l] no higher than it. *)
Fixpoint insert_by_height (h : view_key -> nat) (x : view_key) (l : list view_key) : list view_key :=
  match l with
  | nil => x :: nil
  | y :: l' => if h x <? h y then x :: l else y :: insert_by_height h x l'
  end.

(** The keys [l] sorted by [h], stably: ties keep their order in [l]. *)
Definition sort_by_height (h : view_key -> nat) (l : list view_key) : list view_key :=
  List.fold_left (fun acc x => insert_by_height h x acc) l nil.

(** The keys of the views filed after the declared members: the inductive
    views in the order found, then the record views by height. *)
Definition filed_keys (meets : view_key -> list view_key) (Vs : list view_key) : list view_key :=
  ind_keys Vs ++ sort_by_height (record_height meets Vs) (record_keys Vs).

(** The height of a record view is above that of each record view its
    fields meet, where the height of that one is stable. *)
Lemma record_height_drop : forall meets m x y, In y (record_keys (meets x)) ->
    record_height_iter meets m y = record_height_iter meets (S m) y ->
    record_height_iter meets (S m) y < record_height_iter meets (S m) x.
Proof.
  intros * Hy Hs; rewrite <- Hs; cbn [record_height_iter].
  assert (Hle : forall l, In y l ->
            record_height_iter meets m y <= List.fold_right Nat.max 0 (List.map (record_height_iter meets m) l)).
  { induction l as [| z zs IH]; intros Hin; cbn in *; [ destruct Hin |].
    destruct Hin as [-> | Hin]; [ lia | specialize (IH Hin); lia ]. }
  destruct (record_keys (meets x)) as [| y0 ys] eqn:E; [ destruct Hy |].
  specialize (Hle _ Hy); lia.
Qed.

Lemma insert_by_height_in : forall h x l y, In y (insert_by_height h x l) <-> y = x \/ In y l.
Proof.
  intros h x l; induction l as [| z l IH]; intros y; cbn [insert_by_height].
  - cbn; split; intros H; intuition subst; auto.
  - destruct (h x <? h z); cbn [In]; [| rewrite IH ]; split; intros H; intuition subst; auto.
Qed.

(** The sort keeps the keys. *)
Lemma sort_by_height_in : forall h l y, In y (sort_by_height h l) <-> In y l.
Proof.
  intros h l; unfold sort_by_height.
  enough (H : forall acc y, In y (List.fold_left (fun acc x => insert_by_height h x acc) l acc) <-> In y acc \/ In y l)
    by (intros y; rewrite H; cbn; split; intros Hy; intuition).
  induction l as [| x l IH]; intros acc y; cbn; [ split; intros Hy; intuition |].
  rewrite IH, insert_by_height_in; split; intros Hy; intuition subst; auto.
Qed.

(** The keys sorted by height: no key higher than one after it. *)
Definition height_sorted (h : view_key -> nat) : list view_key -> Prop := Sorted (fun a b => h a <= h b).

(** Inserting keeps the keys sorted. *)
Lemma insert_by_height_sorted : forall h x l, height_sorted h l -> height_sorted h (insert_by_height h x l).
Proof.
  unfold height_sorted; intros h x l H; induction H as [| z l Hl IH Hhd]; cbn [insert_by_height].
  - repeat constructor.
  - destruct (h x <? h z) eqn:E.
    + apply Nat.ltb_lt in E; constructor; [ constructor; assumption | constructor; lia ].
    + apply Nat.ltb_ge in E; constructor; [ exact IH |].
      destruct l as [| w l]; cbn [insert_by_height]; [ constructor; lia |].
      destruct (h x <? h w); constructor; [ lia | inversion Hhd; assumption ].
Qed.

Lemma sort_by_height_sorted : forall h l, height_sorted h (sort_by_height h l).
Proof.
  intros h l; unfold sort_by_height.
  enough (H : forall acc, height_sorted h acc -> height_sorted h (List.fold_left (fun acc x => insert_by_height h x acc) l acc))
    by (apply H; constructor).
  induction l as [| x l IH]; intros acc Hacc; cbn; [ exact Hacc | apply IH, insert_by_height_sorted, Hacc ].
Qed.

(** A key of a sorted list is no higher than one at a later index. *)
Lemma height_sorted_nth : forall h l, height_sorted h l ->
    forall i j a b, List.nth_error l i = Some a -> List.nth_error l j = Some b -> i < j -> h a <= h b.
Proof.
  intros h l Hs; apply Sorted_StronglySorted in Hs; [| intros ? ? ?; lia ].
  induction Hs as [| z l _ IH Hall]; intros [| i] [| j] a b Ha Hb Hij; cbn in Ha, Hb; try discriminate; try lia.
  - injection Ha as <-; rewrite List.Forall_forall in Hall; exact (Hall b (List.nth_error_In _ _ Hb)).
  - exact (IH i j a b Ha Hb ltac:(lia)).
Qed.

(** In the keys sorted by height, a lower key comes first. *)
Lemma sort_by_height_lt : forall h l i j a b, List.nth_error (sort_by_height h l) i = Some a ->
    List.nth_error (sort_by_height h l) j = Some b -> h b < h a -> j < i.
Proof.
  intros * Ha Hb Hab.
  destruct (Compare_dec.lt_eq_lt_dec i j) as [[Hij | ->] | Hji]; [| | exact Hji ].
  - pose proof (height_sorted_nth _ _ (sort_by_height_sorted h l) _ _ _ _ Ha Hb Hij); lia.
  - rewrite Ha in Hb; injection Hb as ->; lia.
Qed.
