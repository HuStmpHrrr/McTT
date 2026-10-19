(** * Groups of Inductive Types: Members, and the Classification of Arguments

    A group ([ind_decl], in [Syntax]) has members: the types it declares,
    then its views, the instances of types of earlier groups its
    constructors nest through.  This file reads a member off a group (its
    type former, its uniform arguments, its constructors) and states the
    classification of an argument type in normal form, which decides
    whether an argument is recursive, and in which member: the one rule of
    positivity (the command, [Core.Syntactic.System.Command], normalizes an
    argument type and classifies its normal form). *)

From Stdlib Require Import List String PeanoNat Bool.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations Sub_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Decidable Equality of Terms

    The pieces of syntax generic in the sorts of terms and entries are
    decided given deciders for those; the terms then by a mutual
    recursion that passes itself to them. *)

Section GenericDec.
  Context {E C : Set} (de : forall x y : E, {x = y} + {x <> y}) (dc : forall x y : C, {x = y} + {x <> y}).

  Fixpoint ptyp_eq_dec_g (t t' : ptyp_g E) {struct t} : {t = t'} + {t <> t'}.
  Proof.
    destruct t as [k Ps | A t], t' as [k' Ps' | A' t']; try (right; discriminate).
    - destruct (Nat.eq_dec k k') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec de Ps Ps') as [<- |]; [ left; reflexivity | right; congruence ].
    - destruct (de A A') as [<- |]; [| right; congruence ].
      destruct (ptyp_eq_dec_g t t') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition carg_eq_dec_g (g g' : carg_g E) : {g = g'} + {g <> g'}.
  Proof.
    destruct g as [A | t], g' as [A' | t']; try (right; discriminate).
    - destruct (de A A') as [<- |]; [ left; reflexivity | right; congruence ].
    - destruct (ptyp_eq_dec_g t t') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition cons_eq_dec_g (cs cs' : list (string * list (carg_g E))) : {cs = cs'} + {cs <> cs'}.
  Proof.
    revert cs'; induction cs as [| [c gs] cs IH]; intros [| [c' gs'] cs']; try (right; discriminate);
      [ left; reflexivity |].
    destruct (string_dec c c') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec carg_eq_dec_g gs gs') as [<- |]; [| right; congruence ].
    destruct (IH cs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition mhead_eq_dec_g (h h' : mhead_g E) : {h = h'} + {h <> h'}.
  Proof.
    destruct h as [p | qc k Is vm], h' as [p' | qc' k' Is' vm']; try (right; discriminate).
    - destruct (qname_eq_dec p p') as [<- |]; [ left; reflexivity | right; congruence ].
    - destruct (qname_eq_dec qc qc') as [<- |]; [| right; congruence ].
      destruct (Nat.eq_dec k k') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec de Is Is') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec Nat.eq_dec vm vm') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition imember_eq_dec_g (M M' : imember_g E C) : {M = M'} + {M <> M'}.
  Proof.
    destruct M as [h ps cs], M' as [h' ps' cs'].
    destruct (mhead_eq_dec_g h h') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec dc ps ps') as [<- |]; [| right; congruence ].
    destruct (cons_eq_dec_g cs cs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition ind_decl_eq_dec_g (D D' : ind_decl_g E C) : {D = D'} + {D <> D'}.
  Proof.
    destruct D as [us S ms], D' as [us' S' ms'].
    destruct (list_eq_dec dc us us') as [<- |]; [| right; congruence ].
    destruct (de S S') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec imember_eq_dec_g ms ms') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition brs_eq_dec_g (Bs Bs' : list (string * nat * E)) : {Bs = Bs'} + {Bs <> Bs'}.
  Proof.
    revert Bs'; induction Bs as [| [[c n] B] Bs IH]; intros [| [[c' n'] B'] Bs']; try (right; discriminate);
      [ left; reflexivity |].
    destruct (string_dec c c') as [<- |]; [| right; congruence ].
    destruct (Nat.eq_dec n n') as [<- |]; [| right; congruence ].
    destruct (de B B') as [<- |]; [| right; congruence ].
    destruct (IH Bs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition eblocks_eq_dec_g (Bks Bks' : list (eblock_g E)) : {Bks = Bks'} + {Bks <> Bks'}.
  Proof.
    revert Bks'; induction Bks as [| [nm oZ A Bs] Bks IH]; intros [| [nm' oZ' A' Bs'] Bks']; try (right; discriminate);
      [ left; reflexivity |].
    destruct (Nat.eq_dec nm nm') as [<- |]; [| right; congruence ].
    assert (HZ : {oZ = oZ'} + {oZ <> oZ'})
      by (destruct oZ as [Z |], oZ' as [Z' |]; try (right; discriminate); [| left; reflexivity ];
          destruct (de Z Z') as [<- |]; [ left; reflexivity | right; congruence ]).
    destruct HZ as [<- |]; [| right; congruence ].
    destruct (de A A') as [<- |]; [| right; congruence ].
    destruct (brs_eq_dec_g Bs Bs') as [<- |]; [| right; congruence ].
    destruct (IH Bks') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.
End GenericDec.

Fixpoint exp_eq_dec (M N : exp) {struct M} : {M = N} + {M <> N}
with modexp_eq_dec (M N : modexp) {struct M} : {M = N} + {M <> N}
with bnd_eq_dec (M N : bnd) {struct M} : {M = N} + {M <> N}
with gunit_eq_dec (M N : gunit) {struct M} : {M = N} + {M <> N}
with moddef_eq_dec (M N : moddef) {struct M} : {M = N} + {M <> N}
with gmod_eq_dec (M N : gmod) {struct M} : {M = N} + {M <> N}
with gentry_eq_dec (M N : gentry) {struct M} : {M = N} + {M <> N}
with centry_eq_dec (M N : centry) {struct M} : {M = N} + {M <> N}.
Proof.
  all: decide equality;
    first [ apply Nat.eq_dec | apply string_dec | apply qname_eq_dec | apply bool_dec
          | apply list_eq_dec, string_dec | apply o2_eq_dec | apply (list_eq_dec exp_eq_dec)
          | apply (list_eq_dec centry_eq_dec) | apply (eblocks_eq_dec_g exp_eq_dec)
          | apply (ind_decl_eq_dec_g exp_eq_dec centry_eq_dec) | idtac ].
  all: try (decide equality; fail).
  all: try (decide equality; apply qname_eq_dec).
  (* the items of an open *)
  apply list_eq_dec; intros; repeat (decide equality || apply string_dec || apply bool_dec).
Defined.

(** Decidable equality of the views of classification. *)
Definition rview_eq_dec (x y : (qname * nat * list exp)%type) : {x = y} + {x <> y}.
Proof.
  destruct x as [[qc k] Cs], y as [[qc' k'] Cs'].
  destruct (qname_eq_dec qc qc') as [<- |]; [| right; congruence ].
  destruct (Nat.eq_dec k k') as [<- |]; [| right; congruence ].
  destruct (list_eq_dec exp_eq_dec Cs Cs') as [<- |]; [ left; reflexivity | right; congruence ].
Defined.

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
  List.rev (List.map (fun g => match g with ca_rec _ => true | ca_arg _ => false end) gs).

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
    [Is] instantiated by [Us]. *)

Definition im_ref (pq : qname) (k : nat) (M : imember) : (qname * nat)%type :=
  match im_head M with
  | mh_decl _ => (pq, k)
  | mh_view qc k' _ _ => (qc, k')
  end.

Definition im_pre (M : imember) (Us : list exp) : list exp :=
  match im_head M with
  | mh_decl _ => Us
  | mh_view _ _ Is _ => List.map (fun I => I[sb_of_list sb_id Us]) Is
  end.

Definition im_ty_at (pq : qname) (k : nat) (M : imember) (Us Ns : list exp) : typ :=
  apps_exp (a_ind (fst (im_ref pq k M)) (snd (im_ref pq k M))) (im_pre M Us ++ Ns).

Definition im_con (M : imember) (c : string) : option (list carg) := cons_lookup (im_cons M) c.

Definition im_is_decl (M : imember) : bool :=
  match im_head M with mh_decl _ => true | mh_view _ _ _ _ => false end.

(** The declared members come first: [ind_ndecl D] of them, then the
    views. *)
Definition ind_ndecl (D : ind_decl) : nat := List.length (List.filter im_is_decl (ind_members D)).

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

    [cls_wkd d np n gs1] sends the context of the domains, the
    non-recursive arguments before, the parameters and the frames into the
    full one: a term in its image mentions no recursive argument and no
    [Self]. *)

(** A view during classification. *)
Definition rview : Set := (qname * nat * list exp)%type.

Definition cls_wkd (d np n : nat) (gs1 : list carg) : wk :=
  wk_pat (List.repeat false d ++ cargs_pat gs1 ++ List.repeat false np ++ List.repeat true n).

(** A [Self] occurs in the uniform arguments [Cs] of a nested occurrence,
    terms over the group's [nu] own uniform parameters, the [n] [Self]s and
    the frames' parameters: they are not in the image of the weakening past
    the [Self]s. *)
Definition selfs_occur (nu n : nat) (Cs : list exp) : bool :=
  let pat := List.repeat false nu ++ List.repeat true n in
  if list_eq_dec exp_eq_dec (List.map (fun C => C[unwk_pat pat]ʷ[wk_pat pat]ʷ) Cs) Cs then false else true.

Section Classify.
  (** The number of uniform parameters of the filed group at [q]. *)
  Variable (grp_nu : qname -> option nat).
  Variables (Vs : list rview) (nu np n : nat) (gs1 : list carg).

  (** A shape under [d] of its domains: a [Self] at the uniform parameters
      and Self-free non-uniform ones; a declared member [k] of a filed
      group at uniform arguments [Cs] in which a [Self] occurs, and no
      argument, domain or non-uniform parameter, and at Self-free
      non-uniform ones: the view [(q, k, Cs)]; or a [Π] over a Self-free
      domain into a shape.  A [Self] thus occurs only strictly positively,
      and in a nested occurrence only in its uniform arguments. *)
  Inductive cls_sh : nat -> exp -> ptyp -> Prop :=
  | cls_sh_self : forall d j Ps,
      j < n ->
      cls_sh d
        (apps_exp (a_var (d + List.length gs1 + np + (n - 1 - j)))
           (vars_from (d + List.length gs1 + (np - nu)) nu ++ List.map (fun P => P[cls_wkd d np n gs1]ʷ) Ps))
        (pt_self j Ps)
  | cls_sh_nest : forall d qc k Cs Ns v,
      grp_nu qc = Some (List.length Cs) ->
      List.nth_error Vs v = Some (qc, k, Cs) ->
      selfs_occur nu n Cs = true ->
      cls_sh d
        (apps_exp (a_ind qc k)
           (List.map (fun C => C[wk_shiftn (d + List.length gs1 + (np - nu))]ʷ) Cs ++
            List.map (fun P => P[cls_wkd d np n gs1]ʷ) Ns))
        (pt_self (n + v) Ns)
  | cls_sh_pi : forall d B T t,
      cls_sh (S d) T t ->
      cls_sh d (a_pi B[cls_wkd d np n gs1]ʷ T) (pt_pi B t).

  (** An argument: Self-free (and free of the recursive arguments before
      it), or recursive of a shape. *)
  Inductive cls_nf : exp -> carg -> Prop :=
  | cls_nf_free : forall A, cls_nf A[cls_wkd 0 np n gs1]ʷ (ca_arg A)
  | cls_nf_rec : forall T t, cls_sh 0 T t -> cls_nf T (ca_rec t).
End Classify.

(** The views a classified argument meets, in order: the view of the
    shape it ends in, if it ends in one. *)
Definition carg_view (n : nat) (g : carg) : list nat :=
  match g with
  | ca_rec t => if n <=? ptyp_mem t then ptyp_mem t - n :: nil else nil
  | ca_arg _ => nil
  end.

(** The views the constructors [cs] meet, constructors in order, arguments
    left to right. *)
Definition cons_views (n : nat) (cs : list (string * list carg)) : list nat :=
  List.concat (List.map (fun c => List.concat (List.map (carg_view n) (snd c))) cs).

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
    instance comes first.  [views_enum sibs acc tr]: the views after those
    found so far, [acc], meet the instances [tr].  The command gives
    [sibs] as a table of the instances it meets, each entry normalized
    there. *)

(** [acc] followed by those of [ss] not in it, in order. *)
Fixpoint views_add (acc ss : list rview) : list rview :=
  match ss with
  | nil => acc
  | s :: ss' => views_add (if List.in_dec rview_eq_dec s acc then acc else acc ++ s :: nil) ss'
  end.

Fixpoint views_enum (sibs : rview -> list rview) (acc tr : list rview) : list rview :=
  match tr with
  | nil => acc
  | x :: tr' => views_enum sibs (if List.in_dec rview_eq_dec x acc then acc else views_add acc (sibs x)) tr'
  end.

(** The siblings of an instance, read off a table, the instance alone if
    it has no entry. *)
Fixpoint sibs_of (tbl : list (rview * list rview)) (x : rview) : list rview :=
  match tbl with
  | nil => x :: nil
  | (y, ss) :: tbl' => if rview_eq_dec x y then ss else sibs_of tbl' x
  end.
