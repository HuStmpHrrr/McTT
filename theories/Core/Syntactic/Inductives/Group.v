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
          | apply (ind_decl_eq_dec_g exp_eq_dec centry_eq_dec)
          | (decide equality; apply (list_eq_dec exp_eq_dec)) | idtac ].
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

    [cls_pat d np n pat] is the pattern of the weakening that sends the
    context of the domains, the non-recursive arguments before ([pat] tells,
    innermost first, which arguments before are recursive), the parameters
    and the frames into the full one: a term in its image mentions no
    recursive argument and no [Self].

    The classification is a function, written as a recognizer: a term is in
    the image of a pattern weakening exactly when it is the image of its own
    preimage candidate ([img_pat]).  A nested occurrence is classified with
    its instance, not yet numbered ([rptyp]); the command numbers the views
    once it has found them all ([rptyp_num]). *)

(** A view during classification. *)
Definition rview : Set := (qname * nat * list exp)%type.

Definition cls_pat (d np n : nat) (pat : list bool) : list bool :=
  List.repeat false d ++ pat ++ List.repeat false np ++ List.repeat true n.

(** The preimage of a term under a pattern weakening, if it has one. *)
Definition img_pat (pat : list bool) (T : exp) : option exp :=
  if exp_eq_dec T T[unwk_pat pat]ʷ[wk_pat pat]ʷ then Some T[unwk_pat pat]ʷ else None.

Fixpoint img_pats (pat : list bool) (Ts : list exp) : option (list exp) :=
  match Ts with
  | nil => Some nil
  | T :: Ts' =>
      match img_pat pat T, img_pats pat Ts' with
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

Fixpoint app_args (M : exp) : list exp :=
  match M with
  | a_app M N => app_args M ++ N :: nil
  | _ => nil
  end.

(** The position of an instance among the views. *)
Fixpoint rview_index (x : rview) (Vs : list rview) : option nat :=
  match Vs with
  | nil => None
  | y :: Vs' => if rview_eq_dec x y then Some 0 else option_map S (rview_index x Vs')
  end.

Definition rview_mem (x : rview) (Vs : list rview) : bool :=
  match rview_index x Vs with Some _ => true | None => false end.

(** A shape as classified, a nested occurrence at its instance; an
    argument as classified. *)
Inductive rptyp : Set :=
| rp_self : nat -> list exp -> rptyp
| rp_nest : rview -> list exp -> rptyp
| rp_pi : exp -> rptyp -> rptyp.

Inductive rcarg : Set :=
| rc_arg : exp -> rcarg
| rc_rec : rptyp -> rcarg.

Definition rcarg_bit (g : rcarg) : bool := match g with rc_rec _ => true | rc_arg _ => false end.

(** The views numbered: the view [v] is the member [n + v]. *)
Fixpoint rptyp_num (n : nat) (Vs : list rview) (t : rptyp) : option ptyp :=
  match t with
  | rp_self j Ps => Some (pt_self j Ps)
  | rp_nest x Ns => option_map (fun v => pt_self (n + v) Ns) (rview_index x Vs)
  | rp_pi B t' => option_map (pt_pi B) (rptyp_num n Vs t')
  end.

Definition rcarg_num (n : nat) (Vs : list rview) (g : rcarg) : option carg :=
  match g with
  | rc_arg A => Some (ca_arg A)
  | rc_rec t => option_map ca_rec (rptyp_num n Vs t)
  end.

Fixpoint rcargs_num (n : nat) (Vs : list rview) (gs : list rcarg) : option (list carg) :=
  match gs with
  | nil => Some nil
  | g :: gs' =>
      match rcarg_num n Vs g, rcargs_num n Vs gs' with
      | Some g', Some gs'' => Some (g' :: gs'')
      | _, _ => None
      end
  end.

Fixpoint rcons_num (n : nat) (Vs : list rview) (cs : list (string * list rcarg)) : option (list (string * list carg)) :=
  match cs with
  | nil => Some nil
  | (c, gs) :: cs' =>
      match rcargs_num n Vs gs, rcons_num n Vs cs' with
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

Section Classify.
  (** The number of uniform parameters of the filed group at [q], if its
      member [k] is a declared one. *)
  Variable (grp_nu : qname -> nat -> option nat).
  Variables (nu np n : nat) (pat : list bool).

  (** A [Self_j] at the uniform parameters and Self-free non-uniform ones,
      under [d] domains: the variable [x] at [args]. *)
  Definition cls_self (d x : nat) (args : list exp) : option rptyp :=
    let b := (d + List.length pat + np)%nat in
    if (b <=? x) && (x <? b + n) then
      if list_eq_dec exp_eq_dec (List.firstn nu args) (vars_from (d + List.length pat + (np - nu)) nu)
      then option_map (rp_self (n - 1 - (x - b))) (img_pats (cls_pat d np n pat) (List.skipn nu args))
      else None
    else None.

  (** A declared member [k] of a filed group at uniform arguments [Cs] in
      which a [Self] occurs, and no argument, domain or non-uniform
      parameter, and at Self-free non-uniform ones: the view [(qc, k, Cs)]. *)
  Definition cls_nest (d : nat) (qc : qname) (k : nat) (args : list exp) : option rptyp :=
    match grp_nu qc k with
    | Some m =>
        if m <=? List.length args then
          match img_pats (List.repeat true (d + List.length pat + (np - nu))) (List.firstn m args),
                img_pats (cls_pat d np n pat) (List.skipn m args) with
          | Some Cs, Some Ns => if selfs_occur nu n Cs then Some (rp_nest (qc, k, Cs) Ns) else None
          | _, _ => None
          end
        else None
    | None => None
    end.

  (** A shape under [d] of its domains: [cls_self], [cls_nest], or a [Π]
      over a Self-free domain into a shape.  A [Self] thus occurs only
      strictly positively, and in a nested occurrence only in its uniform
      arguments. *)
  Fixpoint cls_sh (d : nat) (T : exp) : option rptyp :=
    match T with
    | a_pi B T' =>
        match img_pat (cls_pat d np n pat) B with
        | Some B0 => option_map (rp_pi B0) (cls_sh (S d) T')
        | None => None
        end
    | _ =>
        match app_head T with
        | a_var x => cls_self d x (app_args T)
        | a_ind qc k => cls_nest d qc k (app_args T)
        | _ => None
        end
    end.

  (** An argument: Self-free (and free of the recursive arguments before
      it), or recursive of a shape. *)
  Definition cls_arg (T : exp) : option rcarg :=
    match img_pat (cls_pat 0 np n pat) T with
    | Some A => Some (rc_arg A)
    | None => option_map rc_rec (cls_sh 0 T)
    end.
End Classify.

(** No filed group: the classification as written finds no nested
    occurrence. *)
Definition grp_none : qname -> nat -> option nat := fun _ _ => None.

(** The instances a classified argument meets, in order: the one its
    shape ends in, if it ends in a nested occurrence. *)
Fixpoint rptyp_view (t : rptyp) : list rview :=
  match t with
  | rp_nest x _ => x :: nil
  | rp_pi _ t' => rptyp_view t'
  | rp_self _ _ => nil
  end.

Definition rcarg_view (g : rcarg) : list rview :=
  match g with rc_rec t => rptyp_view t | rc_arg _ => nil end.

(** The instances the constructors [cs] meet, constructors in order,
    arguments left to right. *)
Definition rcons_views (cs : list (string * list rcarg)) : list rview :=
  List.concat (List.map (fun c => List.concat (List.map rcarg_view (snd c))) cs).

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
    instance comes first.  [views_bfs sibs meets acc tr Vs]: from the views
    found so far, [acc], and the instances still to meet, [tr], in order,
    the views are [Vs]; a view found has the instances its constructors
    meet ([meets]) queued after the others.  The command gives [sibs] and
    [meets] as tables of the instances it meets. *)

(** Those of [ss] not in [acc], in order, each once. *)
Fixpoint views_new (acc ss : list rview) : list rview :=
  match ss with
  | nil => nil
  | s :: ss' => if rview_mem s acc then views_new acc ss' else s :: views_new (acc ++ s :: nil) ss'
  end.

(** The views an instance met for the first time adds: its siblings, and
    itself if they do not list it. *)
Definition views_met (sibs : rview -> list rview) (acc : list rview) (x : rview) : list rview :=
  if rview_mem x acc then nil else views_new acc (sibs x ++ x :: nil).

Inductive views_bfs (sibs meets : rview -> list rview) : list rview -> list rview -> list rview -> Prop :=
| views_bfs_done : forall acc, views_bfs sibs meets acc nil acc
| views_bfs_step : forall acc x tr Vs,
    views_bfs sibs meets (acc ++ views_met sibs acc x)
      (tr ++ List.concat (List.map meets (views_met sibs acc x))) Vs ->
    views_bfs sibs meets acc (x :: tr) Vs.

Lemma rview_index_in : forall x Vs v, rview_index x Vs = Some v -> List.nth_error Vs v = Some x.
Proof.
  induction Vs as [| y Vs IH]; cbn; intros v H; [ discriminate |].
  destruct (rview_eq_dec x y) as [-> | _]; [ injection H as <-; reflexivity |].
  destruct (rview_index x Vs) as [v' |] eqn:E; cbn in H; [ injection H as <-; cbn; apply IH; reflexivity | discriminate ].
Qed.

Lemma rview_mem_spec : forall x Vs, rview_mem x Vs = true <-> In x Vs.
Proof.
  unfold rview_mem; induction Vs as [| y Vs IH]; cbn; [ split; [ discriminate | intros [] ] |].
  destruct (rview_eq_dec x y) as [-> | Hne]; [ split; auto |].
  destruct (rview_index x Vs); cbn in *; rewrite <- IH; split; auto.
  intros [-> | H]; [ congruence | exact H ].
Qed.

Lemma views_new_in : forall acc ss x, In x ss -> In x acc \/ In x (views_new acc ss).
Proof.
  intros acc ss; revert acc; induction ss as [| s ss IH]; cbn; intros acc x H; [ destruct H |].
  destruct (rview_mem s acc) eqn:Es.
  - destruct H as [<- | H]; [ left; apply rview_mem_spec; exact Es | exact (IH _ _ H) ].
  - destruct H as [<- | H]; [ right; left; reflexivity |].
    destruct (IH (acc ++ s :: nil) x H) as [H' | H']; [| right; right; exact H' ].
    apply List.in_app_or in H' as [H' | [<- | []]]; [ left; exact H' | right; left; reflexivity ].
Qed.

Lemma views_bfs_incl : forall sibs meets acc tr Vs, views_bfs sibs meets acc tr Vs -> forall y, In y acc -> In y Vs.
Proof. induction 1; intros y Hy; [ exact Hy | apply IHviews_bfs, List.in_or_app; left; exact Hy ]. Qed.

(** Two runs from the same state whose tables agree at the views both find
    find the same views. *)
Lemma views_bfs_functional : forall sibs1 meets1 acc tr Vs1, views_bfs sibs1 meets1 acc tr Vs1 ->
    forall sibs2 meets2 Vs2, views_bfs sibs2 meets2 acc tr Vs2 ->
    (forall x, In x Vs1 -> In x Vs2 -> sibs1 x = sibs2 x /\ meets1 x = meets2 x) -> Vs1 = Vs2.
Proof.
  induction 1 as [acc | acc x tr Vs1 H1 IH]; intros sibs2 meets2 Vs2 H2 Hag; inversion H2; subst; [ reflexivity |].
  match goal with H : views_bfs sibs2 meets2 _ _ Vs2 |- _ => rename H into H5 end.
  assert (Hm : views_met sibs1 acc x = views_met sibs2 acc x).
  { destruct (rview_mem x acc) eqn:Ex; [ unfold views_met; rewrite Ex; reflexivity |].
    assert (Hx : forall sibs meets tr' Vs, views_bfs sibs meets (acc ++ views_met sibs acc x) tr' Vs -> In x Vs).
    { intros * Hb; apply (views_bfs_incl _ _ _ _ _ Hb), List.in_or_app.
      unfold views_met; rewrite Ex.
      destruct (views_new_in acc (sibs x ++ x :: nil) x ltac:(apply List.in_or_app; right; left; reflexivity)) as [Hi | Hi];
        [ left; exact Hi | right; exact Hi ]. }
    pose proof (proj1 (Hag x (Hx _ _ _ _ H1) (Hx _ _ _ _ H5))) as Es.
    unfold views_met; rewrite Ex, Es; reflexivity. }
  assert (Hms : List.map meets1 (views_met sibs1 acc x) = List.map meets2 (views_met sibs1 acc x)).
  { apply List.map_ext_in; intros y Hy.
    assert (Hy1 : In y Vs1) by (apply (views_bfs_incl _ _ _ _ _ H1), List.in_or_app; right; exact Hy).
    assert (Hy2 : In y Vs2) by (rewrite Hm in Hy; apply (views_bfs_incl _ _ _ _ _ H5), List.in_or_app; right; exact Hy).
    exact (proj2 (Hag y Hy1 Hy2)). }
  apply (IH sibs2 meets2); [| exact Hag ].
  rewrite Hms, Hm; exact H5.
Qed.

(** The siblings and the instances met of an instance, read off tables
    aligned with the views; an instance not among them is alone and meets
    nothing. *)
Definition sibs_tbl (Vs : list rview) (Ss : list (list rview)) (x : rview) : list rview :=
  match rview_index x Vs with Some v => List.nth v Ss (x :: nil) | None => x :: nil end.

Definition meets_tbl (Vs : list rview) (Cs : list (list (string * list rcarg))) (x : rview) : list rview :=
  match rview_index x Vs with Some v => rcons_views (List.nth v Cs nil) | None => nil end.
