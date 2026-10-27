From Stdlib Require Import Lia List Morphisms Relation_Definitions RelationClasses Setoid String Wf_nat.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Levels Require Export Ordinals.

(** An item of an open: [(Some n, d, pv)] declares [d] as the member [n] of
    the opened module, [(None, d, pv)] declares [d] as the opened module
    itself; private when [pv].  The surface syntax and the core share it. *)
Definition iitem : Set := (option string * string * bool)%type.

(** * Concrete Syntax Tree *)
Module Cst.

(** ** Modifiers

    [private] hides a definition from importers, [abstract] makes its body
    opaque.  The two are orthogonal, hence a record rather than a variant. *)
Record mods : Set :=
  { md_private : bool
  ; md_abstract : bool }.

Definition md_pub : mods := {| md_private := false; md_abstract := false |}.
Definition md_priv : mods := {| md_private := true; md_abstract := false |}.
Definition md_abs : mods := {| md_private := false; md_abstract := true |}.
Definition md_priv_abs : mods := {| md_private := true; md_abstract := true |}.

(** ** Definition Keywords

    [def] and its shorthands.  Each keyword implies some modifiers, and
    takes the others: [theorem] and [lemma] are [abstract def] and take
    [private]; [fact] and [remark] are [abstract private def] and take
    none; [let] and [given] are [private def] and take [abstract].  A
    modifier the keyword already implies is rejected. *)
Inductive dkw : Set :=
| dk_def | dk_theorem | dk_lemma | dk_fact | dk_remark | dk_let | dk_given.

Definition dkw_name (k : dkw) : string :=
  match k with
  | dk_def => "def" | dk_theorem => "theorem" | dk_lemma => "lemma"
  | dk_fact => "fact" | dk_remark => "remark" | dk_let => "let" | dk_given => "given"
  end.

(** The modifiers of [m k], or why [k] rejects [m]. *)
Definition dkw_mods (k : dkw) (m : mods) : (mods + string)%type :=
  match k with
  | dk_def => inl m
  | dk_theorem | dk_lemma =>
      if md_abstract m then inr (dkw_name k ++ " is already abstract")%string
      else inl {| md_private := md_private m; md_abstract := true |}
  | dk_fact | dk_remark =>
      if orb (md_private m) (md_abstract m) then inr (dkw_name k ++ " takes no modifiers")%string
      else inl md_priv_abs
  | dk_let | dk_given =>
      if md_private m then inr (dkw_name k ++ " is already private")%string
      else inl {| md_private := true; md_abstract := md_abstract m |}
  end.

(** ** Objects, Declarations and Commands

    The two levels of naming are spelled differently.  [::] separates the
    segments of a file path, the name of a compilation unit, which is what
    [glob] holds; [.] selects a member of whatever precedes it, be that an
    internal module, a unit, or a local module.

    [proj] is that postfix dot: [X::Y::Z.W.foo] is a chain of [proj]s over
    [glob ["X"; "Y"; "Z"]], and [A.foo] for a module [A] is one over
    [var "A"].  Module arguments arrive as ordinary [app] nodes, so
    [(X::Y.Z a b).foo] needs no syntax of its own.  Whether a [var], a [proj]
    or an [app] is a module or a term is decided by its position: the head of
    a [proj], the head of an application in such a head, an alias body and an
    open target are modules, everything else is a term.

    [letb] binds one declaration at a time; the parser folds the bindings of
    [let x : A := a; y : B := b in body end] into nested [letb]s.

    A module declaration has one shape at the top level and in a [let]: its
    parameters, and its definition [mdef], a body [where cmds end] or an
    alias [:= E].  The body of a local module is the same list of commands as
    that of a global one.  The branches of an eliminator, the parameters
    and the fields are nested through lists of pairs, all of which have
    [All] schemes registered ([Core.Base]): the mutual principle [cst_ind]
    below is generated. *)
Inductive obj : Set :=
(** [Typeω@i], a large universe, the universe [ω²+i], written
    [Type@{ω^2}] for [i = 0] and [Type@{ω^2+i}]; [ω^2] is not a level. *)
| typ : nat -> obj
(** [Type@{M}], the small universe at the level [M] *)
| suniv : obj -> obj
(** [Level@n], the type of the levels below [ω·(n+1)]; [Level] is [Level@0] *)
| level : nat -> obj
(** A level literal [ω·a + b], written [<b>l] when [a] is [0] and also
    [<b>L] when [a] is [1] *)
| llit : o2 -> obj
(** [succl M] *)
| succl : obj -> obj
(** [maxl M N] *)
| maxl : obj -> obj -> obj
(** [Nat] or [ℕ]: the type bound by [builtin natural] *)
| nat : obj
(** A numeral, of the type bound by [builtin natural] *)
| num : nat -> obj
(** [True] *)
| true_ty : obj
(** [true] *)
| true_tm : obj
(** [False] *)
| false_ty : obj
(** [exfalso M return x . A] *)
| exfalso : obj -> string -> obj -> obj
(** [forall (x : A) -> B] *)
| pi : string -> obj -> obj -> obj
(** [fun (x : A) -> M] *)
| fn : string -> obj -> obj -> obj
(** [M N]: a function or a module applied *)
| app : obj -> obj -> obj
(** A name: a local variable, a module, or a member in scope *)
| var : string -> obj
(** A [::] path, hence at least two segments after a [var]; a unit of one
    segment is written as a [var] *)
| glob : list string -> obj
(** [M.x]: a member of a module *)
| proj : obj -> string -> obj
(** [let d in M end], one declaration at a time *)
| letb : decl -> obj -> obj
(** [elim M at xs (z : Z) -> A | c ys ⇒ B … with … end]: the eliminator
    of a group of inductive types, one block per member in member order,
    the one marked [at] ([true]) the scrutinee's.  A block's binders, the
    non-uniform parameters then the scrutinee, outermost first, each with
    its type if written; its motive under them; its branches, each binding
    the non-uniform parameters, the constructor's arguments and the
    induction hypotheses, in that order *)
| elim : obj -> list (bool * list (string * option obj) * obj * list (string * list string * obj)) -> obj
(** [record T where f := M ; … end]: a value of the record type [T], its
    fields in order, each its name and its value *)
| tuple : obj -> list (string * obj) -> obj

with decl : Set :=
(** [x : A := M], or [x := M] without the type.  A local definition is
    always transparent and has no modifiers. *)
| d_def : string -> option obj -> obj -> decl
(** [module X (ps) md] *)
| d_mod : string -> list (string * obj) -> mdef -> decl

with mdef : Set :=
(** [where cs end] *)
| md_where : list cmd -> mdef
(** [:= E] *)
| md_alias : obj -> mdef

(** A module declaration carries its name, its parameter telescope and its
    definition; a unit's own name is declared by [prog] below, not here.  A
    dotted declaration [module A.B] is parsed as nested ones ([c_mod_dotted]). *)
with cmd : Set :=
(** [private module x (ps) md], private when the flag is set *)
| c_mod : bool -> string -> list (string * obj) -> mdef -> cmd
(** [private abstract def x : A := M end], with its modifiers *)
| c_def : mods -> string -> obj -> obj -> cmd
(** [axiom x : A], a definition with no body; it takes no modifiers. *)
| c_axiom : string -> obj -> cmd
(** [import X::Y] loads the unit [X::Y], so that it may be named.  It
    declares nothing. *)
| c_import : list string -> cmd
(** [c_open fq ip args its] opens the module at member path [ip] of the
    unit [fq], applied to [args], and declares the items [its]; an empty
    [fq] names the module [ip] in scope.  It loads nothing.  So [open A.B
    use (x)] is [c_open nil ["A"; "B"] nil [(Some "x", "x", true)]], and
    [open X::Y Nat export (f as g)] is [c_open ["X"; "Y"] nil [nat] [(Some
    "f", "g", false)]].  [as W] is the item [(None, "W", true)] ([open_cmds]). *)
| c_open : list string -> list string -> list obj -> list iitem -> cmd
(** A command the parser rejects, with the reason, which elaboration
    reports: a definition keyword with a modifier it already implies
    ([def_cmd]). *)
| c_error : string -> cmd
(** [eval M] normalizes [M] and prints the result; [eval M : A] additionally
    checks [M] against [A] rather than inferring its type. *)
| c_eval : obj -> option obj -> cmd
(** [private inductive x (ps) : T where | c (args) … with y : U where …
    end]: the group's uniform parameters [ps], shared, and its members, in
    order: each its name, its type, which binds its non-uniform parameters
    in front of the sort, [forall (n : A) -> S], and its constructors with
    their arguments.  The members' names are in scope in every argument.
    The second flag says whether the group files its recursor module
    [Rec], as one declared by [mutual T where] does. *)
| c_ind : bool -> bool -> list (string * obj) -> list (string * obj * list (string * list (string * obj))) -> cmd
(** [private abstract mutual def (Δ) f (ys) (z : Z) : A := | c xs ⇒ B …
    with g … end], with its modifiers: the common parameters [Δ], and the
    functions, each its name, its parameters (the non-uniform ones, then
    the scrutinee, last), its result type and its clauses. *)
| c_mdef : mods -> list (string * obj) -> list (string * list (string * obj) * obj * list (string * list string * obj)) -> cmd
(** [builtin k := X]: binds the inductive type [X] as the builtin [k];
    [natural] is the one kind. *)
| c_builtin : string -> obj -> cmd
(** [private inductive x (ps) := X Ms]: an inductive alias, the inductive
    type [X] at the arguments [Ms], under the parameters [ps]. *)
| c_ind_alias : bool -> string -> list (string * obj) -> obj -> cmd
(** [private record x (ps) := X Ms]: a record alias, the record type [X]
    at the arguments [Ms], under the parameters [ps]. *)
| c_record_alias : bool -> string -> list (string * obj) -> obj -> cmd
(** [private record x (ps) : S where f : A ; … with cs end]: a record type,
    private when the flag is set: its parameters [ps], its sort [S], its
    fields in order, each its name and its type over the fields before it,
    and its with-area [cs], the commands of its module after the fields
    (none without [with]). *)
| c_record : bool -> string -> list (string * obj) -> obj -> list (string * obj) -> list cmd -> cmd.

(** The mutual induction principle of the family, generated: a list, a
    pair and an option carry [list_all], [prod_all] and [option_all] of the
    motives ([Core.Base]). *)
Scheme obj_mut_ind := Induction for obj Sort Prop
with decl_mut_ind := Induction for decl Sort Prop
with mdef_mut_ind := Induction for mdef Sort Prop
with cmd_mut_ind := Induction for cmd Sort Prop.
Combined Scheme cst_ind from obj_mut_ind, decl_mut_ind, mdef_mut_ind, cmd_mut_ind.

(** [module A₁.….Aₙ.B (ps) md] is [module A₁ where … module Aₙ where module
    B (ps) md end … end]: each [Aᵢ] has no parameters and the one member
    [Aᵢ₊₁].  The grammar gives the path reversed, [B] first.  Only [B], the
    module declared, carries the privacy [pv]; the [Aᵢ] are public. *)
Definition c_mod_dotted (pv : bool) (x : string) (rev_pre : list string) (ps : list (string * obj)) (md : mdef) : cmd :=
  List.fold_left (fun c y => c_mod false y nil (md_where (c :: nil))) rev_pre (c_mod pv x ps md).

(** [k x : A := M end] with the modifiers [m]: the definition, or the
    rejection of [m]. *)
Definition def_cmd (k : dkw) (m : mods) (x : string) (A M : obj) : cmd :=
  match dkw_mods k m with
  | inl m' => c_def m' x A M
  | inr e => c_error e
  end.

(** [mutual k (Δ) f … with g … end] with the modifiers [m], [k] a
    definition keyword: the mutual definition with the modifiers [k] gives
    it, as [def_cmd] gives a single definition, or the rejection of [m]. *)
Definition mdef_cmd (k : dkw) (m : mods) (ps : list (string * obj))
    (fs : list (string * list (string * obj) * obj * list (string * list string * obj))) : cmd :=
  match dkw_mods k m with
  | inl m' => c_mdef m' ps fs
  | inr e => c_error e
  end.

(** [axiom x : A] with the modifiers [m]: the axiom, or the rejection of
    [m]. *)
Definition axiom_cmd (m : mods) (x : string) (A : obj) : cmd :=
  if orb (md_private m) (md_abstract m) then c_error "axiom takes no modifiers" else c_axiom x A.

(** [mutual T (ps) where inductive … end end] with the modifiers [m]: the
    module [T], private with [m], holding the group and its recursor module
    [T.Rec], or the rejection of [abstract]. *)
Definition mutual_cmd (m : mods) (g : string) (ps : list (string * obj))
    (ms : list (string * obj * list (string * list (string * obj)))) : cmd :=
  if md_abstract m then c_error "a group of inductive types takes no abstract"
  else c_mod (md_private m) g nil (md_where (c_ind false true ps ms :: nil)).

(** [open E as W its] is [open E as W] then [open W its]: the items refer
    to the alias, and an open declares either the module or its members. *)
Definition open_cmds (fq ip : list string) (args : list obj) (oW : option string) (its : list iitem)
  : list cmd :=
  match oW with
  | None => c_open fq ip args its :: nil
  | Some W =>
      c_open fq ip args ((None, W, true) :: nil) ::
        match its with
        | nil => nil
        | _ => c_open nil (W :: nil) nil its :: nil
        end
  end.

(** [import X::Y ip args as W its] is [import X::Y] then [open X::Y ip
    args as W its]; a bare [import X::Y] only loads. *)
Definition import_cmds (fq ip : list string) (args : list obj) (oW : option string) (its : list iitem)
  : list cmd :=
  c_import fq ::
    match ip, args, oW, its with
    | nil, nil, None, nil => nil
    | _, _, _, _ => open_cmds fq ip args oW its
    end.

(** A leading import or open, before the unit's header, may not [export]:
    the commands, or their rejection. *)
Definition lead_cmds (cs : list cmd) : list cmd :=
  if List.existsb (fun c => match c with
                            | c_open _ _ _ its => List.existsb (fun it => negb (snd it)) its
                            | _ => false
                            end) cs
  then c_error "export is not allowed before the module header" :: nil
  else cs.

(** A compilation unit: its leading imports and opens, and the one module
    declaration everything else it contains lives in.  That declaration
    names the unit, so its path is a [::] one, and carries the unit's
    parameters.  Only imports and opens may precede it, so no definition is
    ever made outside a module; the grammar admits nothing else there. *)
Definition prog : Set := (list cmd * (list string * list (string * obj) * list cmd))%type.

End Cst.

(** * Names and Paths

    A unit is named by its path, [X::Y::Z], the list ["X"; "Y"; "Z"]; units do
    not nest, so a path is flat.  The syntax names only units ([me_unit]); a
    member of a unit is spelled as a chain of selections from it, [me_mem]
    and [a_mem]. *)
Abbreviation path := (list string).

Definition path_eq_dec := List.list_eq_dec String.string_dec.

Definition path_beq (fp fq : list string) : bool :=
  if path_eq_dec fp fq then true else false.

Lemma path_beq_refl : forall fp, path_beq fp fp = true.
Proof. intros; unfold path_beq; destruct (path_eq_dec fp fp); congruence. Qed.

Lemma path_beq_true : forall fp fq, path_beq fp fq = true -> fp = fq.
Proof. intros * H; unfold path_beq in H; destruct (path_eq_dec fp fq); congruence. Qed.

Lemma path_beq_false : forall fp fq, fp <> fq -> path_beq fp fq = false.
Proof. intros * H; unfold path_beq; destruct (path_eq_dec fp fq); congruence. Qed.

(** [strip_prefix l m] is [m] with the prefix [l] removed, if it is one. *)
Fixpoint strip_prefix (l m : list string) : option (list string) :=
  match l, m with
  | nil, _ => Some m
  | x :: l', y :: m' => if String.eqb x y then strip_prefix l' m' else None
  | _ :: _, nil => None
  end.

Lemma strip_prefix_app : forall l r, strip_prefix l (l ++ r) = Some r.
Proof. induction l; intros; cbn; [ reflexivity | rewrite String.eqb_refl; auto ]. Qed.

Lemma strip_prefix_spec : forall l m r, strip_prefix l m = Some r -> m = l ++ r.
Proof.
  induction l as [| x l IH]; intros [| y m] r H; cbn in H; try discriminate;
    [ injection H as <-; reflexivity | injection H as <-; reflexivity |].
  destruct (String.eqb_spec x y) as [-> |]; [| discriminate ].
  cbn; f_equal; auto.
Qed.

Lemma strip_prefix_snoc : forall l x m r,
    strip_prefix (l ++ x :: nil) m = Some r -> strip_prefix l m = Some (x :: r).
Proof.
  intros * H; apply strip_prefix_spec in H; subst.
  rewrite <- List.app_assoc; apply strip_prefix_app.
Qed.

(** A global is named by [X::Y::Z.a.b.c]: the unit it lives in, by its path,
    then the chain of member selections inside it from the unit's root.
    Names are absolute, also inside the unit being elaborated: an open
    module is named by the same qualified name it will have once it is closed
    and its unit filed, so what a name denotes never depends on where it is
    read, and resolving it is a lookup with no re-expression.

    A qualified name is not syntax: it is the key the global context resolves
    a chain of selections from a unit by, and the name a value of a global
    carries ([dm_global], [d_glob], [ne_glob]).  [q_chain] is the chain,
    empty for the unit itself. *)
Record qname : Set := qname_mk
  { q_unit : path
  ; q_chain : list string }.

Definition qname_eq_dec : forall (x y : qname), {x = y} + {x <> y}.
Proof. decide equality; apply List.list_eq_dec, String.string_dec. Defined.

(** An abbreviation, not a definition: a rule keyed on [q_abs] then has a record
    literal in its conclusion, so inverting it yields equations that
    [discriminate] and [injection] see through. *)
Abbreviation q_abs fp ip := {| q_unit := fp; q_chain := ip |}.

(** The member [x] of the module [mp]. *)
Definition qname_in (mp : qname) (x : string) : qname :=
  {| q_unit := q_unit mp ; q_chain := q_chain mp ++ x :: nil |}.

(** The member chain [ip] of the module [mp]. *)
Definition qname_app (mp : qname) (ip : list string) : qname :=
  {| q_unit := q_unit mp ; q_chain := q_chain mp ++ ip |}.

Lemma qname_app_nil : forall p, qname_app p nil = p.
Proof. intros [u m]; unfold qname_app; cbn; rewrite List.app_nil_r; reflexivity. Qed.

(** The members of [p] inside the module [mp], if [p] is in it. *)
Definition qname_strip (mp p : qname) : option (list string) :=
  if path_beq (q_unit mp) (q_unit p) then strip_prefix (q_chain mp) (q_chain p) else None.

(** * Inductive Declarations

    The declaration of a group of inductive types, as a unit stores it.  It
    is generic in the sorts of terms [E] and context entries [C] so that it
    can be defined before them: [gentry] holds an [ind_decl_g exp centry]
    ([ind_decl]), and no syntactic operation looks inside it, since a
    declaration is always filed closed.

    A group has members ([imember_g]): first the types it declares, in the
    order they are written (one for a single inductive type, several for a
    mutual block), then its views: the instances of types of groups filed
    before, at uniform arguments that mention a member, that its
    constructors nest through (as [List 0l (Rose A)] in
    [Rose A := node (x : A) (ts : List 0l (Rose A))]), in the order the
    command meets them.  The members share the uniform parameters and the
    sort; each has its own non-uniform parameters and constructors.

    - [ind_uparams] is the telescope of the uniform parameters, innermost
      first, closed (the parameters of the enclosing frames outermost);
    - [ind_sort] is the universe every member lives in, a term over the
      uniform parameters;
    - [ind_members] lists the members.

    The type former of member [k] is [a_ind pq k], [pq] the path of the
    group, that of its first member's entry ([ge_ind]): every member is
    named by the group, so that the types of the constructors of one member
    may mention any other member before the entries of the others are
    filed.

    The arguments of a constructor are stratified: a non-recursive argument
    [ca_arg A] has its type [A] over the non-recursive arguments before it
    and the member's parameters, and a recursive argument [ca_rec t] has a
    shape [t] ([ptyp_g]), whose components are over the non-recursive
    arguments before it and the member's parameters.  Nothing may mention a
    recursive argument, so it occupies no binder of the arguments after
    it. *)

(** The shape of a recursive argument: the member [k] of the group at its
    non-uniform parameters [Ps] ([pt_self k Ps]), or a function from [A] to
    a shape ([pt_pi A t]). *)
Inductive ptyp_g (E : Set) : Set :=
(** The member [k] of the group at the non-uniform parameters [Ps]. *)
| pt_self : nat -> list E -> ptyp_g E
(** A function from the domain [A] into a shape, under one more binder. *)
| pt_pi : E -> ptyp_g E -> ptyp_g E.
Arguments pt_self {E}.
Arguments pt_pi {E}.

(** The non-uniform parameters at which a shape ends. *)
Fixpoint ptyp_ps {E : Set} (t : ptyp_g E) : list E :=
  match t with
  | pt_self _ Ps => Ps
  | pt_pi _ t => ptyp_ps t
  end.

(** The member a shape ends in. *)
Fixpoint ptyp_mem {E : Set} (t : ptyp_g E) : nat :=
  match t with
  | pt_self k _ => k
  | pt_pi _ t => ptyp_mem t
  end.

(** In stage A a shape is read by its parameters alone, so it stands for
    them wherever a list of terms is expected. *)
Coercion ptyp_ps : ptyp_g >-> list.

Inductive carg_g (E : Set) : Set :=
(** A non-recursive argument, of a type *)
| ca_arg : E -> carg_g E
(** A recursive argument, of a shape *)
| ca_rec : ptyp_g E -> carg_g E.
Arguments ca_arg {E}.
Arguments ca_rec {E}.

(** The head of a member: a declared type, by the canonical path of its
    own entry ([mh_decl p]), or a view ([mh_view q k Is vm]): the declared
    member [k] of the group filed at [q], at the uniform arguments [Is],
    terms over this group's uniform parameters in which this group's
    members occur, in normal form.  A view of a member of [q]'s group is
    one of all of them: [vm] lists, for each member of [q]'s group in its
    order, the member of this group that is that member at [Is] (the
    [k]-th is the view itself).  The eliminator at a view reads back as
    [q]'s group's eliminator, whose blocks are those of these members.

    Or a record view ([mh_record q Is fl]): the record type filed at [q]
    at the arguments [Is], in which this group's members occur, stored as
    a view's, and the names [fl] of its fields, in order.  A record view
    has one constructor, [rview_con], whose arguments are the record's
    fields in order, classified as a constructor's arguments are; its
    elements are taken apart by
    projection.  No eliminator eliminates at a record view: the record
    views come after every other member and have no block, and the
    recursive results of an argument of a record view are those of its
    fields ([shape_leaves]). *)
Inductive mhead_g (E : Set) : Set :=
(** A declared type, named by the canonical path of its own entry. *)
| mh_decl : qname -> mhead_g E
(** A view: the declared member [k] of the group at [q] at the uniform
    arguments [Is], and the members [vm] of this group its group's members
    are at [Is]. *)
| mh_view : qname -> nat -> list E -> list nat -> mhead_g E
(** A record view: the record type at [q] at the arguments [Is], its
    fields named [fl]. *)
| mh_record : qname -> list E -> list string -> mhead_g E.
Arguments mh_decl {E}.
Arguments mh_view {E}.
Arguments mh_record {E}.

(** The name of the one constructor of a record view: no identifier of
    the surface syntax ([A-Za-z_][A-Za-z0-9_]*, the lexer's) is spelled
    so, so it can be neither written nor captured; the printer shows its
    elements as tuples of the record. *)
Definition rview_con : string := "(tuple)".

(** A member: its head, its non-uniform parameters (a telescope over the
    uniform ones, innermost first) and its constructors, in order, each with
    its arguments, outermost first.  A view's are the filed ones of the
    member of [q]'s group at [Is], classified for this group: a recursive
    argument is one of a member of this group. *)
Record imember_g (E C : Set) : Set := mk_imember
  { (** Whether the member is a declared type or a view, and of what. *)
    im_head : mhead_g E
  (** The non-uniform parameters, over the group's uniform ones,
      innermost first. *)
  ; im_nparams : list C
  (** The constructors in order, each with its arguments, outermost
      first. *)
  ; im_cons : list (string * list (carg_g E)) }.
Arguments mk_imember {E C}.
Arguments im_head {E C}.
Arguments im_nparams {E C}.
Arguments im_cons {E C}.

(** A group of inductive types: the uniform parameters all its members
    share, the one sort they are all of, and the members, the declared
    types in order, then the views. *)
Record ind_decl_g (E C : Set) : Set := mk_ind
  { (** The uniform parameters, innermost first: the group's own, then
        those of the enclosing frames. *)
    ind_uparams : list C
  (** The sort of every member, over the uniform parameters. *)
  ; ind_sort : E
  (** The members: the declared types, then the views. *)
  ; ind_members : list (imember_g E C) }.
Arguments mk_ind {E C}.
Arguments ind_uparams {E C}.
Arguments ind_sort {E C}.
Arguments ind_members {E C}.

(** The declaration of a record type, filed by [ge_record] at its path,
    which names it.  Records are never recursive: no field's type mentions
    the record. *)
Record record_decl_g (E C : Set) : Set := mk_record_decl
  { (** The parameters, innermost first: the record's own, then those of
        the enclosing frames.  A closed telescope. *)
    record_params : list C
  (** The sort, over the parameters. *)
  ; record_sort : E
  (** The fields in order, each named, its type over the fields before it
      (innermost first) and then the parameters. *)
  ; record_fields : list (string * E) }.
Arguments mk_record_decl {E C}.
Arguments record_params {E C}.
Arguments record_sort {E C}.
Arguments record_fields {E C}.

(** A block of an eliminator ([a_elim]), one per member of the group, in
    the group's order: [eb_mk nm oZ A Bs].  The motive [A] binds [nm]
    variables, the member's non-uniform parameters and the scrutinee; [oZ]
    is the type of the scrutinee as written, if it is written, over the
    non-uniform parameters; each branch [(c, n, B)] is the case of the
    constructor [c], in order, and binds [n] variables: the non-uniform
    parameters, the arguments, and one recursive result per recursive
    argument. *)
Inductive eblock_g (E : Set) : Set :=
(** The block of [nm] motive binders, the written scrutinee type [oZ], the
    motive [A] and the branches [Bs]. *)
| eb_mk : nat -> option E -> E -> list (string * nat * E) -> eblock_g E.
Arguments eb_mk {E}.
(** [exp] nests through blocks: with this scheme registered, its generated
    induction principle carries the hypotheses for a block's parts. *)
Scheme All for eblock_g.

(** The number of variables a block's motive binds. *)
Definition eb_nm {E : Set} (b : eblock_g E) : nat := match b with eb_mk nm _ _ _ => nm end.
(** A block's scrutinee type as written, if it is written. *)
Definition eb_ann {E : Set} (b : eblock_g E) : option E := match b with eb_mk _ oZ _ _ => oZ end.
(** A block's motive. *)
Definition eb_motive {E : Set} (b : eblock_g E) : E := match b with eb_mk _ _ A _ => A end.
(** A block's branches, one per constructor of its member, in order. *)
Definition eb_brs {E : Set} (b : eblock_g E) : list (string * nat * E) := match b with eb_mk _ _ _ Bs => Bs end.

(** * Terms, Module Expressions and Units

    Unlike a calculus of explicit substitutions, there is no constructor for
    substitution application and no syntactic category of substitutions.
    Weakenings and substitutions are meta-level operations (recursive
    functions on [exp]) defined further down in this file, and their
    algebraic laws are theorems (in [Core.Syntactic.Substitution]) rather
    than definitional equalities of the object theory. *)

(** The terms, and the module syntax nested in them.  The two are one
    mutual family: a term binds a local module ([a_let] with [b_mod]) and
    selects members of module expressions ([a_mem]), and a module body
    contains terms.

    - [modexp] is a module expression: a unit [me_unit], a local module slot
      [me_var], a submodule [me_mem], an argument [me_app], or a literal unit
      [me_lit].  A literal is produced only by substitution, when
      [ζ] replaces a module slot by its unit.
    - [gunit] is a unit: its parameter telescope, innermost first, and its
      definition, a body or an alias.  The definition is under the parameters.
    - [gmod] is a module body, newest entry last.  Each named entry binds one
      index for the entries after it; a local open ([gm_open]), a
      pre-form the core expands before typing, binds one per item.
    - [centry] is a context entry: an assumption, a definition, or a module
      slot [ce_mod U], which binds one index to the unit [U]. *)
(** The two ways a module's entries are stored: open (a local module) and
    closed (a filed module or an open frame). *)
Inductive smark : Set := sm_open | sm_closed.

Definition smark_eq_dec : forall (s s' : smark), {s = s'} + {s <> s'}.
Proof. decide equality. Defined.

(** The terms and the module syntax are one mutual family; its mutual
    principle [syn_mut_ind] below is written by hand, with one motive per
    sort that the hand-written cases share. *)
Inductive exp : Set :=
(** A large universe: [a_typ n] is [Typeω²+n].  It contains every small
    universe, and the large universes below it. *)
| a_typ : nat -> exp
(** A small universe, at a level: [a_univ t] is [Type@{t}].  The level is an
    arbitrary term of type [Level], so a universe may be indexed by a
    variable, which is what makes universe polymorphism plain [Π]. *)
| a_univ : exp -> exp
(** The type of universe levels below [ω·(n+1)]: [a_level n] is [Level@n],
    and [Level] is [Level@0], the finite levels.  Levels are ordinary terms:
    a function may take and return them, so universe polymorphism is plain
    [Π]. *)
| a_level : nat -> exp
(** A level literal: [a_llit (a, b)] is the ordinal [ω·a + b].  The finite
    level [n], [a_llit (0, n)], is written [<n>l] in the surface syntax. *)
| a_llit : o2 -> exp
(** The successor of a level *)
| a_succl : exp -> exp
(** The join of two levels *)
| a_maxl : exp -> exp -> exp
(** The token [ℕ], written for the type bound by [builtin natural]: like
    a numeral ([a_nlit]), it is not a term of the typing judgment, and
    literal generation ([Builtin]) replaces it by the type former of the
    bound type. *)
| a_ntok : exp
(** The unit type, with η *)
| a_True : exp
(** Its element *)
| a_true : exp
(** The empty type *)
| a_False : exp
(** [a_exfalso A M] eliminates [M] into the motive [A], which binds the
    scrutinee. *)
| a_exfalso : exp -> exp -> exp
(** The type former of the member [k] of the group [pq] of inductive types,
    to be applied to its parameters: [pq] names the group, the path of its
    first member's entry ([ge_ind]). *)
| a_ind : qname -> nat -> exp
(** The constructor [c] of the member [k] of the group [pq], to be applied
    to the parameters and the arguments. *)
| a_con : qname -> nat -> string -> exp
(** A numeral as written.  It is not a term of the typing judgment:
    literal generation ([Builtin]) replaces it by the chain of constructors of the
    inductive type bound as the natural numbers ([builtin natural]). *)
| a_nlit : nat -> exp
(** [a_elim oq Us m Bks M] eliminates [M], of the member [m] of a group of
    inductive types, by the blocks [Bks], one per member of the group in
    its order ([eblock_g]); the result is the motive of block [m].  The
    group is [pq] when [oq = Some pq]; when [oq = None] it is that of the
    scrutinee's type, the member [m] a declared one.  The eliminator
    carries the group's uniform parameters [Us]: a stuck one is read at
    them. *)
| a_elim : option qname -> list exp -> nat -> list (eblock_g exp) -> exp -> exp
(** Functions: [a_pi A B], [B] binding the argument *)
| a_pi : exp -> exp -> exp
(** [a_fn A M], [M] binding the argument *)
| a_fn : exp -> exp -> exp
(** Application *)
| a_app : exp -> exp -> exp
(** Variable *)
| a_var : nat -> exp
(** Local binding: [a_let b B] binds [#0] in [B] to the definition or the
    module [b]. *)
| a_let : bnd -> exp -> exp
(** The member [x] of the module [H].  A member of a global module is
    closed: [X::Y::Z.W.bar] stands for [bar] generalized over the parameters
    of every module enclosing it, outermost first, and is applied to them. *)
| a_mem : modexp -> string -> exp
(** The type former of the record filed at [p], to be applied to its
    parameters *)
| a_record : qname -> exp
(** [a_tuple T fs]: the element of the record type [T] whose fields are
    [fs], by name, in the declaration's order *)
| a_tuple : exp -> list (string * exp) -> exp
(** [a_proj f M]: the field [f] of [M], of a record type *)
| a_proj : string -> exp -> exp
with modexp : Set :=
(** A unit, by its path *)
| me_unit : path -> modexp
(** A local module slot *)
| me_var : nat -> modexp
(** A submodule *)
| me_mem : modexp -> string -> modexp
(** A module applied to one more argument *)
| me_app : modexp -> exp -> modexp
(** A unit given literally; only substitution produces one *)
| me_lit : gunit -> modexp
with bnd : Set :=
(** [b_def oA M]: a definition, of the type [A] when [oA = Some A], and of
    a type it infers when [oA = None] *)
| b_def : option exp -> exp -> bnd
(** [b_mod U]: a local module *)
| b_mod : gunit -> bnd
with gunit : Set :=
(** [gu_mk Δ D]: the parameters, innermost first, and the definition under
    them *)
| gu_mk : list centry -> moddef -> gunit
with moddef : Set :=
(** A body, stored open (a local module: its entries mention the parameters
    and the entries before them) or closed (a filed module or an open frame:
    every entry is closed over the module's full telescope) *)
| md_body : smark -> gmod -> moddef
(** An alias of a module expression *)
| md_alias : modexp -> moddef
with gmod : Set :=
(** The empty body *)
| gm_nil : gmod
(** A named entry after the body before it *)
| gm_ext : gmod -> string -> gentry -> gmod
(** [gm_open Φ H items]: a local open.  It binds one index per item, the
    entries its items generate ([items_gen]); every reader of the body reads
    it as those entries ([body_xp]). *)
| gm_open : gmod -> modexp -> list iitem -> gmod
with gentry : Set :=
(** [ge_def b pv A B]: [b] says whether the definition is transparent, [pv]
    whether it is private, and [B] is [None] for an axiom.  A filed definition
    is closed; a definition of a local body is read in the body's context. *)
| ge_def : bool -> bool -> exp -> option exp -> gentry
(** [ge_mod pv U]: a submodule, private when [pv] *)
| ge_mod : bool -> gunit -> gentry
(** [ge_ind pv pq k D Φ]: the declared member [k] of the group [D] of
    inductive types, private when [pv]: the group's path [pq] (the path of
    the entry of member [0]), and the body [Φ] of the member's module,
    whose members are its constructors (and the recursor), under the
    uniform parameters of [D] ([ind_unit]).  As a term the entry is the
    type former [a_ind pq k]. *)
| ge_ind : bool -> qname -> nat -> ind_decl_g exp centry -> gmod -> gentry
(** [ge_def_mod pv A M U]: a definition with a module part, private when
    [pv]: as a term, the transparent definition of type [A] equal to [M];
    as a module, the unit [U].  An inductive or record alias, or an open's
    item naming a type former, is one: [M] is the alias's target read as a
    term and [U] the alias of it, both over the alias's full telescope.  A
    filed one is closed. *)
| ge_def_mod : bool -> exp -> exp -> gunit -> gentry
(** [ge_record pv p R Φ]: the record type declared by [R], private when
    [pv], at its own path [p], and the body [Φ] of its module, under the
    record's parameters and then a value of the record at them
    ([record_mod_tele]).  As a term the entry is the type former
    [a_record p]. *)
| ge_record : bool -> qname -> record_decl_g exp centry -> gmod -> gentry
with centry : Set :=
(** An assumption of a type *)
| ce_ass : exp -> centry
(** [ce_def A M]: a definition of type [A] *)
| ce_def : exp -> exp -> centry
(** A module slot, holding the unit *)
| ce_mod : gunit -> centry
(** [ce_dm A M U]: a definition with a module part, the local
    [ge_def_mod]: a definition of type [A] equal to [M] and a module slot
    holding [U], at one index *)
| ce_dm : exp -> exp -> gunit -> centry.

Abbreviation typ := exp.
Abbreviation carg := (carg_g exp).
Abbreviation ptyp := (ptyp_g exp).
Abbreviation ind_decl := (ind_decl_g exp centry).
Abbreviation record_decl := (record_decl_g exp centry).
Abbreviation imember := (imember_g exp centry).
Abbreviation mhead := (mhead_g exp).
Abbreviation eblock := (eblock_g exp).

(** A property of every branch of an eliminator, under its binders.  A
    structural recursion on the list, so that a recursive function on terms
    may use it on the branches' bodies. *)
Fixpoint all_brs {A : Type} (f : nat -> A -> Prop) (Bs : list (string * nat * A)) : Prop :=
  match Bs with
  | nil => True
  | b :: Bs' => f (snd (fst b)) (snd b) /\ all_brs f Bs'
  end.

(** A property of every block of an eliminator: of its binder count, its
    annotation, its motive and its branches. *)
Fixpoint all_blocks {A : Set} (f : nat -> option A -> A -> list (string * nat * A) -> Prop) (Bks : list (eblock_g A)) : Prop :=
  match Bks with
  | nil => True
  | eb_mk nm oZ M Bs :: Bks' => f nm oZ M Bs /\ all_blocks f Bks'
  end.

(** The annotation of a block, scoped as [f] says, when there is one. *)
Definition opt_all {A : Set} (f : A -> Prop) (o : option A) : Prop :=
  match o with Some a => f a | None => True end.

(** Each element of a list as [f] says (the uniform parameters an
    eliminator carries). *)
Fixpoint all_list {A : Set} (f : A -> Prop) (l : list A) : Prop :=
  match l with
  | nil => True
  | x :: l' => f x /\ all_list f l'
  end.

Lemma all_brs_Forall : forall {A : Type} (f : nat -> A -> Prop) Bs,
    all_brs f Bs <-> List.Forall (fun b => f (snd (fst b)) (snd b)) Bs.
Proof.
  induction Bs as [| b Bs IH]; cbn; [ split; auto |].
  rewrite IH; split; [ intros []; constructor; assumption | intros H; inversion H; auto ].
Qed.

(** [all_brs] and [all_blocks] are [all_list] at the branch and at the
    block. *)
Lemma all_brs_all_list : forall {A : Set} (f : nat -> A -> Prop) Bs,
    all_brs f Bs <-> all_list (fun b => f (snd (fst b)) (snd b)) Bs.
Proof. induction Bs as [| b Bs IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma all_blocks_all_list : forall {A : Set} (f : nat -> option A -> A -> list (string * nat * A) -> Prop) Bks,
    all_blocks f Bks <-> all_list (fun b => match b with eb_mk nm oZ M Bs => f nm oZ M Bs end) Bks.
Proof. induction Bks as [| [] Bks IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma all_list_Forall : forall {A : Set} (f : A -> Prop) l, all_list f l <-> List.Forall f l.
Proof.
  induction l as [| x l IH]; cbn; split; intros H; auto.
  - destruct H as [H1 H2]; constructor; [ exact H1 | apply IH; exact H2 ].
  - inversion H; subst; split; [ assumption | apply IH; assumption ].
Qed.

(** ** Induction

    The family is nested through [list centry] and [option exp], so its
    induction principle is written by hand.  [syn_mut_ind] has one motive per
    sort; a telescope carries [Forall] of the entry motive, and a definition
    body the motive of every expression it may hold. *)
Section syn_mut_ind.
  Variables (Pe : exp -> Prop) (Pm : modexp -> Prop) (Pb : bnd -> Prop)
    (Pu : gunit -> Prop) (Pd : moddef -> Prop) (Pg : gmod -> Prop)
    (Pn : gentry -> Prop) (Pc : centry -> Prop).

  Hypotheses
    (case_typ : forall i, Pe (a_typ i))
    (case_univ : forall t, Pe t -> Pe (a_univ t))
    (case_level : forall n, Pe (a_level n))
    (case_llit : forall n, Pe (a_llit n))
    (case_succl : forall M, Pe M -> Pe (a_succl M))
    (case_maxl : forall M N, Pe M -> Pe N -> Pe (a_maxl M N))
    (case_ntok : Pe a_ntok)
    (case_True : Pe a_True)
    (case_true : Pe a_true)
    (case_False : Pe a_False)
    (case_exfalso : forall A M, Pe A -> Pe M -> Pe (a_exfalso A M))
    (case_ind : forall p k, Pe (a_ind p k))
    (case_con : forall p k c, Pe (a_con p k c))
    (case_nlit : forall n, Pe (a_nlit n))
    (case_elim : forall oq Us m Bks M,
        List.Forall Pe Us ->
        List.Forall (fun b => (forall Z, eb_ann b = Some Z -> Pe Z) /\ Pe (eb_motive b) /\
                              List.Forall (fun br => Pe (snd br)) (eb_brs b)) Bks ->
        Pe M -> Pe (a_elim oq Us m Bks M))
    (case_pi : forall A B, Pe A -> Pe B -> Pe (a_pi A B))
    (case_fn : forall A M, Pe A -> Pe M -> Pe (a_fn A M))
    (case_app : forall M N, Pe M -> Pe N -> Pe (a_app M N))
    (case_var : forall x, Pe (a_var x))
    (case_let : forall b B, Pb b -> Pe B -> Pe (a_let b B))
    (case_mem : forall H x, Pm H -> Pe (a_mem H x))
    (case_record : forall p, Pe (a_record p))
    (case_tuple : forall T fs, Pe T -> List.Forall (fun f => Pe (snd f)) fs -> Pe (a_tuple T fs))
    (case_proj : forall f M, Pe M -> Pe (a_proj f M))
    (case_me_unit : forall fp, Pm (me_unit fp))
    (case_me_var : forall k, Pm (me_var k))
    (case_me_mem : forall H y, Pm H -> Pm (me_mem H y))
    (case_me_app : forall H N, Pm H -> Pe N -> Pm (me_app H N))
    (case_me_lit : forall U, Pu U -> Pm (me_lit U))
    (case_b_def : forall oA M, (forall A, oA = Some A -> Pe A) -> Pe M -> Pb (b_def oA M))
    (case_b_mod : forall U, Pu U -> Pb (b_mod U))
    (case_gu_mk : forall Δ D, List.Forall Pc Δ -> Pd D -> Pu (gu_mk Δ D))
    (case_md_body : forall s Φ, Pg Φ -> Pd (md_body s Φ))
    (case_md_alias : forall E, Pm E -> Pd (md_alias E))
    (case_gm_nil : Pg gm_nil)
    (case_gm_ext : forall Φ x E, Pg Φ -> Pn E -> Pg (gm_ext Φ x E))
    (case_gm_open : forall Φ H its, Pg Φ -> Pm H -> Pg (gm_open Φ H its))
    (case_ge_def : forall b pv A B, Pe A -> (forall M, B = Some M -> Pe M) -> Pn (ge_def b pv A B))
    (case_ge_mod : forall pv U, Pu U -> Pn (ge_mod pv U))
    (case_ge_ind : forall pv p k D Φ, Pg Φ -> Pn (ge_ind pv p k D Φ))
    (case_ge_def_mod : forall pv A M U, Pe A -> Pe M -> Pu U -> Pn (ge_def_mod pv A M U))
    (case_ge_record : forall pv p R Φ, Pg Φ -> Pn (ge_record pv p R Φ))
    (case_ce_ass : forall A, Pe A -> Pc (ce_ass A))
    (case_ce_def : forall A M, Pe A -> Pe M -> Pc (ce_def A M))
    (case_ce_mod : forall U, Pu U -> Pc (ce_mod U))
    (case_ce_dm : forall A M U, Pe A -> Pe M -> Pu U -> Pc (ce_dm A M U)).

  (** The mutual induction principle on terms, written by hand: the
      branches of an eliminator's blocks are nested through pairs. *)
  Fixpoint exp_mut (M : exp) : Pe M :=
    match M with
    | a_typ i => case_typ i
    | a_univ t => case_univ t (exp_mut t)
    | a_level n => case_level n
    | a_llit n => case_llit n
    | a_succl M => case_succl M (exp_mut M)
    | a_maxl M N => case_maxl M N (exp_mut M) (exp_mut N)
    | a_ntok => case_ntok
    | a_True => case_True
    | a_true => case_true
    | a_False => case_False
    | a_exfalso A M => case_exfalso A M (exp_mut A) (exp_mut M)
    | a_ind p k => case_ind p k
    | a_con p k c => case_con p k c
    | a_nlit n => case_nlit n
    | a_elim oq Us0 m Bks M =>
        case_elim oq Us0 m Bks M
          ((fix us_mut (Us : list exp) : List.Forall Pe Us :=
              match Us with
              | nil => List.Forall_nil _
              | cons U Us' => List.Forall_cons U (exp_mut U) (us_mut Us')
              end) Us0)
          ((fix blocks_mut (Bks : list eblock) :
              List.Forall (fun b => (forall Z, eb_ann b = Some Z -> Pe Z) /\ Pe (eb_motive b) /\
                                    List.Forall (fun br => Pe (snd br)) (eb_brs b)) Bks :=
              match Bks with
              | nil => List.Forall_nil _
              | cons (eb_mk nm oZ A Bs) Bks' =>
                  List.Forall_cons (eb_mk nm oZ A Bs)
                    (conj
                       (match oZ as o return (forall Z, o = Some Z -> Pe Z) with
                        | Some Z0 => fun Z e => match e in _ = o' return match o' with Some Z => Pe Z | None => True end with
                                               | eq_refl => exp_mut Z0 end
                        | None => fun Z e => False_ind _ (match e in _ = o' return match o' with Some _ => False | None => True end with
                                             | eq_refl => I end)
                        end)
                       (conj (exp_mut A)
                          ((fix brs_mut (Bs : list (string * nat * exp)) : List.Forall (fun b => Pe (snd b)) Bs :=
                              match Bs with
                              | nil => List.Forall_nil _
                              | cons b Bs' => List.Forall_cons b (exp_mut (snd b)) (brs_mut Bs')
                              end) Bs)))
                    (blocks_mut Bks')
              end) Bks)
          (exp_mut M)
    | a_pi A B => case_pi A B (exp_mut A) (exp_mut B)
    | a_fn A M => case_fn A M (exp_mut A) (exp_mut M)
    | a_app M N => case_app M N (exp_mut M) (exp_mut N)
    | a_var x => case_var x
    | a_let b B => case_let b B (bnd_mut b) (exp_mut B)
    | a_mem H x => case_mem H x (modexp_mut H)
    | a_record p => case_record p
    | a_tuple T fs0 =>
        case_tuple T fs0 (exp_mut T)
          ((fix fields_mut (fs : list (string * exp)) : List.Forall (fun f => Pe (snd f)) fs :=
              match fs with
              | nil => List.Forall_nil _
              | cons f fs' => List.Forall_cons f (exp_mut (snd f)) (fields_mut fs')
              end) fs0)
    | a_proj f M => case_proj f M (exp_mut M)
    end
  with modexp_mut (H : modexp) : Pm H :=
    match H with
    | me_unit fp => case_me_unit fp
    | me_var k => case_me_var k
    | me_mem H y => case_me_mem H y (modexp_mut H)
    | me_app H N => case_me_app H N (modexp_mut H) (exp_mut N)
    | me_lit U => case_me_lit U (gunit_mut U)
    end
  with bnd_mut (b : bnd) : Pb b :=
    match b with
    | b_def oA M =>
        case_b_def oA M
          (match oA as o return (forall A, o = Some A -> Pe A) with
           | Some A0 => fun A e => match e in _ = o' return match o' with Some A => Pe A | None => True end with
                                  | eq_refl => exp_mut A0 end
           | None => fun A e => False_ind _ (match e in _ = o' return match o' with Some _ => False | None => True end with
                                | eq_refl => I end)
           end)
          (exp_mut M)
    | b_mod U => case_b_mod U (gunit_mut U)
    end
  with gunit_mut (U : gunit) : Pu U :=
    match U with
    | gu_mk Δ D =>
        case_gu_mk Δ D
          ((fix tele_mut (Δ : list centry) : List.Forall Pc Δ :=
              match Δ with
              | nil => List.Forall_nil _
              | cons e Δ' => List.Forall_cons _ (centry_mut e) (tele_mut Δ')
              end) Δ)
          (moddef_mut D)
    end
  with moddef_mut (D : moddef) : Pd D :=
    match D with
    | md_body s Φ => case_md_body s Φ (gmod_mut Φ)
    | md_alias E => case_md_alias E (modexp_mut E)
    end
  with gmod_mut (Φ : gmod) : Pg Φ :=
    match Φ with
    | gm_nil => case_gm_nil
    | gm_ext Φ x E => case_gm_ext Φ x E (gmod_mut Φ) (gentry_mut E)
    | gm_open Φ H its => case_gm_open Φ H its (gmod_mut Φ) (modexp_mut H)
    end
  with gentry_mut (E : gentry) : Pn E :=
    match E with
    | ge_def b pv A B =>
        case_ge_def b pv A B (exp_mut A)
          (match B as o return (forall M, o = Some M -> Pe M) with
           | Some M0 => fun M e => match e in _ = o' return match o' with Some M => Pe M | None => True end with
                                  | eq_refl => exp_mut M0 end
           | None => fun M e => False_ind _ (match e in _ = o' return match o' with Some _ => False | None => True end with
                                | eq_refl => I end)
           end)
    | ge_mod pv U => case_ge_mod pv U (gunit_mut U)
    | ge_ind pv p k D Φ => case_ge_ind pv p k D Φ (gmod_mut Φ)
    | ge_def_mod pv A M U => case_ge_def_mod pv A M U (exp_mut A) (exp_mut M) (gunit_mut U)
    | ge_record pv p R Φ => case_ge_record pv p R Φ (gmod_mut Φ)
    end
  with centry_mut (e : centry) : Pc e :=
    match e with
    | ce_ass A => case_ce_ass A (exp_mut A)
    | ce_def A M => case_ce_def A M (exp_mut A) (exp_mut M)
    | ce_mod U => case_ce_mod U (gunit_mut U)
    | ce_dm A M U => case_ce_dm A M U (exp_mut A) (exp_mut M) (gunit_mut U)
    end.

  Theorem syn_mut_ind :
    (forall M, Pe M) /\ (forall H, Pm H) /\ (forall b, Pb b) /\ (forall U, Pu U) /\
    (forall D, Pd D) /\ (forall Φ, Pg Φ) /\ (forall E, Pn E) /\
    (forall e, Pc e).
  Proof.
    repeat split; [ exact exp_mut | exact modexp_mut | exact bnd_mut | exact gunit_mut
                  | exact moddef_mut | exact gmod_mut | exact gentry_mut
                  | exact centry_mut ].
  Qed.
End syn_mut_ind.

(** ** Chains of Selections *)

(** [H.y1. … .yn], the submodules [pre] selected from [H] in order. *)
Fixpoint me_mems (H : modexp) (pre : list string) : modexp :=
  match pre with
  | nil => H
  | y :: pre' => me_mems (me_mem H y) pre'
  end.

(** [H.y1. … .yn.x] as a term: submodule selections, then a member. *)
Fixpoint member_ref (H : modexp) (ch : list string) : exp :=
  match ch with
  | nil => a_true
  | x :: nil => a_mem H x
  | y :: ch' => member_ref (me_mem H y) ch'
  end.

(** The module named [X::Y.W.Z], [q_abs ["X"; "Y"] ["W"; "Z"]], and the global
    named so, both as selections from the unit. *)
(** [H N1 … Nn]: a module applied to arguments. *)
Fixpoint me_apps (H : modexp) (Ns : list exp) : modexp :=
  match Ns with
  | nil => H
  | N :: Ns' => me_apps (me_app H N) Ns'
  end.

(** A module expression read as the term it spells, as written: a
    selection is the member as a term, an application the term applied; a
    unit, a module slot and a literal spell no term. *)
Fixpoint modexp_as_term (H : modexp) : option exp :=
  match H with
  | me_mem H' y => Some (a_mem H' y)
  | me_app H' N => option_map (fun M => a_app M N) (modexp_as_term H')
  | _ => None
  end.

Definition qname_mod (p : qname) : modexp := me_mems (me_unit (q_unit p)) (q_chain p).

Definition qname_term (p : qname) : exp := member_ref (me_unit (q_unit p)) (q_chain p).

(** The qualified name a chain of selections from a unit spells, and [None]
    for any other module expression. *)
Fixpoint mod_qname (H : modexp) : option qname :=
  match H with
  | me_unit fp => Some (q_abs fp nil)
  | me_mem H y =>
      match mod_qname H with
      | Some p => Some {| q_unit := q_unit p; q_chain := q_chain p ++ y :: nil |}
      | None => None
      end
  | _ => None
  end.

(** ** Units

    A body unit and a body entry, the forms every global module has. *)
Abbreviation gu_body Δ Φ := (gu_mk Δ (md_body sm_closed Φ)).
Abbreviation ge_body pv Δ Φ := (ge_mod pv (gu_body Δ Φ)).
(** A local (open) body unit. *)
Abbreviation gu_open Δ Φ := (gu_mk Δ (md_body sm_open Φ)).

Definition gu_params (U : gunit) : list centry := match U with gu_mk Δ _ => Δ end.

(** The number of uniform parameters of a group. *)
Definition ind_nu (D : ind_decl) : nat := List.length (ind_uparams D).

(** The member [k] of a group. *)
Definition ind_member (D : ind_decl) (k : nat) : option imember := List.nth_error (ind_members D) k.

(** The parameters of a member, innermost first: its non-uniform ones
    inside the group's uniform ones; their numbers. *)
Definition im_params (D : ind_decl) (M : imember) : list centry := im_nparams M ++ ind_uparams D.
(** The number of a member's non-uniform parameters. *)
Definition im_nn (M : imember) : nat := List.length (im_nparams M).
(** The number of all a member's parameters, uniform and non-uniform. *)
Definition im_np (D : ind_decl) (M : imember) : nat := im_nn M + ind_nu D.

(** A declared member, and the path of its entry. *)
Definition im_path (M : imember) : option qname :=
  match im_head M with mh_decl p => Some p | _ => None end.

(** The module of the inductive type [D] of body [Φ], as a unit: it takes
    the uniform parameters, with the frames' parameters outside them, so
    that it is closed, as an alias is. *)
Definition ind_unit (D : ind_decl) (Φ : gmod) : gunit := gu_body (ind_uparams D) Φ.

Definition gu_def (U : gunit) : moddef := match U with gu_mk _ D => D end.

(** The body of a body unit, and the empty body for an alias. *)
Definition gu_mod (U : gunit) : gmod :=
  match U with
  | gu_mk _ (md_body _ Φ) => Φ
  | gu_mk _ (md_alias _) => gm_nil
  end.

(** The number of indices a body binds. *)
Fixpoint gm_binders (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ' _ _ => S (gm_binders Φ')
  | gm_open Φ' _ its => List.length its + gm_binders Φ'
  end.

(** The name an import item declares. *)
Definition iitem_name (it : iitem) : string := let '(_, d, _) := it in d.

(** The names [Φ] declares, outermost last, and a name not among them. *)
Fixpoint gm_names (Φ : gmod) : list string :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' x _ => x :: gm_names Φ'
  | gm_open Φ' _ its => rev (map iitem_name its) ++ gm_names Φ'
  end.

Definition gm_fresh (x : string) (Φ : gmod) : Prop :=
  ~ List.In x (gm_names Φ).

(** ** Notations

    Every notation of the syntax lives in ordinary [constr], in [mctt_scope]:
    there is no custom entry and hence no delimiter to write.  The price is
    that a spelling can denote only one sort, so the normal forms, which
    mirror the expressions constructor for constructor, carry a superscript
    [ⁿ].  Values carry a superscript [ᵈ]; see [Domain_Notations].  The
    notations of each topic are in their own module, after its definitions;
    [Syntax_Notations], at the end, exports all of them but those of module
    bodies ([GlobalCtx_Notations]) and of weakenings ([Wk_Notations]).

    Everything that reads as an atom is at level 0, the postfix forms at
    level 1, and the constructor forms with a recursive last argument at
    level 2. *)
Module Exp_Notations.
  (** A large universe, [a_typ n], is [Typeω@n]: it is the universe ω²+n,
      above every small one. *)
  Notation "'Typeω' @ n" := (a_typ n) (at level 1, n at level 0, format "'Typeω' @ n") : mctt_scope.
  (** A small universe at an arbitrary level term, and — for a literal level —
      the short form the literal-level rules are written with. *)
  Notation "'Type' ⟨ t ⟩" := (a_univ t) (at level 0, t at level 99, format "'Type' ⟨ t ⟩") : mctt_scope.
  Notation "'Type' @ n" := (a_univ (a_llit (ofin n))) (at level 1, n at level 0, format "'Type' @ n") : mctt_scope.
  (** [Level@n] is the type of levels below [ω·(n+1)], and [Level] the
      finite ones, [Level@0]: [Level] is declared second so that it is the
      spelling a level type of sort [0] prints with. *)
  Notation "'Level' @ n" := (a_level n) (at level 1, n at level 0, format "'Level' @ n") : mctt_scope.
  Notation "'Level'" := (a_level 0) : mctt_scope.
  (** The level literals: [𝕃ᵒ o] is the ordinal [o], and [𝕃@n] the finite
      level [n], the surface syntax's [<n>l].  The token is not a word: [lv]
      would make every identifier of that name a keyword. *)
  Notation "'𝕃ᵒ' o" := (a_llit o) (at level 1, o at level 0, format "'𝕃ᵒ' o") : mctt_scope.
  Notation "'𝕃' @ n" := (a_llit (ofin n)) (at level 1, n at level 0, format "'𝕃' @ n") : mctt_scope.
  Notation "'succl' M" := (a_succl M) (at level 2, M at level 1) : mctt_scope.
  Notation "'maxl' M N" := (a_maxl M N) (at level 2, M at level 1, N at level 1) : mctt_scope.
  Notation "'#' n" := (a_var n) (at level 1, n at level 0, format "'#' n") : mctt_scope.
  Notation "'ℕ'" := a_ntok : mctt_scope.
  Notation "'λ' A M" := (a_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Π' A B" := (a_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'ℓ' A ≔ M 'in' B" := (a_let (b_def (Some A) M) B) (at level 2, A at level 1, M at level 60, B at level 60) : mctt_scope.
  Notation "'ℓ' ≔ M 'in' B" := (a_let (b_def None M) B) (at level 2, M at level 60, B at level 60) : mctt_scope.
  Notation "'ℓₘ' U 'in' B" := (a_let (b_mod U) B) (at level 2, U at level 1, B at level 60) : mctt_scope.
  Notation "'⊤'" := a_True : mctt_scope.
  Notation "'⋆'" := a_true : mctt_scope.
  Notation "'⊥'" := a_False : mctt_scope.
  Notation "'efq' M 'return' A" := (a_exfalso A M) (at level 2, M at level 60, A at level 60) : mctt_scope.
  (** Application needs an explicit operator: a [constr] notation may not be
      pure juxtaposition, which is Rocq's own application. *)
  Notation "M $ N" := (a_app M N) (at level 10, left associativity) : mctt_scope.
End Exp_Notations.

(** A module body: [⋄] is empty, and [Φ ⊳ x ↦ E] adds the entry [E] named
    [x]. *)
Module GlobalCtx_Notations.
  Notation "⋄" := gm_nil.
  Notation "Φ ⊳ x ↦ E" := (gm_ext Φ x E) (at level 50, x at level 0).
End GlobalCtx_Notations.

(** * Contexts

    A context entry occupies one de Bruijn index, whether it is an
    assumption, a definition or a module slot. *)
Abbreviation ctx := (list centry).

(** A body as the context entries it binds, innermost first.  A local open
    binds one placeholder per item: a pre-form is never typed.  So does an
    inductive type, which only a filed module declares. *)
Fixpoint body_ctx (Φ : gmod) : ctx :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' _ (ge_def _ _ A (Some M)) => cons (ce_def A M) (body_ctx Φ')
  | gm_ext Φ' _ (ge_def _ _ A None) => cons (ce_ass A) (body_ctx Φ')
  | gm_ext Φ' _ (ge_mod _ U) => cons (ce_mod U) (body_ctx Φ')
  | gm_ext Φ' _ (ge_ind _ _ _ _ _) => cons (ce_ass a_True) (body_ctx Φ')
  | gm_ext Φ' _ (ge_def_mod _ A M U) => cons (ce_dm A M U) (body_ctx Φ')
  | gm_ext Φ' _ (ge_record _ _ _ _) => cons (ce_ass a_True) (body_ctx Φ')
  | gm_open Φ' _ its => List.repeat (ce_ass a_True) (List.length its) ++ body_ctx Φ'
  end.

(** The term part of a body's entry, its type and its body: a definition
    with a body, or a definition with a module part. *)
Definition entry_tm (E : gentry) : option (exp * exp) :=
  match E with
  | ge_def _ _ A (Some M) => Some (A, M)
  | ge_def_mod _ A M _ => Some (A, M)
  | _ => None
  end.

(** The module part of a body's entry, its unit: a module, or a definition
    with a module part. *)
Definition entry_unit (E : gentry) : option gunit :=
  match E with
  | ge_mod _ U => Some U
  | ge_def_mod _ _ _ U => Some U
  | _ => None
  end.

(** The unit a context entry holds: a module slot's, or a definition with
    a module part's. *)
Definition centry_unit (e : centry) : option gunit :=
  match e with
  | ce_mod U | ce_dm _ _ U => Some U
  | _ => None
  end.

(** ** Notations *)
Module Ctx_Notations.
  (** Extension is [▹] rather than the paper's comma: a parsing [,] in [constr]
      would steal Rocq's pair notation.  Both are restricted to [centry] so
      that an unrelated [list] does not print as a context.  A definition
      entry is [Γ ▸ A ≔ M]; it has its own first token because [Γ ▹ A] would
      otherwise be a proper prefix of it. *)
  Notation "⋅" := (@nil centry) : mctt_scope.
  Notation "Γ ▹ A" := (@cons centry (ce_ass A) Γ) (at level 50, left associativity) : mctt_scope.
  Notation "Γ ▸ A ≔ M" := (@cons centry (ce_def A M) Γ) (at level 50, left associativity) : mctt_scope.
  Notation "Γ '▹ₘ' U" := (@cons centry (ce_mod U) Γ) (at level 50, left associativity) : mctt_scope.
  Notation "Γ '▸ₘ' A ≔ M ‖ U" := (@cons centry (ce_dm A M U) Γ) (at level 50, left associativity) : mctt_scope.
End Ctx_Notations.

(** * Universe Indices

    The universes of the model form two tiers:

    - the small tier [us o], indexed by an ordinal [o] below ω² (see
      [Core.Syntactic.Levels.Ordinals]), whose universes are the small universes
      [𝕌@l] whose levels realise an ordinal below [o];
    - the large tier [ul n] (the syntactic [Typeω@n], read as [Typeω²+n]),
      whose universes are every small universe and the large ones [𝕌ω@m] for
      [m < n].

    Every small index is below every large one.  The large tier is the
    default: [ul] is a coercion, so [per_univ_elem i] for a natural number
    [i] is the large universe [Typeω²+i]. *)
Inductive uidx : Set :=
| us : o2 -> uidx
| ul : nat -> uidx.

Coercion ul : nat >-> uidx.

Definition uidx_lt (u v : uidx) : Prop :=
  match u, v with
  | us j, us k => olt j k
  | us _, ul _ => True
  | ul _, us _ => False
  | ul j, ul k => j < k
  end.

Definition uidx_le (u v : uidx) : Prop :=
  match u, v with
  | us j, us k => ole j k
  | us _, ul _ => True
  | ul _, us _ => False
  | ul j, ul k => j <= k
  end.

Lemma uidx_lt_le_trans : forall u v w, uidx_lt u v -> uidx_le v w -> uidx_lt u w.
Proof. intros [] [] []; cbn; intros; auto; try lia; ord. Qed.

Lemma uidx_le_refl : forall u, uidx_le u u.
Proof. intros []; cbn; [ ord | lia ]. Qed.

Lemma uidx_le_trans : forall u v w, uidx_le u v -> uidx_le v w -> uidx_le u w.
Proof. intros [] [] []; cbn; intros; auto; try lia; ord. Qed.

Lemma uidx_lt_le : forall u v, uidx_lt u v -> uidx_le u v.
Proof. intros [] []; cbn; intros; auto; try lia; ord. Qed.

Lemma uidx_wf : well_founded uidx_lt.
Proof.
  assert (Hs : forall j, Acc uidx_lt (us j)).
  { intros j; induction j as [j IH] using (well_founded_ind olt_wf).
    constructor; intros [k | k] Hk; cbn in Hk; [ apply IH; exact Hk | contradiction ]. }
  intros [j | n]; [ apply Hs |].
  induction n as [n IH] using lt_wf_ind; constructor; intros [k | k] Hk; cbn in Hk; [ apply Hs | apply IH; exact Hk ].
Qed.

(** ** Universes at Any Index, as Terms and Values

    A judgment in a universe is the four-value pattern of its two sides in the
    universe's element PER, whichever tier the universe is in.  The lemmas
    are stated at an index [u], through the universe's term [ulvl_tm u] and
    value [ulvl_val u]; the large forms below are their instances at [ul i],
    which is [Typeω@i] by computation. *)
Definition ulvl_tm (u : uidx) : exp :=
  match u with us o => a_univ (a_llit o) | ul n => a_typ n end.

(** A large level whose universe contains the universe at [u]. *)
Definition ulvl_above (u : uidx) : nat :=
  match u with us _ => 0 | ul n => S n end.

(** The large level a type at [u] is also a type of. *)
Definition ulvl (u : uidx) : nat :=
  match u with us _ => 0 | ul n => n end.

Lemma uidx_lt_ulvl_above : forall u, uidx_lt u (ulvl_above u).
Proof. intros []; cbn; [ exact I | lia ]. Qed.

Lemma uidx_le_ulvl : forall u, uidx_le u (ulvl u).
Proof. intros []; cbn; [ exact I | lia ]. Qed.

(** The least index: [Type@0] is below every universe. *)
Lemma uidx_le_least : forall u, uidx_le (us oz) u.
Proof. intros []; cbn; [ ord | exact I ]. Qed.

(** The large levels of two ordered indices are ordered: a small universe
    lives in [Typeω@0], and the large tier's order is the order on levels. *)
Lemma uidx_le_ulvl_le : forall u v, uidx_le u v -> ulvl u <= ulvl v.
Proof. intros [] []; cbn; intros; lia. Qed.

(** The join of two indices: a large universe absorbs a small one. *)
Definition umax (u v : uidx) : uidx :=
  match u, v with
  | us n, us m => us (omax n m)
  | us _, ul i => ul i
  | ul i, us _ => ul i
  | ul i, ul j => ul (max i j)
  end.

Lemma uidx_le_umax_left : forall u v, uidx_le u (umax u v).
Proof. intros [] []; cbn; try exact I; try lia; ord. Qed.

Lemma uidx_le_umax_right : forall u v, uidx_le v (umax u v).
Proof. intros [] []; cbn; try exact I; try lia; ord. Qed.

Lemma umax_lub : forall u v w, uidx_le u w -> uidx_le v w -> uidx_le (umax u v) w.
Proof. intros [] [] []; cbn; intros; try contradiction; try exact I; try lia; ord. Qed.

(** Discharges the order side conditions between universe indices. *)
Ltac solve_uidx :=
  first [ assumption | exact I | solve [ cbn [uidx_lt uidx_le] in *; lia ]
        | solve [ cbn [uidx_lt uidx_le] in *; ord ]
        | solve [ repeat match goal with k : uidx |- _ => destruct k end;
                  cbn [uidx_lt uidx_le] in *; first [ contradiction | exact I | lia | ord ] ] ].


(** * Levels as Expressions

    A flat level [max (c, k₁ + a₁, …, kₙ + aₙ)] is written as an expression by
    folding [maxl] to the left over the atoms, each under its own offset of
    [succl]s.  The constant is written only when it is not [0]: with atoms
    present, [𝕃@0] is the neutral element of [maxl] and would not be a normal
    form.  This is the spelling of a canonical level normal form
    ([nf_lvl] below), so it is also how a level is printed. *)
Fixpoint succl_n (k : nat) (M : exp) : exp :=
  match k with
  | 0 => M
  | S k' => a_succl (succl_n k' M)
  end.

Fixpoint lvl_fold (hd : exp) (xs : list (nat * exp)) : exp :=
  match xs with
  | nil => hd
  | (k, a) :: r => lvl_fold (a_maxl hd (succl_n k a)) r
  end.

Definition lvl_exp_of (c : o2) (xs : list (nat * exp)) : exp :=
  match xs, c with
  | nil, _ => a_llit c
  | (k, a) :: r, (0, 0) => lvl_fold (succl_n k a) r
  | (k, a) :: r, _ => lvl_fold (a_maxl (a_llit c) (succl_n k a)) r
  end.

(** * Normal and Neutral Forms

    Normal forms nest through lists, as terms do: the parameters and
    arguments of a type former or a constructor are a [list nf]; the atoms
    of a canonical level, and the blocks and branches of a stuck
    eliminator, are lists of the small records below, generic in what they
    hold.  Each record has [Scheme All] registered, so that the induction
    principle generated for [nf] and [ne] carries hypotheses for what they
    hold, as [list_all] does for lists. *)

(** An atom [k + a] of a canonical level: the neutral level [a], of type
    [Level@s], with its offset [k]. *)
Record level_atom_g (E : Set) : Set := mk_level_atom
  { (** The offset [k]: the number of successors above the neutral *)
    atom_offset : nat
    (** The sort [s] of the neutral: it is of type [Level@s], so below
        ω·(s+1) *)
  ; atom_sort : nat
    (** The neutral level [a] *)
  ; atom_level : E }.
Arguments mk_level_atom {E}.
Arguments atom_offset {E}.
Arguments atom_sort {E}.
Arguments atom_level {E}.
Scheme All for level_atom_g.

(** A branch of a stuck eliminator: the case of a constructor, binding a
    number of variables. *)
Record normal_branch_g (E : Set) : Set := mk_normal_branch
  { (** The constructor the branch is the case of *)
    branch_constructor : string
    (** The number of variables the branch binds: the member's non-uniform
        parameters, the arguments, and one recursive result per recursive
        argument *)
  ; branch_arity : nat
    (** The branch's body, under those variables *)
  ; branch_body : E }.
Arguments mk_normal_branch {E}.
Arguments branch_constructor {E}.
Arguments branch_arity {E}.
Arguments branch_body {E}.
Scheme All for normal_branch_g.

(** A block of a stuck eliminator, one per member of the group, in the
    group's order. *)
Record normal_block_g (E : Set) : Set := mk_normal_block
  { (** The number of variables the motive binds: the member's
        non-uniform parameters and the scrutinee *)
    block_arity : nat
    (** The motive, under those variables *)
  ; block_motive : E
    (** The branches, one per constructor of the member, in order *)
  ; block_branches : list (normal_branch_g E) }.
Arguments mk_normal_block {E}.
Arguments block_arity {E}.
Arguments block_motive {E}.
Arguments block_branches {E}.
Scheme All for normal_block_g.

(** ** Operations on the Records

    A function on what the records hold acts on the records.  A branch's
    body and a block's motive sit under binders, so the function on a
    branch or a block is told how many: the arity. *)

(** An atom with its neutral mapped. *)
Definition map_level_atom {E F : Set} (f : E -> F) (a : level_atom_g E) : level_atom_g F :=
  mk_level_atom (atom_offset a) (atom_sort a) (f (atom_level a)).

(** A branch with its body mapped, at its arity. *)
Definition map_normal_branch {E F : Set} (f : nat -> E -> F) (br : normal_branch_g E) : normal_branch_g F :=
  mk_normal_branch (branch_constructor br) (branch_arity br) (f (branch_arity br) (branch_body br)).

(** A block with its motive and its branches' bodies mapped, each at its
    arity. *)
Definition map_normal_block {E F : Set} (f : nat -> E -> F) (b : normal_block_g E) : normal_block_g F :=
  mk_normal_block (block_arity b) (f (block_arity b) (block_motive b))
    (List.map (map_normal_branch f) (block_branches b)).

(** [P] holds of a block's motive and of its branches' bodies, each at its
    arity. *)
Definition normal_block_forall {E : Set} (P : nat -> E -> Prop) (b : normal_block_g E) : Prop :=
  P (block_arity b) (block_motive b) /\ all_list (fun br => P (branch_arity br) (branch_body br)) (block_branches b).

(** The boolean [normal_block_forall]. *)
Definition normal_block_forallb {E : Set} (f : nat -> E -> bool) (b : normal_block_g E) : bool :=
  f (block_arity b) (block_motive b) && List.forallb (fun br => f (branch_arity br) (branch_body br)) (block_branches b).

(** ** Using the Generated Hypotheses

    The induction principle of a type nesting through [list] and the
    records gives [list_all] of the motive at a list.  These lemmas turn it
    into what a proof by that induction needs: equal maps, and [all_list]. *)
Lemma list_all_map_ext {A B : Set} (P : A -> Set) (f g : A -> B) : forall l,
    list_all A P l -> (forall x, P x -> f x = g x) -> List.map f l = List.map g l.
Proof. intros l Hl Hfg; induction Hl; cbn; f_equal; auto. Qed.

Lemma list_all_all_list {A : Set} (P : A -> Set) (Q : A -> Prop) : forall l,
    list_all A P l -> (forall x, P x -> Q x) -> all_list Q l.
Proof. intros l Hl HPQ; induction Hl; cbn; auto. Qed.

Lemma list_all_all_list_impl {A : Set} (P : A -> Set) (Q R : A -> Prop) : forall l,
    list_all A P l -> all_list Q l -> (forall x, P x -> Q x -> R x) -> all_list R l.
Proof. intros l Hl; induction Hl as [| x Hx l Hl IH]; cbn; [ auto | intros [Hq Hr] H; split; auto ]. Qed.

Lemma all_list_app {A : Set} (Q : A -> Prop) : forall l l',
    all_list Q l -> all_list Q l' -> all_list Q (l ++ l').
Proof. induction l as [| x l IH]; cbn; [ auto | intros l' [Hx Hl] Hl'; split; auto ]. Qed.

Lemma all_list_map {A B : Set} (f : A -> B) (Q : B -> Prop) : forall l,
    all_list Q (List.map f l) <-> all_list (fun x => Q (f x)) l.
Proof. induction l as [| x l IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma list_all_Forall_map {A B : Set} (P : A -> Set) (Q : B -> Prop) (f : A -> B) : forall l,
    list_all A P l -> (forall x, P x -> Q (f x)) -> List.Forall Q (List.map f l).
Proof. intros l Hl HPQ; induction Hl; constructor; auto. Qed.

(** A goal [List.map f l = List.map g l], or [all_list R l], reduced to one
    goal per element [x] of [l], from the generated hypothesis on [l] (and,
    for [all_list], from an [all_list] hypothesis on [l] when there is
    one): [Hx] the motive at [x], [Hy] that hypothesis at [x].  A record's
    [_all] hypothesis is taken apart, and with it the record. *)
Ltac nested_elements :=
  rewrite ?List.map_map;
  let x := fresh "x" in let Hx := fresh "Hx" in let Hy := fresh "Hy" in
  match goal with
  | Hl : list_all _ _ ?l |- List.map _ ?l = List.map _ ?l =>
      apply (list_all_map_ext _ _ _ l Hl); intros x Hx; try destruct Hx
  | Hl : list_all _ _ ?l, Hq : all_list _ ?l |- all_list _ ?l =>
      apply (list_all_all_list_impl _ _ _ l Hl Hq); intros x Hx Hy; try destruct Hx
  | Hl : list_all _ _ ?l |- all_list _ ?l =>
      apply (list_all_all_list _ _ l Hl); intros x Hx; try destruct Hx
  end.

Lemma list_all_forallb {A : Set} (P : A -> Set) (f : A -> bool) (Q : A -> Prop) : forall l,
    list_all A P l -> (forall x, P x -> f x = true <-> Q x) -> List.forallb f l = true <-> all_list Q l.
Proof.
  intros l Hl HfQ; induction Hl as [| x Hx l Hl IH]; cbn; [ split; auto |].
  rewrite Bool.andb_true_iff, (HfQ x Hx), IH; reflexivity.
Qed.

Inductive nf : Set :=
(** A large universe *)
| nf_typ : nat -> nf
(** A small universe at a canonical level [max (c, k₁ + a₁, …)], in the shape
    of [nf_lvl] below *)
| nf_univ : o2 -> list (level_atom_g ne) -> nf
(** The type [Level@n] *)
| nf_level : nat -> nf
(** A canonical level [max (c, k₁ + a₁, …)]: the atoms are strictly sorted by
    their neutral and their sort (see [Core.Syntactic.Levels.Levels]) with no
    repetition, no atom is of a sort below the constant's tier (the constant
    absorbs it), and the constant [c] is [0] unless it exceeds every
    offset.  [nf_lvl_of] builds
    the normal form of a canonical level [lvl]. *)
| nf_lvl : o2 -> list (level_atom_g ne) -> nf
(** [⊤] *)
| nf_True : nf
(** Its element *)
| nf_true : nf
(** [⊥] *)
| nf_False : nf
(** A [Π] of normal forms *)
| nf_pi : nf -> nf -> nf
(** A function, its domain and body normal *)
| nf_fn : nf -> nf -> nf
(** A member of a group of inductive types at its parameters *)
| nf_indty : qname -> nat -> list nf -> nf
(** A constructor at the parameters of its type and its arguments *)
| nf_con : qname -> nat -> string -> list nf -> nf
(** A neutral *)
| nf_neut : ne -> nf
(** A record type at its parameters *)
| nf_record : qname -> list nf -> nf
(** An element of the record type at [p], η-long: the type's parameters,
    the field names and the fields *)
| nf_tuple : qname -> list nf -> list string -> list nf -> nf
with ne : Set :=
(** The [⊥]-eliminator, always stuck *)
| ne_exfalso : nf -> ne -> ne
(** The eliminator of the group [pq], at its declared member [m], stuck
    on a neutral, at the group's uniform parameters; its blocks carry no
    annotation.  (An eliminator at a view is stuck as the eliminator of the
    view's container's group.) *)
| ne_elim : qname -> list nf -> nat -> list (normal_block_g nf) -> ne -> ne
(** A neutral applied *)
| ne_app : ne -> nf -> ne
(** A variable *)
| ne_var : nat -> ne
(** An opaque definition or an axiom: it does not unfold. *)
| ne_glob : qname -> ne
(** A field of a neutral *)
| ne_proj : string -> ne -> ne.

(** The records at normal forms and neutrals. *)
Abbreviation level_atom := (level_atom_g ne).
Abbreviation normal_branch := (normal_branch_g nf).
Abbreviation normal_block := (normal_block_g nf).

(** The induction principle of normal forms and neutrals, generated: a
    list carries [list_all] of the motive, a record of the records above
    its own [_all]. *)
Scheme nf_nested_ind := Induction for nf Sort Prop
with ne_nested_ind := Induction for ne Sort Prop.
Combined Scheme nf_ne_ind from nf_nested_ind, ne_nested_ind.

(** [M] applied to [args], outermost first. *)
Fixpoint apps_exp (M : exp) (args : list exp) : exp :=
  match args with
  | nil => M
  | N :: args' => apps_exp (a_app M N) args'
  end.

(** The term a normal form stands for (normal forms are a subset of
    terms). *)
Fixpoint nf_to_exp (M : nf) : exp :=
  match M with
  | nf_typ i => a_typ i
  | nf_univ c xs => a_univ (lvl_exp_of c (List.map (fun a => (atom_offset a, ne_to_exp (atom_level a))) xs))
  | nf_level n => a_level n
  | nf_lvl c xs => lvl_exp_of c (List.map (fun a => (atom_offset a, ne_to_exp (atom_level a))) xs)
  | nf_True => a_True
  | nf_true => a_true
  | nf_False => a_False
  | nf_pi A B => a_pi (nf_to_exp A) (nf_to_exp B)
  | nf_fn A M => a_fn (nf_to_exp A) (nf_to_exp M)
  | nf_indty p k Ms => apps_exp (a_ind p k) (List.map nf_to_exp Ms)
  | nf_con p k c Ms => apps_exp (a_con p k c) (List.map nf_to_exp Ms)
  | nf_neut M => ne_to_exp M
  | nf_record p Ms => apps_exp (a_record p) (List.map nf_to_exp Ms)
  | nf_tuple p Ms fs Ns => a_tuple (apps_exp (a_record p) (List.map nf_to_exp Ms)) (List.combine fs (List.map nf_to_exp Ns))
  end
with ne_to_exp (M : ne) : exp :=
  match M with
  | ne_exfalso A M => a_exfalso (nf_to_exp A) (ne_to_exp M)
  | ne_elim p Us m Bks M =>
      a_elim (Some p) (List.map nf_to_exp Us) m
        (List.map (fun b => eb_mk (block_arity b) None (nf_to_exp (block_motive b))
                              (List.map (fun br => (branch_constructor br, branch_arity br, nf_to_exp (branch_body br)))
                                 (block_branches b))) Bks)
        (ne_to_exp M)
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_var x => a_var x
  | ne_glob p => qname_term p
  | ne_proj f M => a_proj f (ne_to_exp M)
  end.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

(** An atom of a canonical level as a term spells it: its offset, and the
    neutral level as a term. *)
Definition atom_exp (a : level_atom) : (nat * exp)%type := (atom_offset a, ne_to_exp (atom_level a)).

(** A branch of a stuck eliminator as a term's branch. *)
Definition branch_exp (br : normal_branch) : (string * nat * exp)%type :=
  (branch_constructor br, branch_arity br, nf_to_exp (branch_body br)).

(** A block of a stuck eliminator as a term's block: it carries no
    annotation. *)
Definition block_exp (b : normal_block) : eblock :=
  eb_mk (block_arity b) None (nf_to_exp (block_motive b)) (List.map branch_exp (block_branches b)).

(** The clauses of [nf_to_exp] at the levels and at a stuck eliminator,
    through the definitions above. *)
Lemma nf_to_exp_univ : forall c xs, nf_to_exp (nf_univ c xs) = a_univ (lvl_exp_of c (List.map atom_exp xs)).
Proof. reflexivity. Qed.

Lemma nf_to_exp_lvl : forall c xs, nf_to_exp (nf_lvl c xs) = lvl_exp_of c (List.map atom_exp xs).
Proof. reflexivity. Qed.

Lemma ne_to_exp_elim : forall p Us m Bks M,
    ne_to_exp (ne_elim p Us m Bks M) = a_elim (Some p) (List.map nf_to_exp Us) m (List.map block_exp Bks) (ne_to_exp M).
Proof. reflexivity. Qed.

(** * Canonical Levels

    A canonical level is its constant and its atoms.  The operations on
    canonical levels, and their order, are [Core.Syntactic.Levels.Levels]; the type
    is here because the universe normal forms below are indexed by it. *)
Definition lvl : Set := (o2 * list level_atom)%type.

Definition nf_lvl_of (l : lvl) : nf := nf_lvl (fst l) (snd l).

Definition nf_univ_of (l : lvl) : nf := nf_univ (fst l) (snd l).

Lemma nf_lvl_of_inj : forall l l', nf_lvl_of l = nf_lvl_of l' -> l = l'.
Proof.
  intros [c xs] [d ys] H; unfold nf_lvl_of in H; cbn in H.
  inversion H; reflexivity.
Qed.

Lemma nf_univ_of_cong : forall l l', nf_lvl_of l = nf_lvl_of l' -> nf_univ_of l = nf_univ_of l'.
Proof. intros ? ? H; apply nf_lvl_of_inj in H as ->; reflexivity. Qed.

(** * Universe Normal Forms

    The universe a type is inferred at, as the algorithmic layer sees it: a
    small universe at a canonical level, or a large one.  It is not the
    semantic index [uidx]: a small universe's semantic index is the realiser
    of its level, an ordinal below ω², while the checker compares the canonical
    levels themselves (see [Core.Syntactic.Levels.Levels]: [unf_le], [unf_max]). *)
Inductive unf : Set :=
(** A small universe at a canonical level *)
| uns : lvl -> unf
(** The large universe [Typeω²+n] *)
| unl : nat -> unf.

Coercion unl : nat >-> unf.

(** The universe normal form itself, and the term it embeds to. *)
Definition univ_nf (u : unf) : nf :=
  match u with uns L => nf_univ_of L | unl n => nf_typ n end.

Definition unf_tm (u : unf) : exp :=
  match u with
  | uns L => a_univ (lvl_exp_of (fst L) (List.map atom_exp (snd L)))
  | unl n => a_typ n
  end.

Lemma nf_to_exp_univ_nf : forall u, nf_to_exp (univ_nf u) = unf_tm u.
Proof. intros [[] |]; reflexivity. Qed.

(** That a normal form is a universe.  This is the side condition of every
    algorithmic rule that asks for a type.  It is a relation and not an
    equation [f W = Some u] of a deciding function [f]: the left-hand side
    of that equation is a [match] stuck on [W], and
    [progressive_inversion] does not terminate on such a hypothesis — it
    inverts it to an equation of the same shape, for ever. *)
Variant is_univ_nf : nf -> unf -> Prop :=
| is_univ_nf_typ : forall i, is_univ_nf (nf_typ i) (unl i)
| is_univ_nf_univ : forall c xs, is_univ_nf (nf_univ c xs) (uns (c, xs)).

Lemma is_univ_nf_univ_nf : forall u, is_univ_nf (univ_nf u) u.
Proof. intros [[] |]; constructor. Qed.

Lemma is_univ_nf_eq : forall W u, is_univ_nf W u -> W = univ_nf u.
Proof. intros ? ? H; destruct H; reflexivity. Qed.

Lemma is_univ_nf_functional : forall W u v, is_univ_nf W u -> is_univ_nf W v -> u = v.
Proof. intros ? ? ? H H'; destruct H; inversion H'; reflexivity. Qed.

(** A normal form with no global at the head of a neutral. *)
Fixpoint nf_clean (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_True | nf_true | nf_False => True
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_clean (atom_level a)) xs
  | nf_pi A B | nf_fn A B => nf_clean A /\ nf_clean B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => all_list nf_clean Ms
  | nf_neut M => ne_clean M
  | nf_record _ Ms => all_list nf_clean Ms
  | nf_tuple _ Ms _ Ns => all_list nf_clean Ms /\ all_list nf_clean Ns
  end
with ne_clean (M : ne) : Prop :=
  match M with
  | ne_exfalso A M => nf_clean A /\ ne_clean M
  | ne_elim _ Us _ Bks M =>
      all_list nf_clean Us /\
      all_list (fun b => nf_clean (block_motive b) /\ all_list (fun br => nf_clean (branch_body br)) (block_branches b)) Bks /\
      ne_clean M
  | ne_app M N => ne_clean M /\ nf_clean N
  | ne_var _ => True
  | ne_glob _ => False
  | ne_proj _ M => ne_clean M
  end.

(** Decidable equality of the records of normal forms, given that of what
    they hold. *)
Section RecordDec.
  Context {E : Set} (de : forall x y : E, {x = y} + {x <> y}).

  Definition level_atom_eq_dec_g (a a' : level_atom_g E) : {a = a'} + {a <> a'}.
  Proof.
    destruct a as [k s u], a' as [k' s' u'].
    destruct (PeanoNat.Nat.eq_dec k k') as [<- |]; [| right; congruence ].
    destruct (PeanoNat.Nat.eq_dec s s') as [<- |]; [| right; congruence ].
    destruct (de u u') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition normal_branch_eq_dec_g (b b' : normal_branch_g E) : {b = b'} + {b <> b'}.
  Proof.
    destruct b as [c n B], b' as [c' n' B'].
    destruct (String.string_dec c c') as [<- |]; [| right; congruence ].
    destruct (PeanoNat.Nat.eq_dec n n') as [<- |]; [| right; congruence ].
    destruct (de B B') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  Definition normal_block_eq_dec_g (b b' : normal_block_g E) : {b = b'} + {b <> b'}.
  Proof.
    destruct b as [nm A Bs], b' as [nm' A' Bs'].
    destruct (PeanoNat.Nat.eq_dec nm nm') as [<- |]; [| right; congruence ].
    destruct (de A A') as [<- |]; [| right; congruence ].
    destruct (List.list_eq_dec normal_branch_eq_dec_g Bs Bs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.
End RecordDec.

(** Equality of normal forms and neutrals is decidable. *)
Fixpoint nf_eq_dec (M M' : nf) {struct M} : {M = M'} + {M <> M'}
with ne_eq_dec (M M' : ne) {struct M} : {M = M'} + {M <> M'}.
Proof.
  (** Names are compared by [string_dec], before [decide equality] could
      take a string apart character by character. *)
  all: decide equality;
    first [ apply PeanoNat.Nat.eq_dec | apply String.string_dec | apply qname_eq_dec | apply o2_eq_dec
          | apply (List.list_eq_dec String.string_dec) | apply (List.list_eq_dec nf_eq_dec)
          | apply (List.list_eq_dec (level_atom_eq_dec_g ne_eq_dec))
          | apply (List.list_eq_dec (normal_block_eq_dec_g nf_eq_dec)) | idtac ].
Defined.

(** ** Notations *)
Module Nf_Notations.
  Notation "'⊤ⁿ'" := nf_True : mctt_scope.
  Notation "'⋆ⁿ'" := nf_true : mctt_scope.
  Notation "'⊥ⁿ'" := nf_False : mctt_scope.
  Notation "'Typeωⁿ' @ n" := (nf_typ n) (at level 1, n at level 0, format "'Typeωⁿ' @ n") : mctt_scope.
  Notation "'univⁿ' c xs" := (nf_univ c xs) (at level 1, c at level 0, xs at level 0, format "'univⁿ'  c  xs") : mctt_scope.
  Notation "'Typeⁿ' @ n" := (nf_univ (ofin n) nil) (at level 1, n at level 0, format "'Typeⁿ' @ n") : mctt_scope.
  Notation "'Levelⁿ' @ n" := (nf_level n) (at level 1, n at level 0, format "'Levelⁿ' @ n") : mctt_scope.
  Notation "'Levelⁿ'" := (nf_level 0) : mctt_scope.
  Notation "'lvⁿ' c xs" := (nf_lvl c xs) (at level 1, c at level 0, xs at level 0, format "'lvⁿ'  c  xs") : mctt_scope.
  Notation "'λⁿ' A M" := (nf_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Πⁿ' A B" := (nf_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'⇑ⁿ' M" := (nf_neut M) (at level 2, M at level 1, format "'⇑ⁿ'  M") : mctt_scope.
  Notation "'#ⁿ' n" := (ne_var n) (at level 1, n at level 0, format "'#ⁿ' n") : mctt_scope.
  Notation "M '$ⁿ' N" := (ne_app M N) (at level 10, left associativity, format "M  $ⁿ  N") : mctt_scope.
  Notation "'efqⁿ' M 'return' A" := (ne_exfalso A M) (at level 2, M at level 60, A at level 60) : mctt_scope.
End Nf_Notations.

(** * Weakenings and Substitutions *)

(** ** Weakenings

    Weakenings are meta-level functions on de Bruijn indices.  They form the
    first of the two tiers of the substitution machinery: lifting a
    substitution under a binder ([sb_q] below) has to weaken the results of
    that substitution by one, so weakening application must already be
    available before substitution application can be defined by structural
    recursion on expressions.
 *)

Definition wk : Set := nat -> nat.

Definition wk_id : wk := fun x => x.
Arguments wk_id _ /.

(** The shift [⇑], which increments every index by one. *)
Definition wk_shift : wk := fun x => S x.
Arguments wk_shift _ /.

(** [wk_q φ] extends [φ] under one binder: it fixes index [0] and shifts the
    image of every other index by one. *)
Definition wk_q (φ : wk) : wk :=
  fun x =>
    match x with
    | 0 => 0
    | S y => S (φ y)
    end.
Arguments wk_q _ _ /.

(** Composition of weakenings is diagrammatic: [wk_compose φ ψ] applies [φ]
    first and then [ψ].  This is the orientation of the paper, and the one for
    which [M[φ]ʷ[ψ]ʷ = M[φ ⊙ ψ]ʷ] holds without a flip. *)
Definition wk_compose (φ ψ : wk) : wk := fun x => ψ (φ x).
Arguments wk_compose _ _ _ /.

(** [wk_qn n φ] is the paper's [q^n(φ)]: [φ] lifted under [n] binders. *)
Fixpoint wk_qn (n : nat) (φ : wk) : wk :=
  match n with
  | 0 => φ
  | S m => wk_q (wk_qn m φ)
  end.

(** [wk_shiftn n] is the paper's [⇑^n], the [n]-fold shift. *)
Definition wk_shiftn (n : nat) : wk := fun x => x + n.
Arguments wk_shiftn _ _ /.

(** Application of a weakening to an expression.  Whenever we pass under a
    binder, the weakening is lifted with [wk_q]; the successor branch of the
    eliminator binds two variables, hence two lifts. *)
Fixpoint exp_wk (M : exp) (φ : wk) : exp :=
  match M with
  | a_typ i => a_typ i
  | a_univ t => a_univ (exp_wk t φ)
  | a_level n => a_level n
  | a_llit n => a_llit n
  | a_succl M => a_succl (exp_wk M φ)
  | a_maxl M N => a_maxl (exp_wk M φ) (exp_wk N φ)
  | a_ntok => a_ntok
  | a_True => a_True
  | a_true => a_true
  | a_False => a_False
  | a_exfalso A M => a_exfalso (exp_wk A (wk_q φ)) (exp_wk M φ)
  | a_ind p k => a_ind p k
  | a_con p k c => a_con p k c
  | a_nlit n => a_nlit n
  | a_elim oq Us m Bks M =>
      a_elim oq (List.map (fun U => exp_wk U φ) Us) m
        (List.map (fun b =>
           match b with
           | eb_mk nm oZ A Bs =>
               eb_mk nm (option_map (fun Z => exp_wk Z (wk_qn (nm - 1) φ)) oZ) (exp_wk A (wk_qn nm φ))
                 (List.map (fun br => (fst br, exp_wk (snd br) (wk_qn (snd (fst br)) φ))) Bs)
           end) Bks)
        (exp_wk M φ)
  | a_pi A B => a_pi (exp_wk A φ) (exp_wk B (wk_q φ))
  | a_fn A M => a_fn (exp_wk A φ) (exp_wk M (wk_q φ))
  | a_app M N => a_app (exp_wk M φ) (exp_wk N φ)
  | a_var x => a_var (φ x)
  | a_let b B => a_let (bnd_wk b φ) (exp_wk B (wk_q φ))
  | a_mem H x => a_mem (modexp_wk H φ) x
  | a_record p => a_record p
  | a_tuple T fs => a_tuple (exp_wk T φ) (List.map (fun f => (fst f, exp_wk (snd f) φ)) fs)
  | a_proj f M => a_proj f (exp_wk M φ)
  end
with modexp_wk (H : modexp) (φ : wk) : modexp :=
  match H with
  | me_unit fp => me_unit fp
  | me_var k => me_var (φ k)
  | me_mem H y => me_mem (modexp_wk H φ) y
  | me_app H N => me_app (modexp_wk H φ) (exp_wk N φ)
  | me_lit U => me_lit (gunit_wk U φ)
  end
with bnd_wk (b : bnd) (φ : wk) : bnd :=
  match b with
  | b_def oA M => b_def (match oA with Some A => Some (exp_wk A φ) | None => None end) (exp_wk M φ)
  | b_mod U => b_mod (gunit_wk U φ)
  end
(** The entry of a telescope at position [i] from the outermost is under [i]
    binders, and the definition under all of them. *)
with gunit_wk (U : gunit) (φ : wk) : gunit :=
  match U with
  | gu_mk Δ D =>
      gu_mk ((fix tele_wk (Δ : list centry) : list centry :=
                match Δ with
                | nil => nil
                | cons e Δ' => cons (centry_wk e (wk_qn (List.length Δ') φ)) (tele_wk Δ')
                end) Δ)
            (moddef_wk D (wk_qn (List.length Δ) φ))
  end
with moddef_wk (D : moddef) (φ : wk) : moddef :=
  match D with
  | md_body sm Φ => md_body sm (gmod_wk Φ φ)
  | md_alias E => md_alias (modexp_wk E φ)
  end
with gmod_wk (Φ : gmod) (φ : wk) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gmod_wk Φ φ) x (gentry_wk E (wk_qn (gm_binders Φ) φ))
  | gm_open Φ H its => gm_open (gmod_wk Φ φ) (modexp_wk H (wk_qn (gm_binders Φ) φ)) its
  end
with gentry_wk (E : gentry) (φ : wk) : gentry :=
  match E with
  | ge_def b pv A B => ge_def b pv (exp_wk A φ) (match B with Some M => Some (exp_wk M φ) | None => None end)
  | ge_mod pv U => ge_mod pv (gunit_wk U φ)
  | ge_ind pv p k D Φ => ge_ind pv p k D (gmod_wk Φ (wk_qn (ind_nu D) φ))
  | ge_def_mod pv A M U => ge_def_mod pv (exp_wk A φ) (exp_wk M φ) (gunit_wk U φ)
  | ge_record pv p R Φ => ge_record pv p R (gmod_wk Φ (wk_qn (S (List.length (record_params R))) φ))
  end
with centry_wk (e : centry) (φ : wk) : centry :=
  match e with
  | ce_ass A => ce_ass (exp_wk A φ)
  | ce_def A M => ce_def (exp_wk A φ) (exp_wk M φ)
  | ce_mod U => ce_mod (gunit_wk U φ)
  | ce_dm A M U => ce_dm (exp_wk A φ) (exp_wk M φ) (gunit_wk U φ)
  end.

(** A telescope under [φ], each entry under the binders of the entries outside
    it. *)
Fixpoint tele_wk (Δ : ctx) (φ : wk) : ctx :=
  match Δ with
  | nil => nil
  | cons e Δ' => cons (centry_wk e (wk_qn (List.length Δ') φ)) (tele_wk Δ' φ)
  end.

(** ** Substitutions

    A substitution maps each de Bruijn index to an entry, [sentry]: a
    variable, which is a variable of either sort, a term for a term variable,
    or a module expression for a module slot.  Like weakenings, substitutions
    are not part of the object syntax: applying one is a meta-level recursion
    on the expression.

    An entry of the wrong sort reads as a closed default, [a_true] or the
    module [me_unit nil], which every operation fixes.  The
    defaults are the semantic projections of an entry of the other sort, so
    evaluation commutes with every substitution. *)
Inductive sentry : Set :=
(** A variable of either sort *)
| se_var : nat -> sentry
(** A term, for a term variable *)
| se_exp : exp -> sentry
(** A module expression, for a module slot *)
| se_mod : modexp -> sentry
(** [se_dm N H]: a term and a module expression, for a definition with a
    module part ([ce_dm]); each sort reads its own component *)
| se_dm : exp -> modexp -> sentry.

Definition sub : Set := nat -> sentry.

Definition exp_junk : exp := a_true.
Definition modexp_junk : modexp := me_unit nil.

(** The term an entry gives a term variable. *)
Definition sentry_exp (e : sentry) : exp :=
  match e with
  | se_var x => a_var x
  | se_exp M => M
  | se_mod _ => exp_junk
  | se_dm N _ => N
  end.

(** The module expression an entry gives a module variable. *)
Definition sentry_modexp (e : sentry) : modexp :=
  match e with
  | se_var x => me_var x
  | se_exp _ => modexp_junk
  | se_mod H => H
  | se_dm _ H => H
  end.

(** An entry under a weakening, componentwise. *)
Definition sentry_wk (e : sentry) (φ : wk) : sentry :=
  match e with
  | se_var x => se_var (φ x)
  | se_exp M => se_exp (exp_wk M φ)
  | se_mod H => se_mod (modexp_wk H φ)
  | se_dm N H => se_dm (exp_wk N φ) (modexp_wk H φ)
  end.

Definition sb_id : sub := fun x => se_var x.
Arguments sb_id _ /.

(** Extension (cons).  [sb_extend σ e] sends index [0] to [e] and index
    [S y] to [σ y]; the paper writes it [σ ▹ M/x₀]. *)
Definition sb_extend (σ : sub) (e : sentry) : sub :=
  fun x =>
    match x with
    | 0 => e
    | S y => σ y
    end.
Arguments sb_extend _ _ _ /.

(** Postcomposition of a substitution with a weakening, pointwise. *)
Definition sb_wk (σ : sub) (φ : wk) : sub := fun x => sentry_wk (σ x) φ.
Arguments sb_wk _ _ _ /.

(** The embedding [ι] of weakenings into substitutions. *)
Definition sb_of_wk (φ : wk) : sub := fun x => se_var (φ x).
Arguments sb_of_wk _ _ /.

(** [⇑] regarded as a substitution. *)
Definition sb_shift : sub := sb_of_wk wk_shift.
Arguments sb_shift _ /.

(** Lifting a substitution under a binder: [q(σ) := σ[⇑], x₀/x₀].

    Unlike the other operations, [sb_q] is never unfolded by
    [simpl]: keeping it folded is what makes goals mentioning [q σ] readable,
    and it is what lets [simpl] normalise the body of [exp_sub] without
    exposing the encoding of lifting.  Use [sb_q_zero] and [sb_q_succ] to
    compute with it. *)
Definition sb_q (σ : sub) : sub := sb_extend (sb_wk σ wk_shift) (se_var 0).
Arguments sb_q : simpl never.

(** [sb_qn n σ] is the paper's [q^n(σ)]. *)
Fixpoint sb_qn (n : nat) (σ : sub) : sub :=
  match n with
  | 0 => σ
  | S m => sb_q (sb_qn m σ)
  end.

(** Application of a substitution to an expression. *)
Fixpoint exp_sub (M : exp) (σ : sub) : exp :=
  match M with
  | a_typ i => a_typ i
  | a_univ t => a_univ (exp_sub t σ)
  | a_level n => a_level n
  | a_llit n => a_llit n
  | a_succl M => a_succl (exp_sub M σ)
  | a_maxl M N => a_maxl (exp_sub M σ) (exp_sub N σ)
  | a_ntok => a_ntok
  | a_True => a_True
  | a_true => a_true
  | a_False => a_False
  | a_exfalso A M => a_exfalso (exp_sub A (sb_q σ)) (exp_sub M σ)
  | a_ind p k => a_ind p k
  | a_con p k c => a_con p k c
  | a_nlit n => a_nlit n
  | a_elim oq Us m Bks M =>
      a_elim oq (List.map (fun U => exp_sub U σ) Us) m
        (List.map (fun b =>
           match b with
           | eb_mk nm oZ A Bs =>
               eb_mk nm (option_map (fun Z => exp_sub Z (sb_qn (nm - 1) σ)) oZ) (exp_sub A (sb_qn nm σ))
                 (List.map (fun br => (fst br, exp_sub (snd br) (sb_qn (snd (fst br)) σ))) Bs)
           end) Bks)
        (exp_sub M σ)
  | a_pi A B => a_pi (exp_sub A σ) (exp_sub B (sb_q σ))
  | a_fn A M => a_fn (exp_sub A σ) (exp_sub M (sb_q σ))
  | a_app M N => a_app (exp_sub M σ) (exp_sub N σ)
  | a_var x => sentry_exp (σ x)
  | a_let b B => a_let (bnd_sub b σ) (exp_sub B (sb_q σ))
  | a_mem H x => a_mem (modexp_sub H σ) x
  | a_record p => a_record p
  | a_tuple T fs => a_tuple (exp_sub T σ) (List.map (fun f => (fst f, exp_sub (snd f) σ)) fs)
  | a_proj f M => a_proj f (exp_sub M σ)
  end
with modexp_sub (H : modexp) (σ : sub) : modexp :=
  match H with
  | me_unit fp => me_unit fp
  | me_var k => sentry_modexp (σ k)
  | me_mem H y => me_mem (modexp_sub H σ) y
  | me_app H N => me_app (modexp_sub H σ) (exp_sub N σ)
  | me_lit U => me_lit (gunit_sub U σ)
  end
with bnd_sub (b : bnd) (σ : sub) : bnd :=
  match b with
  | b_def oA M => b_def (match oA with Some A => Some (exp_sub A σ) | None => None end) (exp_sub M σ)
  | b_mod U => b_mod (gunit_sub U σ)
  end
with gunit_sub (U : gunit) (σ : sub) : gunit :=
  match U with
  | gu_mk Δ D =>
      gu_mk ((fix tele_sub (Δ : list centry) : list centry :=
                match Δ with
                | nil => nil
                | cons e Δ' => cons (centry_sub e (sb_qn (List.length Δ') σ)) (tele_sub Δ')
                end) Δ)
            (moddef_sub D (sb_qn (List.length Δ) σ))
  end
with moddef_sub (D : moddef) (σ : sub) : moddef :=
  match D with
  | md_body sm Φ => md_body sm (gmod_sub Φ σ)
  | md_alias E => md_alias (modexp_sub E σ)
  end
with gmod_sub (Φ : gmod) (σ : sub) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gmod_sub Φ σ) x (gentry_sub E (sb_qn (gm_binders Φ) σ))
  | gm_open Φ H its => gm_open (gmod_sub Φ σ) (modexp_sub H (sb_qn (gm_binders Φ) σ)) its
  end
with gentry_sub (E : gentry) (σ : sub) : gentry :=
  match E with
  | ge_def b pv A B => ge_def b pv (exp_sub A σ) (match B with Some M => Some (exp_sub M σ) | None => None end)
  | ge_mod pv U => ge_mod pv (gunit_sub U σ)
  | ge_ind pv p k D Φ => ge_ind pv p k D (gmod_sub Φ (sb_qn (ind_nu D) σ))
  | ge_def_mod pv A M U => ge_def_mod pv (exp_sub A σ) (exp_sub M σ) (gunit_sub U σ)
  | ge_record pv p R Φ => ge_record pv p R (gmod_sub Φ (sb_qn (S (List.length (record_params R))) σ))
  end
with centry_sub (e : centry) (σ : sub) : centry :=
  match e with
  | ce_ass A => ce_ass (exp_sub A σ)
  | ce_def A M => ce_def (exp_sub A σ) (exp_sub M σ)
  | ce_mod U => ce_mod (gunit_sub U σ)
  | ce_dm A M U => ce_dm (exp_sub A σ) (exp_sub M σ) (gunit_sub U σ)
  end.

Fixpoint tele_sub (Δ : ctx) (σ : sub) : ctx :=
  match Δ with
  | nil => nil
  | cons e Δ' => cons (centry_sub e (sb_qn (List.length Δ') σ)) (tele_sub Δ' σ)
  end.

Definition sentry_sub (e : sentry) (τ : sub) : sentry :=
  match e with
  | se_var x => τ x
  | se_exp M => se_exp (exp_sub M τ)
  | se_mod H => se_mod (modexp_sub H τ)
  | se_dm N H => se_dm (exp_sub N τ) (modexp_sub H τ)
  end.

(** Composition of substitutions, again diagrammatic: [sb_compose σ τ]
    applies [σ] first and then [τ]. *)
Definition sb_compose (σ τ : sub) : sub := fun x => sentry_sub (σ x) τ.
Arguments sb_compose _ _ _ /.

(** ** Equality of Weakenings and Substitutions

    Weakenings and substitutions are functions, so the algebraic laws that the
    paper states as equalities of weakenings or of substitutions (for instance
    [q(id) = id]) are function equalities.  Rather than assume functional
    extensionality — this development is otherwise axiom-free — we use
    pointwise equality throughout, and lift it through the two application
    operations with the congruence lemmas [exp_wk_wk_eq] and [exp_sub_sb_eq]
    below.  The [Proper] instances registered for those lemmas make ordinary
    [rewrite] work with pointwise hypotheses.
 *)

Definition wk_eq : relation wk := pointwise_relation nat eq.
Definition sb_eq : relation sub := pointwise_relation nat eq.

#[export]
Instance wk_eq_Equivalence : Equivalence wk_eq := _.
#[export]
Instance sb_eq_Equivalence : Equivalence sb_eq := _.

(** ** Notations

    Weakening and substitution application are postfix, at level 1;
    [M[σ]] and [M[φ]ʷ] share the prefix [M [ _] and differ only in the
    closing token.  [σ ⨟ τ] is diagrammatic composition: [σ] first, then
    [τ]. *)
Module Sub_Notations.
  Notation "M [ σ ]" := (exp_sub M σ) (at level 1, left associativity, σ at level 60, format "M [ σ ]") : mctt_scope.
  Notation "M [ φ ]ʷ" := (exp_wk M φ) (at level 1, left associativity, φ at level 60, format "M [ φ ]ʷ") : mctt_scope.
  Notation "H [ σ ]ᵐ" := (modexp_sub H σ) (at level 1, left associativity, σ at level 60, format "H [ σ ]ᵐ") : mctt_scope.
  Notation "U [ σ ]ᵘ" := (gunit_sub U σ) (at level 1, left associativity, σ at level 60, format "U [ σ ]ᵘ") : mctt_scope.
  Notation "'Id'" := sb_id : mctt_scope.
  Notation "'Wk'" := sb_shift : mctt_scope.
  Notation "σ ⨟ τ" := (sb_compose σ τ) (at level 45, right associativity, format "σ ⨟ τ") : mctt_scope.
  Notation "σ ,, M" := (sb_extend σ (se_exp M)) (at level 50, left associativity, format "σ ,, M") : mctt_scope.
  Notation "σ ',,ₘ' H" := (sb_extend σ (se_mod H)) (at level 50, left associativity, format "σ  ,,ₘ  H") : mctt_scope.
  Notation "σ ',,ᵈ' N ‖ H" := (sb_extend σ (se_dm N H)) (at level 50, left associativity, format "σ  ,,ᵈ  N  ‖  H") : mctt_scope.
  Notation "'q' σ" := (sb_q σ) (at level 30, σ at level 2) : mctt_scope.
End Sub_Notations.

(** Weakenings have their own notation module, outside [Syntax_Notations]:
    after [Substitution.v] establishes that the embedding [ι] is faithful the
    development speaks almost exclusively of substitutions. *)
Module Wk_Notations.
  (** [↑] is the paper's [⇑] as a weakening.  The glyph differs because [⇑] is
      already the neutral-value embedding of [Domain_Notations], and because the
      development needs to keep the shift weakening apart from the shift
      substitution [Wk = ι ↑]. *)
  Notation "↑" := wk_shift : mctt_scope.
  Notation "φ ⊙ ψ" := (wk_compose φ ψ) (at level 40, left associativity) : mctt_scope.
  Notation "'ι' φ" := (sb_of_wk φ) (at level 30) : mctt_scope.
End Wk_Notations.

(** ** Telescopes

    A member of a parameterized module is checked in the telescope of
    parameters it lives under, and stored generalized over it by these two
    folds.  They are the [exp]-level counterparts of the
    elaborator's [tele_pi]/[tele_fn], which work on [Cst.obj] and so cannot
    appear in a judgment.

    A [ctx] is innermost-first, so the head of [Δ] is the parameter bound last
    and must become the innermost binder: the recursion wraps the head first
    and works outward.  Folding the other way reverses the telescope, and the
    result is still a well-formed [exp], so nothing catches it early.

    A local definition in a telescope is generalized as a [let], as a section
    does with [Let], and a module slot as a local module.  A definition with
    a module part is substituted in, its term for its term uses and the
    literal of its unit for its module uses, as a body's entry is filled in
    ([gm_fill]).  The elaborator only builds parameter telescopes of
    assumptions. *)
Fixpoint ctx_pi (Δ : ctx) (A : typ) : typ :=
  match Δ with
  | nil => A
  | cons (ce_ass B) Δ' => ctx_pi Δ' (a_pi B A)
  | cons (ce_def B N) Δ' => ctx_pi Δ' (a_let (b_def (Some B) N) A)
  | cons (ce_mod U) Δ' => ctx_pi Δ' (a_let (b_mod U) A)
  | cons (ce_dm _ N U) Δ' => ctx_pi Δ' (exp_sub A (sb_extend sb_id (se_dm N (me_lit U))))
  end.

(** The [λ]-counterpart of [ctx_pi]. *)
Fixpoint ctx_fn (Δ : ctx) (M : exp) : exp :=
  match Δ with
  | nil => M
  | cons (ce_ass B) Δ' => ctx_fn Δ' (a_fn B M)
  | cons (ce_def B N) Δ' => ctx_fn Δ' (a_let (b_def (Some B) N) M)
  | cons (ce_mod U) Δ' => ctx_fn Δ' (a_let (b_mod U) M)
  | cons (ce_dm _ N U) Δ' => ctx_fn Δ' (exp_sub M (sb_extend sb_id (se_dm N (me_lit U))))
  end.

(** * The Global Context

    Names have two levels, spelled differently in the surface language and
    represented differently here.  [X::Y::Z] names a unit; units are not
    declared inside one another, so the [::] level is flat.  [X.W] names an
    internal module of one unit; internal modules nest, so the [.] level is a
    module.

    The global context is the units filed so far, [Θ], and the stack [Ξ] of
    the modules open around the point being checked.

    A member is stored closed: [wf_gentry_def] generalizes its type and body
    over the parameters of every enclosing module, outermost first.  Nothing
    about a member depends on where it is read from, so resolving a path hands
    the stored entry back unchanged, and evaluation needs no syntactic
    operations. *)

(** ** Filed Units

    The units filed so far, newest first, keyed by absolute path; each is
    checked against the ones after it. *)
Definition gdeps : Set := list (path * gunit).

Fixpoint gds_lookup (Θ : gdeps) (fp : path) : option gunit :=
  match Θ with
  | nil => None
  | (fq, U) :: Θ' => if path_beq fp fq then Some U else gds_lookup Θ' fp
  end.

(** One [gdeps] is below another when everything filed in it is filed, the
    same, in the other: what filing more units, or merging, preserves. *)
Definition gds_sub (Θ Θ' : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> gds_lookup Θ' fp = Some U.

Notation "Θ ⊑ Θ'" := (gds_sub Θ Θ') (at level 70) : type_scope.

Lemma gds_sub_refl : forall Θ, gds_sub Θ Θ.
Proof. intros ? ? ? H; exact H. Qed.

Lemma gds_sub_trans : forall Θ1 Θ2 Θ3, gds_sub Θ1 Θ2 -> gds_sub Θ2 Θ3 -> gds_sub Θ1 Θ3.
Proof. intros * H12 H23 ? ? H; apply H23, H12, H. Qed.

Lemma gds_lookup_in : forall Θ fp U,
    gds_lookup Θ fp = Some U ->
    List.In (fp, U) Θ.
Proof.
  induction Θ as [| [fq V] Θ IH]; cbn; intros * Heq; [ discriminate |].
  destruct (path_beq fp fq) eqn:Hb; [| right; auto ].
  apply path_beq_true in Hb as ->; injection Heq as ->; left; reflexivity.
Qed.

(** Filing a unit whose path is fresh changes nothing below it. *)
Lemma gds_sub_cons : forall Θ fp U,
    gds_lookup Θ fp = None ->
    Θ ⊑ (fp, U) :: Θ.
Proof.
  intros * Hn fq V H; cbn.
  destruct (path_beq fq fp) eqn:Hb; [ apply path_beq_true in Hb; subst; congruence | exact H ].
Qed.

(** ** The Definition Stack

    The modules open around the point being checked, innermost first, each
    recorded with its own (absolute) module path.  Their parameters are the
    local context members are checked in, [gs_tele]: the innermost frame's
    parameters are bound last, so they come first.  A frame also records
    what it is the module of ([frame_kind]): a module, or a type former
    that is also a module, whose declaration is read off the frame while
    it is open, as it is filed only when the frame closes. *)

(** What an open frame is the module of. *)
Inductive frame_kind : Set :=
(** An ordinary module *)
| fk_module
(** The module of the declared member [k] of the group [D] at [pq] *)
| fk_ind (pq : qname) (k : nat) (D : ind_decl)
(** The module of the record type declared by [R], at the frame's own
    path *)
| fk_record (R : record_decl).

(** The own parameters [Δ] of a module of kind [K] that are checked one
    frame out, where the module is declared: all of them, but for a
    record's module, whose last parameter is a value of the record, typed
    only inside the record's own frame, where the record is found. *)
Definition frame_params (K : frame_kind) (Δ : ctx) : ctx :=
  match K with
  | fk_record _ => List.tl Δ
  | fk_module | fk_ind _ _ _ => Δ
  end.

Definition gstack : Set := list (qname * frame_kind * gunit).

Fixpoint gs_tele (Ξ : gstack) : ctx :=
  match Ξ with
  | nil => nil
  | (_, _, U) :: Ξ' => gu_params U ++ gs_tele Ξ'
  end.

(** ** A Fixed Global Context

    The semantic model and the two metatheorems about NbE are stated for one
    global context at a time.  Found by instance resolution, it keeps their
    judgments in the short forms of [Core.Semantic.Fixed]. *)
Class GCtx : Set := gc_mk
  { gc_deps : gdeps
  ; gc_stack : gstack }.

(** * Scope and Notations *)

#[global] Bind Scope mctt_scope with exp.
#[global] Bind Scope mctt_scope with modexp.
#[global] Bind Scope mctt_scope with gunit.
#[global] Bind Scope mctt_scope with sub.
#[global] Bind Scope mctt_scope with nf.
#[global] Bind Scope mctt_scope with ne.
Open Scope mctt_scope.

(** The substitution sending the innermost binders to the terms [Ms],
    outermost first, and the others as [σ] does. *)
Fixpoint sb_of_list (σ : sub) (Ms : list exp) : sub :=
  match Ms with
  | nil => σ
  | M :: Ms' => sb_of_list (sb_extend σ (se_exp M)) Ms'
  end.

(** The type of the type former of the member [M] applied to [Us], its
    outermost parameters: the [Π] over the others, at [Us]. *)
Definition ind_ty_at (D : ind_decl) (M : imember) (Us : list exp) : typ :=
  exp_sub (ctx_pi (List.firstn (im_np D M - List.length Us) (im_params D M)) (exp_wk (ind_sort D) (wk_shiftn (im_nn M))))
    (sb_of_list sb_id Us).

(** The notations of terms, contexts, normal forms and substitutions. *)
Module Syntax_Notations.
  Export Exp_Notations Ctx_Notations Nf_Notations Sub_Notations.
End Syntax_Notations.
