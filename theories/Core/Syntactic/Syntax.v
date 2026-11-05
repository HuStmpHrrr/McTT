From Stdlib Require Import Lia List Morphisms Relation_Definitions RelationClasses Setoid String Wf_nat.
From Stdlib Require Bool.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Levels Require Export Ordinals.

(** An item of an open: [(Some n, d, pv)] declares [d] as the member [n] of
    the opened module, [(None, d, pv)] declares [d] as the opened module
    itself; private when [pv].  The surface syntax and the core share it. *)
Definition import_item : Set := (option string * string * bool)%type.

(** * Concrete Syntax Tree *)
Module Cst.

(** ** Modifiers

    [private] hides a definition from importers, [abstract] makes its body
    opaque.  The two are orthogonal, hence a record rather than a variant. *)
Record modifiers : Set :=
  { modifiers_private : bool
  ; modifiers_abstract : bool }.

Definition public_modifiers : modifiers := {| modifiers_private := false; modifiers_abstract := false |}.
Definition private_modifiers : modifiers := {| modifiers_private := true; modifiers_abstract := false |}.
Definition abstract_modifiers : modifiers := {| modifiers_private := false; modifiers_abstract := true |}.
Definition private_abstract_modifiers : modifiers := {| modifiers_private := true; modifiers_abstract := true |}.

(** ** Definition Keywords

    [def] and its shorthands.  Each keyword implies some modifiers, and
    takes the others: [theorem] and [lemma] are [abstract def] and take
    [private]; [fact] and [remark] are [abstract private def] and take
    none; [let] and [given] are [private def] and take [abstract].  A
    modifier the keyword already implies is rejected. *)
Inductive definition_keyword : Set :=
| definition_keyword_def | definition_keyword_theorem | definition_keyword_lemma | definition_keyword_fact | definition_keyword_remark | definition_keyword_let | definition_keyword_given.

Definition definition_keyword_name (k : definition_keyword) : string :=
  match k with
  | definition_keyword_def => "def" | definition_keyword_theorem => "theorem" | definition_keyword_lemma => "lemma"
  | definition_keyword_fact => "fact" | definition_keyword_remark => "remark" | definition_keyword_let => "let" | definition_keyword_given => "given"
  end.

(** The modifiers of [m k], or why [k] rejects [m]. *)
Definition definition_keyword_mods (k : definition_keyword) (m : modifiers) : (modifiers + string)%type :=
  match k with
  | definition_keyword_def => inl m
  | definition_keyword_theorem | definition_keyword_lemma =>
      if modifiers_abstract m then inr (definition_keyword_name k ++ " is already abstract")%string
      else inl {| modifiers_private := modifiers_private m; modifiers_abstract := true |}
  | definition_keyword_fact | definition_keyword_remark =>
      if orb (modifiers_private m) (modifiers_abstract m) then inr (definition_keyword_name k ++ " takes no modifiers")%string
      else inl private_abstract_modifiers
  | definition_keyword_let | definition_keyword_given =>
      if modifiers_private m then inr (definition_keyword_name k ++ " is already private")%string
      else inl {| modifiers_private := true; modifiers_abstract := modifiers_abstract m |}
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

    [let_in] binds one declaration at a time; the parser folds the bindings of
    [let x : A := a; y : B := b in body end] into nested [let_in]s.

    A module declaration has one shape at the top level and in a [let]: its
    parameters, and its definition [mdef], a body [where cmds end] or an
    alias [:= E].  The body of a local module is the same list of commands as
    that of a global one.  The branches of an eliminator, the parameters
    and the fields are nested through lists of pairs, all of which have
    [All] schemes registered ([Core.Base]): the mutual principle [cst_ind]
    below is generated. *)
Inductive expression : Set :=
(** [Typeω@i], a large universe, the universe [ω²+i], written
    [Type@{ω^2}] for [i = 0] and [Type@{ω^2+i}]; [ω^2] is not a level. *)
| typ : nat -> expression
(** [Type@{M}], the small universe at the level [M] *)
| suniv : expression -> expression
(** [Level@n], the type of the levels below [ω·(n+1)]; [Level] is [Level@0] *)
| level : nat -> expression
(** A level literal [ω·a + b], written [<b>l] when [a] is [0] and also
    [<b>L] when [a] is [1] *)
| llit : o2 -> expression
(** [succl M] *)
| succl : expression -> expression
(** [maxl M N] *)
| maxl : expression -> expression -> expression
(** [Nat] or [ℕ]: the type bound by [builtin natural] *)
| nat : expression
(** A numeral, of the type bound by [builtin natural] *)
| num : nat -> expression
(** [True] *)
| true_ty : expression
(** [true] *)
| true_tm : expression
(** [False] *)
| false_ty : expression
(** [exfalso M return A]: the proof [M] of [False], eliminated into [A] *)
| exfalso : expression -> expression -> expression
(** [Prop], the universe of propositions *)
| prop : expression
(** [/\ (h : P) -> Q]: the conjunction of [P] and [Q], [Q] seeing [h] *)
| and_ty : string -> expression -> expression -> expression
(** [conj (m : P) q]: a proof of a conjunction, its first component [m]
    at [P], then its second [q] *)
| and_intro : expression -> expression -> expression -> expression
(** [left M]: the first component of a proof of a conjunction *)
| and_left : expression -> expression
(** [right M]: its second component *)
| and_right : expression -> expression
(** [forall (x : A) -> B] *)
| pi : string -> expression -> expression -> expression
(** [fun (x : A) -> M] *)
| fn : string -> expression -> expression -> expression
(** [M N]: a function or a module applied *)
| app : expression -> expression -> expression
(** A name: a local variable, a module, or a member in scope *)
| var : string -> expression
(** A [::] path, hence at least two segments after a [var]; a unit of one
    segment is written as a [var] *)
| glob : list string -> expression
(** [M.x]: a member of a module *)
| proj : expression -> string -> expression
(** [let d in M end], one declaration at a time *)
| let_in : decl -> expression -> expression
(** [elim M at xs (z : Z) -> A | c ys ⇒ B … with … end]: the eliminator
    of a group of inductive types, one block per member in member order,
    the one marked [at] ([true]) the scrutinee's.  A block's binders, the
    non-uniform parameters then the scrutinee, outermost first, each with
    its type if written; its motive under them; its branches, each binding
    the non-uniform parameters, the constructor's arguments and the
    induction hypotheses, in that order *)
| elim : expression -> list (bool * list (string * option expression) * expression * list (string * list string * expression)) -> expression
(** [record T where f := M ; … end]: a value of the record type [T], its
    fields in order, each its name and its value *)
| tuple : expression -> list (string * expression) -> expression

with decl : Set :=
(** [x : A := M], or [x := M] without the type.  A local definition is
    always transparent and has no modifiers. *)
| d_def : string -> option expression -> expression -> decl
(** [module X (ps) md] *)
| d_mod : string -> list (string * expression) -> mdef -> decl

with mdef : Set :=
(** [where cs end] *)
| md_where : list cmd -> mdef
(** [:= E] *)
| md_alias : expression -> mdef

(** A module declaration carries its name, its parameter telescope and its
    definition; a unit's own name is declared by [prog] below, not here.  A
    dotted declaration [module A.B] is parsed as nested ones ([c_mod_dotted]). *)
with cmd : Set :=
(** [private module x (ps) md], private when the flag is set *)
| c_mod : bool -> string -> list (string * expression) -> mdef -> cmd
(** [private abstract def x : A := M end], with its modifiers *)
| c_def : modifiers -> string -> expression -> expression -> cmd
(** [axiom x : A], a definition with no body; it takes no modifiers. *)
| c_axiom : string -> expression -> cmd
(** [import X::Y] loads the unit [X::Y], so that it may be named.  It
    declares nothing. *)
| c_import : list string -> cmd
(** [c_open fq ip args its] opens the module at member path [ip] of the
    unit [fq], applied to [args], and declares the items [its]; an empty
    [fq] names the module [ip] in scope.  It loads nothing.  So [open A.B
    use (x)] is [c_open nil ["A"; "B"] nil [(Some "x", "x", true)]], and
    [open X::Y Nat export (f as g)] is [c_open ["X"; "Y"] nil [nat] [(Some
    "f", "g", false)]].  [as W] is the item [(None, "W", true)] ([open_cmds]). *)
| c_open : list string -> list string -> list expression -> list import_item -> cmd
(** A command the parser rejects, with the reason, which elaboration
    reports: a definition keyword with a modifier it already implies
    ([def_cmd]). *)
| c_error : string -> cmd
(** [eval M] normalizes [M] and prints the result; [eval M : A] additionally
    checks [M] against [A] rather than inferring its type. *)
| c_eval : expression -> option expression -> cmd
(** [private inductive x (ps) : T where | c (args) … with y : U where …
    end]: the group's uniform parameters [ps], shared, and its members, in
    order: each its name, its type, which binds its non-uniform parameters
    in front of the sort, [forall (n : A) -> S], and its constructors with
    their arguments.  The members' names are in scope in every argument.
    The second flag says whether the group files its recursor module
    [Rec], as one declared by [mutual T where] does. *)
| c_ind : bool -> bool -> list (string * expression) -> list (string * expression * list (string * list (string * expression))) -> cmd
(** [private abstract mutual def (Δ) f (ys) (z : Z) : A := | c xs ⇒ B …
    with g … end], with its modifiers: the common parameters [Δ], and the
    functions, each its name, its parameters (the non-uniform ones, then
    the scrutinee, last), its result type and its clauses. *)
| c_mdef : modifiers -> list (string * expression) -> list (string * list (string * expression) * expression * list (string * list string * expression)) -> cmd
(** [builtin k := X]: binds the inductive type [X] as the builtin [k];
    [natural] is the one kind. *)
| c_builtin : string -> expression -> cmd
(** [private inductive x (ps) := X Ms]: an inductive alias, the inductive
    type [X] at the arguments [Ms], under the parameters [ps]. *)
| c_ind_alias : bool -> string -> list (string * expression) -> expression -> cmd
(** [private record x (ps) := X Ms]: a record alias, the record type [X]
    at the arguments [Ms], under the parameters [ps]. *)
| c_record_alias : bool -> string -> list (string * expression) -> expression -> cmd
(** [private record x (ps) : S where f : A ; … with cs end]: a record type,
    private when the flag is set: its parameters [ps], its sort [S], its
    fields in order, each its name and its type over the fields before it,
    and its with-area [cs], the commands of its module after the fields
    (none without [with]). *)
| c_record : bool -> string -> list (string * expression) -> expression -> list (string * expression) -> list cmd -> cmd.

(** The mutual induction principle of the family, generated: a list, a
    pair and an option carry [list_all], [prod_all] and [option_all] of the
    motives ([Core.Base]). *)
Scheme expression_mut_ind := Induction for expression Sort Prop
with decl_mut_ind := Induction for decl Sort Prop
with mdef_mut_ind := Induction for mdef Sort Prop
with cmd_mut_ind := Induction for cmd Sort Prop.
Combined Scheme cst_ind from expression_mut_ind, decl_mut_ind, mdef_mut_ind, cmd_mut_ind.

(** [module A₁.….Aₙ.B (ps) md] is [module A₁ where … module Aₙ where module
    B (ps) md end … end]: each [Aᵢ] has no parameters and the one member
    [Aᵢ₊₁].  The grammar gives the path reversed, [B] first.  Only [B], the
    module declared, carries the privacy [pv]; the [Aᵢ] are public. *)
Definition c_mod_dotted (pv : bool) (x : string) (rev_pre : list string) (ps : list (string * expression)) (md : mdef) : cmd :=
  List.fold_left (fun c y => c_mod false y nil (md_where (c :: nil))) rev_pre (c_mod pv x ps md).

(** [k x : A := M end] with the modifiers [m]: the definition, or the
    rejection of [m]. *)
Definition def_cmd (k : definition_keyword) (m : modifiers) (x : string) (A M : expression) : cmd :=
  match definition_keyword_mods k m with
  | inl m' => c_def m' x A M
  | inr e => c_error e
  end.

(** [mutual k (Δ) f … with g … end] with the modifiers [m], [k] a
    definition keyword: the mutual definition with the modifiers [k] gives
    it, as [def_cmd] gives a single definition, or the rejection of [m]. *)
Definition mdef_cmd (k : definition_keyword) (m : modifiers) (ps : list (string * expression))
    (fs : list (string * list (string * expression) * expression * list (string * list string * expression))) : cmd :=
  match definition_keyword_mods k m with
  | inl m' => c_mdef m' ps fs
  | inr e => c_error e
  end.

(** [axiom x : A] with the modifiers [m]: the axiom, or the rejection of
    [m]. *)
Definition axiom_cmd (m : modifiers) (x : string) (A : expression) : cmd :=
  if orb (modifiers_private m) (modifiers_abstract m) then c_error "axiom takes no modifiers" else c_axiom x A.

(** [mutual T (ps) where inductive … end end] with the modifiers [m]: the
    module [T], private with [m], holding the group and its recursor module
    [T.Rec], or the rejection of [abstract]. *)
Definition mutual_cmd (m : modifiers) (g : string) (ps : list (string * expression))
    (ms : list (string * expression * list (string * list (string * expression)))) : cmd :=
  if modifiers_abstract m then c_error "a group of inductive types takes no abstract"
  else c_mod (modifiers_private m) g nil (md_where (c_ind false true ps ms :: nil)).

(** [open E as W its] is [open E as W] then [open W its]: the items refer
    to the alias, and an open declares either the module or its members. *)
Definition open_cmds (fq ip : list string) (args : list expression) (oW : option string) (its : list import_item)
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
Definition import_cmds (fq ip : list string) (args : list expression) (oW : option string) (its : list import_item)
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
Definition prog : Set := (list cmd * (list string * list (string * expression) * list cmd))%type.

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
    [ca_arg r A] has its type [A] over the non-recursive arguments before it
    and the member's parameters, and a recursive argument [ca_rec t] has a
    shape [t] ([ptyp_g]), whose components are over the non-recursive
    arguments before it and the member's parameters.  Nothing may mention a
    recursive argument, so it occupies no binder of the arguments after
    it. *)

(** The three kinds of abstraction: what a binder ranges over, and of
    what sort a type is.  A type of a universe ([Typeω@i] or [Type⟨l⟩]),
    whose elements are compared; a proposition ([Prop]), whose elements
    are all equal and are kept, not evaluated; a type of levels
    ([LevelSort]), whose elements are levels.  A binder carries the kind
    of its domain ([ce_ass], [a_pi]), a [Π] also its codomain's, and a
    value's kind is read from its head ([domain_kind]).  The typed fill
    writes every kind, from the sort the typed term infers to. *)
Inductive abs_kind : Set :=
(** Over the elements of a type of a universe *)
| ak_relevant
(** Over the proofs of a proposition *)
| ak_propositional
(** Over the elements of a type of levels *)
| ak_level.

Definition abs_kind_eq_dec : forall (κ κ' : abs_kind), {κ = κ'} + {κ <> κ'}.
Proof. decide equality. Defined.

(** The kinds whose elements are evaluated rather than kept: every kind
    but the propositions'. *)
Inductive evaluated_kind : abs_kind -> Prop :=
(** A type of a universe *)
| evaluated_kind_relevant : evaluated_kind ak_relevant
(** A type of levels *)
| evaluated_kind_level : evaluated_kind ak_level.

(** A kind is evaluated, or the propositions'. *)
Lemma evaluated_kind_or_propositional : forall κ, evaluated_kind κ \/ κ = ak_propositional.
Proof. intros []; [ left; constructor | right; reflexivity | left; constructor ]. Qed.

(** The propositions' kind is not evaluated. *)
Lemma evaluated_kind_not_propositional : forall κ, evaluated_kind κ -> κ <> ak_propositional.
Proof. intros κ H; destruct H; discriminate. Qed.

(** The shape of a recursive argument: the member [k] of the group at its
    non-uniform parameters [Ps] ([pt_self k Ps]), or a function from [A] to
    a shape ([pt_pi A t]).  A domain is in the group's sort, a universe
    ([decl_typed_doms]), so it is of the kind [ak_relevant]. *)
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

(** The arguments of a constructor, as the core command classifies them. *)
Inductive carg_g (E : Set) : Set :=
(** A non-recursive argument [ca_arg κ A], of the type [A], whose kind
    is [κ]: [ak_relevant] for a type in the group's sort,
    [ak_propositional] for a proposition (an argument with no induction
    hypothesis, kept as a proof), never [ak_level] ([carg_kind]).  The
    core command computes [κ] from [A]'s inferred type; the
    declaration's well-formedness checks it. *)
| ca_arg : abs_kind -> E -> carg_g E
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
  ; record_fields : list (string * E)
  (** The kind of each field, parallel to [record_fields] (the [k]-th is
      the [k]-th field's): [ak_propositional] for a field whose type is a
      proposition, [ak_relevant] for one in the record's sort, never
      [ak_level] ([field_kind]).  The core command computes it; the
      declaration's well-formedness checks it. *)
  ; record_field_kinds : list abs_kind }.
Arguments mk_record_decl {E C}.
Arguments record_params {E C}.
Arguments record_sort {E C}.
Arguments record_fields {E C}.
Arguments record_field_kinds {E C}.

(** A block of an eliminator ([a_elim]), one per member of the group, in
    the group's order: [eb_mk nm Z A Bs].  The motive [A] binds [nm]
    variables, the member's non-uniform parameters and the scrutinee; [Z]
    is the type of the scrutinee, over the non-uniform parameters (the
    typed fill writes it where the user does not); each branch [(c, n, B)]
    is the case of the constructor [c], in order, and binds [n] variables:
    the non-uniform parameters, the arguments, and one recursive result per
    recursive argument. *)
Inductive eblock_g (E : Set) : Set :=
(** The block of [nm] motive binders, the scrutinee type [Z], the motive
    [A] and the branches [Bs]. *)
| eb_mk : nat -> E -> E -> list (string * nat * E) -> eblock_g E.
Arguments eb_mk {E}.
(** [exp] nests through blocks: with this scheme registered, its generated
    induction principle carries the hypotheses for a block's parts. *)
Scheme All for eblock_g.

(** The number of variables a block's motive binds. *)
Definition eb_binder_count {E : Set} (b : eblock_g E) : nat := match b with eb_mk nm _ _ _ => nm end.
(** A block's scrutinee type. *)
Definition eb_scrutinee_type {E : Set} (b : eblock_g E) : E := match b with eb_mk _ Z _ _ => Z end.
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
Inductive storage_mark : Set := sm_open | sm_closed.

Definition storage_mark_eq_dec : forall (s s' : storage_mark), {s = s'} + {s <> s'}.
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
(** The sort of the types of levels, [LevelSort], a type of [Typeω@0].  Its
    types are the types of levels and the [Π]s between them; no universe
    contains it or them, so a level is built only from levels. *)
| a_level_sort : exp
(** A level literal: [a_llit (a, b)] is the ordinal [ω·a + b].  The finite
    level [n], [a_llit (0, n)], is written [<n>l] in the surface syntax. *)
| a_llit : o2 -> exp
(** The successor of a level *)
| a_succl : exp -> exp
(** The join of two levels *)
| a_maxl : exp -> exp -> exp
(** The universe of propositions [Prop], a type of [Type@0].  A proposition is
    a type, but no universe [Type@{L}] contains it: [Prop] sits beside the
    cumulative hierarchy. *)
| a_prop : exp
(** The true proposition [⊤] *)
| a_True : exp
(** The introduction of [⊤] *)
| a_tt : exp
(** The false proposition [⊥] *)
| a_False : exp
(** [a_absurd C M]: ex falso, the proof [M] of [⊥] eliminated into the
    type [C], of either sort *)
| a_absurd : exp -> exp -> exp
(** [a_and P Q]: the dependent conjunction of propositions [Σₚ P Q], a
    proposition; [Q] binds a proof of [P] *)
| a_and : exp -> exp -> exp
(** [a_conj P Q M N]: the proof of the conjunction [Σₚ P Q], [Q] binding a
    proof of [P], from a proof [M] of [P] and a proof [N] of [Q] at [M] *)
| a_conj : exp -> exp -> exp -> exp -> exp
(** The proof of the first component of a conjunction *)
| a_left : exp -> exp
(** The proof of the second component of a conjunction *)
| a_right : exp -> exp
(** The type former of the member [k] of the group [pq] of inductive types,
    to be applied to its parameters: [pq] names the group, the path of its
    first member's entry ([ge_ind]). *)
| a_ind : qname -> nat -> exp
(** The constructor [c] of the member [k] of the group [pq], to be applied
    to the parameters and the arguments. *)
| a_con : qname -> nat -> string -> exp
(** [a_elim κ pq Us m Bks M] eliminates [M], of the member [m] of the group
    [pq] of inductive types, by the blocks [Bks], one per member of the
    group in its order ([eblock_g]); the result is the motive of block [m].
    The motives are of the kind [κ]: types of a universe ([ak_relevant])
    or propositions ([ak_propositional]), never types of levels
    ([motive_kind]); an elimination into propositions is a proof, which
    evaluation does not reach.  The eliminator carries the
    group's uniform parameters [Us]: a stuck one is read at them.  The
    typed fill writes the group, the parameters and the sort, read off the
    scrutinee's type. *)
| a_elim : abs_kind -> qname -> list exp -> nat -> list (eblock_g exp) -> exp -> exp
(** [a_pi κd κc A B], [B] binding the argument: the abstraction over a
    domain [A] of the kind [κd] into a codomain of the kind [κc] — a type
    of functions at [ak_relevant], the impredicative universal
    quantification, a proposition, at [ak_propositional], a type of
    levels, out of a type of levels, at [ak_level] ([pi_kinds]) *)
| a_pi : abs_kind -> abs_kind -> exp -> exp -> exp
(** [a_fn A M], [M] binding the argument *)
| a_fn : exp -> exp -> exp
(** Application *)
| a_app : exp -> exp -> exp
(** Variable *)
| a_var : nat -> exp
(** Local binding: [a_let b B] binds [#0] in [B] to the definition or the
    module [b]. *)
| a_let : binding -> exp -> exp
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
with binding : Set :=
(** [b_def A M]: a definition [M] of the type [A].  Every local definition
    is annotated: evaluation keeps the type of each variable it binds, and
    the typed fill annotates a definition written without one. *)
| b_def : exp -> exp -> binding
(** [b_mod U]: a local module *)
| b_mod : gunit -> binding
with gunit : Set :=
(** [gu_mk Δ D]: the parameters, innermost first, and the definition under
    them *)
| gu_mk : list centry -> moddef -> gunit
with moddef : Set :=
(** A body, stored open (a local module: its entries mention the parameters
    and the entries before them) or closed (a filed module or an open frame:
    every entry is closed over the module's full telescope) *)
| md_body : storage_mark -> gmod -> moddef
(** An alias of a module expression *)
| md_alias : modexp -> moddef
with gmod : Set :=
(** The empty body *)
| gm_nil : gmod
(** A named entry after the body before it *)
| gm_ext : gmod -> string -> gentry -> gmod
(** [gm_open Φ H items Φg]: a local open, as written, with the entries
    its items generate, binding the indices [Φg] binds, one per item
    once filled ([gens_body]).  [Φg] is those
    generated private-or-public definitions, annotated with their types, a
    fragment (entries over [gm_nil]) read over the expansion of [Φ], the
    [k]-th under the [k] before it ([gens_body]).  The open phase of the
    command semantics fills it ([items_gen]); typing pins it to the
    generation ([body_xp]), and evaluation reads the body expanded
    ([gm_expand]). *)
| gm_open : gmod -> modexp -> list import_item -> gmod -> gmod
with gentry : Set :=
(** [ge_def b pv κ A B]: [b] says whether the definition is transparent,
    [pv] whether it is private, [κ] the kind of its type [A] (a proof at
    [ak_propositional], a level at [ak_level]), and [B] is [None] for an
    axiom.  A filed definition is closed; a definition of a local body is
    read in the body's context. *)
| ge_def : bool -> bool -> abs_kind -> exp -> option exp -> gentry
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
(** [ce_ass κ A]: an assumption of a type [A] of the kind [κ] *)
| ce_ass : abs_kind -> exp -> centry
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
    scrutinee type, its motive and its branches. *)
Fixpoint all_blocks {A : Set} (f : nat -> A -> A -> list (string * nat * A) -> Prop) (Bks : list (eblock_g A)) : Prop :=
  match Bks with
  | nil => True
  | eb_mk nm Z M Bs :: Bks' => f nm Z M Bs /\ all_blocks f Bks'
  end.

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

Lemma all_blocks_all_list : forall {A : Set} (f : nat -> A -> A -> list (string * nat * A) -> Prop) Bks,
    all_blocks f Bks <-> all_list (fun b => match b with eb_mk nm Z M Bs => f nm Z M Bs end) Bks.
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
  Variables (Pe : exp -> Prop) (Pm : modexp -> Prop) (Pb : binding -> Prop)
    (Pu : gunit -> Prop) (Pd : moddef -> Prop) (Pg : gmod -> Prop)
    (Pn : gentry -> Prop) (Pc : centry -> Prop).

  Hypotheses
    (case_typ : forall i, Pe (a_typ i))
    (case_univ : forall t, Pe t -> Pe (a_univ t))
    (case_level : forall n, Pe (a_level n))
    (case_level_sort : Pe a_level_sort)
    (case_llit : forall n, Pe (a_llit n))
    (case_succl : forall M, Pe M -> Pe (a_succl M))
    (case_maxl : forall M N, Pe M -> Pe N -> Pe (a_maxl M N))
    (case_prop : Pe a_prop)
    (case_True : Pe a_True)
    (case_tt : Pe a_tt)
    (case_False : Pe a_False)
    (case_absurd : forall A M, Pe A -> Pe M -> Pe (a_absurd A M))
    (case_and : forall P Q, Pe P -> Pe Q -> Pe (a_and P Q))
    (case_conj : forall P Q M N, Pe P -> Pe Q -> Pe M -> Pe N -> Pe (a_conj P Q M N))
    (case_left : forall M, Pe M -> Pe (a_left M))
    (case_right : forall M, Pe M -> Pe (a_right M))
    (case_ind : forall p k, Pe (a_ind p k))
    (case_con : forall p k c, Pe (a_con p k c))
    (case_elim : forall κ pq Us m Bks M,
        List.Forall Pe Us ->
        List.Forall (fun b => Pe (eb_scrutinee_type b) /\ Pe (eb_motive b) /\
                              List.Forall (fun br => Pe (snd br)) (eb_brs b)) Bks ->
        Pe M -> Pe (a_elim κ pq Us m Bks M))
    (case_pi : forall κd κc A B, Pe A -> Pe B -> Pe (a_pi κd κc A B))
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
    (case_b_def : forall A M, Pe A -> Pe M -> Pb (b_def A M))
    (case_b_mod : forall U, Pu U -> Pb (b_mod U))
    (case_gu_mk : forall Δ D, List.Forall Pc Δ -> Pd D -> Pu (gu_mk Δ D))
    (case_md_body : forall s Φ, Pg Φ -> Pd (md_body s Φ))
    (case_md_alias : forall E, Pm E -> Pd (md_alias E))
    (case_gm_nil : Pg gm_nil)
    (case_gm_ext : forall Φ x E, Pg Φ -> Pn E -> Pg (gm_ext Φ x E))
    (case_gm_open : forall Φ H its Φg, Pg Φ -> Pm H -> Pg Φg -> Pg (gm_open Φ H its Φg))
    (case_ge_def : forall b pv κ A B, Pe A -> (forall M, B = Some M -> Pe M) -> Pn (ge_def b pv κ A B))
    (case_ge_mod : forall pv U, Pu U -> Pn (ge_mod pv U))
    (case_ge_ind : forall pv p k D Φ, Pg Φ -> Pn (ge_ind pv p k D Φ))
    (case_ge_def_mod : forall pv A M U, Pe A -> Pe M -> Pu U -> Pn (ge_def_mod pv A M U))
    (case_ge_record : forall pv p R Φ, Pg Φ -> Pn (ge_record pv p R Φ))
    (case_ce_ass : forall κ A, Pe A -> Pc (ce_ass κ A))
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
    | a_level_sort => case_level_sort
    | a_llit n => case_llit n
    | a_succl M => case_succl M (exp_mut M)
    | a_maxl M N => case_maxl M N (exp_mut M) (exp_mut N)
    | a_prop => case_prop
    | a_True => case_True
    | a_tt => case_tt
    | a_False => case_False
    | a_absurd A M => case_absurd A M (exp_mut A) (exp_mut M)
    | a_and P Q => case_and P Q (exp_mut P) (exp_mut Q)
    | a_conj P Q M N => case_conj P Q M N (exp_mut P) (exp_mut Q) (exp_mut M) (exp_mut N)
    | a_left M => case_left M (exp_mut M)
    | a_right M => case_right M (exp_mut M)
    | a_ind p k => case_ind p k
    | a_con p k c => case_con p k c
    | a_elim κ pq Us0 m Bks M =>
        case_elim κ pq Us0 m Bks M
          ((fix us_mut (Us : list exp) : List.Forall Pe Us :=
              match Us with
              | nil => List.Forall_nil _
              | cons U Us' => List.Forall_cons U (exp_mut U) (us_mut Us')
              end) Us0)
          ((fix blocks_mut (Bks : list eblock) :
              List.Forall (fun b => Pe (eb_scrutinee_type b) /\ Pe (eb_motive b) /\
                                    List.Forall (fun br => Pe (snd br)) (eb_brs b)) Bks :=
              match Bks with
              | nil => List.Forall_nil _
              | cons (eb_mk nm Z A Bs) Bks' =>
                  List.Forall_cons (eb_mk nm Z A Bs)
                    (conj (exp_mut Z)
                       (conj (exp_mut A)
                          ((fix brs_mut (Bs : list (string * nat * exp)) : List.Forall (fun b => Pe (snd b)) Bs :=
                              match Bs with
                              | nil => List.Forall_nil _
                              | cons b Bs' => List.Forall_cons b (exp_mut (snd b)) (brs_mut Bs')
                              end) Bs)))
                    (blocks_mut Bks')
              end) Bks)
          (exp_mut M)
    | a_pi κd κc A B => case_pi κd κc A B (exp_mut A) (exp_mut B)
    | a_fn A M => case_fn A M (exp_mut A) (exp_mut M)
    | a_app M N => case_app M N (exp_mut M) (exp_mut N)
    | a_var x => case_var x
    | a_let b B => case_let b B (binding_mut b) (exp_mut B)
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
  with binding_mut (b : binding) : Pb b :=
    match b with
    | b_def A M => case_b_def A M (exp_mut A) (exp_mut M)
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
    | gm_open Φ H its Φg => case_gm_open Φ H its Φg (gmod_mut Φ) (modexp_mut H) (gmod_mut Φg)
    end
  with gentry_mut (E : gentry) : Pn E :=
    match E with
    | ge_def b pv κ A B =>
        case_ge_def b pv κ A B (exp_mut A)
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
    | ce_ass κ A => case_ce_ass κ A (exp_mut A)
    | ce_def A M => case_ce_def A M (exp_mut A) (exp_mut M)
    | ce_mod U => case_ce_mod U (gunit_mut U)
    | ce_dm A M U => case_ce_dm A M U (exp_mut A) (exp_mut M) (gunit_mut U)
    end.

  Theorem syn_mut_ind :
    (forall M, Pe M) /\ (forall H, Pm H) /\ (forall b, Pb b) /\ (forall U, Pu U) /\
    (forall D, Pd D) /\ (forall Φ, Pg Φ) /\ (forall E, Pn E) /\
    (forall e, Pc e).
  Proof.
    repeat split; [ exact exp_mut | exact modexp_mut | exact binding_mut | exact gunit_mut
                  | exact moddef_mut | exact gmod_mut | exact gentry_mut
                  | exact centry_mut ].
  Qed.
End syn_mut_ind.

(** A body with no local open: every stored body is one, and so is every
    expanded body. *)
Fixpoint gm_noopen (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' _ _ => gm_noopen Φ'
  | gm_open _ _ _ _ => False
  end.

(** ** Chains of Selections *)

(** [H.y1. … .yn], the submodules [pre] selected from [H] in order. *)
Fixpoint me_mems (H : modexp) (pre : list string) : modexp :=
  match pre with
  | nil => H
  | y :: pre' => me_mems (me_mem H y) pre'
  end.

(** The unit a total function returns where its input has none: at an
    entry of a context that is no module slot.  Never a user unit, and
    never read where a unit exists; it is the empty closed body. *)
Definition gunit_default : gunit := gu_mk nil (md_body sm_closed gm_nil).

(** [H.y1. … .yn.x] as a term: submodule selections, then a member.  The
    empty chain names no member and is never read (every chain of a
    lookup has a member); its term is the closed [Propₘ]. *)
Fixpoint member_ref (H : modexp) (ch : list string) : exp :=
  match ch with
  | nil => a_prop
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
  | gm_open Φ' _ _ Φg => gm_binders Φg + gm_binders Φ'
  end.

(** The name an import item declares. *)
Definition import_item_name (it : import_item) : string := let '(_, d, _) := it in d.

(** The names [Φ] declares, outermost last, and a name not among them. *)
Fixpoint gm_names (Φ : gmod) : list string :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' x _ => x :: gm_names Φ'
  | gm_open Φ' _ its _ => rev (map import_item_name its) ++ gm_names Φ'
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
  Notation "'Type' @ n" := (a_univ (a_llit (ordinal_of_nat n))) (at level 1, n at level 0, format "'Type' @ n") : mctt_scope.
  (** [Level@n] is the type of levels below [ω·(n+1)], and [Level] the
      finite ones, [Level@0]: [Level] is declared second so that it is the
      spelling a level type of sort [0] prints with. *)
  Notation "'Level' @ n" := (a_level n) (at level 1, n at level 0, format "'Level' @ n") : mctt_scope.
  Notation "'Level'" := (a_level 0) : mctt_scope.
  Notation "'LevelSort'" := a_level_sort : mctt_scope.
  (** The level literals: [𝕃ᵒ o] is the ordinal [o], and [𝕃@n] the finite
      level [n], the surface syntax's [<n>l].  The token is not a word: [lv]
      would make every identifier of that name a keyword. *)
  Notation "'𝕃ᵒ' o" := (a_llit o) (at level 1, o at level 0, format "'𝕃ᵒ' o") : mctt_scope.
  Notation "'𝕃' @ n" := (a_llit (ordinal_of_nat n)) (at level 1, n at level 0, format "'𝕃' @ n") : mctt_scope.
  Notation "'succl' M" := (a_succl M) (at level 2, M at level 1) : mctt_scope.
  Notation "'maxl' M N" := (a_maxl M N) (at level 2, M at level 1, N at level 1) : mctt_scope.
  Notation "'#' n" := (a_var n) (at level 1, n at level 0, format "'#' n") : mctt_scope.
  Notation "'λ' A M" := (a_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  (** The three [Π]s of [a_pi]: into a type of a universe, out of a
      domain of the kind [κ] ([Π{κ}]); into a proposition ([∀ₚ{κ}]); and
      between types of levels ([Πₗ]). *)
  Notation "'Π' '{' κ '}' A B" := (a_pi κ ak_relevant A B) (at level 2, κ at level 0, A at level 1, B at level 60) : mctt_scope.
  Notation "'Πₗ' A B" := (a_pi ak_level ak_level A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'ℓ' A ≔ M 'in' B" := (a_let (b_def A M) B) (at level 2, A at level 1, M at level 60, B at level 60) : mctt_scope.
  Notation "'ℓₘ' U 'in' B" := (a_let (b_mod U) B) (at level 2, U at level 1, B at level 60) : mctt_scope.
  (** A bare [Prop] would be Rocq's own sort, so the notation is decorated. *)
  Notation "'Propₘ'" := a_prop : mctt_scope.
  Notation "'⊤'" := a_True : mctt_scope.
  Notation "'⊥'" := a_False : mctt_scope.
  Notation "'efq' M 'return' C" := (a_absurd C M) (at level 2, M at level 60, C at level 60) : mctt_scope.
  Notation "'∀ₚ' '{' κ '}' A P" := (a_pi κ ak_propositional A P) (at level 2, κ at level 0, A at level 1, P at level 60) : mctt_scope.
  Notation "'Σₚ' P Q" := (a_and P Q) (at level 2, P at level 1, Q at level 60) : mctt_scope.
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

(** The path of the sibling [y] of the member [p]: the member [y] of the
    module [p] is in. *)
Definition qname_sibling (p : qname) (y : string) : qname :=
  {| q_unit := q_unit p ; q_chain := List.removelast (q_chain p) ++ y :: nil |}.

(** A body as the context entries it binds, innermost first.

    An inductive type or a record type, which only a filed module
    declares, binds its module: the inductive type [y] of the group [pq]
    is the member [y] of the module [pq] is in, and a record type is
    filed at its path [p].  Its term part, the type former, is named by
    its path ([a_ind], [a_record]), never by the index.

    [body_ctx] reads expanded bodies: an open is expanded first, into the
    entries its items generate ([body_xp]), and an unexpanded open binds no
    entry here.  For example, [Φ = [open M use (n); def r : #0 = #0 ≔ …]]
    has two binders ([gm_binders]) but [body_ctx Φ] holds only [r]'s entry;
    no reader reads it, every one reads the expansion
    [[private def n : ℕ ≔ M.n; def r : … ≔ …]], whose context has an entry
    per binder. *)
Fixpoint body_ctx (Φ : gmod) : ctx :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' _ (ge_def _ _ _ A (Some M)) => cons (ce_def A M) (body_ctx Φ')
  | gm_ext Φ' _ (ge_def _ _ κ A None) => cons (ce_ass κ A) (body_ctx Φ')
  | gm_ext Φ' _ (ge_mod _ U) => cons (ce_mod U) (body_ctx Φ')
  | gm_ext Φ' y (ge_ind _ pq _ _ _) => cons (ce_mod (gu_mk nil (md_alias (qname_mod (qname_sibling pq y))))) (body_ctx Φ')
  | gm_ext Φ' _ (ge_def_mod _ A M U) => cons (ce_dm A M U) (body_ctx Φ')
  | gm_ext Φ' _ (ge_record _ p _ _) => cons (ce_mod (gu_mk nil (md_alias (qname_mod p)))) (body_ctx Φ')
  | gm_open Φ' _ _ _ => body_ctx Φ'
  end.

(** The term part of a body's entry, its type and its body: a definition
    with a body, or a definition with a module part. *)
Definition entry_tm (E : gentry) : option (exp * exp) :=
  match E with
  | ge_def _ _ _ A (Some M) => Some (A, M)
  | ge_def_mod _ A M _ => Some (A, M)
  | _ => None
  end.

(** The kind of the types of a sort written as a term: [Prop]'s are
    propositions, [LevelSort]'s types of levels, a universe's types of a
    universe.  The sort of an inductive group or of a record is such a
    term, so the kind of its elements is read off it. *)
Definition sort_exp_kind (S : exp) : abs_kind :=
  match S with
  | a_prop => ak_propositional
  | a_level_sort => ak_level
  | _ => ak_relevant
  end.

(** The kind of a body's entry's term part: a definition's own; a
    definition with a module part is of a type of a universe. *)
Definition entry_kind (E : gentry) : abs_kind :=
  match E with
  | ge_def _ _ κ _ _ => κ
  | _ => ak_relevant
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
      entry is [Γ ▸ A ≔ M]; it has its own first token because [Γ ▹{κ} A]
      would otherwise be a proper prefix of it.  An assumption names its
      kind: [Γ ▹{ak_level} Level@0]. *)
  Notation "⋅" := (@nil centry) : mctt_scope.
  Notation "Γ '▹' '{' κ '}' A" := (@cons centry (ce_ass κ A) Γ) (at level 50, κ at level 0, left associativity) : mctt_scope.
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
Inductive universe_index : Set :=
| us : o2 -> universe_index
| ul : nat -> universe_index.

Coercion ul : nat >-> universe_index.

Definition universe_index_lt (u v : universe_index) : Prop :=
  match u, v with
  | us j, us k => ordinal_lt j k
  | us _, ul _ => True
  | ul _, us _ => False
  | ul j, ul k => j < k
  end.

Definition universe_index_le (u v : universe_index) : Prop :=
  match u, v with
  | us j, us k => ordinal_le j k
  | us _, ul _ => True
  | ul _, us _ => False
  | ul j, ul k => j <= k
  end.

Lemma universe_index_lt_le_trans : forall u v w, universe_index_lt u v -> universe_index_le v w -> universe_index_lt u w.
Proof. intros [] [] []; cbn; intros; auto; try lia; ordinal_solve. Qed.

Lemma universe_index_le_refl : forall u, universe_index_le u u.
Proof. intros []; cbn; [ ordinal_solve | lia ]. Qed.

Lemma universe_index_le_trans : forall u v w, universe_index_le u v -> universe_index_le v w -> universe_index_le u w.
Proof. intros [] [] []; cbn; intros; auto; try lia; ordinal_solve. Qed.

Lemma universe_index_lt_le : forall u v, universe_index_lt u v -> universe_index_le u v.
Proof. intros [] []; cbn; intros; auto; try lia; ordinal_solve. Qed.

Lemma universe_index_wf : well_founded universe_index_lt.
Proof.
  assert (Hs : forall j, Acc universe_index_lt (us j)).
  { intros j; induction j as [j IH] using (well_founded_ind ordinal_lt_wf).
    constructor; intros [k | k] Hk; cbn in Hk; [ apply IH; exact Hk | contradiction ]. }
  intros [j | n]; [ apply Hs |].
  induction n as [n IH] using lt_wf_ind; constructor; intros [k | k] Hk; cbn in Hk; [ apply Hs | apply IH; exact Hk ].
Qed.

(** ** Universes at Any Index, as Terms and Values

    A judgment in a universe is the four-value pattern of its two sides in the
    universe's element PER, whichever tier the universe is in.  The lemmas
    are stated at an index [u], through the universe's term [universe_index_term u] and
    value [universe_index_value u]; the large forms below are their instances at [ul i],
    which is [Typeω@i] by computation. *)
Definition universe_index_term (u : universe_index) : exp :=
  match u with us o => a_univ (a_llit o) | ul n => a_typ n end.

(** A large level whose universe contains the universe at [u]. *)
Definition large_level_above (u : universe_index) : nat :=
  match u with us _ => 0 | ul n => S n end.

(** The large level a type at [u] is also a type of. *)
Definition large_level (u : universe_index) : nat :=
  match u with us _ => 0 | ul n => n end.

Lemma universe_index_lt_large_level_above : forall u, universe_index_lt u (large_level_above u).
Proof. intros []; cbn; [ exact I | lia ]. Qed.

Lemma universe_index_le_large_level : forall u, universe_index_le u (large_level u).
Proof. intros []; cbn; [ exact I | lia ]. Qed.

(** The least index: [Type@0] is below every universe. *)
Lemma universe_index_le_least : forall u, universe_index_le (us ordinal_zero) u.
Proof. intros []; cbn; [ ordinal_solve | exact I ]. Qed.

(** The large levels of two ordered indices are ordered: a small universe
    lives in [Typeω@0], and the large tier's order is the order on levels. *)
Lemma universe_index_le_large_level_le : forall u v, universe_index_le u v -> large_level u <= large_level v.
Proof. intros [] []; cbn; intros; lia. Qed.

(** The join of two indices: a large universe absorbs a small one. *)
Definition universe_index_max (u v : universe_index) : universe_index :=
  match u, v with
  | us n, us m => us (ordinal_max n m)
  | us _, ul i => ul i
  | ul i, us _ => ul i
  | ul i, ul j => ul (max i j)
  end.

Lemma universe_index_le_universe_index_max_left : forall u v, universe_index_le u (universe_index_max u v).
Proof. intros [] []; cbn; try exact I; try lia; ordinal_solve. Qed.

Lemma universe_index_le_universe_index_max_right : forall u v, universe_index_le v (universe_index_max u v).
Proof. intros [] []; cbn; try exact I; try lia; ordinal_solve. Qed.

Lemma universe_index_max_lub : forall u v w, universe_index_le u w -> universe_index_le v w -> universe_index_le (universe_index_max u v) w.
Proof. intros [] [] []; cbn; intros; try contradiction; try exact I; try lia; ordinal_solve. Qed.

(** Discharges the order side conditions between universe indices. *)
Ltac solve_universe_index :=
  first [ assumption | exact I | solve [ cbn [universe_index_lt universe_index_le] in *; lia ]
        | solve [ cbn [universe_index_lt universe_index_le] in *; ordinal_solve ]
        | solve [ repeat match goal with k : universe_index |- _ => destruct k end;
                  cbn [universe_index_lt universe_index_le] in *; first [ contradiction | exact I | lia | ordinal_solve ] ] ].


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
    (** The scrutinee's type, under the non-uniform parameters: all those
        variables but the last *)
  ; block_scrutinee_type : E
    (** The motive, under those variables *)
  ; block_motive : E
    (** The branches, one per constructor of the member, in order *)
  ; block_branches : list (normal_branch_g E) }.
Arguments mk_normal_block {E}.
Arguments block_arity {E}.
Arguments block_scrutinee_type {E}.
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

(** A block with its scrutinee type, its motive and its branches' bodies
    mapped, each at the number of variables it is under. *)
Definition map_normal_block {E F : Set} (f : nat -> E -> F) (b : normal_block_g E) : normal_block_g F :=
  mk_normal_block (block_arity b) (f (block_arity b - 1) (block_scrutinee_type b)) (f (block_arity b) (block_motive b))
    (List.map (map_normal_branch f) (block_branches b)).

(** [P] holds of a block's scrutinee type, its motive and its branches'
    bodies, each at the number of variables it is under. *)
Definition normal_block_forall {E : Set} (P : nat -> E -> Prop) (b : normal_block_g E) : Prop :=
  P (block_arity b - 1) (block_scrutinee_type b) /\ P (block_arity b) (block_motive b) /\
    all_list (fun br => P (branch_arity br) (branch_body br)) (block_branches b).

(** The boolean [normal_block_forall]. *)
Definition normal_block_forallb {E : Set} (f : nat -> E -> bool) (b : normal_block_g E) : bool :=
  f (block_arity b - 1) (block_scrutinee_type b) && f (block_arity b) (block_motive b) &&
    List.forallb (fun br => f (branch_arity br) (branch_body br)) (block_branches b).

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
(** The sort of the types of levels *)
| nf_level_sort : nf
(** A canonical level [max (c, k₁ + a₁, …)]: the atoms are strictly sorted by
    their neutral and their sort (see [Core.Syntactic.Levels.Levels]) with no
    repetition, no atom is of a sort below the constant's tier (the constant
    absorbs it), and the constant [c] is [0] unless it exceeds every
    offset.  [nf_lvl_of] builds
    the normal form of a canonical level [lvl]. *)
| nf_lvl : o2 -> list (level_atom_g ne) -> nf
(** [Prop] *)
| nf_prop : nf
(** [⊤] *)
| nf_True : nf
(** A proof, as a term.  Proofs are never evaluated, so the term is not
    normal: it is the proof as written, its free variables bound by local
    definitions to the readbacks of their values ([Core.Semantic.Readback]).
    Normal forms are compared up to their proofs
    ([nf_eq_upto_proofs]). *)
| nf_proof : exp -> nf
(** [⊥] *)
| nf_False : nf
(** A [Σₚ] of normal forms *)
| nf_and : nf -> nf -> nf
(** A [Π] of normal forms, out of a domain of the kind [κd] into a
    codomain of the kind [κc] ([a_pi]): a [∀] at [ak_propositional] *)
| nf_pi : abs_kind -> abs_kind -> nf -> nf -> nf
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
(** Ex falso at a type, with its proof of [⊥] as a term: a proof is not
    evaluated, so it is stuck on nothing *)
| ne_absurd : nf -> exp -> ne
(** The eliminator of the group [pq], at its declared member [m], stuck
    on a neutral, at the group's uniform parameters; its blocks carry the
    scrutinee types, motives and branches.  (An eliminator at a view is stuck as the eliminator of the
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
  | nf_level_sort => a_level_sort
  | nf_lvl c xs => lvl_exp_of c (List.map (fun a => (atom_offset a, ne_to_exp (atom_level a))) xs)
  | nf_prop => a_prop
  | nf_True => a_True
  | nf_proof M => M
  | nf_False => a_False
  | nf_and P Q => a_and (nf_to_exp P) (nf_to_exp Q)
  | nf_pi κd κc A B => a_pi κd κc (nf_to_exp A) (nf_to_exp B)
  | nf_fn A M => a_fn (nf_to_exp A) (nf_to_exp M)
  | nf_indty p k Ms => apps_exp (a_ind p k) (List.map nf_to_exp Ms)
  | nf_con p k c Ms => apps_exp (a_con p k c) (List.map nf_to_exp Ms)
  | nf_neut M => ne_to_exp M
  | nf_record p Ms => apps_exp (a_record p) (List.map nf_to_exp Ms)
  | nf_tuple p Ms fs Ns => a_tuple (apps_exp (a_record p) (List.map nf_to_exp Ms)) (List.combine fs (List.map nf_to_exp Ns))
  end
with ne_to_exp (M : ne) : exp :=
  match M with
  | ne_absurd A M => a_absurd (nf_to_exp A) M
  | ne_elim p Us m Bks M =>
      a_elim ak_relevant p (List.map nf_to_exp Us) m
        (List.map (fun b => eb_mk (block_arity b) (nf_to_exp (block_scrutinee_type b)) (nf_to_exp (block_motive b))
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

(** A block of a stuck eliminator as a term's block. *)
Definition block_exp (b : normal_block) : eblock :=
  eb_mk (block_arity b) (nf_to_exp (block_scrutinee_type b)) (nf_to_exp (block_motive b)) (List.map branch_exp (block_branches b)).

(** The clauses of [nf_to_exp] at the levels and at a stuck eliminator,
    through the definitions above. *)
Lemma nf_to_exp_univ : forall c xs, nf_to_exp (nf_univ c xs) = a_univ (lvl_exp_of c (List.map atom_exp xs)).
Proof. reflexivity. Qed.

Lemma nf_to_exp_lvl : forall c xs, nf_to_exp (nf_lvl c xs) = lvl_exp_of c (List.map atom_exp xs).
Proof. reflexivity. Qed.

Lemma ne_to_exp_elim : forall p Us m Bks M,
    ne_to_exp (ne_elim p Us m Bks M) = a_elim ak_relevant p (List.map nf_to_exp Us) m (List.map block_exp Bks) (ne_to_exp M).
Proof. reflexivity. Qed.

(** * Canonical Levels

    A canonical level is its constant and its atoms.  The operations on
    canonical levels, and their order, are [Core.Syntactic.Levels.Levels]; the type
    is here because the universe normal forms below are indexed by it. *)
Definition lvl : Set := (o2 * list level_atom)%type.

Definition nf_lvl_of (l : lvl) : nf := nf_lvl (fst l) (snd l).

(** [lets_exp bs M]: [M] under the local definitions [bs], outermost
    first; the readback of a kept proof binds the positions it reads so
    ([Core.Semantic.Readback.Definitions.read_proof_kept]). *)
Definition lets_exp (bs : list binding) (M : exp) : exp := List.fold_right a_let M bs.

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
    semantic index [universe_index]: a small universe's semantic index is the realiser
    of its level, an ordinal below ω², while the checker compares the canonical
    levels themselves (see [Core.Syntactic.Levels.Levels]: [universe_nf_le], [universe_nf_max]). *)
Inductive universe_nf : Set :=
(** A small universe at a canonical level *)
| universe_small : lvl -> universe_nf
(** The large universe [Typeω²+n] *)
| universe_large : nat -> universe_nf.

Coercion universe_large : nat >-> universe_nf.

(** The universe normal form itself, and the term it embeds to. *)
Definition universe_nf_to_nf (u : universe_nf) : nf :=
  match u with universe_small L => nf_univ_of L | universe_large n => nf_typ n end.

Definition universe_nf_tm (u : universe_nf) : exp :=
  match u with
  | universe_small L => a_univ (lvl_exp_of (fst L) (List.map atom_exp (snd L)))
  | universe_large n => a_typ n
  end.

Lemma nf_to_exp_univ_nf : forall u, nf_to_exp (universe_nf_to_nf u) = universe_nf_tm u.
Proof. intros [[] |]; reflexivity. Qed.

(** That a normal form is a universe.  This is the side condition of every
    algorithmic rule that asks for a type.  It is a relation and not an
    equation [f W = Some u] of a deciding function [f]: the left-hand side
    of that equation is a [match] stuck on [W], and
    [progressive_inversion] does not terminate on such a hypothesis — it
    inverts it to an equation of the same shape, for ever. *)
Variant is_univ_nf : nf -> universe_nf -> Prop :=
| is_univ_nf_typ : forall i, is_univ_nf (nf_typ i) (universe_large i)
| is_univ_nf_univ : forall c xs, is_univ_nf (nf_univ c xs) (universe_small (c, xs)).

Lemma is_univ_nf_univ_nf : forall u, is_univ_nf (universe_nf_to_nf u) u.
Proof. intros [[] |]; constructor. Qed.

Lemma is_univ_nf_eq : forall W u, is_univ_nf W u -> W = universe_nf_to_nf u.
Proof. intros ? ? H; destruct H; reflexivity. Qed.

Lemma is_univ_nf_functional : forall W u v, is_univ_nf W u -> is_univ_nf W v -> u = v.
Proof. intros ? ? ? H H'; destruct H; inversion H'; reflexivity. Qed.

(** A normal form with no global at the head of a neutral.  Its proofs are
    not inspected. *)
Fixpoint nf_clean (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_proof _ | nf_False => True
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_clean (atom_level a)) xs
  | nf_pi _ _ A B | nf_fn A B | nf_and A B => nf_clean A /\ nf_clean B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => all_list nf_clean Ms
  | nf_neut M => ne_clean M
  | nf_record _ Ms => all_list nf_clean Ms
  | nf_tuple _ Ms _ Ns => all_list nf_clean Ms /\ all_list nf_clean Ns
  end
with ne_clean (M : ne) : Prop :=
  match M with
  | ne_absurd A _ => nf_clean A
  | ne_elim _ Us _ Bks M =>
      all_list nf_clean Us /\
      all_list (fun b => nf_clean (block_scrutinee_type b) /\ nf_clean (block_motive b) /\
                         all_list (fun br => nf_clean (branch_body br)) (block_branches b)) Bks /\
      ne_clean M
  | ne_app M N => ne_clean M /\ nf_clean N
  | ne_var _ => True
  | ne_glob _ => False
  | ne_proj _ M => ne_clean M
  end.

(** ** Decidable Equality of Terms

    The pieces of syntax generic in the sorts of terms and entries are
    decided given deciders for those; the terms then by a mutual
    recursion that passes itself to them.  Normal forms hold proofs as
    terms, so their equality is decided after. *)

Section GenericDec.
  Context {E C : Set} (de : forall x y : E, {x = y} + {x <> y}) (dc : forall x y : C, {x = y} + {x <> y}).

  (** Equality of shapes is decidable. *)
  Fixpoint ptyp_eq_dec_g (t t' : ptyp_g E) {struct t} : {t = t'} + {t <> t'}.
  Proof.
    destruct t as [k Ps | A t], t' as [k' Ps' | A' t']; try (right; discriminate).
    - destruct (PeanoNat.Nat.eq_dec k k') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec de Ps Ps') as [<- |]; [ left; reflexivity | right; congruence ].
    - destruct (de A A') as [<- |]; [| right; congruence ].
      destruct (ptyp_eq_dec_g t t') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of constructor arguments is decidable. *)
  Definition carg_eq_dec_g (g g' : carg_g E) : {g = g'} + {g <> g'}.
  Proof.
    destruct g as [r A | t], g' as [r' A' | t']; try (right; discriminate).
    - destruct (abs_kind_eq_dec r r') as [<- |]; [| right; congruence ].
      destruct (de A A') as [<- |]; [ left; reflexivity | right; congruence ].
    - destruct (ptyp_eq_dec_g t t') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of lists of constructors is decidable. *)
  Definition cons_eq_dec_g (cs cs' : list (string * list (carg_g E))) : {cs = cs'} + {cs <> cs'}.
  Proof.
    revert cs'; induction cs as [| [c gs] cs IH]; intros [| [c' gs'] cs']; try (right; discriminate);
      [ left; reflexivity |].
    destruct (String.string_dec c c') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec carg_eq_dec_g gs gs') as [<- |]; [| right; congruence ].
    destruct (IH cs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of member heads is decidable. *)
  Definition mhead_eq_dec_g (h h' : mhead_g E) : {h = h'} + {h <> h'}.
  Proof.
    destruct h as [p | qc k Is vm | qr Is fl], h' as [p' | qc' k' Is' vm' | qr' Is' fl']; try (right; discriminate).
    - destruct (qname_eq_dec p p') as [<- |]; [ left; reflexivity | right; congruence ].
    - destruct (qname_eq_dec qc qc') as [<- |]; [| right; congruence ].
      destruct (PeanoNat.Nat.eq_dec k k') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec de Is Is') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec PeanoNat.Nat.eq_dec vm vm') as [<- |]; [ left; reflexivity | right; congruence ].
    - destruct (qname_eq_dec qr qr') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec de Is Is') as [<- |]; [| right; congruence ].
      destruct (list_eq_dec String.string_dec fl fl') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of members is decidable. *)
  Definition imember_eq_dec_g (M M' : imember_g E C) : {M = M'} + {M <> M'}.
  Proof.
    destruct M as [h ps cs], M' as [h' ps' cs'].
    destruct (mhead_eq_dec_g h h') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec dc ps ps') as [<- |]; [| right; congruence ].
    destruct (cons_eq_dec_g cs cs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of groups is decidable. *)
  Definition ind_decl_eq_dec_g (D D' : ind_decl_g E C) : {D = D'} + {D <> D'}.
  Proof.
    destruct D as [us S ms], D' as [us' S' ms'].
    destruct (list_eq_dec dc us us') as [<- |]; [| right; congruence ].
    destruct (de S S') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec imember_eq_dec_g ms ms') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of lists of branches is decidable. *)
  Definition brs_eq_dec_g (Bs Bs' : list (string * nat * E)) : {Bs = Bs'} + {Bs <> Bs'}.
  Proof.
    revert Bs'; induction Bs as [| [[c n] B] Bs IH]; intros [| [[c' n'] B'] Bs']; try (right; discriminate);
      [ left; reflexivity |].
    destruct (String.string_dec c c') as [<- |]; [| right; congruence ].
    destruct (PeanoNat.Nat.eq_dec n n') as [<- |]; [| right; congruence ].
    destruct (de B B') as [<- |]; [| right; congruence ].
    destruct (IH Bs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of lists of eliminator blocks is decidable. *)
  Definition eblocks_eq_dec_g (Bks Bks' : list (eblock_g E)) : {Bks = Bks'} + {Bks <> Bks'}.
  Proof.
    revert Bks'; induction Bks as [| [nm Z A Bs] Bks IH]; intros [| [nm' Z' A' Bs'] Bks']; try (right; discriminate);
      [ left; reflexivity |].
    destruct (PeanoNat.Nat.eq_dec nm nm') as [<- |]; [| right; congruence ].
    destruct (de Z Z') as [<- |]; [| right; congruence ].
    destruct (de A A') as [<- |]; [| right; congruence ].
    destruct (brs_eq_dec_g Bs Bs') as [<- |]; [| right; congruence ].
    destruct (IH Bks') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of named terms (the fields of a record) is decidable. *)
  Definition named_eq_dec_g (x y : (string * E)%type) : {x = y} + {x <> y}.
  Proof.
    destruct x as [a x], y as [b y].
    destruct (String.string_dec a b) as [<- |]; [| right; congruence ].
    destruct (de x y) as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.

  (** Equality of record declarations is decidable. *)
  Definition record_decl_eq_dec_g (R R' : record_decl_g E C) : {R = R'} + {R <> R'}.
  Proof.
    destruct R as [Δ S fs rs], R' as [Δ' S' fs' rs'].
    destruct (list_eq_dec dc Δ Δ') as [<- |]; [| right; congruence ].
    destruct (de S S') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec named_eq_dec_g fs fs') as [<- |]; [| right; congruence ].
    destruct (list_eq_dec abs_kind_eq_dec rs rs') as [<- |]; [ left; reflexivity | right; congruence ].
  Defined.
End GenericDec.

(** Equality of terms, and of the module syntax nested in them, is
    decidable. *)
Fixpoint exp_eq_dec (M N : exp) {struct M} : {M = N} + {M <> N}
with modexp_eq_dec (M N : modexp) {struct M} : {M = N} + {M <> N}
with binding_eq_dec (M N : binding) {struct M} : {M = N} + {M <> N}
with gunit_eq_dec (M N : gunit) {struct M} : {M = N} + {M <> N}
with moddef_eq_dec (M N : moddef) {struct M} : {M = N} + {M <> N}
with gmod_eq_dec (M N : gmod) {struct M} : {M = N} + {M <> N}
with gentry_eq_dec (M N : gentry) {struct M} : {M = N} + {M <> N}
with centry_eq_dec (M N : centry) {struct M} : {M = N} + {M <> N}.
Proof.
  all: decide equality;
    first [ apply PeanoNat.Nat.eq_dec | apply String.string_dec | apply qname_eq_dec | apply Bool.bool_dec
          | apply list_eq_dec, String.string_dec | apply o2_eq_dec | apply (list_eq_dec exp_eq_dec)
          | apply (list_eq_dec centry_eq_dec) | apply (eblocks_eq_dec_g exp_eq_dec)
          | apply (ind_decl_eq_dec_g exp_eq_dec centry_eq_dec)
          | apply (record_decl_eq_dec_g exp_eq_dec centry_eq_dec)
          | apply (list_eq_dec (named_eq_dec_g exp_eq_dec))
          | (decide equality; apply (list_eq_dec exp_eq_dec)) | idtac ].
  all: try (decide equality; fail).
  all: try (decide equality; apply qname_eq_dec).
  (* the items of an open *)
  apply list_eq_dec; intros; repeat (decide equality || apply String.string_dec || apply Bool.bool_dec).
Defined.

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
    destruct b as [nm Z A Bs], b' as [nm' Z' A' Bs'].
    destruct (PeanoNat.Nat.eq_dec nm nm') as [<- |]; [| right; congruence ].
    destruct (de Z Z') as [<- |]; [| right; congruence ].
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
          | apply abs_kind_eq_dec | apply exp_eq_dec
          | apply (List.list_eq_dec String.string_dec) | apply (List.list_eq_dec nf_eq_dec)
          | apply (List.list_eq_dec (level_atom_eq_dec_g ne_eq_dec))
          | apply (List.list_eq_dec (normal_block_eq_dec_g nf_eq_dec)) | idtac ].
Defined.

(** ** Equality up to Proofs

    Proofs are irrelevant: two normal forms that differ only in their
    proofs stand for equal terms.  Nothing is erased: the normal forms
    are compared structurally, any two proofs related. *)

#[local] Open Scope bool_scope.

(** The boolean of a decision. *)
Definition dec_eqb {A : Type} (d : forall x y : A, {x = y} + {x <> y}) (x y : A) : bool :=
  if d x y then true else false.

Lemma dec_eqb_true : forall {A} (d : forall x y : A, {x = y} + {x <> y}) x y, dec_eqb d x y = true <-> x = y.
Proof. intros; unfold dec_eqb; destruct (d x y); split; congruence. Qed.

Lemma dec_eqb_refl : forall {A} (d : forall x y : A, {x = y} + {x <> y}) x, dec_eqb d x x = true.
Proof. intros; apply dec_eqb_true; reflexivity. Qed.

Lemma dec_eqb_sym : forall {A} (d : forall x y : A, {x = y} + {x <> y}) x y, dec_eqb d x y = dec_eqb d y x.
Proof. intros; unfold dec_eqb; destruct (d x y), (d y x); congruence. Qed.

(** Two lists related pointwise by a boolean comparison. *)
Fixpoint list_eqb {A : Set} (f : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | nil, nil => true
  | x :: r, x' :: r' => f x x' && list_eqb f r r'
  | _, _ => false
  end.

(** [nf_eqb_upto_proofs W W'] is the decision procedure for equality of
    normal forms up to their proofs: the two normal forms have the same
    shape, with the same kinds, indices, names and levels, and any two
    proofs ([nf_proof], and the proof of a stuck ex falso) are related.
    Statements use the relation [nf_eq_upto_proofs] below; the checker
    runs this function.  For example [Vec ⟨n, nf_proof P1⟩] and
    [Vec ⟨n, nf_proof P2⟩] are related, while [Πⁿ{ak_relevant} A B] and
    [Πⁿ{ak_level} A B] are not. *)
Fixpoint nf_eqb_upto_proofs (W W' : nf) {struct W} : bool :=
  match W, W' with
  | nf_typ i, nf_typ i' => Nat.eqb i i'
  | nf_univ c xs, nf_univ c' xs' =>
      dec_eqb o2_eq_dec c c' &&
      list_eqb (fun a a' => Nat.eqb (atom_offset a) (atom_offset a') && Nat.eqb (atom_sort a) (atom_sort a') &&
                            ne_eqb_upto_proofs (atom_level a) (atom_level a')) xs xs'
  | nf_level n, nf_level n' => Nat.eqb n n'
  | nf_level_sort, nf_level_sort => true
  | nf_lvl c xs, nf_lvl c' xs' =>
      dec_eqb o2_eq_dec c c' &&
      list_eqb (fun a a' => Nat.eqb (atom_offset a) (atom_offset a') && Nat.eqb (atom_sort a) (atom_sort a') &&
                            ne_eqb_upto_proofs (atom_level a) (atom_level a')) xs xs'
  | nf_prop, nf_prop => true
  | nf_True, nf_True => true
  | nf_proof _, nf_proof _ => true
  | nf_False, nf_False => true
  | nf_and P Q, nf_and P' Q' => nf_eqb_upto_proofs P P' && nf_eqb_upto_proofs Q Q'
  | nf_pi κd κc A B, nf_pi κd' κc' A' B' =>
      dec_eqb abs_kind_eq_dec κd κd' && dec_eqb abs_kind_eq_dec κc κc' &&
      nf_eqb_upto_proofs A A' && nf_eqb_upto_proofs B B'
  | nf_fn A M, nf_fn A' M' => nf_eqb_upto_proofs A A' && nf_eqb_upto_proofs M M'
  | nf_indty p k Ms, nf_indty p' k' Ms' =>
      dec_eqb qname_eq_dec p p' && Nat.eqb k k' && list_eqb nf_eqb_upto_proofs Ms Ms'
  | nf_con p k c Ms, nf_con p' k' c' Ms' =>
      dec_eqb qname_eq_dec p p' && Nat.eqb k k' && dec_eqb String.string_dec c c' && list_eqb nf_eqb_upto_proofs Ms Ms'
  | nf_neut M, nf_neut M' => ne_eqb_upto_proofs M M'
  | nf_record p Ms, nf_record p' Ms' => dec_eqb qname_eq_dec p p' && list_eqb nf_eqb_upto_proofs Ms Ms'
  | nf_tuple p Ms fs Ns, nf_tuple p' Ms' fs' Ns' =>
      dec_eqb qname_eq_dec p p' && list_eqb nf_eqb_upto_proofs Ms Ms' &&
      dec_eqb (List.list_eq_dec String.string_dec) fs fs' && list_eqb nf_eqb_upto_proofs Ns Ns'
  | _, _ => false
  end
(** The same for neutrals. *)
with ne_eqb_upto_proofs (M M' : ne) {struct M} : bool :=
  match M, M' with
  | ne_absurd A _, ne_absurd A' _ => nf_eqb_upto_proofs A A'
  | ne_elim p Us m Bks N, ne_elim p' Us' m' Bks' N' =>
      dec_eqb qname_eq_dec p p' && list_eqb nf_eqb_upto_proofs Us Us' && Nat.eqb m m' &&
      list_eqb (fun b b' =>
                  Nat.eqb (block_arity b) (block_arity b') &&
                  nf_eqb_upto_proofs (block_scrutinee_type b) (block_scrutinee_type b') &&
                  nf_eqb_upto_proofs (block_motive b) (block_motive b') &&
                  list_eqb (fun br br' =>
                              dec_eqb String.string_dec (branch_constructor br) (branch_constructor br') &&
                              Nat.eqb (branch_arity br) (branch_arity br') &&
                              nf_eqb_upto_proofs (branch_body br) (branch_body br'))
                    (block_branches b) (block_branches b')) Bks Bks' &&
      ne_eqb_upto_proofs N N'
  | ne_app N A, ne_app N' A' => ne_eqb_upto_proofs N N' && nf_eqb_upto_proofs A A'
  | ne_var x, ne_var x' => Nat.eqb x x'
  | ne_glob p, ne_glob p' => dec_eqb qname_eq_dec p p'
  | ne_proj f N, ne_proj f' N' => dec_eqb String.string_dec f f' && ne_eqb_upto_proofs N N'
  | _, _ => false
  end.

(** Two normal forms are equal up to their proofs: the relation of
    statements, decided by [nf_eqb_upto_proofs]. *)
Definition nf_eq_upto_proofs (W W' : nf) : Prop := nf_eqb_upto_proofs W W' = true.

(** Two neutrals are equal up to their proofs. *)
Definition ne_eq_upto_proofs (M M' : ne) : Prop := ne_eqb_upto_proofs M M' = true.

(** *** Lists *)

Lemma list_eqb_refl_all : forall {A : Set} (Q : A -> Type) (f : A -> A -> bool) l,
    Base.list_all A Q l -> (forall x, Q x -> f x x = true) -> list_eqb f l l = true.
Proof. intros * Hl Hf; induction Hl; cbn; [ reflexivity | rewrite Hf, IHHl by assumption; reflexivity ]. Qed.

Lemma list_eqb_sym_all : forall {A : Set} (Q : A -> Type) (f : A -> A -> bool) l,
    Base.list_all A Q l -> (forall x, Q x -> forall y, f x y = f y x) -> forall l', list_eqb f l l' = list_eqb f l' l.
Proof.
  intros * Hl Hf; induction Hl; intros [| y l']; cbn; try reflexivity.
  rewrite (Hf _ ltac:(eassumption) y), IHHl; reflexivity.
Qed.

Lemma list_eqb_trans_all : forall {A : Set} (Q : A -> Type) (f : A -> A -> bool) l,
    Base.list_all A Q l -> (forall x, Q x -> forall y z, f x y = true -> f y z = true -> f x z = true) ->
    forall l' l'', list_eqb f l l' = true -> list_eqb f l' l'' = true -> list_eqb f l l'' = true.
Proof.
  intros * Hl Hf; induction Hl; intros [| y l'] [| z l''] H1 H2; cbn in *; try discriminate; try reflexivity.
  apply Bool.andb_true_iff in H1 as [H1 H1']; apply Bool.andb_true_iff in H2 as [H2 H2'].
  rewrite (Hf _ ltac:(eassumption) _ _ H1 H2), (IHHl _ _ H1' H2'); reflexivity.
Qed.

(** Related lists stay related under maps that respect the relation of
    their elements: the list case of the congruence lemmas (renaming,
    un-weakening). *)
Lemma list_eqb_map_all : forall {A B : Set} (Q : A -> Type) (f : A -> A -> bool) (f' : B -> B -> bool) (g g' : A -> B) l,
    Base.list_all A Q l -> (forall x, Q x -> forall y, f x y = true -> f' (g x) (g' y) = true) ->
    forall l', list_eqb f l l' = true -> list_eqb f' (List.map g l) (List.map g' l') = true.
Proof.
  intros * Hl Hf; induction Hl; intros [| y l'] H; cbn in *; try discriminate; try reflexivity.
  apply Bool.andb_true_iff in H as [H H']; rewrite (Hf _ ltac:(eassumption) _ H), (IHHl _ H'); reflexivity.
Qed.

(** Lists related under maps that reflect the relation of their elements
    are related: the list case of the injectivity lemmas. *)
Lemma list_eqb_map_inv_all : forall {A B : Set} (Q : A -> Type) (f : A -> A -> bool) (f' : B -> B -> bool) (g : A -> B) l,
    Base.list_all A Q l -> (forall x, Q x -> forall y, f' (g x) (g y) = true -> f x y = true) ->
    forall l', list_eqb f' (List.map g l) (List.map g l') = true -> list_eqb f l l' = true.
Proof.
  intros * Hl Hf; induction Hl; intros [| y l'] H; cbn in *; try discriminate; try reflexivity.
  apply Bool.andb_true_iff in H as [H H']; rewrite (Hf _ ltac:(eassumption) _ H), (IHHl _ H'); reflexivity.
Qed.

(** Related lists have the same length. *)
Lemma list_eqb_length : forall {A : Set} (f : A -> A -> bool) l l', list_eqb f l l' = true -> List.length l = List.length l'.
Proof.
  intros A f; induction l as [| x l IH]; intros [| y l'] H; cbn in *; try discriminate; [ reflexivity |].
  apply Bool.andb_true_iff in H as [_ H]; f_equal; exact (IH _ H).
Qed.

(** The comparison of two appends, at prefixes of one length, is that of
    their parts. *)
Lemma list_eqb_app_eq : forall {A : Set} (f : A -> A -> bool) l1 l1' l2 l2', List.length l1 = List.length l1' ->
    list_eqb f (l1 ++ l2) (l1' ++ l2') = (list_eqb f l1 l1' && list_eqb f l2 l2').
Proof.
  intros A f; induction l1 as [| x l1 IH]; intros [| y l1'] * H; cbn in *; try discriminate; [ reflexivity |].
  rewrite IH by congruence; destruct (f x y); reflexivity.
Qed.

(** Splits conjunctions of booleans, in the hypotheses and the goal. *)
Ltac eqb_split :=
  repeat match goal with
         | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [? ?]
         | |- (_ && _) = true => apply Bool.andb_true_iff; split
         end.

(** Turns the boolean equalities of the hypotheses into equalities and
    closes the leaves they give. *)
Ltac eqb_leaves :=
  repeat match goal with
         | H : Nat.eqb _ _ = true |- _ => apply PeanoNat.Nat.eqb_eq in H
         | H : dec_eqb _ _ _ = true |- _ => apply dec_eqb_true in H
         end;
  try (apply PeanoNat.Nat.eqb_eq; congruence); try (apply dec_eqb_true; congruence).

(** *** An Equivalence *)

Lemma nf_ne_eqb_upto_proofs_refl :
  (forall W, nf_eqb_upto_proofs W W = true) /\ (forall M, ne_eqb_upto_proofs M M = true).
Proof.
  apply nf_ne_ind; intros; cbn [nf_eqb_upto_proofs ne_eqb_upto_proofs]; eqb_split;
    rewrite ?PeanoNat.Nat.eqb_refl, ?dec_eqb_refl; try assumption; try reflexivity;
    try (eapply list_eqb_refl_all; [ eassumption |]; cbn; intros x Hx).
  all: try (destruct Hx; cbn; rewrite !PeanoNat.Nat.eqb_refl; cbn; assumption).
  all: try assumption.
  - destruct Hx as [n' Z HZ A' HA brs Hbrs]; cbn; rewrite PeanoNat.Nat.eqb_refl, HZ, HA; cbn.
    eapply list_eqb_refl_all; [ exact Hbrs |]; intros br Hbr; destruct Hbr; cbn.
    rewrite dec_eqb_refl, PeanoNat.Nat.eqb_refl; assumption.
Qed.

Lemma nf_ne_eqb_upto_proofs_sym :
  (forall W W', nf_eqb_upto_proofs W W' = nf_eqb_upto_proofs W' W) /\
  (forall M M', ne_eqb_upto_proofs M M' = ne_eqb_upto_proofs M' M).
Proof.
  apply nf_ne_ind; intros;
    lazymatch goal with |- nf_eqb_upto_proofs _ ?W = _ => destruct W | |- ne_eqb_upto_proofs _ ?M = _ => destruct M end;
    cbn [nf_eqb_upto_proofs ne_eqb_upto_proofs]; try reflexivity.
  all: repeat (match goal with |- (_ && _) = (_ && _) => apply (f_equal2 andb) end);
    try apply PeanoNat.Nat.eqb_sym; try apply dec_eqb_sym; try (match goal with H : forall _, _ = _ |- _ => apply H end).
  all: try (eapply list_eqb_sym_all; [ eassumption |]; intros x Hx y).
  all: try solve [ apply Hx ].
  all: destruct Hx; cbn -[nf_eqb_upto_proofs ne_eqb_upto_proofs list_eqb Nat.eqb dec_eqb];
    repeat (match goal with |- (_ && _) = (_ && _) => apply (f_equal2 andb) end); try apply PeanoNat.Nat.eqb_sym; try solve [ auto ].
  all: eapply list_eqb_sym_all; [ eassumption |]; intros br Hbr br'; destruct Hbr;
    cbn -[nf_eqb_upto_proofs ne_eqb_upto_proofs list_eqb Nat.eqb dec_eqb];
    repeat (match goal with |- (_ && _) = (_ && _) => apply (f_equal2 andb) end);
    try apply PeanoNat.Nat.eqb_sym; try apply dec_eqb_sym; auto.
Qed.

Lemma nf_ne_eqb_upto_proofs_trans :
  (forall W W' W'', nf_eqb_upto_proofs W W' = true -> nf_eqb_upto_proofs W' W'' = true -> nf_eqb_upto_proofs W W'' = true) /\
  (forall M M' M'', ne_eqb_upto_proofs M M' = true -> ne_eqb_upto_proofs M' M'' = true -> ne_eqb_upto_proofs M M'' = true).
Proof.
  apply nf_ne_ind; intros;
    lazymatch goal with
    | H1 : nf_eqb_upto_proofs _ ?W = true, H2 : nf_eqb_upto_proofs ?W ?W' = true |- _ => destruct W, W'
    | H1 : ne_eqb_upto_proofs _ ?M = true, H2 : ne_eqb_upto_proofs ?M ?M' = true |- _ => destruct M, M'
    end;
    cbn [nf_eqb_upto_proofs ne_eqb_upto_proofs] in *; try discriminate; try reflexivity.
  all: eqb_split; eqb_leaves; try solve [ eauto ].
  all: eapply list_eqb_trans_all; [ eassumption | | eassumption | eassumption ]; intros x Hx y z Hxy Hyz; try solve [ eauto ].
  all: destruct Hx; cbn -[nf_eqb_upto_proofs ne_eqb_upto_proofs list_eqb Nat.eqb dec_eqb] in *; eqb_split; eqb_leaves;
    try solve [ eauto ].
  all: eapply list_eqb_trans_all; [ eassumption | | eassumption | eassumption ]; intros br Hbr br' br'' Hb1 Hb2; destruct Hbr;
    cbn -[nf_eqb_upto_proofs ne_eqb_upto_proofs list_eqb Nat.eqb dec_eqb] in *; eqb_split; eqb_leaves; eauto.
Qed.

#[export] Instance nf_eq_upto_proofs_Equivalence : Equivalence nf_eq_upto_proofs.
Proof.
  split; unfold nf_eq_upto_proofs; repeat intro.
  - apply nf_ne_eqb_upto_proofs_refl.
  - rewrite (proj1 nf_ne_eqb_upto_proofs_sym); assumption.
  - eapply (proj1 nf_ne_eqb_upto_proofs_trans); eassumption.
Qed.

#[export] Instance ne_eq_upto_proofs_Equivalence : Equivalence ne_eq_upto_proofs.
Proof.
  split; unfold ne_eq_upto_proofs; repeat intro.
  - apply nf_ne_eqb_upto_proofs_refl.
  - rewrite (proj2 nf_ne_eqb_upto_proofs_sym); assumption.
  - eapply (proj2 nf_ne_eqb_upto_proofs_trans); eassumption.
Qed.

(** Two lists of normal forms equal up to their proofs, element by element
    (the comparison of the arguments of [nf_indty]). *)
Definition nfs_eq_upto_proofs (Ws Ws' : list nf) : Prop := list_eqb nf_eqb_upto_proofs Ws Ws' = true.

#[export] Instance nfs_eq_upto_proofs_Equivalence : Equivalence nfs_eq_upto_proofs.
Proof.
  unfold nfs_eq_upto_proofs; split.
  - intros Ws; induction Ws; cbn; [ reflexivity |]; rewrite (proj1 nf_ne_eqb_upto_proofs_refl), IHWs; reflexivity.
  - intros Ws; induction Ws as [| W Ws IH]; intros [| W' Ws'] H; cbn in *; try discriminate; [ reflexivity |].
    apply Bool.andb_true_iff in H as [H1 H2]; rewrite (proj1 nf_ne_eqb_upto_proofs_sym), H1, (IH _ H2); reflexivity.
  - intros Ws; induction Ws as [| W Ws IH]; intros [| W' Ws'] [| W'' Ws''] H H'; cbn in *; try discriminate; [ reflexivity |].
    apply Bool.andb_true_iff in H as [H1 H2]; apply Bool.andb_true_iff in H' as [H1' H2'].
    rewrite ((proj1 nf_ne_eqb_upto_proofs_trans) _ _ _ H1 H1'), (IH _ _ H2 H2'); reflexivity.
Qed.

(** The lists, cons by cons. *)
Lemma nfs_eq_upto_proofs_cons : forall W W' Ws Ws',
    nfs_eq_upto_proofs (W :: Ws) (W' :: Ws') <-> nf_eq_upto_proofs W W' /\ nfs_eq_upto_proofs Ws Ws'.
Proof. intros; unfold nfs_eq_upto_proofs, nf_eq_upto_proofs; cbn; apply Bool.andb_true_iff. Qed.

(** Appended related lists are related. *)
Lemma nfs_eq_upto_proofs_app : forall Ms Ms' Ns Ns',
    nfs_eq_upto_proofs Ms Ms' -> nfs_eq_upto_proofs Ns Ns' -> nfs_eq_upto_proofs (Ms ++ Ns) (Ms' ++ Ns').
Proof.
  unfold nfs_eq_upto_proofs; induction Ms as [| M Ms IH]; intros [| M' Ms'] * H H'; cbn in *; try discriminate; [ exact H' |].
  apply Bool.andb_true_iff in H as [H1 H2]; rewrite H1, (IH _ _ _ H2 H'); reflexivity.
Qed.

(** The formers taking lists of normal forms respect the relation. *)
Lemma nf_con_upto_proofs : forall p k c Ms Ms', nfs_eq_upto_proofs Ms Ms' -> nf_eq_upto_proofs (nf_con p k c Ms) (nf_con p k c Ms').
Proof. intros * H; unfold nf_eq_upto_proofs; cbn; rewrite !dec_eqb_refl, PeanoNat.Nat.eqb_refl; exact H. Qed.

Lemma nf_indty_upto_proofs : forall p k Ms Ms', nfs_eq_upto_proofs Ms Ms' -> nf_eq_upto_proofs (nf_indty p k Ms) (nf_indty p k Ms').
Proof. intros * H; unfold nf_eq_upto_proofs; cbn; rewrite !dec_eqb_refl, PeanoNat.Nat.eqb_refl; exact H. Qed.

Lemma nf_record_upto_proofs : forall p Ms Ms', nfs_eq_upto_proofs Ms Ms' -> nf_eq_upto_proofs (nf_record p Ms) (nf_record p Ms').
Proof. intros * H; unfold nf_eq_upto_proofs; cbn; rewrite !dec_eqb_refl; exact H. Qed.

(** Two lists of branches of a stuck eliminator equal up to their proofs,
    the comparison of [ne_eqb_upto_proofs]. *)
Definition branches_eq_upto_proofs (Bs Bs' : list normal_branch) : Prop :=
  list_eqb (fun br br' =>
              dec_eqb String.string_dec (branch_constructor br) (branch_constructor br') &&
              Nat.eqb (branch_arity br) (branch_arity br') &&
              nf_eqb_upto_proofs (branch_body br) (branch_body br')) Bs Bs' = true.

(** Two lists of blocks likewise. *)
Definition blocks_eq_upto_proofs (Bks Bks' : list normal_block) : Prop :=
  list_eqb (fun b b' =>
              Nat.eqb (block_arity b) (block_arity b') &&
              nf_eqb_upto_proofs (block_scrutinee_type b) (block_scrutinee_type b') &&
              nf_eqb_upto_proofs (block_motive b) (block_motive b') &&
              list_eqb (fun br br' =>
                          dec_eqb String.string_dec (branch_constructor br) (branch_constructor br') &&
                          Nat.eqb (branch_arity br) (branch_arity br') &&
                          nf_eqb_upto_proofs (branch_body br) (branch_body br'))
                (block_branches b) (block_branches b')) Bks Bks' = true.

Lemma branches_eq_upto_proofs_nil : branches_eq_upto_proofs nil nil.
Proof. reflexivity. Qed.

Lemma branches_eq_upto_proofs_cons : forall c n W W' Bs Bs', nf_eq_upto_proofs W W' -> branches_eq_upto_proofs Bs Bs' ->
    branches_eq_upto_proofs (mk_normal_branch c n W :: Bs) (mk_normal_branch c n W' :: Bs').
Proof.
  intros * H H'; unfold branches_eq_upto_proofs, nf_eq_upto_proofs in *; cbn.
  rewrite dec_eqb_refl, PeanoNat.Nat.eqb_refl, H, H'; reflexivity.
Qed.

Lemma blocks_eq_upto_proofs_nil : blocks_eq_upto_proofs nil nil.
Proof. reflexivity. Qed.

Lemma blocks_eq_upto_proofs_cons : forall n Z Z' A A' Bs Bs' Bks Bks',
    nf_eq_upto_proofs Z Z' -> nf_eq_upto_proofs A A' -> branches_eq_upto_proofs Bs Bs' -> blocks_eq_upto_proofs Bks Bks' ->
    blocks_eq_upto_proofs (mk_normal_block n Z A Bs :: Bks) (mk_normal_block n Z' A' Bs' :: Bks').
Proof.
  intros * HZ HA HB HK; unfold blocks_eq_upto_proofs, branches_eq_upto_proofs, nf_eq_upto_proofs in *; cbn.
  rewrite PeanoNat.Nat.eqb_refl, HZ, HA, HB, HK; reflexivity.
Qed.

(** The neutral formers respect the relation. *)
Lemma ne_app_upto_proofs : forall M M' N N', ne_eq_upto_proofs M M' -> nf_eq_upto_proofs N N' ->
    ne_eq_upto_proofs (ne_app M N) (ne_app M' N').
Proof. intros * H H'; unfold ne_eq_upto_proofs, nf_eq_upto_proofs in *; cbn; rewrite H, H'; reflexivity. Qed.

Lemma ne_proj_upto_proofs : forall f M M', ne_eq_upto_proofs M M' -> ne_eq_upto_proofs (ne_proj f M) (ne_proj f M').
Proof. intros * H; unfold ne_eq_upto_proofs in *; cbn; rewrite dec_eqb_refl, H; reflexivity. Qed.

Lemma ne_elim_upto_proofs : forall p Us Us' k Bks Bks' M M',
    nfs_eq_upto_proofs Us Us' -> blocks_eq_upto_proofs Bks Bks' -> ne_eq_upto_proofs M M' ->
    ne_eq_upto_proofs (ne_elim p Us k Bks M) (ne_elim p Us' k Bks' M').
Proof.
  intros * HU HB HM; unfold ne_eq_upto_proofs, nfs_eq_upto_proofs, blocks_eq_upto_proofs in *; cbn.
  rewrite dec_eqb_refl, PeanoNat.Nat.eqb_refl, HU, HB, HM; reflexivity.
Qed.

(** The formers are injective up to proofs. *)
Lemma nf_pi_upto_proofs_inv : forall κd κc A B κd' κc' A' B',
    nf_eq_upto_proofs (nf_pi κd κc A B) (nf_pi κd' κc' A' B') ->
    κd = κd' /\ κc = κc' /\ nf_eq_upto_proofs A A' /\ nf_eq_upto_proofs B B'.
Proof. unfold nf_eq_upto_proofs; cbn; intros * H; eqb_split; eqb_leaves; subst; repeat split; assumption. Qed.

Lemma nf_indty_upto_proofs_inv : forall p k Ms p' k' Ms',
    nf_eq_upto_proofs (nf_indty p k Ms) (nf_indty p' k' Ms') -> p = p' /\ k = k' /\ nfs_eq_upto_proofs Ms Ms'.
Proof. unfold nf_eq_upto_proofs, nfs_eq_upto_proofs; cbn; intros * H; eqb_split; eqb_leaves; subst; repeat split; assumption. Qed.

Lemma nf_record_upto_proofs_inv : forall p Ms p' Ms',
    nf_eq_upto_proofs (nf_record p Ms) (nf_record p' Ms') -> p = p' /\ nfs_eq_upto_proofs Ms Ms'.
Proof. unfold nf_eq_upto_proofs, nfs_eq_upto_proofs; cbn; intros * H; eqb_split; eqb_leaves; subst; split; [ reflexivity | assumption ]. Qed.

(** Related lists have related elements at each position. *)
Lemma nfs_eq_upto_proofs_nth : forall Ms Ms' j M, nfs_eq_upto_proofs Ms Ms' -> List.nth_error Ms j = Some M ->
    exists M', List.nth_error Ms' j = Some M' /\ nf_eq_upto_proofs M M'.
Proof.
  unfold nfs_eq_upto_proofs, nf_eq_upto_proofs; induction Ms as [| N Ms IH]; intros [| N' Ms'] [| j] M H Hj;
    cbn in *; try discriminate; apply Bool.andb_true_iff in H as [H1 H2].
  - injection Hj as <-; eauto.
  - eauto.
Qed.

Lemma nfs_eq_upto_proofs_length : forall Ms Ms', nfs_eq_upto_proofs Ms Ms' -> List.length Ms = List.length Ms'.
Proof. intros * H; exact (list_eqb_length _ _ _ H). Qed.

(** So do the binding formers. *)
Lemma nf_fn_upto_proofs : forall A A' M M', nf_eq_upto_proofs A A' -> nf_eq_upto_proofs M M' ->
    nf_eq_upto_proofs (nf_fn A M) (nf_fn A' M').
Proof. intros * H H'; unfold nf_eq_upto_proofs in *; cbn; rewrite H, H'; reflexivity. Qed.

Lemma nf_pi_upto_proofs : forall κd κc A A' B B', nf_eq_upto_proofs A A' -> nf_eq_upto_proofs B B' ->
    nf_eq_upto_proofs (nf_pi κd κc A B) (nf_pi κd κc A' B').
Proof. intros * H H'; unfold nf_eq_upto_proofs in *; cbn; rewrite !dec_eqb_refl, H, H'; reflexivity. Qed.

Lemma nf_and_upto_proofs : forall P P' Q Q', nf_eq_upto_proofs P P' -> nf_eq_upto_proofs Q Q' ->
    nf_eq_upto_proofs (nf_and P Q) (nf_and P' Q').
Proof. intros * H H'; unfold nf_eq_upto_proofs in *; cbn; rewrite H, H'; reflexivity. Qed.

Lemma nf_tuple_upto_proofs : forall p Ms Ms' fs Ns Ns', nfs_eq_upto_proofs Ms Ms' -> nfs_eq_upto_proofs Ns Ns' ->
    nf_eq_upto_proofs (nf_tuple p Ms fs Ns) (nf_tuple p Ms' fs Ns').
Proof. intros * H H'; unfold nf_eq_upto_proofs; cbn; rewrite !dec_eqb_refl; unfold nfs_eq_upto_proofs in *; rewrite H, H'; reflexivity. Qed.

(** [auto] closes reflexive goals of the relations (an atom is in a list
    in which it occurs: [level_atoms_In]). *)
#[export] Hint Extern 1 (nf_eq_upto_proofs _ _) => reflexivity : core.
#[export] Hint Extern 1 (ne_eq_upto_proofs _ _) => reflexivity : core.
#[export] Hint Extern 1 (nfs_eq_upto_proofs _ _) => reflexivity : core.

(** Equal normal forms are equal up to proofs. *)
Lemma nf_eq_upto_proofs_of_eq : forall W W', W = W' -> nf_eq_upto_proofs W W'.
Proof. intros * ->; reflexivity. Qed.

Lemma ne_eq_upto_proofs_of_eq : forall M M', M = M' -> ne_eq_upto_proofs M M'.
Proof. intros * ->; reflexivity. Qed.

(** Equality up to proofs is decidable, by its decision procedure. *)
Definition nf_eq_upto_proofs_dec (W W' : nf) : {nf_eq_upto_proofs W W'} + {~ nf_eq_upto_proofs W W'} :=
  Bool.bool_dec (nf_eqb_upto_proofs W W') true.

Definition ne_eq_upto_proofs_dec (M M' : ne) : {ne_eq_upto_proofs M M'} + {~ ne_eq_upto_proofs M M'} :=
  Bool.bool_dec (ne_eqb_upto_proofs M M') true.


(** ** Notations *)
Module Nf_Notations.
  Notation "'Propⁿ'" := nf_prop : mctt_scope.
  Notation "'∀ₚⁿ' '{' κ '}' A P" := (nf_pi κ ak_propositional A P) (at level 2, κ at level 0, A at level 1, P at level 60) : mctt_scope.
  Notation "'Σₚⁿ' P Q" := (nf_and P Q) (at level 2, P at level 1, Q at level 60) : mctt_scope.
  Notation "'⊤ⁿ'" := nf_True : mctt_scope.
  Notation "'⊥ⁿ'" := nf_False : mctt_scope.
  Notation "'Typeωⁿ' @ n" := (nf_typ n) (at level 1, n at level 0, format "'Typeωⁿ' @ n") : mctt_scope.
  Notation "'univⁿ' c xs" := (nf_univ c xs) (at level 1, c at level 0, xs at level 0, format "'univⁿ'  c  xs") : mctt_scope.
  Notation "'Typeⁿ' @ n" := (nf_univ (ordinal_of_nat n) nil) (at level 1, n at level 0, format "'Typeⁿ' @ n") : mctt_scope.
  Notation "'Levelⁿ' @ n" := (nf_level n) (at level 1, n at level 0, format "'Levelⁿ' @ n") : mctt_scope.
  Notation "'Levelⁿ'" := (nf_level 0) : mctt_scope.
  Notation "'LevelSortⁿ'" := nf_level_sort : mctt_scope.
  Notation "'lvⁿ' c xs" := (nf_lvl c xs) (at level 1, c at level 0, xs at level 0, format "'lvⁿ'  c  xs") : mctt_scope.
  Notation "'λⁿ' A M" := (nf_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Πⁿ' '{' κ '}' A B" := (nf_pi κ ak_relevant A B) (at level 2, κ at level 0, A at level 1, B at level 60) : mctt_scope.
  Notation "'Πₗⁿ' A B" := (nf_pi ak_level ak_level A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'⇑ⁿ' M" := (nf_neut M) (at level 2, M at level 1, format "'⇑ⁿ'  M") : mctt_scope.
  Notation "'#ⁿ' n" := (ne_var n) (at level 1, n at level 0, format "'#ⁿ' n") : mctt_scope.
  Notation "M '$ⁿ' N" := (ne_app M N) (at level 10, left associativity, format "M  $ⁿ  N") : mctt_scope.
  Notation "'efqⁿ' M 'return' A" := (ne_absurd A M) (at level 2, M at level 60, A at level 60) : mctt_scope.
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
  | a_level_sort => a_level_sort
  | a_llit n => a_llit n
  | a_succl M => a_succl (exp_wk M φ)
  | a_maxl M N => a_maxl (exp_wk M φ) (exp_wk N φ)
  | a_prop => a_prop
  | a_True => a_True
  | a_tt => a_tt
  | a_False => a_False
  | a_absurd A M => a_absurd (exp_wk A φ) (exp_wk M φ)
  | a_and P Q => a_and (exp_wk P φ) (exp_wk Q (wk_q φ))
  | a_conj P Q M N => a_conj (exp_wk P φ) (exp_wk Q (wk_q φ)) (exp_wk M φ) (exp_wk N φ)
  | a_left M => a_left (exp_wk M φ)
  | a_right M => a_right (exp_wk M φ)
  | a_ind p k => a_ind p k
  | a_con p k c => a_con p k c
  | a_elim r pq Us m Bks M =>
      a_elim r pq (List.map (fun U => exp_wk U φ) Us) m
        (List.map (fun b =>
           match b with
           | eb_mk nm Z A Bs =>
               eb_mk nm (exp_wk Z (wk_qn (nm - 1) φ)) (exp_wk A (wk_qn nm φ))
                 (List.map (fun br => (fst br, exp_wk (snd br) (wk_qn (snd (fst br)) φ))) Bs)
           end) Bks)
        (exp_wk M φ)
  | a_pi κd κc A B => a_pi κd κc (exp_wk A φ) (exp_wk B (wk_q φ))
  | a_fn A M => a_fn (exp_wk A φ) (exp_wk M (wk_q φ))
  | a_app M N => a_app (exp_wk M φ) (exp_wk N φ)
  | a_var x => a_var (φ x)
  | a_let b B => a_let (binding_wk b φ) (exp_wk B (wk_q φ))
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
with binding_wk (b : binding) (φ : wk) : binding :=
  match b with
  | b_def A M => b_def (exp_wk A φ) (exp_wk M φ)
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
  | gm_open Φ H its Φg =>
      gm_open (gmod_wk Φ φ) (modexp_wk H (wk_qn (gm_binders Φ) φ)) its (gmod_wk Φg (wk_qn (gm_binders Φ) φ))
  end
with gentry_wk (E : gentry) (φ : wk) : gentry :=
  match E with
  | ge_def b pv r A B => ge_def b pv r (exp_wk A φ) (match B with Some M => Some (exp_wk M φ) | None => None end)
  | ge_mod pv U => ge_mod pv (gunit_wk U φ)
  | ge_ind pv p k D Φ => ge_ind pv p k D (gmod_wk Φ (wk_qn (ind_nu D) φ))
  | ge_def_mod pv A M U => ge_def_mod pv (exp_wk A φ) (exp_wk M φ) (gunit_wk U φ)
  | ge_record pv p R Φ => ge_record pv p R (gmod_wk Φ (wk_qn (S (List.length (record_params R))) φ))
  end
with centry_wk (e : centry) (φ : wk) : centry :=
  match e with
  | ce_ass κ A => ce_ass κ (exp_wk A φ)
  | ce_def A M => ce_def (exp_wk A φ) (exp_wk M φ)
  | ce_mod U => ce_mod (gunit_wk U φ)
  | ce_dm A M U => ce_dm (exp_wk A φ) (exp_wk M φ) (gunit_wk U φ)
  end.

(** ** The Scope of a Term

    [exp_free_bound M] is the least [k] such that every free index of [M]
    is below [k]: the number of environment positions the readback of a
    proof must bind so that the proof is copied as written.  A term under
    [n] binders has the bound of its body less [n]. *)
Fixpoint exp_free_bound (M : exp) : nat :=
  match M with
  | a_typ _ | a_level _ | a_level_sort | a_llit _ | a_prop | a_True | a_tt | a_False
  | a_ind _ _ | a_con _ _ _ | a_record _ => 0
  | a_univ t => exp_free_bound t
  | a_succl M | a_left M | a_right M | a_proj _ M => exp_free_bound M
  | a_maxl M N | a_absurd M N | a_app M N => Nat.max (exp_free_bound M) (exp_free_bound N)
  | a_and A B | a_pi _ _ A B | a_fn A B => Nat.max (exp_free_bound A) (exp_free_bound B - 1)
  | a_conj P Q M N =>
      Nat.max (Nat.max (exp_free_bound P) (exp_free_bound Q - 1)) (Nat.max (exp_free_bound M) (exp_free_bound N))
  | a_elim _ _ Us _ Bks M =>
      Nat.max (List.list_max (List.map exp_free_bound Us))
        (Nat.max (List.list_max (List.map (fun b =>
           match b with
           | eb_mk nm Z A Bs =>
               Nat.max (exp_free_bound Z - (nm - 1))
                 (Nat.max (exp_free_bound A - nm)
                    (List.list_max (List.map (fun br => exp_free_bound (snd br) - snd (fst br)) Bs)))
           end) Bks))
           (exp_free_bound M))
  | a_var x => S x
  | a_let b B => Nat.max (binding_free_bound b) (exp_free_bound B - 1)
  | a_mem H _ => modexp_free_bound H
  | a_tuple T fs => Nat.max (exp_free_bound T) (List.list_max (List.map (fun f => exp_free_bound (snd f)) fs))
  end
with modexp_free_bound (H : modexp) : nat :=
  match H with
  | me_unit _ => 0
  | me_var k => S k
  | me_mem H _ => modexp_free_bound H
  | me_app H N => Nat.max (modexp_free_bound H) (exp_free_bound N)
  | me_lit U => gunit_free_bound U
  end
with binding_free_bound (b : binding) : nat :=
  match b with
  | b_def A M => Nat.max (exp_free_bound A) (exp_free_bound M)
  | b_mod U => gunit_free_bound U
  end
with gunit_free_bound (U : gunit) : nat :=
  match U with
  | gu_mk Δ D =>
      Nat.max ((fix tele_free_bound (Δ : list centry) : nat :=
                  match Δ with
                  | nil => 0
                  | cons e Δ' => Nat.max (centry_free_bound e - List.length Δ') (tele_free_bound Δ')
                  end) Δ)
        (moddef_free_bound D - List.length Δ)
  end
with moddef_free_bound (D : moddef) : nat :=
  match D with
  | md_body _ Φ => gmod_free_bound Φ
  | md_alias E => modexp_free_bound E
  end
with gmod_free_bound (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ E => Nat.max (gmod_free_bound Φ) (gentry_free_bound E - gm_binders Φ)
  | gm_open Φ H _ Φg =>
      Nat.max (gmod_free_bound Φ) (Nat.max (modexp_free_bound H - gm_binders Φ) (gmod_free_bound Φg - gm_binders Φ))
  end
with gentry_free_bound (E : gentry) : nat :=
  match E with
  | ge_def _ _ _ A B => Nat.max (exp_free_bound A) (match B with Some M => exp_free_bound M | None => 0 end)
  | ge_mod _ U => gunit_free_bound U
  | ge_ind _ _ _ D Φ => gmod_free_bound Φ - ind_nu D
  | ge_def_mod _ A M U => Nat.max (exp_free_bound A) (Nat.max (exp_free_bound M) (gunit_free_bound U))
  | ge_record _ _ R Φ => gmod_free_bound Φ - S (List.length (record_params R))
  end
with centry_free_bound (e : centry) : nat :=
  match e with
  | ce_ass _ A => exp_free_bound A
  | ce_def A M => Nat.max (exp_free_bound A) (exp_free_bound M)
  | ce_mod U => gunit_free_bound U
  | ce_dm A M U => Nat.max (exp_free_bound A) (Nat.max (exp_free_bound M) (gunit_free_bound U))
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

    An entry of the wrong sort reads as a closed term, [Propₘ] or the
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

(** The term an entry gives a term variable. *)
Definition sentry_exp (e : sentry) : exp :=
  match e with
  | se_var x => a_var x
  | se_exp M => M
  (** A module entry gives a term variable [Propₘ], never a user term:
      only for totality of the read.  It must be a closed term, fixed by
      every substitution, so that evaluation commutes with substitution;
      it evaluates to what a module entry of an environment gives a term
      variable ([env_var]).  For example [(#0)[se_mod H .: σ]] is [Propₘ],
      which stays [Propₘ] under any further substitution; a variable
      would not: [#0[se_mod H .: σ][τ]] would be the entry [τ 0]. *)
  | se_mod _ => a_prop
  | se_dm N _ => N
  end.

(** The module expression an entry gives a module variable. *)
Definition sentry_modexp (e : sentry) : modexp :=
  match e with
  | se_var x => me_var x
  (** A term entry gives a module variable the empty unit, never a user
      module expression: only for totality of the read.  Like the term
      read of a module entry, it must be closed and fixed by every
      substitution, so that evaluation commutes with substitution. *)
  | se_exp _ => me_unit nil
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
  | a_level_sort => a_level_sort
  | a_llit n => a_llit n
  | a_succl M => a_succl (exp_sub M σ)
  | a_maxl M N => a_maxl (exp_sub M σ) (exp_sub N σ)
  | a_prop => a_prop
  | a_True => a_True
  | a_tt => a_tt
  | a_False => a_False
  | a_absurd A M => a_absurd (exp_sub A σ) (exp_sub M σ)
  | a_and P Q => a_and (exp_sub P σ) (exp_sub Q (sb_q σ))
  | a_conj P Q M N => a_conj (exp_sub P σ) (exp_sub Q (sb_q σ)) (exp_sub M σ) (exp_sub N σ)
  | a_left M => a_left (exp_sub M σ)
  | a_right M => a_right (exp_sub M σ)
  | a_ind p k => a_ind p k
  | a_con p k c => a_con p k c
  | a_elim r pq Us m Bks M =>
      a_elim r pq (List.map (fun U => exp_sub U σ) Us) m
        (List.map (fun b =>
           match b with
           | eb_mk nm Z A Bs =>
               eb_mk nm (exp_sub Z (sb_qn (nm - 1) σ)) (exp_sub A (sb_qn nm σ))
                 (List.map (fun br => (fst br, exp_sub (snd br) (sb_qn (snd (fst br)) σ))) Bs)
           end) Bks)
        (exp_sub M σ)
  | a_pi κd κc A B => a_pi κd κc (exp_sub A σ) (exp_sub B (sb_q σ))
  | a_fn A M => a_fn (exp_sub A σ) (exp_sub M (sb_q σ))
  | a_app M N => a_app (exp_sub M σ) (exp_sub N σ)
  | a_var x => sentry_exp (σ x)
  | a_let b B => a_let (binding_sub b σ) (exp_sub B (sb_q σ))
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
with binding_sub (b : binding) (σ : sub) : binding :=
  match b with
  | b_def A M => b_def (exp_sub A σ) (exp_sub M σ)
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
  | gm_open Φ H its Φg =>
      gm_open (gmod_sub Φ σ) (modexp_sub H (sb_qn (gm_binders Φ) σ)) its (gmod_sub Φg (sb_qn (gm_binders Φ) σ))
  end
with gentry_sub (E : gentry) (σ : sub) : gentry :=
  match E with
  | ge_def b pv r A B => ge_def b pv r (exp_sub A σ) (match B with Some M => Some (exp_sub M σ) | None => None end)
  | ge_mod pv U => ge_mod pv (gunit_sub U σ)
  | ge_ind pv p k D Φ => ge_ind pv p k D (gmod_sub Φ (sb_qn (ind_nu D) σ))
  | ge_def_mod pv A M U => ge_def_mod pv (exp_sub A σ) (exp_sub M σ) (gunit_sub U σ)
  | ge_record pv p R Φ => ge_record pv p R (gmod_sub Φ (sb_qn (S (List.length (record_params R))) σ))
  end
with centry_sub (e : centry) (σ : sub) : centry :=
  match e with
  | ce_ass κ A => ce_ass κ (exp_sub A σ)
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
    elaborator's [tele_pi]/[tele_fn], which work on [Cst.expression] and so cannot
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
    assumptions.  Each binder is at its assumption's kind, into the kind
    [κc] of the result. *)
Fixpoint ctx_pi_at (κc : abs_kind) (Δ : ctx) (A : typ) : typ :=
  match Δ with
  | nil => A
  | cons (ce_ass κ B) Δ' => ctx_pi_at κc Δ' (a_pi κ κc B A)
  | cons (ce_def B N) Δ' => ctx_pi_at κc Δ' (a_let (b_def B N) A)
  | cons (ce_mod U) Δ' => ctx_pi_at κc Δ' (a_let (b_mod U) A)
  | cons (ce_dm _ N U) Δ' => ctx_pi_at κc Δ' (exp_sub A (sb_extend sb_id (se_dm N (me_lit U))))
  end.

(** The type of functions over [Δ] into a type of a universe; over a
    proposition [ctx_pi_at ak_propositional] is the proposition
    universally quantified over [Δ], and into a type of levels
    [ctx_pi_at ak_level] the type of levels over [Δ]. *)
Abbreviation ctx_pi := (ctx_pi_at ak_relevant).

(** The [λ]-counterpart of [ctx_pi]. *)
Fixpoint ctx_fn (Δ : ctx) (M : exp) : exp :=
  match Δ with
  | nil => M
  | cons (ce_ass _ B) Δ' => ctx_fn Δ' (a_fn B M)
  | cons (ce_def B N) Δ' => ctx_fn Δ' (a_let (b_def B N) M)
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
