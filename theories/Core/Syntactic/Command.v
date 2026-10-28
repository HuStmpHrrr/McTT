(** * Commands

    The core commands a unit is elaborated into: names are resolved, and an
    import is a load and the declaration of its items.  Their meaning, as steps of
    the global state, is given in [Core.Syntactic.System.Command]. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** A group of inductive declarations as written ([core_cmd_inductive]): one type, or
    the types of a mutual block, in order.  The group's own uniform
    parameters [raw_decl_uparams] (innermost first, over the enclosing frames'
    parameters) are shared; each member has its name, its non-uniform
    parameters (innermost first, over the uniform ones), its sort (over the
    uniform ones; the members' sorts are one) and its constructors, each
    with its named arguments, outermost first.  An argument's type is over
    the arguments before it, all of them binders, then the member's
    parameters, then the declared types themselves, [Self_0] (outermost) …
    [Self_(n-1)], variables of types [Π (params). S] bound outside the
    parameters (but inside those of the enclosing frames): a recursive
    occurrence of the [j]-th type is [Self_j] at all its own parameters.
    The command classifies the arguments of each constructor on the normal
    forms of their types, and so finds the group's views, into the
    structural declaration it files. *)
Record raw_member : Set := mk_rmem
  { (** The member's name *)
    raw_member_name : string
    (** Its non-uniform parameters, innermost first *)
  ; raw_member_nparams : ctx
    (** Its sort, over the uniform parameters *)
  ; raw_member_sort : exp
    (** Its constructors, each with its named arguments, outermost
        first *)
  ; raw_member_cons : list (string * list (string * exp)) }.

(** A group as written: see [raw_member]. *)
Record raw_decl : Set := mk_raw
  { (** The group's own uniform parameters, innermost first *)
    raw_decl_uparams : ctx
    (** The declared members, in order *)
  ; raw_decl_members : list raw_member
    (** Whether the group files the recursor module [Rec] in its frame, as
        a group declared by [mutual T where] does *)
  ; raw_decl_rec_field : bool }.

(** A function of a [mutual def] as written ([core_cmd_mdef]): its name, its
    non-uniform parameters [ys] (innermost first, over the block's
    parameters [Δ]), the type of its scrutinee (over [ys]), its result type
    (over the scrutinee and [ys]) and its clauses, one per constructor of
    its member in order, each binding the non-uniform parameters, the
    arguments and the recursive results (over [Δ]). *)
Record raw_fun : Set := mk_rfun
  { (** The function's name *)
    raw_fun_name : string
    (** Its non-uniform parameters [ys], innermost first *)
  ; raw_fun_nparams : ctx
    (** The scrutinee's type, over [ys] *)
  ; raw_fun_scrut : exp
    (** The result type, over the scrutinee and [ys] *)
  ; raw_fun_res : exp
    (** The clauses: constructor name, number of binders, body *)
  ; raw_fun_clauses : list (string * nat * exp) }.


(** The core commands. *)
Inductive core_cmd : Set :=
(** [def x : A := M] and [axiom x : A]: transparency, privacy, type and
    body.  An axiom has no body; an [abstract] [def] is opaque, not
    bodiless. *)
| core_cmd_def : string -> bool -> bool -> typ -> option exp -> core_cmd
(** [module x (Δ) where cs end], private or not *)
| core_cmd_mod : string -> bool -> ctx -> list core_cmd -> core_cmd
(** [module x (Δ) := E]: an alias, under its own parameters, private or not. *)
| core_cmd_alias : string -> bool -> ctx -> modexp -> core_cmd
(** [core_cmd_load fp]: load the unit [fp] if it is not filed yet. *)
| core_cmd_load : path -> core_cmd
(** [core_cmd_open E items]: check that [E] is a module, and declare the items,
    as definitions and aliases of this frame. *)
| core_cmd_open : modexp -> list iitem -> core_cmd
(** [eval M], or [eval M : A] *)
| core_cmd_eval : exp -> option typ -> core_cmd
(** [inductive x (Δ) : S where | c … with y : T where | … end], private or
    not: the group as written, its parameters over those of the enclosing
    frames.  It makes an entry per declared type, each the module, over the
    uniform parameters, of the type's constructors (and the recursor). *)
| core_cmd_inductive : bool -> raw_decl -> core_cmd
(** [mutual def (Δ) f (ys) (z : Z) : A | … with g … end], abstract and
    private or not: one function per member of a group, in any order,
    each filed as the definition [λ Δ ys z. a_elim (Some pq) m Bks z] of
    the group's eliminator at its member [m]. *)
| core_cmd_mdef : bool -> bool -> ctx -> list raw_fun -> core_cmd
(** [builtin k := X]: the module [X], as written, is bound as the builtin
    [k]; the command resolves it to the inductive type it names. *)
| core_cmd_builtin : string -> modexp -> core_cmd
(** [inductive x (Δ) := X]: the inductive alias [x] of the inductive type
    the module [X], as written, names, under its own parameters [Δ]. *)
| core_cmd_inductive_alias : string -> bool -> ctx -> modexp -> core_cmd
(** [record x (Δ) := X]: the record alias [x] of the record type the
    module [X], as written, names, under its own parameters [Δ]. *)
| core_cmd_record_alias : string -> bool -> ctx -> modexp -> core_cmd
(** [record x (Δ) : S where f : T ; … with cs end], private or not: the
    record's own parameters [Δ], over those of the enclosing frames, its
    sort over them, its fields in order, each over the fields before it
    (innermost first) and the parameters, and the commands [cs] of its
    with-area, run in the record's module after its field definitions. *)
| core_cmd_record : string -> bool -> ctx -> typ -> list (string * typ) -> list core_cmd -> core_cmd
(** [core_cmd_gen c]: the command [c], generated by a declaration, not written.
    It is taken exactly as generated: it runs as [c] does, but none of
    what is done to written commands is done to it, since it is built
    from the typed, already filled declaration [D].  Its literals are not
    generated (a typed term has none) and its eliminators are not filled
    (its own carry their group and uniform parameters); and its privacy
    is not checked, since privacy is a check on what the user writes: the
    types a declaration generates may hold the normal forms of its
    argument types, which can name private members the declaration itself
    names only through public ones.  The elaborator never produces it
    ([ElabSpec.elab_spec_written]). *)
| core_cmd_gen : core_cmd -> core_cmd.

(** A written command: no generated command in it ([core_cmd_gen]), at any
    depth of nesting. *)
Fixpoint cmd_written (c : core_cmd) : Prop :=
  match c with
  | core_cmd_gen _ => False
  | core_cmd_mod _ _ _ cs => List.fold_right (fun c P => cmd_written c /\ P) True cs
  | core_cmd_record _ _ _ _ _ cs => List.fold_right (fun c P => cmd_written c /\ P) True cs
  | _ => True
  end.

(** Written commands, each. *)
Definition cmds_written (cs : list core_cmd) : Prop := List.Forall cmd_written cs.

Lemma cmd_written_mod : forall x pv Δ cs, cmd_written (core_cmd_mod x pv Δ cs) <-> cmds_written cs.
Proof.
  intros; cbn; unfold cmds_written; induction cs as [| c cs IH]; cbn;
    [ split; constructor | rewrite List.Forall_cons_iff, IH; reflexivity ].
Qed.

Lemma cmd_written_record : forall x pv Δ S fs cs, cmd_written (core_cmd_record x pv Δ S fs cs) <-> cmds_written cs.
Proof.
  intros; cbn; unfold cmds_written; induction cs as [| c cs IH]; cbn;
    [ split; constructor | rewrite List.Forall_cons_iff, IH; reflexivity ].
Qed.
(** A unit: its leading imports, its parameters, its body. *)
Definition cunit : Set := (list core_cmd * ctx * list core_cmd)%type.

(** A written unit: its leading imports and its body. *)
Definition unit_written (u : cunit) : Prop := let '(imps, _, cs) := u in cmds_written imps /\ cmds_written cs.

Definition prog_path (prg : Cst.prog) : path :=
  let '(_, (fp, _, _)) := prg in fp.
