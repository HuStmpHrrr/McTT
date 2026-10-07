From Stdlib Require Import Lia List Morphisms Relation_Definitions RelationClasses Setoid String Wf_nat.

From Mctt.Core Require Import Base.

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
    that of a global one. *)
Inductive obj : Set :=
(** [Type@i], a large universe *)
| typ : nat -> obj
(** [Type@{M}], the small universe at the level [M] *)
| suniv : obj -> obj
(** [Level], the type of universe levels *)
| level : obj
(** A level literal, written [<n>l] *)
| llit : nat -> obj
(** [succl M] *)
| succl : obj -> obj
(** [maxl M N] *)
| maxl : obj -> obj -> obj
(** [Nat] *)
| nat : obj
(** [zero], and the numerals *)
| zero : obj
(** [succ M] *)
| succ : obj -> obj
(** [rec M return x . A | zero => MZ | succ y, r => MS end] *)
| natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
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
(** A [::] path, hence at least two segments after a [var] *)
| glob : list string -> obj
(** [M.x]: a member of a module *)
| proj : obj -> string -> obj
(** [let d in M end], one declaration at a time *)
| letb : decl -> obj -> obj

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
| c_eval : obj -> option obj -> cmd.

(** The family is nested through [list], so its induction principle is written
    by hand: a parameter list and a command list carry [Forall] of their
    motives. *)
Section cst_mut_ind.
  Variables (Po : obj -> Prop) (Pd : decl -> Prop) (Pm : mdef -> Prop) (Pc : cmd -> Prop).

  Hypotheses
    (case_typ : forall n, Po (typ n))
    (case_suniv : forall o, Po o -> Po (suniv o))
    (case_level : Po level)
    (case_llit : forall n, Po (llit n))
    (case_succl : forall o, Po o -> Po (succl o))
    (case_maxl : forall o1 o2, Po o1 -> Po o2 -> Po (maxl o1 o2))
    (case_nat : Po nat)
    (case_zero : Po zero)
    (case_succ : forall o, Po o -> Po (succ o))
    (case_natrec : forall o1 x o2 o3 y z o4, Po o1 -> Po o2 -> Po o3 -> Po o4 -> Po (natrec o1 x o2 o3 y z o4))
    (case_true_ty : Po true_ty)
    (case_true_tm : Po true_tm)
    (case_false_ty : Po false_ty)
    (case_exfalso : forall o1 x o2, Po o1 -> Po o2 -> Po (exfalso o1 x o2))
    (case_pi : forall x o1 o2, Po o1 -> Po o2 -> Po (pi x o1 o2))
    (case_fn : forall x o1 o2, Po o1 -> Po o2 -> Po (fn x o1 o2))
    (case_app : forall o1 o2, Po o1 -> Po o2 -> Po (app o1 o2))
    (case_var : forall x, Po (var x))
    (case_glob : forall fp, Po (glob fp))
    (case_proj : forall o x, Po o -> Po (proj o x))
    (case_letb : forall d o, Pd d -> Po o -> Po (letb d o))
    (case_d_def : forall x oA o2, match oA with Some A => Po A | None => True end -> Po o2 -> Pd (d_def x oA o2))
    (case_d_mod : forall x ps md, List.Forall (fun p => Po (snd p)) ps -> Pm md -> Pd (d_mod x ps md))
    (case_md_where : forall cs, List.Forall Pc cs -> Pm (md_where cs))
    (case_md_alias : forall o, Po o -> Pm (md_alias o))
    (case_c_mod : forall pv x ps md, List.Forall (fun p => Po (snd p)) ps -> Pm md -> Pc (c_mod pv x ps md))
    (case_c_def : forall m x o1 o2, Po o1 -> Po o2 -> Pc (c_def m x o1 o2))
    (case_c_axiom : forall x o, Po o -> Pc (c_axiom x o))
    (case_c_import : forall fq, Pc (c_import fq))
    (case_c_open : forall fq ip args its, List.Forall Po args -> Pc (c_open fq ip args its))
    (case_c_error : forall e, Pc (c_error e))
    (case_c_eval : forall o oA, Po o -> match oA with Some A => Po A | None => True end -> Pc (c_eval o oA)).

  Fixpoint obj_mut (o : obj) : Po o :=
    match o with
    | typ n => case_typ n
    | suniv o => case_suniv o (obj_mut o)
    | level => case_level
    | llit n => case_llit n
    | succl o => case_succl o (obj_mut o)
    | maxl o1 o2 => case_maxl o1 o2 (obj_mut o1) (obj_mut o2)
    | nat => case_nat
    | zero => case_zero
    | succ o => case_succ o (obj_mut o)
    | natrec o1 x o2 o3 y z o4 => case_natrec o1 x o2 o3 y z o4 (obj_mut o1) (obj_mut o2) (obj_mut o3) (obj_mut o4)
    | true_ty => case_true_ty
    | true_tm => case_true_tm
    | false_ty => case_false_ty
    | exfalso o1 x o2 => case_exfalso o1 x o2 (obj_mut o1) (obj_mut o2)
    | pi x o1 o2 => case_pi x o1 o2 (obj_mut o1) (obj_mut o2)
    | fn x o1 o2 => case_fn x o1 o2 (obj_mut o1) (obj_mut o2)
    | app o1 o2 => case_app o1 o2 (obj_mut o1) (obj_mut o2)
    | var x => case_var x
    | glob fp => case_glob fp
    | proj o x => case_proj o x (obj_mut o)
    | letb d o => case_letb d o (decl_mut d) (obj_mut o)
    end
  with decl_mut (d : decl) : Pd d :=
    match d with
    | d_def x oA o2 =>
        case_d_def x oA o2
          (match oA as oA0 return match oA0 with Some A => Po A | None => True end with
           | Some A' => obj_mut A'
           | None => I
           end)
          (obj_mut o2)
    | d_mod x ps md =>
        case_d_mod x ps md
          ((fix go (ps : list (string * obj)) : List.Forall (fun p => Po (snd p)) ps :=
              match ps with
              | nil => List.Forall_nil _
              | p :: ps' => List.Forall_cons p (obj_mut (snd p)) (go ps')
              end) ps)
          (mdef_mut md)
    end
  with mdef_mut (md : mdef) : Pm md :=
    match md with
    | md_where cs =>
        case_md_where cs
          ((fix go (cs : list cmd) : List.Forall Pc cs :=
              match cs with
              | nil => List.Forall_nil _
              | c :: cs' => List.Forall_cons c (cmd_mut c) (go cs')
              end) cs)
    | md_alias o => case_md_alias o (obj_mut o)
    end
  with cmd_mut (c : cmd) : Pc c :=
    match c with
    | c_mod pv x ps md =>
        case_c_mod pv x ps md
          ((fix go (ps : list (string * obj)) : List.Forall (fun p => Po (snd p)) ps :=
              match ps with
              | nil => List.Forall_nil _
              | p :: ps' => List.Forall_cons p (obj_mut (snd p)) (go ps')
              end) ps)
          (mdef_mut md)
    | c_def m x o1 o2 => case_c_def m x o1 o2 (obj_mut o1) (obj_mut o2)
    | c_axiom x o => case_c_axiom x o (obj_mut o)
    | c_import fq => case_c_import fq
    | c_open fq ip args its =>
        case_c_open fq ip args its
          ((fix go (os : list obj) : List.Forall Po os :=
              match os with
              | nil => List.Forall_nil _
              | o :: os' => List.Forall_cons o (obj_mut o) (go os')
              end) args)
    | c_error e => case_c_error e
    | c_eval o oA =>
        case_c_eval o oA (obj_mut o)
          (match oA as oA0 return match oA0 with Some A => Po A | None => True end with
           | Some A' => obj_mut A'
           | None => I
           end)
    end.

  Theorem cst_mut_ind : (forall o, Po o) /\ (forall d, Pd d) /\ (forall md, Pm md) /\ (forall c, Pc c).
  Proof. repeat split; [ exact obj_mut | exact decl_mut | exact mdef_mut | exact cmd_mut ]. Qed.
End cst_mut_ind.

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

(** [axiom x : A] with the modifiers [m]: the axiom, or the rejection of
    [m]. *)
Definition axiom_cmd (m : mods) (x : string) (A : obj) : cmd :=
  if orb (md_private m) (md_abstract m) then c_error "axiom takes no modifiers" else c_axiom x A.

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

(** An abbreviation, not a definition: a rule keyed on [q_abs] then has a record
    literal in its conclusion, so inverting it yields equations that
    [discriminate] and [injection] see through. *)
Abbreviation q_abs fp ip := {| q_unit := fp; q_chain := ip |}.

(** A unit is named by a nonempty path, and a term by a nonempty member
    chain: a module is not an [exp] and has no type. *)
Definition qname_valid (p : qname) : Prop :=
  q_unit p <> nil /\ q_chain p <> nil.

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
Inductive exp : Set :=
(** A large universe: [a_typ n] is [Typeω+n].  It contains every small
    universe, and the large universes below it. *)
| a_typ : nat -> exp
(** A small universe, at a level: [a_univ t] is [Type@{t}].  The level is an
    arbitrary term of type [Level], so a universe may be indexed by a
    variable, which is what makes universe polymorphism plain [Π]. *)
| a_univ : exp -> exp
(** The type of universe levels.  Levels are ordinary terms: a function may
    take and return them, so universe polymorphism is plain [Π]. *)
| a_level : exp
(** A level literal: [a_llit n] is the [n]-th level, written [<n>l] in the
    surface syntax. *)
| a_llit : nat -> exp
(** The successor of a level *)
| a_succl : exp -> exp
(** The join of two levels *)
| a_maxl : exp -> exp -> exp
(** Natural numbers *)
| a_nat : exp
(** [zero] *)
| a_zero : exp
(** [succ M] *)
| a_succ : exp -> exp
(** [a_natrec A MZ MS M] eliminates [M] into the motive [A], which binds the
    scrutinee; [MS] binds the predecessor and the recursive result. *)
| a_natrec : exp -> exp -> exp -> exp -> exp
(** The unit type, with η *)
| a_True : exp
(** Its element *)
| a_true : exp
(** The empty type *)
| a_False : exp
(** [a_exfalso A M] eliminates [M] into the motive [A], which binds the
    scrutinee. *)
| a_exfalso : exp -> exp -> exp
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
(** A body *)
| md_body : gmod -> moddef
(** An alias of a module expression *)
| md_alias : modexp -> moddef
with gmod : Set :=
(** The empty body *)
| gm_nil : gmod
(** A named entry after the body before it *)
| gm_ext : gmod -> string -> gentry -> gmod
(** [gm_open Φ H items]: a local open, as the elaborator writes it.  It
    binds one index per item.  The core expands it into [gm_ext] entries
    before typing ([Imports]); no typing rule mentions it. *)
| gm_open : gmod -> modexp -> list iitem -> gmod
with gentry : Set :=
(** [ge_def b pv A B]: [b] says whether the definition is transparent, [pv]
    whether it is private, and [B] is [None] for an axiom.  A filed definition
    is closed; a definition of a local body is read in the body's context. *)
| ge_def : bool -> bool -> exp -> option exp -> gentry
(** [ge_mod pv U]: a submodule, private when [pv] *)
| ge_mod : bool -> gunit -> gentry
with centry : Set :=
(** An assumption of a type *)
| ce_ass : exp -> centry
(** [ce_def A M]: a definition of type [A] *)
| ce_def : exp -> exp -> centry
(** A module slot, holding the unit *)
| ce_mod : gunit -> centry.

Abbreviation typ := exp.

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
    (case_level : Pe a_level)
    (case_llit : forall n, Pe (a_llit n))
    (case_succl : forall M, Pe M -> Pe (a_succl M))
    (case_maxl : forall M N, Pe M -> Pe N -> Pe (a_maxl M N))
    (case_nat : Pe a_nat)
    (case_zero : Pe a_zero)
    (case_succ : forall M, Pe M -> Pe (a_succ M))
    (case_natrec : forall A MZ MS M, Pe A -> Pe MZ -> Pe MS -> Pe M -> Pe (a_natrec A MZ MS M))
    (case_True : Pe a_True)
    (case_true : Pe a_true)
    (case_False : Pe a_False)
    (case_exfalso : forall A M, Pe A -> Pe M -> Pe (a_exfalso A M))
    (case_pi : forall A B, Pe A -> Pe B -> Pe (a_pi A B))
    (case_fn : forall A M, Pe A -> Pe M -> Pe (a_fn A M))
    (case_app : forall M N, Pe M -> Pe N -> Pe (a_app M N))
    (case_var : forall x, Pe (a_var x))
    (case_let : forall b B, Pb b -> Pe B -> Pe (a_let b B))
    (case_mem : forall H x, Pm H -> Pe (a_mem H x))
    (case_me_unit : forall fp, Pm (me_unit fp))
    (case_me_var : forall k, Pm (me_var k))
    (case_me_mem : forall H y, Pm H -> Pm (me_mem H y))
    (case_me_app : forall H N, Pm H -> Pe N -> Pm (me_app H N))
    (case_me_lit : forall U, Pu U -> Pm (me_lit U))
    (case_b_def : forall oA M, (forall A, oA = Some A -> Pe A) -> Pe M -> Pb (b_def oA M))
    (case_b_mod : forall U, Pu U -> Pb (b_mod U))
    (case_gu_mk : forall Δ D, List.Forall Pc Δ -> Pd D -> Pu (gu_mk Δ D))
    (case_md_body : forall Φ, Pg Φ -> Pd (md_body Φ))
    (case_md_alias : forall E, Pm E -> Pd (md_alias E))
    (case_gm_nil : Pg gm_nil)
    (case_gm_ext : forall Φ x E, Pg Φ -> Pn E -> Pg (gm_ext Φ x E))
    (case_gm_open : forall Φ H its, Pg Φ -> Pm H -> Pg (gm_open Φ H its))
    (case_ge_def : forall b pv A B, Pe A -> (forall M, B = Some M -> Pe M) -> Pn (ge_def b pv A B))
    (case_ge_mod : forall pv U, Pu U -> Pn (ge_mod pv U))
    (case_ce_ass : forall A, Pe A -> Pc (ce_ass A))
    (case_ce_def : forall A M, Pe A -> Pe M -> Pc (ce_def A M))
    (case_ce_mod : forall U, Pu U -> Pc (ce_mod U)).

  Fixpoint exp_mut (M : exp) : Pe M :=
    match M with
    | a_typ i => case_typ i
    | a_univ t => case_univ t (exp_mut t)
    | a_level => case_level
    | a_llit n => case_llit n
    | a_succl M => case_succl M (exp_mut M)
    | a_maxl M N => case_maxl M N (exp_mut M) (exp_mut N)
    | a_nat => case_nat
    | a_zero => case_zero
    | a_succ M => case_succ M (exp_mut M)
    | a_natrec A MZ MS M => case_natrec A MZ MS M (exp_mut A) (exp_mut MZ) (exp_mut MS) (exp_mut M)
    | a_True => case_True
    | a_true => case_true
    | a_False => case_False
    | a_exfalso A M => case_exfalso A M (exp_mut A) (exp_mut M)
    | a_pi A B => case_pi A B (exp_mut A) (exp_mut B)
    | a_fn A M => case_fn A M (exp_mut A) (exp_mut M)
    | a_app M N => case_app M N (exp_mut M) (exp_mut N)
    | a_var x => case_var x
    | a_let b B => case_let b B (bnd_mut b) (exp_mut B)
    | a_mem H x => case_mem H x (modexp_mut H)
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
    | md_body Φ => case_md_body Φ (gmod_mut Φ)
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
    end
  with centry_mut (e : centry) : Pc e :=
    match e with
    | ce_ass A => case_ce_ass A (exp_mut A)
    | ce_def A M => case_ce_def A M (exp_mut A) (exp_mut M)
    | ce_mod U => case_ce_mod U (gunit_mut U)
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
  | nil => a_zero
  | x :: nil => a_mem H x
  | y :: ch' => member_ref (me_mem H y) ch'
  end.

(** The module named [X::Y.W.Z], [q_abs ["X"; "Y"] ["W"; "Z"]], and the global
    named so, both as selections from the unit. *)
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
Abbreviation gu_body Δ Φ := (gu_mk Δ (md_body Φ)).
Abbreviation ge_body pv Δ Φ := (ge_mod pv (gu_body Δ Φ)).

Definition gu_params (U : gunit) : list centry := match U with gu_mk Δ _ => Δ end.

Definition gu_def (U : gunit) : moddef := match U with gu_mk _ D => D end.

(** The body of a body unit, and the empty body for an alias. *)
Definition gu_mod (U : gunit) : gmod :=
  match U with
  | gu_mk _ (md_body Φ) => Φ
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

(** ** Numerals *)

Fixpoint nat_to_exp n : exp :=
  match n with
  | 0 => a_zero
  | S m => a_succ (nat_to_exp m)
  end.
Definition num_to_exp n := nat_to_exp (Nat.of_num_uint n).

Fixpoint exp_to_nat e : option nat :=
  match e with
  | a_zero => Some 0
  | a_succ e' =>
      match exp_to_nat e' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.
Definition exp_to_num e :=
  match exp_to_nat e with
  | Some n => Some (Nat.to_num_uint n)
  | None => None
  end.

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
  Notation "'Type' @ n" := (a_typ n) (at level 1, n at level 0, format "'Type' @ n") : mctt_scope.
  (** A small universe at an arbitrary level term, and — for a literal level —
      the short form the stage-1 rules are written with. *)
  Notation "'Typeˢ' ⟨ t ⟩" := (a_univ t) (at level 0, t at level 99, format "'Typeˢ' ⟨ t ⟩") : mctt_scope.
  Notation "'Typeˢ' @ n" := (a_univ (a_llit n)) (at level 1, n at level 0, format "'Typeˢ' @ n") : mctt_scope.
  Notation "'Level'" := a_level : mctt_scope.
  (** The level literals: [𝕃@n] is the surface syntax's [<n>l].  The token is
      not a word: [lv] would make every identifier of that name a keyword. *)
  Notation "'𝕃' @ n" := (a_llit n) (at level 1, n at level 0, format "'𝕃' @ n") : mctt_scope.
  Notation "'succl' M" := (a_succl M) (at level 2, M at level 1) : mctt_scope.
  Notation "'maxl' M N" := (a_maxl M N) (at level 2, M at level 1, N at level 1) : mctt_scope.
  Notation "'#' n" := (a_var n) (at level 1, n at level 0, format "'#' n") : mctt_scope.
  Notation "'ℕ'" := a_nat : mctt_scope.
  Notation "'zero'" := a_zero : mctt_scope.
  Notation "'succ' M" := (a_succ M) (at level 2, M at level 1) : mctt_scope.
  Notation "'λ' A M" := (a_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Π' A B" := (a_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'ℓ' A ≔ M 'in' B" := (a_let (b_def (Some A) M) B) (at level 2, A at level 1, M at level 60, B at level 60) : mctt_scope.
  Notation "'ℓ' ≔ M 'in' B" := (a_let (b_def None M) B) (at level 2, M at level 60, B at level 60) : mctt_scope.
  Notation "'ℓₘ' U 'in' B" := (a_let (b_mod U) B) (at level 2, U at level 1, B at level 60) : mctt_scope.
  Notation "'rec' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (a_natrec A MZ MS M) (at level 0, M at level 60, A at level 60, MZ at level 60, MS at level 60) : mctt_scope.
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

(** The type of an entry; a module slot has none, and reads as [⊤]. *)
Definition ce_typ (e : centry) : typ :=
  match e with
  | ce_ass A | ce_def A _ => A
  | ce_mod _ => a_True
  end.

(** A body as the context entries it binds, innermost first.  A local open
    binds one placeholder per item: a pre-form is never typed. *)
Fixpoint body_ctx (Φ : gmod) : ctx :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' _ (ge_def _ _ A (Some M)) => cons (ce_def A M) (body_ctx Φ')
  | gm_ext Φ' _ (ge_def _ _ A None) => cons (ce_ass A) (body_ctx Φ')
  | gm_ext Φ' _ (ge_mod _ U) => cons (ce_mod U) (body_ctx Φ')
  | gm_open Φ' _ its => List.repeat (ce_ass a_nat) (List.length its) ++ body_ctx Φ'
  end.

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
    does with [Let], and a module slot as a local module.  The elaborator only
    builds parameter telescopes of assumptions. *)
Fixpoint ctx_pi (Δ : ctx) (A : typ) : typ :=
  match Δ with
  | nil => A
  | cons (ce_ass B) Δ' => ctx_pi Δ' (a_pi B A)
  | cons (ce_def B N) Δ' => ctx_pi Δ' (a_let (b_def (Some B) N) A)
  | cons (ce_mod U) Δ' => ctx_pi Δ' (a_let (b_mod U) A)
  end.

Fixpoint ctx_fn (Δ : ctx) (M : exp) : exp :=
  match Δ with
  | nil => M
  | cons (ce_ass B) Δ' => ctx_fn Δ' (a_fn B M)
  | cons (ce_def B N) Δ' => ctx_fn Δ' (a_let (b_def (Some B) N) M)
  | cons (ce_mod U) Δ' => ctx_fn Δ' (a_let (b_mod U) M)
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
End Ctx_Notations.

(** * Universe Indices

    The universes of the model form two tiers, both of them families indexed
    by a natural number:

    - the small tier [us j], whose universes are the small universes
      [𝕌ˢ@m] for [m < j];
    - the large tier [ul n] (the syntactic [Type@n], read as [Typeω+n]),
      whose universes are every small universe and the large ones [𝕌@m] for
      [m < n].

    Every small index is below every large one.  The large tier is the
    default: [ul] is a coercion, so [per_univ_elem i] for a level [i] is the
    large universe [Typeω+i]. *)
Inductive uidx : Set :=
| us : nat -> uidx
| ul : nat -> uidx.

Coercion ul : nat >-> uidx.

Definition uidx_lt (u v : uidx) : Prop :=
  match u, v with
  | us j, us k => j < k
  | us _, ul _ => True
  | ul _, us _ => False
  | ul j, ul k => j < k
  end.

Definition uidx_le (u v : uidx) : Prop :=
  match u, v with
  | us j, us k => j <= k
  | us _, ul _ => True
  | ul _, us _ => False
  | ul j, ul k => j <= k
  end.

Lemma uidx_lt_le_trans : forall u v w, uidx_lt u v -> uidx_le v w -> uidx_lt u w.
Proof. intros [] [] []; cbn; intros; auto; lia. Qed.

Lemma uidx_le_refl : forall u, uidx_le u u.
Proof. intros []; cbn; lia. Qed.

Lemma uidx_le_trans : forall u v w, uidx_le u v -> uidx_le v w -> uidx_le u w.
Proof. intros [] [] []; cbn; intros; auto; lia. Qed.

Lemma uidx_lt_le : forall u v, uidx_lt u v -> uidx_le u v.
Proof. intros [] []; cbn; intros; auto; lia. Qed.

Lemma uidx_wf : well_founded uidx_lt.
Proof.
  assert (Hs : forall j, Acc uidx_lt (us j)).
  { induction j as [j IH] using lt_wf_ind; constructor; intros [k | k] Hk; cbn in Hk; [ apply IH; exact Hk | contradiction ]. }
  intros [j | n]; [ apply Hs |].
  induction n as [n IH] using lt_wf_ind; constructor; intros [k | k] Hk; cbn in Hk; [ apply Hs | apply IH; exact Hk ].
Qed.

(** ** Universes at Any Index, as Terms and Values

    A judgment in a universe is the four-value pattern of its two sides in the
    universe's element PER, whichever tier the universe is in.  The lemmas
    are stated at an index [u], through the universe's term [ulvl_tm u] and
    value [ulvl_val u]; the large forms below are their instances at [ul i],
    which is [Type@i] by computation. *)
Definition ulvl_tm (u : uidx) : exp :=
  match u with us n => a_univ (a_llit n) | ul n => a_typ n end.

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

(** The least index: [Typeˢ@0] is below every universe. *)
Lemma uidx_le_least : forall u, uidx_le (us 0) u.
Proof. intros []; cbn; [ lia | exact I ]. Qed.

(** The large levels of two ordered indices are ordered: a small universe
    lives in [Type@0], and the large tier's order is the order on levels. *)
Lemma uidx_le_ulvl_le : forall u v, uidx_le u v -> ulvl u <= ulvl v.
Proof. intros [] []; cbn; intros; lia. Qed.

(** The join of two indices: a large universe absorbs a small one. *)
Definition umax (u v : uidx) : uidx :=
  match u, v with
  | us n, us m => us (max n m)
  | us _, ul i => ul i
  | ul i, us _ => ul i
  | ul i, ul j => ul (max i j)
  end.

Lemma uidx_le_umax_left : forall u v, uidx_le u (umax u v).
Proof. intros [] []; cbn; try exact I; lia. Qed.

Lemma uidx_le_umax_right : forall u v, uidx_le v (umax u v).
Proof. intros [] []; cbn; try exact I; lia. Qed.

Lemma umax_lub : forall u v w, uidx_le u w -> uidx_le v w -> uidx_le (umax u v) w.
Proof. intros [] [] []; cbn; intros; try contradiction; try exact I; lia. Qed.

(** Discharges the order side conditions between universe indices. *)
Ltac solve_uidx :=
  first [ assumption | exact I | solve [ cbn [uidx_lt uidx_le] in *; lia ]
        | solve [ repeat match goal with k : uidx |- _ => destruct k end;
                  cbn [uidx_lt uidx_le] in *; first [ contradiction | exact I | lia ] ] ].


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

Definition lvl_exp_of (c : nat) (xs : list (nat * exp)) : exp :=
  match xs, c with
  | nil, _ => a_llit c
  | (k, a) :: r, 0 => lvl_fold (succl_n k a) r
  | (k, a) :: r, S _ => lvl_fold (a_maxl (a_llit c) (succl_n k a)) r
  end.

(** * Normal and Neutral Forms *)
Inductive nf : Set :=
(** A large universe *)
| nf_typ : nat -> nf
(** A small universe at a canonical level [max (c, k₁ + a₁, …)], in the shape
    of [nf_lvl] below *)
| nf_univ : nat -> lvl_atoms -> nf
(** The type [Level] *)
| nf_level : nf
(** A canonical level [max (c, k₁ + a₁, …)]: the atoms are strictly sorted by
    [ne_cmp] (see [Core.Syntactic.Levels]) with no repetition, and the
    constant [c] is [0] unless it exceeds every offset.  [nf_lvl_of] builds
    the normal form of a canonical level [lvl]. *)
| nf_lvl : nat -> lvl_atoms -> nf
(** [ℕ] *)
| nf_nat : nf
(** [zero] *)
| nf_zero : nf
(** [succ] of a normal form *)
| nf_succ : nf -> nf
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
(** A neutral *)
| nf_neut : ne -> nf
with ne : Set :=
(** The [ℕ]-eliminator stuck on a neutral *)
| ne_natrec : nf -> nf -> nf -> ne -> ne
(** The [⊥]-eliminator, always stuck *)
| ne_exfalso : nf -> ne -> ne
(** A neutral applied *)
| ne_app : ne -> nf -> ne
(** A variable *)
| ne_var : nat -> ne
(** An opaque definition or an axiom: it does not unfold. *)
| ne_glob : qname -> ne
(** The atoms of a canonical level, each with its offset.  They are their own
    sort rather than a [list (nat * ne)] so that the family stays mutual and
    [Scheme] generates the induction principle. *)
with lvl_atoms : Set :=
| la_nil : lvl_atoms
| la_cons : nat -> ne -> lvl_atoms -> lvl_atoms
.

Fixpoint nf_to_exp (M : nf) : exp :=
  match M with
  | nf_typ i => a_typ i
  | nf_univ c xs => a_univ (lvl_exp_of c (la_to_list xs))
  | nf_level => a_level
  | nf_lvl c xs => lvl_exp_of c (la_to_list xs)
  | nf_nat => a_nat
  | nf_zero => a_zero
  | nf_succ M => a_succ (nf_to_exp M)
  | nf_True => a_True
  | nf_true => a_true
  | nf_False => a_False
  | nf_pi A B => a_pi (nf_to_exp A) (nf_to_exp B)
  | nf_fn A M => a_fn (nf_to_exp A) (nf_to_exp M)
  | nf_neut M => ne_to_exp M
  end
with ne_to_exp (M : ne) : exp :=
  match M with
  | ne_natrec A MZ MS M => a_natrec (nf_to_exp A) (nf_to_exp MZ) (nf_to_exp MS) (ne_to_exp M)
  | ne_exfalso A M => a_exfalso (nf_to_exp A) (ne_to_exp M)
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_var x => a_var x
  | ne_glob p => qname_term p
  end
with la_to_list (xs : lvl_atoms) : list (nat * exp) :=
  match xs with
  | la_nil => nil
  | la_cons k M r => (k, ne_to_exp M) :: la_to_list r
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

(** * Canonical Levels

    A canonical level is its constant and its atoms.  The operations on
    canonical levels, and their order, are [Core.Syntactic.Levels]; the type
    is here because the universe normal forms below are indexed by it. *)
Definition lvl : Set := (nat * lvl_atoms)%type.

Definition nf_lvl_of (l : lvl) : nf := nf_lvl (fst l) (snd l).

Definition nf_univ_of (l : lvl) : nf := nf_univ (fst l) (snd l).

Lemma nf_lvl_of_inj : forall l l', nf_lvl_of l = nf_lvl_of l' -> l = l'.
Proof.
  intros [c xs] [d ys] H; unfold nf_lvl_of in H; cbn in H.
  inversion H; reflexivity.
Qed.

Lemma nf_univ_of_cong : forall l l', nf_lvl_of l = nf_lvl_of l' -> nf_univ_of l = nf_univ_of l'.
Proof. intros ? ? H; apply nf_lvl_of_inj in H as ->; reflexivity. Qed.

Lemma nf_univ_of_inj : forall l l', nf_univ_of l = nf_univ_of l' -> l = l'.
Proof.
  intros [c xs] [d ys] H; unfold nf_univ_of in H; cbn in H.
  inversion H; reflexivity.
Qed.

(** * Universe Normal Forms

    The universe a type is inferred at, as the algorithmic layer sees it: a
    small universe at a canonical level, or a large one.  It is not the
    semantic index [uidx]: a small universe's semantic index is the realiser
    of its level, a natural number, while the checker compares the canonical
    levels themselves (see [Core.Syntactic.Levels]: [unf_le], [unf_max]). *)
Inductive unf : Set :=
(** A small universe at a canonical level *)
| uns : lvl -> unf
(** The large universe [Typeω+n] *)
| unl : nat -> unf.

Coercion unl : nat >-> unf.

(** The universe normal form itself, and the term it embeds to. *)
Definition univ_nf (u : unf) : nf :=
  match u with uns L => nf_univ_of L | unl n => nf_typ n end.

Definition unf_tm (u : unf) : exp :=
  match u with
  | uns L => a_univ (lvl_exp_of (fst L) (la_to_list (snd L)))
  | unl n => a_typ n
  end.

Lemma nf_to_exp_univ_nf : forall u, nf_to_exp (univ_nf u) = unf_tm u.
Proof. intros [[] |]; reflexivity. Qed.

(** That a normal form is a universe.  This is the side condition of every
    algorithmic rule that asks for a type.  It is a relation and not the
    equation [univ_nf_idx W = Some u] of the deciding function below: the
    left-hand side of that equation is a [match] stuck on [W], and
    [progressive_inversion] does not terminate on such a hypothesis — it
    inverts it to an equation of the same shape, for ever. *)
Variant is_univ_nf : nf -> unf -> Prop :=
| isu_typ : forall i, is_univ_nf (nf_typ i) (unl i)
| isu_univ : forall c xs, is_univ_nf (nf_univ c xs) (uns (c, xs)).

Lemma is_univ_nf_univ_nf : forall u, is_univ_nf (univ_nf u) u.
Proof. intros [[] |]; constructor. Qed.

Lemma is_univ_nf_eq : forall W u, is_univ_nf W u -> W = univ_nf u.
Proof. intros ? ? H; destruct H; reflexivity. Qed.

Lemma is_univ_nf_functional : forall W u v, is_univ_nf W u -> is_univ_nf W v -> u = v.
Proof. intros ? ? ? H H'; destruct H; inversion H'; reflexivity. Qed.

(** The universe itself, as the deciding function the checker runs.  It is
    used in the checker's code, never as an index or a side condition of a
    rule. *)
Definition univ_nf_idx (W : nf) : option unf :=
  match W with nf_typ i => Some (unl i) | nf_univ c xs => Some (uns (c, xs)) | _ => None end.

Lemma univ_nf_idx_is_univ_nf : forall W u, univ_nf_idx W = Some u -> is_univ_nf W u.
Proof. intros [] ? H; cbn in H; inversion H; constructor. Qed.

Lemma univ_nf_idx_none : forall W u, univ_nf_idx W = None -> ~ is_univ_nf W u.
Proof. intros [] ? H Hu; cbn in H; try discriminate; inversion Hu. Qed.

(** A normal form with no global at the head of a neutral. *)

Fixpoint nf_clean (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_level | nf_nat | nf_zero | nf_True | nf_true | nf_False => True
  | nf_univ _ xs | nf_lvl _ xs => la_clean xs
  | nf_succ W => nf_clean W
  | nf_pi A B | nf_fn A B => nf_clean A /\ nf_clean B
  | nf_neut M => ne_clean M
  end
with ne_clean (M : ne) : Prop :=
  match M with
  | ne_natrec A MZ MS M => nf_clean A /\ nf_clean MZ /\ nf_clean MS /\ ne_clean M
  | ne_exfalso A M => nf_clean A /\ ne_clean M
  | ne_app M N => ne_clean M /\ nf_clean N
  | ne_var _ => True
  | ne_glob _ => False
  end
with la_clean (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ M r => ne_clean M /\ la_clean r
  end.

Fact nf_eq_dec : forall (M M' : nf),
    ({M = M'} + {M <> M'})%type
with ne_eq_dec : forall (M M' : ne),
    ({M = M'} + {M <> M'})%type
with la_eq_dec : forall (xs xs' : lvl_atoms),
    ({xs = xs'} + {xs <> xs'})%type.
Proof.
  all: intros; decide equality;
    repeat (apply PeanoNat.Nat.eq_dec || decide equality || apply String.string_dec).
Defined.

(** ** Notations *)
Module Nf_Notations.
  Notation "'ℕⁿ'" := nf_nat : mctt_scope.
  Notation "'zeroⁿ'" := nf_zero : mctt_scope.
  Notation "'succⁿ' M" := (nf_succ M) (at level 2, M at level 1) : mctt_scope.
  Notation "'⊤ⁿ'" := nf_True : mctt_scope.
  Notation "'⋆ⁿ'" := nf_true : mctt_scope.
  Notation "'⊥ⁿ'" := nf_False : mctt_scope.
  Notation "'Typeⁿ' @ n" := (nf_typ n) (at level 1, n at level 0, format "'Typeⁿ' @ n") : mctt_scope.
  Notation "'univⁿ' c xs" := (nf_univ c xs) (at level 1, c at level 0, xs at level 0, format "'univⁿ'  c  xs") : mctt_scope.
  Notation "'Typeˢⁿ' @ n" := (nf_univ n la_nil) (at level 1, n at level 0, format "'Typeˢⁿ' @ n") : mctt_scope.
  Notation "'Levelⁿ'" := nf_level : mctt_scope.
  Notation "'lvⁿ' c xs" := (nf_lvl c xs) (at level 1, c at level 0, xs at level 0, format "'lvⁿ'  c  xs") : mctt_scope.
  Notation "'λⁿ' A M" := (nf_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Πⁿ' A B" := (nf_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'⇑ⁿ' M" := (nf_neut M) (at level 2, M at level 1, format "'⇑ⁿ'  M") : mctt_scope.
  Notation "'#ⁿ' n" := (ne_var n) (at level 1, n at level 0, format "'#ⁿ' n") : mctt_scope.
  Notation "M '$ⁿ' N" := (ne_app M N) (at level 10, left associativity, format "M  $ⁿ  N") : mctt_scope.
  Notation "'recⁿ' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (ne_natrec A MZ MS M) (at level 0, M at level 60, A at level 60, MZ at level 60, MS at level 60) : mctt_scope.
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
  | a_level => a_level
  | a_llit n => a_llit n
  | a_succl M => a_succl (exp_wk M φ)
  | a_maxl M N => a_maxl (exp_wk M φ) (exp_wk N φ)
  | a_nat => a_nat
  | a_zero => a_zero
  | a_succ M => a_succ (exp_wk M φ)
  | a_natrec A MZ MS M =>
      a_natrec (exp_wk A (wk_q φ))
               (exp_wk MZ φ)
               (exp_wk MS (wk_q (wk_q φ)))
               (exp_wk M φ)
  | a_True => a_True
  | a_true => a_true
  | a_False => a_False
  | a_exfalso A M => a_exfalso (exp_wk A (wk_q φ)) (exp_wk M φ)
  | a_pi A B => a_pi (exp_wk A φ) (exp_wk B (wk_q φ))
  | a_fn A M => a_fn (exp_wk A φ) (exp_wk M (wk_q φ))
  | a_app M N => a_app (exp_wk M φ) (exp_wk N φ)
  | a_var x => a_var (φ x)
  | a_let b B => a_let (bnd_wk b φ) (exp_wk B (wk_q φ))
  | a_mem H x => a_mem (modexp_wk H φ) x
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
  | md_body Φ => md_body (gmod_wk Φ φ)
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
  end
with centry_wk (e : centry) (φ : wk) : centry :=
  match e with
  | ce_ass A => ce_ass (exp_wk A φ)
  | ce_def A M => ce_def (exp_wk A φ) (exp_wk M φ)
  | ce_mod U => ce_mod (gunit_wk U φ)
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

    An entry of the wrong sort reads as a closed default, [a_zero] or the
    module [me_unit nil], which every operation fixes.  The
    defaults are the semantic projections of an entry of the other sort, so
    evaluation commutes with every substitution. *)
Inductive sentry : Set :=
(** A variable of either sort *)
| se_var : nat -> sentry
(** A term, for a term variable *)
| se_exp : exp -> sentry
(** A module expression, for a module slot *)
| se_mod : modexp -> sentry.

Definition sub : Set := nat -> sentry.

Definition exp_junk : exp := a_zero.
Definition modexp_junk : modexp := me_unit nil.

Definition sentry_exp (e : sentry) : exp :=
  match e with
  | se_var x => a_var x
  | se_exp M => M
  | se_mod _ => exp_junk
  end.

Definition sentry_modexp (e : sentry) : modexp :=
  match e with
  | se_var x => me_var x
  | se_exp _ => modexp_junk
  | se_mod H => H
  end.

Definition sentry_wk (e : sentry) (φ : wk) : sentry :=
  match e with
  | se_var x => se_var (φ x)
  | se_exp M => se_exp (exp_wk M φ)
  | se_mod H => se_mod (modexp_wk H φ)
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
  | a_level => a_level
  | a_llit n => a_llit n
  | a_succl M => a_succl (exp_sub M σ)
  | a_maxl M N => a_maxl (exp_sub M σ) (exp_sub N σ)
  | a_nat => a_nat
  | a_zero => a_zero
  | a_succ M => a_succ (exp_sub M σ)
  | a_natrec A MZ MS M =>
      a_natrec (exp_sub A (sb_q σ))
               (exp_sub MZ σ)
               (exp_sub MS (sb_q (sb_q σ)))
               (exp_sub M σ)
  | a_True => a_True
  | a_true => a_true
  | a_False => a_False
  | a_exfalso A M => a_exfalso (exp_sub A (sb_q σ)) (exp_sub M σ)
  | a_pi A B => a_pi (exp_sub A σ) (exp_sub B (sb_q σ))
  | a_fn A M => a_fn (exp_sub A σ) (exp_sub M (sb_q σ))
  | a_app M N => a_app (exp_sub M σ) (exp_sub N σ)
  | a_var x => sentry_exp (σ x)
  | a_let b B => a_let (bnd_sub b σ) (exp_sub B (sb_q σ))
  | a_mem H x => a_mem (modexp_sub H σ) x
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
  | md_body Φ => md_body (gmod_sub Φ σ)
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
  end
with centry_sub (e : centry) (σ : sub) : centry :=
  match e with
  | ce_ass A => ce_ass (exp_sub A σ)
  | ce_def A M => ce_def (exp_sub A σ) (exp_sub M σ)
  | ce_mod U => ce_mod (gunit_sub U σ)
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
    parameters are bound last, so they come first. *)
Definition gstack : Set := list (qname * gunit).

Fixpoint gs_tele (Ξ : gstack) : ctx :=
  match Ξ with
  | nil => nil
  | (_, U) :: Ξ' => gu_params U ++ gs_tele Ξ'
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

(** The notations of terms, contexts, normal forms and substitutions. *)
Module Syntax_Notations.
  Export Exp_Notations Ctx_Notations Nf_Notations Sub_Notations.
End Syntax_Notations.
