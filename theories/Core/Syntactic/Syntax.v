From Stdlib Require Import List Morphisms Relation_Definitions RelationClasses Setoid String.

From Mctt.Core Require Import Base.

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

(** ** Import Specifications

    What an [import] brings into scope.  [i_open] makes the module reachable
    under its full path, [i_as] additionally binds a short alias, and [i_use]
    binds the listed members directly.  The names an [import] [use]s are
    checked by the core: each must be a public definition or a submodule of
    the imported module. *)
Inductive ispec : Set :=
| i_open : ispec
| i_as : string -> ispec
| i_use : list string -> ispec.

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
    import target are modules, everything else is a term.

    [letb] binds one declaration at a time; the parser folds the bindings of
    [let x : A := a; y : B := b in body end] into nested [letb]s.

    A module declaration has one shape at the top level and in a [let]: its
    parameters, and its definition [mdef], a body [where cmds end] or an
    alias [:= E].  The body of a local module is the same list of commands as
    that of a global one. *)
Inductive obj : Set :=
| typ : nat -> obj
| nat : obj
| zero : obj
| succ : obj -> obj
| natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
| true_ty : obj
| true_tm : obj
| false_ty : obj
| exfalso : obj -> string -> obj -> obj
| pi : string -> obj -> obj -> obj
| fn : string -> obj -> obj -> obj
| app : obj -> obj -> obj
| var : string -> obj
(** A [::] path, hence at least two segments after a [var] *)
| glob : list string -> obj
| proj : obj -> string -> obj
| letb : decl -> obj -> obj

with decl : Set :=
(** [x : A := M].  A local definition is always transparent and has no
    modifiers. *)
| d_def : string -> obj -> obj -> decl
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
| c_mod : string -> list (string * obj) -> mdef -> cmd
| c_def : mods -> string -> obj -> obj -> cmd
(** [c_import fp ip] imports the module at internal path [ip] of the unit at
    file path [fp].  An empty [fp] is this unit, so [import A.B] is
    [c_import nil ["A"; "B"]] and [import X::Y] is [c_import ["X"; "Y"] nil]. *)
| c_import : list string -> list string -> ispec -> cmd
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
    (case_d_def : forall x o1 o2, Po o1 -> Po o2 -> Pd (d_def x o1 o2))
    (case_d_mod : forall x ps md, List.Forall (fun p => Po (snd p)) ps -> Pm md -> Pd (d_mod x ps md))
    (case_md_where : forall cs, List.Forall Pc cs -> Pm (md_where cs))
    (case_md_alias : forall o, Po o -> Pm (md_alias o))
    (case_c_mod : forall x ps md, List.Forall (fun p => Po (snd p)) ps -> Pm md -> Pc (c_mod x ps md))
    (case_c_def : forall m x o1 o2, Po o1 -> Po o2 -> Pc (c_def m x o1 o2))
    (case_c_import : forall fp ip spec, Pc (c_import fp ip spec))
    (case_c_eval : forall o oA, Po o -> match oA with Some A => Po A | None => True end -> Pc (c_eval o oA)).

  Fixpoint obj_mut (o : obj) : Po o :=
    match o with
    | typ n => case_typ n
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
    | d_def x o1 o2 => case_d_def x o1 o2 (obj_mut o1) (obj_mut o2)
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
    | c_mod x ps md =>
        case_c_mod x ps md
          ((fix go (ps : list (string * obj)) : List.Forall (fun p => Po (snd p)) ps :=
              match ps with
              | nil => List.Forall_nil _
              | p :: ps' => List.Forall_cons p (obj_mut (snd p)) (go ps')
              end) ps)
          (mdef_mut md)
    | c_def m x o1 o2 => case_c_def m x o1 o2 (obj_mut o1) (obj_mut o2)
    | c_import fp ip spec => case_c_import fp ip spec
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
    [Aᵢ₊₁].  The grammar gives the path reversed, [B] first. *)
Definition c_mod_dotted (x : string) (rev_pre : list string) (ps : list (string * obj)) (md : mdef) : cmd :=
  List.fold_left (fun c y => c_mod y nil (md_where (c :: nil))) rev_pre (c_mod x ps md).

(** A compilation unit: its imports, and the one module declaration everything
    else it contains lives in.  That declaration names the unit, so its path is a
    [::] one, and carries the unit's parameters.  Only imports may precede it, so
    no definition is ever made outside a module.  The imports are [c_import]s;
    the grammar admits nothing else there. *)
Definition prog : Set := (list cmd * (list string * list (string * obj) * list cmd))%type.

End Cst.

(** * Abstract Syntax Tree

    Unlike a calculus of explicit substitutions, there is no constructor for
    substitution application and no syntactic category of substitutions.  Weakenings and substitutions are meta-level operations
    (recursive functions on [exp]) defined further down in this file, and their
    algebraic laws are theorems (in [Core.Syntactic.Substitution]) rather than
    definitional equalities of the object theory.
 *)

(** ** Qualified Names

    A reference to a global is [X::Y::Z.a.b.c]: the unit it lives in, named
    absolutely, then the chain of member selections inside it from the unit's
    root.  Names are absolute, also inside the unit being elaborated: an open
    module is named by the same path it will have once it is closed and its
    unit filed, so what a path denotes never depends on where it is read, and
    resolving it is a lookup with no re-expression.

    The same record names a module: [p_mems] is then the chain to it, empty
    for the unit itself. *)
Record path : Set := path_mk
  { p_unit : list string
  ; p_mems : list string }.

(** An abbreviation, not a definition: a rule keyed on [p_abs] then has a record
    literal in its conclusion, so inverting it yields equations that
    [discriminate] and [injection] see through. *)
Abbreviation p_abs fp ip := {| p_unit := fp; p_mems := ip |}.

(** A unit is named by a nonempty file path, and a path to a term by a nonempty
    member chain: a module is not an [exp] and has no type. *)
Definition path_valid (p : path) : Prop :=
  p_unit p <> nil /\ p_mems p <> nil.

(** The member [x] of the module [mp]. *)
Definition path_in (mp : path) (x : string) : path :=
  {| p_unit := p_unit mp ; p_mems := p_mems mp ++ x :: nil |}.

(** The terms, and the module syntax nested in them.  The two are one
    mutual family: a term binds a local module ([a_let] with [b_mod]) and
    selects members of module expressions ([a_mem]), and a module body
    contains terms.

    - [modexp] is a module expression: a global module [me_path], a local
      module slot [me_var], a submodule [me_mem], an argument [me_app], or a
      literal unit [me_lit].  A literal is produced only by substitution, when
      [ζ] replaces a module slot by its unit.
    - [gunit] is a unit: its parameter telescope, innermost first, and its
      definition, a body or an alias.  The definition is under the parameters.
    - [gmod] is a module body, newest entry last.  Each named entry binds one
      index for the entries after it; a check entry ([gm_check]) binds none.
    - [centry] is a context entry: an assumption, a definition, or a module
      slot [ce_mod U], which binds one index to the unit [U]. *)
Inductive exp : Set :=
(** Universe *)
| a_typ : nat -> exp
(** Natural numbers *)
| a_nat : exp
| a_zero : exp
| a_succ : exp -> exp
| a_natrec : exp -> exp -> exp -> exp -> exp
(** The unit type, with η *)
| a_True : exp
| a_true : exp
(** The empty type.  [a_exfalso A M] eliminates [M] into the motive [A], which
    binds the scrutinee. *)
| a_False : exp
| a_exfalso : exp -> exp -> exp
(** Functions *)
| a_pi : exp -> exp -> exp
| a_fn : exp -> exp -> exp
| a_app : exp -> exp -> exp
(** Variable *)
| a_var : nat -> exp
(** Globals.  [X::Y::Z.W.bar] is [a_glob (p_abs ["X"; "Y"; "Z"] ["W"; "bar"])],
    also when [X::Y::Z] is the unit being elaborated.  A global is closed: it
    stands for the member generalized over the parameters of every module
    enclosing it, outermost first, and is applied to them.  Inside its own
    module those are the parameter variables in scope. *)
| a_glob : path -> exp
(** Local binding: [a_let b B] binds [#0] in [B] to the definition or the
    module [b]. *)
| a_let : bnd -> exp -> exp
(** The member [x] of the module [H]. *)
| a_mem : modexp -> string -> exp
with modexp : Set :=
| me_path : path -> modexp
| me_var : nat -> modexp
| me_mem : modexp -> string -> modexp
| me_app : modexp -> exp -> modexp
| me_lit : gunit -> modexp
with bnd : Set :=
(** [b_def A M]: a definition of type [A] *)
| b_def : exp -> exp -> bnd
| b_mod : gunit -> bnd
with gunit : Set :=
| gu_mk : list centry -> moddef -> gunit
with moddef : Set :=
| md_body : gmod -> moddef
| md_alias : modexp -> moddef
with gmod : Set :=
| gm_nil : gmod
| gm_ext : gmod -> string -> gentry -> gmod
| gm_check : gmod -> bcheck -> gmod
(** The check-only entries of a local body: an [import] of a module, with the
    names it [use]s, and an [eval], which no rule accepts. *)
with bcheck : Set :=
| bc_import : modexp -> list string -> bcheck
| bc_eval : exp -> option exp -> bcheck
(** [ge_def b pv A B]: [b] says whether the definition is transparent, [pv]
    whether it is private, and [B] is [None] for an axiom.  A filed definition
    is closed; a definition of a local body is read in the body's context. *)
with gentry : Set :=
| ge_def : bool -> bool -> exp -> option exp -> gentry
| ge_mod : gunit -> gentry
with centry : Set :=
| ce_ass : exp -> centry
| ce_def : exp -> exp -> centry
| ce_mod : gunit -> centry.

Abbreviation typ := exp.

(** ** Contexts

    A context entry occupies one de Bruijn index, whether it is an
    assumption, a definition or a module slot. *)
Abbreviation ctx := (list centry).

(** The type of an entry; a module slot has none, and reads as [⊤]. *)
Definition ce_typ (e : centry) : typ :=
  match e with
  | ce_ass A | ce_def A _ => A
  | ce_mod _ => a_True
  end.

(** ** Units

    A body unit and a body entry, the forms every global module has. *)
Abbreviation gu_body Δ Φ := (gu_mk Δ (md_body Φ)).
Abbreviation ge_body Δ Φ := (ge_mod (gu_body Δ Φ)).

Definition gu_params (U : gunit) : ctx := match U with gu_mk Δ _ => Δ end.

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
  | gm_check Φ' _ => gm_binders Φ'
  end.

(** A body as the context entries it binds, innermost first.  A check entry
    binds nothing. *)
Fixpoint body_ctx (Φ : gmod) : ctx :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' _ (ge_def _ _ A (Some M)) => cons (ce_def A M) (body_ctx Φ')
  | gm_ext Φ' _ (ge_def _ _ A None) => cons (ce_ass A) (body_ctx Φ')
  | gm_ext Φ' _ (ge_mod U) => cons (ce_mod U) (body_ctx Φ')
  | gm_check Φ' _ => body_ctx Φ'
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
  | cons (ce_def B N) Δ' => ctx_pi Δ' (a_let (b_def B N) A)
  | cons (ce_mod U) Δ' => ctx_pi Δ' (a_let (b_mod U) A)
  end.

Fixpoint ctx_fn (Δ : ctx) (M : exp) : exp :=
  match Δ with
  | nil => M
  | cons (ce_ass B) Δ' => ctx_fn Δ' (a_fn B M)
  | cons (ce_def B N) Δ' => ctx_fn Δ' (a_let (b_def B N) M)
  | cons (ce_mod U) Δ' => ctx_fn Δ' (a_let (b_mod U) M)
  end.

(** ** Induction

    The family is nested through [list centry] and [option exp], so its
    induction principle is written by hand.  [syn_mut_ind] has one motive per
    sort; a telescope carries [Forall] of the entry motive, and a definition
    body the motive of every expression it may hold. *)
Section syn_mut_ind.
  Variables (Pe : exp -> Prop) (Pm : modexp -> Prop) (Pb : bnd -> Prop)
    (Pu : gunit -> Prop) (Pd : moddef -> Prop) (Pg : gmod -> Prop)
    (Pk : bcheck -> Prop) (Pn : gentry -> Prop) (Pc : centry -> Prop).

  Hypotheses
    (case_typ : forall i, Pe (a_typ i))
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
    (case_glob : forall p, Pe (a_glob p))
    (case_let : forall b B, Pb b -> Pe B -> Pe (a_let b B))
    (case_mem : forall H x, Pm H -> Pe (a_mem H x))
    (case_me_path : forall p, Pm (me_path p))
    (case_me_var : forall k, Pm (me_var k))
    (case_me_mem : forall H y, Pm H -> Pm (me_mem H y))
    (case_me_app : forall H N, Pm H -> Pe N -> Pm (me_app H N))
    (case_me_lit : forall U, Pu U -> Pm (me_lit U))
    (case_b_def : forall A M, Pe A -> Pe M -> Pb (b_def A M))
    (case_b_mod : forall U, Pu U -> Pb (b_mod U))
    (case_gu_mk : forall Δ D, List.Forall Pc Δ -> Pd D -> Pu (gu_mk Δ D))
    (case_md_body : forall Φ, Pg Φ -> Pd (md_body Φ))
    (case_md_alias : forall E, Pm E -> Pd (md_alias E))
    (case_gm_nil : Pg gm_nil)
    (case_gm_ext : forall Φ x E, Pg Φ -> Pn E -> Pg (gm_ext Φ x E))
    (case_gm_check : forall Φ c, Pg Φ -> Pk c -> Pg (gm_check Φ c))
    (case_bc_import : forall E ns, Pm E -> Pk (bc_import E ns))
    (case_bc_eval : forall M A, Pe M -> (forall A', A = Some A' -> Pe A') -> Pk (bc_eval M A))
    (case_ge_def : forall b pv A B, Pe A -> (forall M, B = Some M -> Pe M) -> Pn (ge_def b pv A B))
    (case_ge_mod : forall U, Pu U -> Pn (ge_mod U))
    (case_ce_ass : forall A, Pe A -> Pc (ce_ass A))
    (case_ce_def : forall A M, Pe A -> Pe M -> Pc (ce_def A M))
    (case_ce_mod : forall U, Pu U -> Pc (ce_mod U)).

  Fixpoint exp_mut (M : exp) : Pe M :=
    match M with
    | a_typ i => case_typ i
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
    | a_glob p => case_glob p
    | a_let b B => case_let b B (bnd_mut b) (exp_mut B)
    | a_mem H x => case_mem H x (modexp_mut H)
    end
  with modexp_mut (H : modexp) : Pm H :=
    match H with
    | me_path p => case_me_path p
    | me_var k => case_me_var k
    | me_mem H y => case_me_mem H y (modexp_mut H)
    | me_app H N => case_me_app H N (modexp_mut H) (exp_mut N)
    | me_lit U => case_me_lit U (gunit_mut U)
    end
  with bnd_mut (b : bnd) : Pb b :=
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
    | md_body Φ => case_md_body Φ (gmod_mut Φ)
    | md_alias E => case_md_alias E (modexp_mut E)
    end
  with gmod_mut (Φ : gmod) : Pg Φ :=
    match Φ with
    | gm_nil => case_gm_nil
    | gm_ext Φ x E => case_gm_ext Φ x E (gmod_mut Φ) (gentry_mut E)
    | gm_check Φ c => case_gm_check Φ c (gmod_mut Φ) (bcheck_mut c)
    end
  with bcheck_mut (c : bcheck) : Pk c :=
    match c with
    | bc_import E ns => case_bc_import E ns (modexp_mut E)
    | bc_eval M A =>
        case_bc_eval M A (exp_mut M)
          (match A as o return (forall A', o = Some A' -> Pe A') with
           | Some A0 => fun A' e => match e in _ = o' return match o' with Some A' => Pe A' | None => True end with
                                   | eq_refl => exp_mut A0 end
           | None => fun A' e => False_ind _ (match e in _ = o' return match o' with Some _ => False | None => True end with
                                 | eq_refl => I end)
           end)
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
    | ge_mod U => case_ge_mod U (gunit_mut U)
    end
  with centry_mut (e : centry) : Pc e :=
    match e with
    | ce_ass A => case_ce_ass A (exp_mut A)
    | ce_def A M => case_ce_def A M (exp_mut A) (exp_mut M)
    | ce_mod U => case_ce_mod U (gunit_mut U)
    end.

  Theorem syn_mut_ind :
    (forall M, Pe M) /\ (forall H, Pm H) /\ (forall b, Pb b) /\ (forall U, Pu U) /\
    (forall D, Pd D) /\ (forall Φ, Pg Φ) /\ (forall c, Pk c) /\ (forall E, Pn E) /\
    (forall e, Pc e).
  Proof.
    repeat split; [ exact exp_mut | exact modexp_mut | exact bnd_mut | exact gunit_mut
                  | exact moddef_mut | exact gmod_mut | exact bcheck_mut | exact gentry_mut
                  | exact centry_mut ].
  Qed.
End syn_mut_ind.

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

(** ** Syntactic Normal/Neutral Form *)
Inductive nf : Set :=
| nf_typ : nat -> nf
| nf_nat : nf
| nf_zero : nf
| nf_succ : nf -> nf
| nf_True : nf
| nf_true : nf
| nf_False : nf
| nf_pi : nf -> nf -> nf
| nf_fn : nf -> nf -> nf
| nf_neut : ne -> nf
with ne : Set :=
| ne_natrec : nf -> nf -> nf -> ne -> ne
| ne_exfalso : nf -> ne -> ne
| ne_app : ne -> nf -> ne
| ne_var : nat -> ne
(** An opaque definition or an axiom: it does not unfold. *)
| ne_glob : path -> ne
.

Fixpoint nf_to_exp (M : nf) : exp :=
  match M with
  | nf_typ i => a_typ i
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
  | ne_glob p => a_glob p
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

(** A normal form with no global at the head of a neutral. *)

Fixpoint nf_clean (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_nat | nf_zero | nf_True | nf_true | nf_False => True
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
  end.

Fact nf_eq_dec : forall (M M' : nf),
    ({M = M'} + {M <> M'})%type
with ne_eq_dec : forall (M M' : ne),
    ({M = M'} + {M <> M'})%type.
Proof.
  all: intros; decide equality;
    repeat (apply PeanoNat.Nat.eq_dec || decide equality || apply String.string_dec).
Defined.

(** * Weakenings

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
  | a_glob p => a_glob p
  | a_let b B => a_let (bnd_wk b φ) (exp_wk B (wk_q φ))
  | a_mem H x => a_mem (modexp_wk H φ) x
  end
with modexp_wk (H : modexp) (φ : wk) : modexp :=
  match H with
  | me_path p => me_path p
  | me_var k => me_var (φ k)
  | me_mem H y => me_mem (modexp_wk H φ) y
  | me_app H N => me_app (modexp_wk H φ) (exp_wk N φ)
  | me_lit U => me_lit (gunit_wk U φ)
  end
with bnd_wk (b : bnd) (φ : wk) : bnd :=
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
  | md_body Φ => md_body (gmod_wk Φ φ)
  | md_alias E => md_alias (modexp_wk E φ)
  end
with gmod_wk (Φ : gmod) (φ : wk) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gmod_wk Φ φ) x (gentry_wk E (wk_qn (gm_binders Φ) φ))
  | gm_check Φ c => gm_check (gmod_wk Φ φ) (bcheck_wk c (wk_qn (gm_binders Φ) φ))
  end
with bcheck_wk (c : bcheck) (φ : wk) : bcheck :=
  match c with
  | bc_import E ns => bc_import (modexp_wk E φ) ns
  | bc_eval M A => bc_eval (exp_wk M φ) (match A with Some A => Some (exp_wk A φ) | None => None end)
  end
with gentry_wk (E : gentry) (φ : wk) : gentry :=
  match E with
  | ge_def b pv A B => ge_def b pv (exp_wk A φ) (match B with Some M => Some (exp_wk M φ) | None => None end)
  | ge_mod U => ge_mod (gunit_wk U φ)
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

(** * Substitutions

    A substitution maps each de Bruijn index to an entry, [sentry]: a
    variable, which is a variable of either sort, a term for a term variable,
    or a module expression for a module slot.  Like weakenings, substitutions
    are not part of the object syntax: applying one is a meta-level recursion
    on the expression.

    An entry of the wrong sort reads as a closed default, [a_zero] or the
    module [me_path (p_abs nil nil)], which every operation fixes.  The
    defaults are the semantic projections of an entry of the other sort, so
    evaluation commutes with every substitution. *)
Inductive sentry : Set :=
| se_var : nat -> sentry
| se_exp : exp -> sentry
| se_mod : modexp -> sentry.

Definition sub : Set := nat -> sentry.

Definition exp_junk : exp := a_zero.
Definition modexp_junk : modexp := me_path {| p_unit := nil; p_mems := nil |}.

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
  | a_glob p => a_glob p
  | a_let b B => a_let (bnd_sub b σ) (exp_sub B (sb_q σ))
  | a_mem H x => a_mem (modexp_sub H σ) x
  end
with modexp_sub (H : modexp) (σ : sub) : modexp :=
  match H with
  | me_path p => me_path p
  | me_var k => sentry_modexp (σ k)
  | me_mem H y => me_mem (modexp_sub H σ) y
  | me_app H N => me_app (modexp_sub H σ) (exp_sub N σ)
  | me_lit U => me_lit (gunit_sub U σ)
  end
with bnd_sub (b : bnd) (σ : sub) : bnd :=
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
  | md_body Φ => md_body (gmod_sub Φ σ)
  | md_alias E => md_alias (modexp_sub E σ)
  end
with gmod_sub (Φ : gmod) (σ : sub) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gmod_sub Φ σ) x (gentry_sub E (sb_qn (gm_binders Φ) σ))
  | gm_check Φ c => gm_check (gmod_sub Φ σ) (bcheck_sub c (sb_qn (gm_binders Φ) σ))
  end
with bcheck_sub (c : bcheck) (σ : sub) : bcheck :=
  match c with
  | bc_import E ns => bc_import (modexp_sub E σ) ns
  | bc_eval M A => bc_eval (exp_sub M σ) (match A with Some A => Some (exp_sub A σ) | None => None end)
  end
with gentry_sub (E : gentry) (σ : sub) : gentry :=
  match E with
  | ge_def b pv A B => ge_def b pv (exp_sub A σ) (match B with Some M => Some (exp_sub M σ) | None => None end)
  | ge_mod U => ge_mod (gunit_sub U σ)
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

#[global] Bind Scope mctt_scope with exp.
#[global] Bind Scope mctt_scope with modexp.
#[global] Bind Scope mctt_scope with gunit.
#[global] Bind Scope mctt_scope with sub.
#[global] Bind Scope mctt_scope with nf.
#[global] Bind Scope mctt_scope with ne.
Open Scope mctt_scope.

(** ** Syntactic Notations

    Every notation below lives in ordinary [constr]: there is no custom entry
    and hence no delimiter to write.  The price is that a spelling can denote
    only one sort, so the normal forms — which mirror the expressions
    constructor for constructor — carry a superscript [ⁿ].  Values carry a
    superscript [ᵈ]; see [Domain_Notations]. *)
Module Syntax_Notations.
  (** Substitution and weakening application come first, so that level 1 is
      created left associative; everything else that reads as an atom is at
      level 0, and the constructor forms with a recursive last argument are at
      level 2. *)
  Notation "M [ σ ]" := (exp_sub M σ) (at level 1, left associativity, σ at level 60, format "M [ σ ]") : mctt_scope.
  Notation "M [ φ ]ʷ" := (exp_wk M φ) (at level 1, left associativity, φ at level 60, format "M [ φ ]ʷ") : mctt_scope.
  Notation "H [ σ ]ᵐ" := (modexp_sub H σ) (at level 1, left associativity, σ at level 60, format "H [ σ ]ᵐ") : mctt_scope.
  Notation "U [ σ ]ᵘ" := (gunit_sub U σ) (at level 1, left associativity, σ at level 60, format "U [ σ ]ᵘ") : mctt_scope.
  Notation "'Type' @ n" := (a_typ n) (at level 1, n at level 0, format "'Type' @ n") : mctt_scope.
  Notation "'#' n" := (a_var n) (at level 1, n at level 0, format "'#' n") : mctt_scope.
  Notation "'ℕ'" := a_nat : mctt_scope.
  Notation "'zero'" := a_zero : mctt_scope.
  Notation "'succ' M" := (a_succ M) (at level 2, M at level 1) : mctt_scope.
  Notation "'λ' A M" := (a_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Π' A B" := (a_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'ℓ' A ≔ M 'in' B" := (a_let (b_def A M) B) (at level 2, A at level 1, M at level 60, B at level 60) : mctt_scope.
  Notation "'ℓₘ' U 'in' B" := (a_let (b_mod U) B) (at level 2, U at level 1, B at level 60) : mctt_scope.
  Notation "'rec' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (a_natrec A MZ MS M) (at level 0, M at level 60, A at level 60, MZ at level 60, MS at level 60) : mctt_scope.
  Notation "'⊤'" := a_True : mctt_scope.
  Notation "'⋆'" := a_true : mctt_scope.
  Notation "'⊥'" := a_False : mctt_scope.
  Notation "'efq' M 'return' A" := (a_exfalso A M) (at level 2, M at level 60, A at level 60) : mctt_scope.
  (** Application needs an explicit operator: a [constr] notation may not be
      pure juxtaposition, which is Rocq's own application. *)
  Notation "M $ N" := (a_app M N) (at level 10, left associativity) : mctt_scope.

  (** *** Substitutions

      [σ ⨟ τ] is diagrammatic composition: [σ] first, then [τ]. *)
  Notation "'Id'" := sb_id : mctt_scope.
  Notation "'Wk'" := sb_shift : mctt_scope.
  Notation "σ ⨟ τ" := (sb_compose σ τ) (at level 45, right associativity, format "σ ⨟ τ") : mctt_scope.
  Notation "σ ,, M" := (sb_extend σ (se_exp M)) (at level 50, left associativity, format "σ ,, M") : mctt_scope.
  Notation "σ ',,ₘ' H" := (sb_extend σ (se_mod H)) (at level 50, left associativity, format "σ  ,,ₘ  H") : mctt_scope.
  Notation "'q' σ" := (sb_q σ) (at level 30, σ at level 2) : mctt_scope.

  (** *** Contexts

      Extension is [▹] rather than the paper's comma: a parsing [,] in [constr]
      would steal Rocq's pair notation.  Both are restricted to [centry] so
      that an unrelated [list] does not print as a context.  A definition
      entry is [Γ ▸ A ≔ M]; it has its own first token because [Γ ▹ A] would
      otherwise be a proper prefix of it. *)
  Notation "⋅" := (@nil centry) : mctt_scope.
  Notation "Γ ▹ A" := (@cons centry (ce_ass A) Γ) (at level 50, left associativity) : mctt_scope.
  Notation "Γ ▸ A ≔ M" := (@cons centry (ce_def A M) Γ) (at level 50, left associativity) : mctt_scope.
  Notation "Γ '▹ₘ' U" := (@cons centry (ce_mod U) Γ) (at level 50, left associativity) : mctt_scope.

  (** *** Normal and Neutral Forms *)
  Notation "'ℕⁿ'" := nf_nat : mctt_scope.
  Notation "'zeroⁿ'" := nf_zero : mctt_scope.
  Notation "'succⁿ' M" := (nf_succ M) (at level 2, M at level 1) : mctt_scope.
  Notation "'⊤ⁿ'" := nf_True : mctt_scope.
  Notation "'⋆ⁿ'" := nf_true : mctt_scope.
  Notation "'⊥ⁿ'" := nf_False : mctt_scope.
  Notation "'Typeⁿ' @ n" := (nf_typ n) (at level 1, n at level 0, format "'Typeⁿ' @ n") : mctt_scope.
  Notation "'λⁿ' A M" := (nf_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Πⁿ' A B" := (nf_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'⇑ⁿ' M" := (nf_neut M) (at level 2, M at level 1, format "'⇑ⁿ'  M") : mctt_scope.
  Notation "'#ⁿ' n" := (ne_var n) (at level 1, n at level 0, format "'#ⁿ' n") : mctt_scope.
  Notation "M '$ⁿ' N" := (ne_app M N) (at level 10, left associativity, format "M  $ⁿ  N") : mctt_scope.
  Notation "'recⁿ' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (ne_natrec A MZ MS M) (at level 0, M at level 60, A at level 60, MZ at level 60, MS at level 60) : mctt_scope.
  Notation "'efqⁿ' M 'return' A" := (ne_exfalso A M) (at level 2, M at level 60, A at level 60) : mctt_scope.
End Syntax_Notations.

(** ** Notations for Weakenings

    Weakenings are their own sort, in their own module: after [Substitution.v]
    establishes that the embedding [ι] is faithful the development speaks almost
    exclusively of substitutions. *)
Module Wk_Notations.
  (** [↑] is the paper's [⇑] as a weakening.  The glyph differs because [⇑] is
      already the neutral-value embedding of [Domain_Notations], and because the
      development needs to keep the shift weakening apart from the shift
      substitution [Wk = ι ↑]. *)
  Notation "↑" := wk_shift : mctt_scope.
  Notation "φ ⊙ ψ" := (wk_compose φ ψ) (at level 40, left associativity) : mctt_scope.
  Notation "'ι' φ" := (sb_of_wk φ) (at level 30) : mctt_scope.
End Wk_Notations.
