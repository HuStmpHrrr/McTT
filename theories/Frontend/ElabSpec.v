From Stdlib Require Import List Permutation String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Command.

Import Syntax_Notations.

(** * A Declarative Specification of Elaboration

    This file defines [elab_spec prg u], which holds when the surface unit
    [prg] elaborates to the core unit [u].  The definition does not use the
    elaborator's data structures.  [Frontend/ElabCorrect.v] proves that
    [elaborate_core] computes exactly this relation.

    The spec makes the following design choices.

    - There is no symbol table.  The members of a frame are the names
      declared by the core commands that the frame has emitted so far.
    - A frame binds each name at most once, whether as an import alias, a
      member or a parameter.  Declaring a name twice in the same frame is an
      error.  Declaring a name that an enclosing frame binds shadows it.
    - A name is looked up first in the local binders, then in the open frames
      from the innermost outward, and finally in the aliases of the unit's
      leading imports.  The first binding found wins.
    - The parameters of the open frames are λ-variables.  A member of an open
      frame is written as its absolute path, applied to the parameters of its
      own frame and of every frame enclosing it.
    - A module that is not open at the use site is reached through a module
      reference.  Only its public definitions can be selected, and the user
      writes its arguments explicitly.
    - The elaborator does not read other units.  A path into an imported unit
      is accepted as written, and type checking decides whether it is valid.

    The comments below explain the definitions with this running example.

      module Main where
        module M (A : Type@0) where
          def id (x : A) : A := x end
          module N (B : Type@0) where
            def k (x : A) (y : B) : A := id x end
          end
        end
        def j : forall (x : Nat) -> Nat := M.id Nat end
      end

    It elaborates to the following core unit, where [Main.M.id] stands for
    [a_glob (p_abs ["Main"] ["M"; "id"])] and the transparency and privacy
    flags of [cc_def] are omitted.  [ElabExamples.running_spec] checks this.

      cc_mod "M" (⋅ ▹ Type@0)
        [ cc_def "id" (Π #0 #1) (λ #0 #0);
          cc_mod "N" (⋅ ▹ Type@0)
            [ cc_def "k" (Π #1 (Π #1 #3)) (λ #1 (λ #1 (Main.M.id $ #3 $ #1))) ] ];
      cc_def "j" (Π ℕ ℕ) (Main.M.id $ ℕ)

    Inside [M], [id] is used as [Main.M.id $ A]: it is applied to the
    parameter of its frame.  In the body of [k], [A] is [#3], so [id x] is
    [Main.M.id $ #3 $ #1].  Outside [M], in [j], no parameter is open, so the
    user supplies [A] by writing [M.id Nat]. *)

(** ** Declarations Read Off Core Commands *)

(** [cc_name c] is the name that the core command [c] declares, if any.
    Definitions and modules declare a name; imports and evaluations do not. *)
Definition cc_name (c : ccmd) : option string :=
  match c with
  | cc_def x _ _ _ _ | cc_mod x _ _ => Some x
  | cc_import _ _ | cc_eval _ _ => None
  end.

(** [declares cs x] holds when some command in [cs] declares [x]. *)
Definition declares (cs : list ccmd) (x : string) : Prop :=
  exists c, In c cs /\ cc_name c = Some x.

(** [decl_names cs] lists the names that [cs] declares, in order. *)
Definition decl_names (cs : list ccmd) : list string :=
  flat_map (fun c => match cc_name c with Some x => x :: nil | None => nil end) cs.

(** [cs_member cs x c] holds when [c] is the last command in [cs] that
    declares [x].  It gives the meaning of [x] as a member of a module whose
    commands are [cs].  A frame never declares a name twice, so [c] is in fact
    the only such command. *)
Definition cs_member (cs : list ccmd) (x : string) (c : ccmd) : Prop :=
  exists cs1 cs2, cs = cs1 ++ c :: cs2 /\ cc_name c = Some x /\ ~ declares cs2 x.

(** ** What a Name Denotes *)

(** A module reference names a module that is not open at the use site.
    - [sr_unit] is the path of the unit that contains the module.
    - [sr_mems] is the chain of member names from the unit's root to the
      module.
    - [sr_sig] is the list of the module's commands.  It is [None] when the
      module belongs to another unit, since the elaborator does not read other
      units.  Such a reference is called _opaque_.
    - [sr_args] lists the arguments supplied so far, outermost first.

    In the running example, [M] used in [j] is the reference with unit
    [Main], chain [["M"]], the commands of [M], and no arguments. *)
Record sref : Set := sr_mk
  { sr_unit : fpath
  ; sr_mems : list string
  ; sr_sig : option (list ccmd)
  ; sr_args : list exp }.

(** [sr_app R args] adds [args] to the arguments of [R]. *)
Definition sr_app (R : sref) (args : list exp) : sref :=
  sr_mk (sr_unit R) (sr_mems R) (sr_sig R) (sr_args R ++ args).

(** An import alias names a module, or a definition of a module. *)
Inductive starget : Set :=
| st_mod : sref -> starget
| st_def : sref -> string -> starget.

(** An object denotes a term, a module, or the definition [x] of a module
    [R].  The third form is needed for [M.f a], where the argument [a] belongs
    to [M] but is written after the projection [.f].  It becomes a term once
    [R] has all its arguments ([as_term]).  In the running example, [M.id]
    denotes [s_def R "id"], where [R] is the reference to [M] described above,
    and [M.id Nat] denotes [s_def (sr_app R [ℕ]) "id"]. *)
Inductive sres : Set :=
| s_term : exp -> sres
| s_mod : sref -> sres
| s_def : sref -> string -> sres.

(** [st_res t] is the denotation of the alias target [t]. *)
Definition st_res (t : starget) : sres :=
  match t with
  | st_mod R => s_mod R
  | st_def R x => s_def R x
  end.

(** [apps M args] applies [M] to each of [args] in turn. *)
Definition apps (M : exp) (args : list exp) : exp := fold_left a_app args M.

(** [sapp r N] applies the denotation [r] to [N].  For a term, this is
    ordinary application.  For a module, or a definition of one, [N] becomes
    one more module argument. *)
Definition sapp (r : sres) (N : exp) : sres :=
  match r with
  | s_term M => s_term (M $ N)
  | s_mod R => s_mod (sr_app R (N :: nil))
  | s_def R x => s_def (sr_app R (N :: nil)) x
  end.

(** [as_term r M] holds when the denotation [r] can be used as the term [M].
    - A term is itself.
    - The definition [x] of [R] is the absolute path of [x] applied to the
      arguments of [R].  A member is a closed constant, generalized over the
      parameters of the modules enclosing it, so it is a term whatever the
      number of arguments.  Type checking decides whether they fit.
    - An opaque reference with a nonempty member chain is the path it names,
      applied to its arguments.  Type checking decides whether the path names
      a definition.
    - A module of the current unit is never a term.

    In the running example, [M.id Nat] is the term [Main.M.id $ ℕ].  [M.id]
    alone is the term [Main.M.id], of type [Π (A : Type@0). Π A A]. *)
Inductive as_term : sres -> exp -> Prop :=
| at_term : forall M, as_term (s_term M) M
| at_def : forall R x,
    as_term (s_def R x) (apps (a_glob (p_abs (sr_unit R) (sr_mems R ++ x :: nil))) (sr_args R))
| at_opaque : forall R,
    sr_sig R = None ->
    sr_mems R <> nil ->
    as_term (s_mod R) (apps (a_glob (p_abs (sr_unit R) (sr_mems R))) (sr_args R)).

(** *** Member Selection

    [select R x t] holds when [R.x] denotes [t].
    - If [R] is opaque, [R.x] is an opaque reference whose chain is extended
      by [x].  Privacy is not checked in this case (REVISIT, as in the
      elaborator).
    - If [R] declares [x] as a public definition, [R.x] is that definition.
      A private definition cannot be selected.  It is visible only in its own
      frame and the frames nested in it, where [fbind] finds it directly.
    - If [R] declares [x] as a module with parameters [Δ], [R.x] is a
      reference to that module.  It keeps the arguments of [R].

    In the running example, [M.id] selects the public definition [id], and
    [M.N] would select a reference to [N]. *)
Inductive select : sref -> string -> starget -> Prop :=
| sl_opaque : forall R x,
    sr_sig R = None ->
    select R x (st_mod (sr_mk (sr_unit R) (sr_mems R ++ x :: nil) None (sr_args R)))
| sl_def : forall R x cs b A M,
    sr_sig R = Some cs ->
    cs_member cs x (cc_def x b false A M) ->
    select R x (st_def R x)
| sl_mod : forall R x cs Δ cs',
    sr_sig R = Some cs ->
    cs_member cs x (cc_mod x Δ cs') ->
    select R x (st_mod (sr_mk (sr_unit R) (sr_mems R ++ x :: nil) (Some cs') (sr_args R))).

(** *** Weakening

    A denotation built at one point may be used [k] binders further in.  These
    functions shift all its terms by [k]. *)
Definition shift_by (k : nat) (M : exp) : exp := M[wk_shiftn k]ʷ.

Definition wk_sref (k : nat) (R : sref) : sref :=
  sr_mk (sr_unit R) (sr_mems R) (sr_sig R) (map (shift_by k) (sr_args R)).

Definition wk_starget (k : nat) (t : starget) : starget :=
  match t with
  | st_mod R => st_mod (wk_sref k R)
  | st_def R x => st_def (wk_sref k R) x
  end.

(** ** Scopes *)

(** A scope records what the imports of a frame bind.  The leading imports
    of a unit also build a scope.
    - [ss_alias] lists the aliases, latest first.
    - [ss_units] lists the units imported so far.  An imported unit can be
      named by its full path. *)
Record sscope : Set := ss_mk
  { ss_alias : list (string * starget)
  ; ss_units : list fpath }.

(** The empty scope binds nothing. *)
Definition ss_empty : sscope := ss_mk nil nil.

(** [ss_binds sc y t] holds when [sc] has the alias [y] for [t].  Every alias
    is checked for freshness when it is made, so a scope has at most one alias
    per name ([ss_wf]). *)
Definition ss_binds (sc : sscope) (y : string) (t : starget) : Prop := In (y, t) (ss_alias sc).

(** [ss_free sc y] holds when [sc] has no alias named [y]. *)
Definition ss_free (sc : sscope) (y : string) : Prop := ~ In y (map fst (ss_alias sc)).

(** [ss_wf sc] states that [sc] has at most one alias per name. *)
Definition ss_wf (sc : sscope) : Prop := NoDup (map fst (ss_alias sc)).

(** [ss_add y t sc] adds the alias [y] for [t] to [sc]. *)
Definition ss_add (y : string) (t : starget) (sc : sscope) : sscope :=
  ss_mk ((y, t) :: ss_alias sc) (ss_units sc).

(** [ss_add_unit fp sc] records that the unit [fp] is imported.  An import
    from the current unit ([fp = nil]) records nothing. *)
Definition ss_add_unit (fp : fpath) (sc : sscope) : sscope :=
  match fp with
  | nil => sc
  | _ => ss_mk (ss_alias sc) (fp :: ss_units sc)
  end.

(** An open frame is a module, or the unit itself, whose body is being
    elaborated.
    - [sf_path] is its member chain from the unit's root.  It is [nil] for
      the unit itself.
    - [sf_params] lists its parameters and their elaborated types, in
      declaration order.
    - [sf_cmds] lists the core commands it has emitted so far, in order.
    - [sf_scope] records what its imports bind.

    While the body of [k] is elaborated in the running example, three frames
    are open, innermost first.
    - [N] has path [["M"; "N"]], parameter [B], and no commands yet.
    - [M] has path [["M"]], parameter [A], and the command for [id].
    - [Main] has path [nil], no parameters, and no commands yet.  The command
      for [M] is emitted only when [M] ends. *)
Record sframe : Set := sf_mk
  { sf_path : list string
  ; sf_params : list (string * typ)
  ; sf_cmds : list ccmd
  ; sf_scope : sscope }.

(** [sf_new ch ps] is a new frame with member chain [ch] and parameters
    [ps]. *)
Definition sf_new (ch : list string) (ps : list (string * typ)) : sframe := sf_mk ch ps nil ss_empty.

(** [sf_emit F c] appends the command [c] to [F]. *)
Definition sf_emit (F : sframe) (c : ccmd) : sframe :=
  sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ c :: nil) (sf_scope F).

(** [ptele ps] is the parameter list [ps] as a core context, innermost
    first. *)
Definition ptele (ps : list (string * typ)) : ctx := rev (map snd ps).


(** [sf_taken F] lists the names that [F] binds as members or parameters. *)
Definition sf_taken (F : sframe) : list string := decl_names (sf_cmds F) ++ map fst (sf_params F).

(** [sf_names F] lists all the names that [F] binds: its aliases, its members
    and its parameters. *)
Definition sf_names (F : sframe) : list string := map fst (ss_alias (sf_scope F)) ++ sf_taken F.

(** [sf_binds F x] holds when [F] binds [x]. *)
Definition sf_binds (F : sframe) (x : string) : Prop := In x (sf_names F).

(** A name may be declared in a frame only if the frame does not bind it yet.
    This applies to members, and to aliases made by [import … as] or [use].
    A name that an enclosing frame binds may be declared again, and the new
    binding shadows the old one. *)
Definition sf_fresh (F : sframe) (x : string) : Prop := ~ sf_binds F x.

(** [sf_wf F] states that [F] binds each name at most once.  Freshness keeps
    it true. *)
Definition sf_wf (F : sframe) : Prop := NoDup (sf_names F).

(** ** Pre-application

    This is the core of option B.  The parameters of the open frames are
    λ-variables.  Seen from a use site, the local binders come first, then the
    parameters of the innermost frame, then those of the next frame outward,
    and so on.  Within each frame, the last parameter is the nearest.

    Suppose a frame has [n] parameters, and [off] binders lie between the use
    site and its last parameter.  Then its parameters, in declaration order,
    are

      [#(off + n - 1), …, #(off + 1), #off]

    which is [vars_desc off n].

    A member of an open frame is stored generalized over the parameters of its
    own frame and of every enclosing frame, outermost first.  A use of the
    member therefore applies it to exactly those variables.  Let [F] be the
    member's frame, [Fs] the frames enclosing [F], and [off] the number of
    binders between the use site and the last parameter of [F].  Then
    [preapp off (F :: Fs) args] holds when [args] are the variables to apply
    the member to.  They start with the parameters of the outermost frame and
    end with those of [F].  Frames nested inside [F] add no arguments; their
    parameters are among the [off] binders.

    In the running example, the body of [k] uses [id] under the binders [x]
    and [y].  The member [id] belongs to [M].  Between the use site and [A]
    lie [y], [x] and [B], so [off] is [3].  [Main] has no parameters, so
    [preapp 3 [M; Main] [#3]] holds, and [id] is applied to [#3]. *)
Definition vars_desc (off n : nat) : list exp :=
  map (fun i => a_var (off + (n - 1 - i))) (seq 0 n).

Inductive preapp : nat -> list sframe -> list exp -> Prop :=
| preapp_nil : forall off, preapp off nil nil
| preapp_cons : forall off F Fs args,
    preapp (off + List.length (sf_params F)) Fs args ->
    preapp off (F :: Fs) (args ++ vars_desc off (List.length (sf_params F))).


(** ** Name Resolution in the Open Frames *)

(** [fr_binds fp off Fs F x r] holds when the open frame [F] binds [x] to
    [r].  Here [fp] is the current unit, [Fs] are the frames enclosing [F],
    and [off] binders lie between the use site and the last parameter of [F].
    A frame binds a name at most once, so at most one rule applies. *)
Inductive fr_binds (fp : fpath) (off : nat) (Fs : list sframe) (F : sframe) : string -> sres -> Prop :=
(** An alias was resolved where its import appeared, outside these [off]
    binders, so it is weakened by [off]. *)
| fr_alias : forall x t,
    ss_binds (sf_scope F) x t ->
    fr_binds fp off Fs F x (st_res (wk_starget off t))
(** A member definition, public or private, is its absolute path applied to
    the variables that [preapp] gives. *)
| fr_def : forall x b pv A M vs,
    cs_member (sf_cmds F) x (cc_def x b pv A M) ->
    preapp off (F :: Fs) vs ->
    fr_binds fp off Fs F x (s_term (apps (a_glob (p_abs fp (sf_path F ++ x :: nil))) vs))
(** A member module is a reference that carries the same variables as its
    arguments. *)
| fr_mod : forall x Δ cs vs,
    cs_member (sf_cmds F) x (cc_mod x Δ cs) ->
    preapp off (F :: Fs) vs ->
    fr_binds fp off Fs F x
      (s_mod (sr_mk fp (sf_path F ++ x :: nil) (Some cs) vs))
(** A parameter is a variable.  It lies [off] binders back, plus one binder
    for each parameter declared after it. *)
| fr_param : forall x ps1 A ps2,
    sf_params F = ps1 ++ (x, A) :: ps2 ->
    fr_binds fp off Fs F x (s_term (a_var (off + List.length ps2))).

(** [fbind fp O off Fs x r] holds when the name [x], which is not bound
    locally, denotes [r].  Here [O] is the scope of the unit's leading
    imports, and [off] binders lie between the use site and the last parameter
    of the first frame in [Fs].  The innermost frame that binds [x] decides.
    If no frame binds [x], it is looked up in the aliases of [O].

    In the running example, [id] in the body of [k] is found as follows.  [N]
    does not bind [id], so the search moves to [M], with [off] increased by
    the one parameter of [N] from [2] to [3].  [M] binds [id] as a member
    definition, so [id] denotes [Main.M.id $ #3]. *)
Inductive fbind (fp : fpath) (O : sscope) : nat -> list sframe -> string -> sres -> Prop :=
| fb_here : forall off F Fs x r,
    fr_binds fp off Fs F x r ->
    fbind fp O off (F :: Fs) x r
| fb_next : forall off F Fs x r,
    ~ sf_binds F x ->
    fbind fp O (off + List.length (sf_params F)) Fs x r ->
    fbind fp O off (F :: Fs) x r
| fb_outer : forall off x t,
    ss_binds O x t ->
    fbind fp O off nil x (st_res (wk_starget off t)).

(** ** Local Binders *)

(** A local binding is one of the following.
    - [lb_var x] is a λ-variable.  An [abstract] [let] is also one, because
      its body is hidden behind its binder.
    - [lb_let x M] is a transparent [let].  Every use of [x] is replaced by
      [M], so its core binder is never referenced.
    - [lb_mod x R] is a [let module].  It names the module [R] and has no core
      binder. *)
Inductive lbind : Set :=
| lb_var : string -> lbind
| lb_let : string -> exp -> lbind
| lb_mod : string -> sref -> lbind.

Definition lb_name (b : lbind) : string :=
  match b with lb_var x | lb_let x _ | lb_mod x _ => x end.

(** [lb_binders b] is the number of core binders that [b] introduces. *)
Definition lb_binders (b : lbind) : nat :=
  match b with lb_var _ | lb_let _ _ => 1 | lb_mod _ _ => 0 end.

(** [nbinders L] is the number of core binders in [L].  Local bindings are
    listed innermost first. *)
Definition nbinders (L : list lbind) : nat := fold_right (fun b n => lb_binders b + n) 0 L.

(** [lbound L x k b] holds when [b] is the innermost binding of [x] in [L],
    and [k] core binders lie between [b] and the use site. *)
Definition lbound (L : list lbind) (x : string) (k : nat) (b : lbind) : Prop :=
  exists L1 L2, L = L1 ++ b :: L2 /\ lb_name b = x /\ ~ In x (map lb_name L1) /\ k = nbinders L1.

(** [ldenote k b] is what the binding [b] denotes [k] binders further in.
    The body of a [let] was elaborated outside the [let]'s own binder, so it
    is shifted by [k + 1]. *)
Definition ldenote (k : nat) (b : lbind) : sres :=
  match b with
  | lb_var _ => s_term (a_var k)
  | lb_let _ M => s_term (shift_by (S k) M)
  | lb_mod _ R => s_mod (wk_sref k R)
  end.

(** ** Objects

    [sel fp O Fs L o r] holds when the surface object [o] denotes [r].  Here
    [fp] is the current unit, [O] is the scope of its leading imports, [Fs]
    are the open frames, innermost first, and [L] are the local bindings.
    [selt fp O Fs L o M] holds when [o] denotes the term [M].

    In the running example, the body of [k] is elaborated with the local
    bindings [[lb_var "y"; lb_var "x"]].  So [x] is [#1], [id] is resolved by
    [fbind] with [off = 2], and [id x] is [Main.M.id $ #3 $ #1]. *)

(** [unit_in fp O Fs] holds when the unit [fp] is imported, by a leading
    import or by an import in one of the open frames.  Only then can it be
    named by its full path. *)
Definition unit_in (fp : fpath) (O : sscope) (Fs : list sframe) : Prop :=
  In fp (ss_units O) \/ exists F, In F Fs /\ In fp (ss_units (sf_scope F)).

Section Objects.
  Variable (fp : fpath) (O : sscope) (Fs : list sframe).

  Inductive sel : list lbind -> Cst.obj -> sres -> Prop :=
  | sel_typ : forall L n, sel L (Cst.typ n) (s_term (Type@n))
  | sel_nat : forall L, sel L Cst.nat (s_term ℕ)
  | sel_zero : forall L, sel L Cst.zero (s_term zero)
  | sel_succ : forall L o M, selt L o M -> sel L (Cst.succ o) (s_term (succ M))
  | sel_natrec : forall L on mx om oz sx sr os N A MZ MS,
      selt L on N ->
      selt (lb_var mx :: L) om A ->
      selt L oz MZ ->
      selt (lb_var sr :: lb_var sx :: L) os MS ->
      sel L (Cst.natrec on mx om oz sx sr os) (s_term (rec N return A | zero -> MZ | succ -> MS end))
  | sel_pi : forall L x oA oB A B,
      selt L oA A -> selt (lb_var x :: L) oB B -> sel L (Cst.pi x oA oB) (s_term (Π A B))
  | sel_fn : forall L x oA oM A M,
      selt L oA A -> selt (lb_var x :: L) oM M -> sel L (Cst.fn x oA oM) (s_term (λ A M))
  (** What the head denotes decides whether this is a term application or a
      module argument ([sapp]). *)
  | sel_app : forall L o1 o2 r N,
      selt L o2 N -> sel L o1 r -> sel L (Cst.app o1 o2) (sapp r N)
  | sel_local : forall L x k b,
      lbound L x k b -> sel L (Cst.var x) (ldenote k b)
  | sel_frame : forall L x r,
      ~ In x (map lb_name L) ->
      fbind fp O (nbinders L) Fs x r ->
      sel L (Cst.var x) r
  | sel_glob : forall L fq,
      unit_in fq O Fs -> sel L (Cst.glob fq) (s_mod (sr_mk fq nil None nil))
  | sel_proj : forall L o x R t,
      sel L o (s_mod R) -> select R x t -> sel L (Cst.proj o x) (st_res t)
  (** [let x : A := M in B] elaborates to [(λ A B) $ M], with one core binder.
      Inside [B], a transparent [x] stands for [M] itself, and an [abstract]
      [x] is the bound variable. *)
  | sel_let : forall L m x oA oM ob A M B,
      Cst.md_abstract m = false ->
      selt L oA A -> selt L oM M -> selt (lb_let x M :: L) ob B ->
      sel L (Cst.letb (Cst.d_def m x oA oM) ob) (s_term ((λ A B) $ M))
  | sel_let_abs : forall L m x oA oM ob A M B,
      Cst.md_abstract m = true ->
      selt L oA A -> selt L oM M -> selt (lb_var x :: L) ob B ->
      sel L (Cst.letb (Cst.d_def m x oA oM) ob) (s_term ((λ A B) $ M))
  (** [let module x := E in B] adds no core binder.  Inside [B], [x] names the
      module that [E] denotes. *)
  | sel_let_mod : forall L x oE ob R B,
      sel L oE (s_mod R) -> selt (lb_mod x R :: L) ob B ->
      sel L (Cst.letb (Cst.d_mod x oE) ob) (s_term B)

  with selt : list lbind -> Cst.obj -> exp -> Prop :=
  | selt_intro : forall L o r M, sel L o r -> as_term r M -> selt L o M.

  (** [sparams] elaborates a parameter list.  Each type can refer to the
      earlier parameters as λ-variables. *)
  Inductive sparams : list lbind -> list (string * Cst.obj) -> list (string * typ) -> Prop :=
  | sp_nil : forall L, sparams L nil nil
  | sp_cons : forall L x oA ps A tys,
      selt L oA A ->
      sparams (lb_var x :: L) ps tys ->
      sparams L ((x, oA) :: ps) ((x, A) :: tys).
End Objects.

(** ** Imports *)

(** [itarget fp O Fs fq ip R] holds when [import fq.ip] refers to the module
    [R].  If [fq] is [nil], the import names a module of the current unit, and
    the dotted name [ip] is resolved as an object with no local binders.
    Otherwise it names a module of another unit, and [R] is opaque. *)
Inductive itarget (fp : fpath) (O : sscope) (Fs : list sframe) : fpath -> list string -> sref -> Prop :=
| it_local : forall x ip R,
    sel fp O Fs nil (fold_left Cst.proj ip (Cst.var x)) (s_mod R) ->
    itarget fp O Fs nil (x :: ip) R
| it_unit : forall fq ip,
    fq <> nil -> itarget fp O Fs fq ip (sr_mk fq ip None nil).

(** [alias_fresh taken sc y] holds when [y] can be made an alias.  It must not
    be one of the [taken] names, which are the members and parameters of the
    frame ([sf_taken]).  It must not be an alias in [sc] either.  The leading
    imports have no frame, so their [taken] is empty. *)
Definition alias_fresh (taken : list string) (sc : sscope) (y : string) : Prop :=
  ~ In y taken /\ ss_free sc y.

(** [use (n₁; …)] binds each [nᵢ] to the member [R.nᵢ], in order.  Each name
    must be fresh, also with respect to the names bound before it. *)
Inductive use_binds (R : sref) (taken : list string) : list string -> sscope -> sscope -> Prop :=
| ub_nil : forall sc, use_binds R taken nil sc sc
| ub_cons : forall n ns t sc sc',
    alias_fresh taken sc n ->
    select R n t ->
    use_binds R taken ns (ss_add n t sc) sc' ->
    use_binds R taken (n :: ns) sc sc'.

(** [ibinds R taken spec sc sc'] holds when importing the module [R] with the
    specification [spec] extends the scope [sc] to [sc'].  A plain import
    binds nothing, [as y] binds [y] to [R], and [use] binds the listed
    members. *)
Inductive ibinds (R : sref) (taken : list string) : Cst.ispec -> sscope -> sscope -> Prop :=
| ib_open : forall sc, ibinds R taken Cst.i_open sc sc
| ib_as : forall y sc, alias_fresh taken sc y -> ibinds R taken (Cst.i_as y) sc (ss_add y (st_mod R) sc)
| ib_use : forall ns sc sc', use_binds R taken ns sc sc' -> ibinds R taken (Cst.i_use ns) sc sc'.

(** Only an import of another unit produces a core command. *)
Definition import_cmd (fq : fpath) (ip : list string) : option ccmd :=
  match fq with
  | nil => None
  | _ => Some (cc_import fq ip)
  end.

Definition opt_list {A} (o : option A) : list A :=
  match o with Some a => a :: nil | None => nil end.

(** [simport fp O Fs taken sc c sc' oc] describes the import command [c] in a
    frame whose scope is [sc] and whose members and parameters are [taken].
    The import is resolved with [O] and [Fs].  It changes the scope to [sc']
    and emits [oc], which is at most one core command. *)
Inductive simport (fp : fpath) (O : sscope) (Fs : list sframe) (taken : list string)
  : sscope -> Cst.cmd -> sscope -> option ccmd -> Prop :=
| si_intro : forall sc fq ip spec R sc',
    itarget fp O Fs fq ip R ->
    ibinds R taken spec (ss_add_unit fq sc) sc' ->
    simport fp O Fs taken sc (Cst.c_import fq ip spec) sc' (import_cmd fq ip).

(** ** Commands

    [scmd fp O Fs F c F'] holds when the command [c] takes the innermost open
    frame [F] to [F'].  Here [fp] is the current unit, [O] is the scope of its
    leading imports, and [Fs] are the frames enclosing [F].  A command changes
    only the innermost frame. *)
Inductive scmd (fp : fpath) (O : sscope) : list sframe -> sframe -> Cst.cmd -> sframe -> Prop :=
(** A definition sees the members declared before it, but not itself.  Its
    name must be fresh in the frame.  [abstract] makes it opaque, and
    [private] makes it private. *)
| sc_def : forall Fs F m x oA oM A M,
    sf_fresh F x ->
    selt fp O (F :: Fs) nil oA A ->
    selt fp O (F :: Fs) nil oM M ->
    scmd fp O Fs F (Cst.c_def m x oA oM)
      (sf_emit F (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A M))
| sc_eval : forall Fs F oM M,
    selt fp O (F :: Fs) nil oM M ->
    scmd fp O Fs F (Cst.c_eval oM None) (sf_emit F (cc_eval M None))
| sc_eval_typ : forall Fs F oM oA M A,
    selt fp O (F :: Fs) nil oM M ->
    selt fp O (F :: Fs) nil oA A ->
    scmd fp O Fs F (Cst.c_eval oM (Some oA)) (sf_emit F (cc_eval M (Some A)))
| sc_import : forall Fs F fq ip spec sc' oc,
    simport fp O (F :: Fs) (sf_taken F) (sf_scope F) (Cst.c_import fq ip spec) sc' oc ->
    scmd fp O Fs F (Cst.c_import fq ip spec) (sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ opt_list oc) sc')
(** [module x (ps) where body end] requires [x] to be fresh in [F] and the
    parameter names to be distinct.  The parameters are elaborated in [F].
    The body is elaborated in a new frame for [x], nested in [F].  The
    resulting module becomes a member of [F]. *)
| sc_mod : forall Fs F x ps body tys N,
    sf_fresh F x ->
    NoDup (map fst ps) ->
    sparams fp O (F :: Fs) nil ps tys ->
    scmds fp O (F :: Fs) (sf_new (sf_path F ++ x :: nil) tys) body N ->
    scmd fp O Fs F (Cst.c_mod (x :: nil) ps body) (sf_emit F (cc_mod x (ptele tys) (sf_cmds N)))
(** [module x.p (ps) where … end] declares a module [x] without parameters,
    fresh in [F], that contains [module p (ps) where … end]. *)
| sc_mod_path : forall Fs F x p ps body N,
    p <> nil ->
    sf_fresh F x ->
    scmd fp O (F :: Fs) (sf_new (sf_path F ++ x :: nil) nil) (Cst.c_mod p ps body) N ->
    scmd fp O Fs F (Cst.c_mod (x :: p) ps body) (sf_emit F (cc_mod x ⋅ (sf_cmds N)))

with scmds (fp : fpath) (O : sscope) : list sframe -> sframe -> list Cst.cmd -> sframe -> Prop :=
| scs_nil : forall Fs F, scmds fp O Fs F nil F
| scs_cons : forall Fs F c cs F1 F2,
    scmd fp O Fs F c F1 -> scmds fp O Fs F1 cs F2 -> scmds fp O Fs F (c :: cs) F2.

(** [simports] elaborates the imports that precede the unit's declaration.
    They lie outside all frames, and each is resolved in the scope that the
    earlier ones built.  An alias only needs to be fresh with respect to the
    earlier leading aliases. *)
Inductive simports (fp : fpath) : sscope -> list Cst.cmd -> sscope -> list ccmd -> Prop :=
| sis_nil : forall O, simports fp O nil O nil
| sis_cons : forall O fq ip spec O1 oc cs O2 is,
    simport fp O nil nil O (Cst.c_import fq ip spec) O1 oc ->
    simports fp O1 cs O2 is ->
    simports fp O (Cst.c_import fq ip spec :: cs) O2 (opt_list oc ++ is).

(** ** Units

    A unit has the form [import …; module fp (ps) where cs end].  Its leading
    imports are elaborated first.  Its parameters, which must have distinct
    names, are elaborated next, in the scope of those imports.  Its body is
    elaborated last, in the unit's own frame, whose member chain is [nil].
    The core unit consists of the commands of the leading imports, the
    parameter context, and the commands of the frame. *)
Inductive elab_spec : Cst.prog -> cunit -> Prop :=
| es_intro : forall imports fp ps cs O imps tys F,
    simports fp ss_empty imports O imps ->
    NoDup (map fst ps) ->
    sparams fp O nil nil ps tys ->
    scmds fp O nil (sf_new nil tys) cs F ->
    elab_spec (imports, (fp, ps, cs)) (imps, ptele tys, sf_cmds F).

(** ** The Invariant

    Elaboration keeps every name bound at most once in each frame, and in the
    scope of the leading imports.  So [fr_binds] gives each name at most one
    meaning, which the correctness proof relies on. *)

Lemma NoDup_insert : forall (l1 l2 : list string) x,
    NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> NoDup (l1 ++ x :: l2).
Proof.
  intros. apply (Permutation_NoDup (Permutation_middle l1 l2 x)).
  constructor; assumption.
Qed.

Lemma decl_names_app : forall cs1 cs2, decl_names (cs1 ++ cs2) = decl_names cs1 ++ decl_names cs2.
Proof. intros; unfold decl_names; apply flat_map_app. Qed.

Lemma sf_wf_emit : forall F c,
    sf_wf F ->
    (forall x, cc_name c = Some x -> sf_fresh F x) ->
    sf_wf (sf_emit F c).
Proof.
  unfold sf_wf, sf_fresh, sf_binds, sf_names, sf_taken, sf_emit; cbn; intros F c Hw Hf.
  rewrite decl_names_app. unfold decl_names at 2; cbn.
  destruct (cc_name c) as [x |]; cbn; rewrite ?app_nil_r, <- ?app_assoc in *; [| assumption ].
  rewrite !app_assoc, <- (app_assoc _ (x :: nil)). cbn. apply NoDup_insert; rewrite <- !app_assoc; [ assumption |].
  apply Hf; reflexivity.
Qed.

Lemma alias_fresh_wf : forall taken sc y t,
    NoDup (map fst (ss_alias sc) ++ taken) -> alias_fresh taken sc y ->
    NoDup (map fst (ss_alias (ss_add y t sc)) ++ taken).
Proof.
  intros * Hw [Ht Hs]. cbn. constructor; [| assumption ].
  intros Hin; apply in_app_or in Hin as [|]; auto.
Qed.

Lemma ibinds_wf : forall R taken spec sc sc',
    ibinds R taken spec sc sc' ->
    NoDup (map fst (ss_alias sc) ++ taken) -> NoDup (map fst (ss_alias sc') ++ taken).
Proof.
  induction 1 as [| | ns sc sc' Hu]; intros Hw; [ assumption | eapply alias_fresh_wf; eassumption |].
  induction Hu; [ assumption |]. apply IHHu. eapply alias_fresh_wf; eassumption.
Qed.

Lemma ss_alias_add_unit : forall fq sc, ss_alias (ss_add_unit fq sc) = ss_alias sc.
Proof. intros [] ?; reflexivity. Qed.

Lemma simport_wf : forall fp O Fs taken sc c sc' oc,
    simport fp O Fs taken sc c sc' oc ->
    NoDup (map fst (ss_alias sc) ++ taken) -> NoDup (map fst (ss_alias sc') ++ taken).
Proof.
  intros * Hs Hw. inversion Hs; subst. eapply ibinds_wf; [ eassumption |].
  rewrite ss_alias_add_unit; assumption.
Qed.

Lemma sf_wf_new : forall ch tys, NoDup (map fst tys) -> sf_wf (sf_new ch tys).
Proof. intros; unfold sf_wf, sf_names, sf_taken, sf_new; cbn; assumption. Qed.

Scheme scmd_wf_ind := Induction for scmd Sort Prop
  with scmds_wf_ind := Induction for scmds Sort Prop.

(** Commands keep a frame well formed. *)
Theorem scmd_wf : forall fp O Fs F c F', scmd fp O Fs F c F' -> sf_wf F -> sf_wf F'.
Proof.
  intros fp O.
  apply (scmd_wf_ind fp O (fun Fs F c F' _ => sf_wf F -> sf_wf F') (fun Fs F cs F' _ => sf_wf F -> sf_wf F'));
    intros; auto.
  - apply sf_wf_emit; [ assumption |]. intros ? [=<-]; assumption.
  - apply sf_wf_emit; [ assumption |]. discriminate.
  - apply sf_wf_emit; [ assumption |]. discriminate.
  - unfold sf_wf, sf_names, sf_taken in *; cbn.
    rewrite decl_names_app.
    replace (decl_names (opt_list oc)) with (@nil string)
      by (inversion s; subst; destruct fq; reflexivity).
    rewrite app_nil_r. eapply simport_wf; eassumption.
  - apply sf_wf_emit; [ assumption |]. intros ? [=<-]; assumption.
  - apply sf_wf_emit; [ assumption |]. intros ? [=<-]; assumption.
Qed.

Theorem scmds_wf : forall fp O Fs F cs F', scmds fp O Fs F cs F' -> sf_wf F -> sf_wf F'.
Proof. induction 1; eauto using scmd_wf. Qed.

Theorem simports_wf : forall fp O cs O' is, simports fp O cs O' is -> ss_wf O -> ss_wf O'.
Proof.
  induction 1; intros Hw; [ assumption |]. apply IHsimports.
  unfold ss_wf in *. pose proof (simport_wf _ _ _ _ _ _ _ _ H) as Hs.
  rewrite !app_nil_r in Hs. auto.
Qed.
