From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Command.

Import Syntax_Notations.

(** * A Declarative Specification of Elaboration

    When a surface unit [Cst.prog] elaborates to the core unit [cunit]: the
    relation [elab_spec] at the end of this file.  It is stated over its own
    small vocabulary — scopes, frames, module references — and mentions none of
    the elaborator's data structures ([Frontend/Resolve.v],
    [Frontend/Elaborator.v]); [Frontend/ElabCorrect.v] proves that
    [elaborate_core] computes exactly this relation.

    The design choices, each a rule below:

    - The members of a frame are *read off the core commands it has emitted
      so far*: a name is a member of a frame iff one of its [cc_def]/[cc_mod]
      declares it, and the members of a nested module are those its own
      [cc_mod] body declares.  So the spec keeps no symbol table besides the
      output.
    - A name is resolved, innermost first, against: the local binders ([λ],
      [Π], [rec], [let], [let module]); then, frame by frame from the innermost
      open frame outward, the frame's import aliases, its members, its
      parameters; then the aliases of the imports that precede the unit.  The
      first binding found wins, so every outer binding is shadowed.
    - A *parameter* of an open frame is a λ-variable; a *member* of an open
      frame is its absolute path [p_abs unit (chain ++ [x])] *pre-applied* to
      the parameters of every frame from its own outward (rule [preapp]).
    - Through a *module reference* ([sref]: a module not open at the use site,
      or one of an imported unit) only public definitions are reachable, and
      no parameter is supplied: the arguments are the ones written.
    - Units are opaque: a path into an imported unit names whatever it names;
      typing decides. *)

(** ** Declarations Read Off Core Commands *)

(** The name a core command declares as a member of its frame. *)
Definition cc_name (c : ccmd) : option string :=
  match c with
  | cc_def x _ _ _ _ | cc_mod x _ _ => Some x
  | cc_import _ _ | cc_eval _ _ => None
  end.

Definition declares (cs : list ccmd) (x : string) : Prop :=
  exists c, In c cs /\ cc_name c = Some x.

(** [c] is the last of the commands [cs] to declare [x]: what [x] means as a
    member of a frame (or module) whose commands are [cs].  The elaborator
    never declares a name twice in one frame, so "last" is "only". *)
Definition cs_member (cs : list ccmd) (x : string) (c : ccmd) : Prop :=
  exists cs1 cs2, cs = cs1 ++ c :: cs2 /\ cc_name c = Some x /\ ~ declares cs2 x.

(** ** What a Name Denotes *)

(** A reference to a module that is not open at the use site: the unit it is
    in and its member chain; its members, as the commands of its [cc_mod]
    ([None] for a module of an imported unit, which is opaque); its arity, the
    number of parameters of the modules from its unit's root down to it
    included, which every member of it is generalized over; and the arguments
    supplied so far, outermost first.  An opaque reference has arity [0]: its
    arguments are not counted, typing checks them. *)
Record sref : Set := sr_mk
  { sr_unit : fpath
  ; sr_mems : list string
  ; sr_sig : option (list ccmd)
  ; sr_arity : nat
  ; sr_args : list exp }.

Definition sr_app (R : sref) (args : list exp) : sref :=
  sr_mk (sr_unit R) (sr_mems R) (sr_sig R) (sr_arity R) (sr_args R ++ args).

(** What an import alias names: a module, or a (public) definition of one. *)
Inductive starget : Set :=
| st_mod : sref -> starget
| st_def : sref -> string -> starget.

(** What an object denotes: a term; a module; or a definition [x] of a module
    reference, which becomes a term once the reference has all its arguments
    ([as_term]).  The last is what lets [M.f a] supply the module argument [a]
    of [M] after the projection. *)
Inductive sres : Set :=
| s_term : exp -> sres
| s_mod : sref -> sres
| s_def : sref -> string -> sres.

Definition st_res (t : starget) : sres :=
  match t with
  | st_mod R => s_mod R
  | st_def R x => s_def R x
  end.

Definition apps (M : exp) (args : list exp) : exp := fold_left a_app args M.

(** Application of a denotation to one argument: a term application, or one
    more argument for a module. *)
Definition sapp (r : sres) (N : exp) : sres :=
  match r with
  | s_term M => s_term (M $ N)
  | s_mod R => s_mod (sr_app R (N :: nil))
  | s_def R x => s_def (sr_app R (N :: nil)) x
  end.

(** When a denotation is a term.  A definition of a module reference needs
    the reference's arity of arguments; a path into an imported unit is a term
    if it names a member at all (typing decides the rest); a module of this
    unit is never a term. *)
Inductive as_term : sres -> exp -> Prop :=
| at_term : forall M, as_term (s_term M) M
| at_def : forall R x,
    sr_arity R <= List.length (sr_args R) ->
    as_term (s_def R x) (apps (a_glob (p_abs (sr_unit R) (sr_mems R ++ x :: nil))) (sr_args R))
| at_opaque : forall R,
    sr_sig R = None ->
    sr_mems R <> nil ->
    as_term (s_mod R) (apps (a_glob (p_abs (sr_unit R) (sr_mems R))) (sr_args R)).

(** *** Member Selection

    [select R x t]: [R.x] denotes [t].  Only a *public* definition can be
    selected: a private one is visible only from its own frame and the frames
    nested in it, which reach it as a member of an open frame ([fbind]), never
    through a reference.  A member of an opaque reference is opaque; its
    privacy is not checked (REVISIT, as in the elaborator). *)
Inductive select : sref -> string -> starget -> Prop :=
| sl_opaque : forall R x,
    sr_sig R = None ->
    select R x (st_mod (sr_mk (sr_unit R) (sr_mems R ++ x :: nil) None 0 (sr_args R)))
| sl_def : forall R x cs b A M,
    sr_sig R = Some cs ->
    cs_member cs x (cc_def x b false A M) ->
    select R x (st_def R x)
| sl_mod : forall R x cs Δ cs',
    sr_sig R = Some cs ->
    cs_member cs x (cc_mod x Δ cs') ->
    select R x (st_mod (sr_mk (sr_unit R) (sr_mems R ++ x :: nil) (Some cs')
                          (sr_arity R + List.length Δ) (sr_args R))).

(** *** Weakening

    A denotation made at one point and used [k] binders further in. *)
Definition shift_by (k : nat) (M : exp) : exp := M[wk_shiftn k]ʷ.

Definition wk_sref (k : nat) (R : sref) : sref :=
  sr_mk (sr_unit R) (sr_mems R) (sr_sig R) (sr_arity R) (map (shift_by k) (sr_args R)).

Definition wk_starget (k : nat) (t : starget) : starget :=
  match t with
  | st_mod R => st_mod (wk_sref k R)
  | st_def R x => st_def (wk_sref k R) x
  end.

(** ** Scopes *)

(** What the imports of one frame (or the leading imports of the unit) bind:
    aliases, latest first, and the units made reachable by their full path. *)
Record sscope : Set := ss_mk
  { ss_alias : list (string * starget)
  ; ss_units : list fpath }.

Definition ss_empty : sscope := ss_mk nil nil.

(** [y] is bound to [t] by the latest alias for it. *)
Definition ss_binds (sc : sscope) (y : string) (t : starget) : Prop :=
  exists al1 al2, ss_alias sc = al1 ++ (y, t) :: al2 /\ ~ In y (map fst al1).

Definition ss_free (sc : sscope) (y : string) : Prop := ~ In y (map fst (ss_alias sc)).

Definition ss_add (y : string) (t : starget) (sc : sscope) : sscope :=
  ss_mk ((y, t) :: ss_alias sc) (ss_units sc).

(** An import of another unit makes it reachable; one of this unit does not. *)
Definition ss_add_unit (fp : fpath) (sc : sscope) : sscope :=
  match fp with
  | nil => sc
  | _ => ss_mk (ss_alias sc) (fp :: ss_units sc)
  end.

(** An open frame: its member chain from the unit's root ([nil] for the unit
    itself), its parameters with their types in declaration order, the core
    commands it has emitted so far in order, and what its imports bind. *)
Record sframe : Set := sf_mk
  { sf_path : list string
  ; sf_params : list (string * typ)
  ; sf_cmds : list ccmd
  ; sf_scope : sscope }.

Definition sf_new (ch : list string) (ps : list (string * typ)) : sframe := sf_mk ch ps nil ss_empty.

Definition sf_emit (F : sframe) (c : ccmd) : sframe :=
  sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ c :: nil) (sf_scope F).

(** A frame's parameters as a core context, innermost first. *)
Definition ptele (ps : list (string * typ)) : ctx := rev (map snd ps).

(** Does the frame bind [x] at all — by an alias, a member, a parameter? *)
Definition sf_binds (F : sframe) (x : string) : Prop :=
  ~ ss_free (sf_scope F) x \/ declares (sf_cmds F) x \/ In x (map fst (sf_params F)).

(** A name can be declared in a frame if the frame has no member and no alias
    of that name.  Shadowing a parameter of the frame, or anything of an
    enclosing frame, is allowed. *)
Definition sf_fresh (F : sframe) (x : string) : Prop :=
  ss_free (sf_scope F) x /\ ~ declares (sf_cmds F) x.

(** ** Pre-application

    The heart of option B.  The parameters of the open frames are λ-variables:
    the frames' telescope, innermost frame first and each frame's last
    parameter first, follows the local binders of the use site.  So a frame
    whose telescope starts [off] binders in has its parameters, in declaration
    order, at

      [#(off + n - 1), …, #(off + 1), #off]      ([n] parameters)

    which is [vars_desc off n].  A member of an open frame is stored closed —
    generalized over the parameters of that frame and all frames enclosing it,
    outermost first — so it is used applied to exactly those variables:

      [preapp off (F :: Fs) args]

    says that the member of the innermost frame [F] of the stack [F :: Fs],
    whose telescope starts [off] binders in, is applied to [args]: the
    variables of the outermost frame first, then inward, ending with those of
    [F].  The frames inside [F] (open at the use site, but not enclosing the
    member) contribute nothing; their parameters are among the [off] binders
    skipped. *)
Definition vars_desc (off n : nat) : list exp :=
  map (fun i => a_var (off + (n - 1 - i))) (seq 0 n).

Inductive preapp : nat -> list sframe -> list exp -> Prop :=
| preapp_nil : forall off, preapp off nil nil
| preapp_cons : forall off F Fs args,
    preapp (off + List.length (sf_params F)) Fs args ->
    preapp off (F :: Fs) (args ++ vars_desc off (List.length (sf_params F))).

(** ** Name Resolution in the Open Frames

    [fbind fp O off Fs x r]: in the unit [fp], with leading imports [O], the
    name [x] — not bound locally — denotes [r] when the telescope of the first
    frame of [Fs] starts [off] binders in.  Within a frame an alias comes
    before a member, a member before a parameter; a frame binding [x] at all
    hides every frame outside it.  An alias was resolved in the scope of its
    frame, outside all its local binders and inner frames' parameters, so it is
    weakened by [off]. *)
Inductive fbind (fp : fpath) (O : sscope) : nat -> list sframe -> string -> sres -> Prop :=
| fb_alias : forall off F Fs x t,
    ss_binds (sf_scope F) x t ->
    fbind fp O off (F :: Fs) x (st_res (wk_starget off t))
(** A member definition of an open frame, private or not, pre-applied. *)
| fb_def : forall off F Fs x b pv A M vs,
    ss_free (sf_scope F) x ->
    cs_member (sf_cmds F) x (cc_def x b pv A M) ->
    preapp off (F :: Fs) vs ->
    fbind fp O off (F :: Fs) x (s_term (apps (a_glob (p_abs fp (sf_path F ++ x :: nil))) vs))
(** A module member of an open frame: a reference, pre-applied likewise; its
    arity counts those arguments and its own parameters. *)
| fb_mod : forall off F Fs x Δ cs vs,
    ss_free (sf_scope F) x ->
    cs_member (sf_cmds F) x (cc_mod x Δ cs) ->
    preapp off (F :: Fs) vs ->
    fbind fp O off (F :: Fs) x
      (s_mod (sr_mk fp (sf_path F ++ x :: nil) (Some cs) (List.length vs + List.length Δ) vs))
(** A parameter: the variable [preapp] passes for it — the last parameter of
    that name, as many binders past [off] as there are parameters after it. *)
| fb_param : forall off F Fs x ps1 A ps2,
    ss_free (sf_scope F) x ->
    ~ declares (sf_cmds F) x ->
    sf_params F = ps1 ++ (x, A) :: ps2 ->
    ~ In x (map fst ps2) ->
    fbind fp O off (F :: Fs) x (s_term (a_var (off + List.length ps2)))
| fb_next : forall off F Fs x r,
    ~ sf_binds F x ->
    fbind fp O (off + List.length (sf_params F)) Fs x r ->
    fbind fp O off (F :: Fs) x r
(** Outside all frames: the leading imports' aliases. *)
| fb_outer : forall off x t,
    ss_binds O x t ->
    fbind fp O off nil x (st_res (wk_starget off t)).

(** ** Local Binders *)

(** A local binding: a λ-variable (also an [abstract] [let], whose body is
    hidden behind its binder), a transparent [let] (inlined, so its binder is
    unused), or a [let module] (no binder). *)
Inductive lbind : Set :=
| lb_var : string -> lbind
| lb_let : string -> exp -> lbind
| lb_mod : string -> sref -> lbind.

Definition lb_name (b : lbind) : string :=
  match b with lb_var x | lb_let x _ | lb_mod x _ => x end.

Definition lb_binders (b : lbind) : nat :=
  match b with lb_var _ | lb_let _ _ => 1 | lb_mod _ _ => 0 end.

(** The number of core binders of the local bindings [L], innermost first. *)
Definition nbinders (L : list lbind) : nat := fold_right (fun b n => lb_binders b + n) 0 L.

(** [x] is bound by [b], the innermost binding of that name, with [k] binders
    between [b] and the use site. *)
Definition lbound (L : list lbind) (x : string) (k : nat) (b : lbind) : Prop :=
  exists L1 L2, L = L1 ++ b :: L2 /\ lb_name b = x /\ ~ In x (map lb_name L1) /\ k = nbinders L1.

(** What a local binding denotes [k] binders in: a [let]'s body was
    elaborated outside its own binder, so it moves [k + 1]. *)
Definition ldenote (k : nat) (b : lbind) : sres :=
  match b with
  | lb_var _ => s_term (a_var k)
  | lb_let _ M => s_term (shift_by (S k) M)
  | lb_mod _ R => s_mod (wk_sref k R)
  end.

(** ** Objects

    [sel fp O Fs L o r]: in the unit [fp], with leading imports [O], open
    frames [Fs] (innermost first) and local bindings [L], the object [o]
    denotes [r]; [selt] when it denotes the term [M]. *)

(** A unit can be named by its full path only where it is imported: by a
    leading import or one of an open frame. *)
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
  (** A term application, or a module argument: [sapp] decides by the head. *)
  | sel_app : forall L o1 o2 r N,
      selt L o2 N -> sel L o1 r -> sel L (Cst.app o1 o2) (sapp r N)
  | sel_local : forall L x k b,
      lbound L x k b -> sel L (Cst.var x) (ldenote k b)
  | sel_frame : forall L x r,
      ~ In x (map lb_name L) ->
      fbind fp O (nbinders L) Fs x r ->
      sel L (Cst.var x) r
  | sel_glob : forall L fq,
      unit_in fq O Fs -> sel L (Cst.glob fq) (s_mod (sr_mk fq nil None 0 nil))
  | sel_proj : forall L o x R t,
      sel L o (s_mod R) -> select R x t -> sel L (Cst.proj o x) (st_res t)
  (** [let x : A := M in B]: one core binder, [(λ A B) $ M].  Inside [B], a
      transparent [x] is [M] itself, an [abstract] one the bound variable. *)
  | sel_let : forall L m x oA oM ob A M B,
      Cst.md_abstract m = false ->
      selt L oA A -> selt L oM M -> selt (lb_let x M :: L) ob B ->
      sel L (Cst.letb (Cst.d_def m x oA oM) ob) (s_term ((λ A B) $ M))
  | sel_let_abs : forall L m x oA oM ob A M B,
      Cst.md_abstract m = true ->
      selt L oA A -> selt L oM M -> selt (lb_var x :: L) ob B ->
      sel L (Cst.letb (Cst.d_def m x oA oM) ob) (s_term ((λ A B) $ M))
  (** [let module x := E in B] emits nothing: [x] names the module [E]. *)
  | sel_let_mod : forall L x oE ob R B,
      sel L oE (s_mod R) -> selt (lb_mod x R :: L) ob B ->
      sel L (Cst.letb (Cst.d_mod x oE) ob) (s_term B)

  with selt : list lbind -> Cst.obj -> exp -> Prop :=
  | selt_intro : forall L o r M, sel L o r -> as_term r M -> selt L o M.

  (** A parameter telescope: each type sees the earlier parameters as
      λ-variables. *)
  Inductive sparams : list lbind -> list (string * Cst.obj) -> list (string * typ) -> Prop :=
  | sp_nil : forall L, sparams L nil nil
  | sp_cons : forall L x oA ps A tys,
      selt L oA A ->
      sparams (lb_var x :: L) ps tys ->
      sparams L ((x, oA) :: ps) ((x, A) :: tys).
End Objects.

(** ** Imports *)

(** What [import fq.ip] refers to.  A module of this unit ([fq = nil]) is the
    dotted name [ip] resolved as an object, outside any local binder; a module
    of another unit is opaque. *)
Inductive itarget (fp : fpath) (O : sscope) (Fs : list sframe) : fpath -> list string -> sref -> Prop :=
| it_local : forall x ip R,
    sel fp O Fs nil (fold_left Cst.proj ip (Cst.var x)) (s_mod R) ->
    itarget fp O Fs nil (x :: ip) R
| it_unit : forall fq ip,
    fq <> nil -> itarget fp O Fs fq ip (sr_mk fq ip None 0 nil).

(** [use (n₁; …)] binds each [nᵢ] in turn to the member [R.nᵢ]; the names may
    not repeat an alias of the scope. *)
Inductive use_binds (R : sref) : list string -> sscope -> sscope -> Prop :=
| ub_nil : forall sc, use_binds R nil sc sc
| ub_cons : forall n ns t sc sc',
    ss_free sc n ->
    select R n t ->
    use_binds R ns (ss_add n t sc) sc' ->
    use_binds R (n :: ns) sc sc'.

Inductive ibinds (R : sref) : Cst.ispec -> sscope -> sscope -> Prop :=
| ib_open : forall sc, ibinds R Cst.i_open sc sc
| ib_as : forall y sc, ss_free sc y -> ibinds R (Cst.i_as y) sc (ss_add y (st_mod R) sc)
| ib_use : forall ns sc sc', use_binds R ns sc sc' -> ibinds R (Cst.i_use ns) sc sc'.

(** Only an import of another unit is a core command. *)
Definition import_cmd (fq : fpath) (ip : list string) : option ccmd :=
  match fq with
  | nil => None
  | _ => Some (cc_import fq ip)
  end.

Definition opt_list {A} (o : option A) : list A :=
  match o with Some a => a :: nil | None => nil end.

(** An import, resolved in the scope [O]/[Fs], updates the import scope [sc]
    and emits at most one command. *)
Inductive simport (fp : fpath) (O : sscope) (Fs : list sframe) : sscope -> Cst.cmd -> sscope -> option ccmd -> Prop :=
| si_intro : forall sc fq ip spec R sc',
    itarget fp O Fs fq ip R ->
    ibinds R spec (ss_add_unit fq sc) sc' ->
    simport fp O Fs sc (Cst.c_import fq ip spec) sc' (import_cmd fq ip).

(** ** Commands

    [scmd fp O Fs F c F']: in the unit [fp] with leading imports [O], the
    command [c] takes the innermost open frame [F], enclosed by the frames
    [Fs], to [F'].  A command only ever changes the innermost frame. *)
Inductive scmd (fp : fpath) (O : sscope) : list sframe -> sframe -> Cst.cmd -> sframe -> Prop :=
(** A definition sees the members before it, not itself; [abstract] makes it
    opaque, [private] private. *)
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
    simport fp O (F :: Fs) (sf_scope F) (Cst.c_import fq ip spec) sc' oc ->
    scmd fp O Fs F (Cst.c_import fq ip spec) (sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ opt_list oc) sc')
(** [module x (ps) where body end]: the parameters are elaborated in [F],
    the body in a new frame [x] inside it, which becomes a member of [F]. *)
| sc_mod : forall Fs F x ps body tys N,
    sf_fresh F x ->
    sparams fp O (F :: Fs) nil ps tys ->
    scmds fp O (F :: Fs) (sf_new (sf_path F ++ x :: nil) tys) body N ->
    scmd fp O Fs F (Cst.c_mod (x :: nil) ps body) (sf_emit F (cc_mod x (ptele tys) (sf_cmds N)))
(** [module x.p (ps) where …]: a module [x] without parameters, holding
    [module p (ps) where …]. *)
| sc_mod_path : forall Fs F x p ps body N,
    p <> nil ->
    sf_fresh F x ->
    scmd fp O (F :: Fs) (sf_new (sf_path F ++ x :: nil) nil) (Cst.c_mod p ps body) N ->
    scmd fp O Fs F (Cst.c_mod (x :: p) ps body) (sf_emit F (cc_mod x ⋅ (sf_cmds N)))

with scmds (fp : fpath) (O : sscope) : list sframe -> sframe -> list Cst.cmd -> sframe -> Prop :=
| scs_nil : forall Fs F, scmds fp O Fs F nil F
| scs_cons : forall Fs F c cs F1 F2,
    scmd fp O Fs F c F1 -> scmds fp O Fs F1 cs F2 -> scmds fp O Fs F (c :: cs) F2.

(** The imports that precede the unit's declaration: outside all frames, each
    resolved in the scope the earlier ones built. *)
Inductive simports (fp : fpath) : sscope -> list Cst.cmd -> sscope -> list ccmd -> Prop :=
| sis_nil : forall O, simports fp O nil O nil
| sis_cons : forall O fq ip spec O1 oc cs O2 is,
    simport fp O nil O (Cst.c_import fq ip spec) O1 oc ->
    simports fp O1 cs O2 is ->
    simports fp O (Cst.c_import fq ip spec :: cs) O2 (opt_list oc ++ is).

(** ** Units

    A unit [import …; module fp (ps) where cs end]: the leading imports; the
    parameters, which see them; the body, in the unit's own frame (member
    chain [nil]).  It elaborates to its leading imports' commands, its
    parameter telescope, and its frame's commands. *)
Inductive elab_spec : Cst.prog -> cunit -> Prop :=
| es_intro : forall imports fp ps cs O imps tys F,
    simports fp ss_empty imports O imps ->
    sparams fp O nil nil ps tys ->
    scmds fp O nil (sf_new nil tys) cs F ->
    elab_spec (imports, (fp, ps, cs)) (imps, ptele tys, sf_cmds F).
