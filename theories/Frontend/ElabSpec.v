From Stdlib Require Import List Permutation String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members Command.

Import Syntax_Notations.

(** * A Declarative Specification of Elaboration

    [elab_spec prg u] holds when the surface unit [prg] elaborates to the core
    unit [u].  [Frontend/ElabCorrect.v] proves that [elaborate_core] computes
    exactly this relation.

    Elaboration only resolves names; it never looks inside a module.

    - The members of a frame are the names declared by the core commands it
      has emitted so far, so there is no separate symbol table.
    - A frame binds each name at most once, as an import alias, a member or a
      parameter.  Redeclaring a name in the same frame is an error; declaring
      a name that an enclosing frame binds shadows it.
    - A name is looked up in the local binders, then in the open frames from
      the innermost outward, then in the aliases of the unit's leading
      imports.
    - The parameters of the open frames are λ-variables.  A member of an open
      frame is its absolute path applied to the parameters of its own frame
      and of every enclosing frame.
    - Where an object stands decides what it is: the head of a projection,
      the head of an application there, an alias body and an import target
      are module expressions ([selm]), everything else is a term ([sel]).  A
      projection is the core's member selection, so what [M.x] names, and
      whether it may be named, is left to typing.

    The running example of this file is

<<
module Main where
  module M (A : Type@0) where
    def id (x : A) : A := x end
    module N (B : Type@0) where
      def k (x : A) (y : B) : A := id x end
    end
  end
  def j : forall (x : Nat) -> Nat := M.id Nat end
end
>>

    which elaborates to the core unit below ([ElabExamples.running_spec]).
    [Main.M.id] abbreviates [a_glob (p_abs ["Main"] ["M"; "id"])], [⟨Main.M⟩]
    the module expression [me_path (p_abs ["Main"] ["M"])], and the flags of
    [cc_def] are omitted.

<<
cc_mod "M" (⋅ ▹ Type@0)
  [ cc_def "id" (Π #0 #1) (λ #0 #0);
    cc_mod "N" (⋅ ▹ Type@0)
      [ cc_def "k" (Π #1 (Π #1 #3)) (λ #1 (λ #1 (Main.M.id $ #3 $ #1))) ] ];
cc_def "j" (Π ℕ ℕ) (⟨Main.M⟩.id $ ℕ)
>>

    In the body of [k], [A] is [#3], so [id x] is [Main.M.id $ #3 $ #1].  In
    [j], [M] is closed, so [M.id] selects the member [id] of the module
    [⟨Main.M⟩], and [A] is written: [M.id Nat]. *)

(** ** Declarations Read Off Core Commands *)

(** [cc_name c] is the name that the core command [c] declares, if any. *)
Definition cc_name (c : ccmd) : option string :=
  match c with
  | cc_def x _ _ _ _ | cc_mod x _ _ | cc_alias x _ _ => Some x
  | cc_import _ _ _ | cc_eval _ _ => None
  end.

(** [declares cs x] holds when some command in [cs] declares [x]. *)
Definition declares (cs : list ccmd) (x : string) : Prop :=
  exists c, In c cs /\ cc_name c = Some x.

(** [decl_names cs] lists the names that [cs] declares, in order. *)
Definition decl_names (cs : list ccmd) : list string :=
  flat_map (fun c => match cc_name c with Some x => x :: nil | None => nil end) cs.

(** ** What a Name Denotes *)

(** An import alias: [as y] names the imported module, and [use (n)] its
    member [n], whatever that is. *)
Inductive starget : Set :=
| st_mod : modexp -> starget
| st_mem : modexp -> string -> starget.

(** [wk_starget k t] is [t] seen [k] binders further in. *)
Definition wk_starget (k : nat) (t : starget) : starget :=
  match t with
  | st_mod E => st_mod (modexp_wk E (wk_shiftn k))
  | st_mem E n => st_mem (modexp_wk E (wk_shiftn k)) n
  end.

(** A name denotes a member of an open frame, applied to its frames'
    parameters; a variable; or an alias. *)
Inductive sden : Set :=
| sd_glob : path -> list exp -> sden
| sd_var : nat -> sden
| sd_alias : starget -> sden.

(** [mapps H args] applies the module expression [H] to each of [args] in
    turn. *)
Definition mapps (H : modexp) (args : list exp) : modexp := fold_left me_app args H.

(** What a denotation is as a term.  A module alias is not one. *)
Inductive den_term : sden -> exp -> Prop :=
| dt_glob : forall p vs, den_term (sd_glob p vs) (apps (a_glob p) vs)
| dt_var : forall k, den_term (sd_var k) #k
| dt_mem : forall E n, den_term (sd_alias (st_mem E n)) (a_mem E n).

(** What a denotation is as a module expression.  A variable is a module slot;
    the core rejects it if it is a term variable. *)
Inductive den_mod : sden -> modexp -> Prop :=
| dm_glob : forall p vs, den_mod (sd_glob p vs) (mapps (me_path p) vs)
| dm_var : forall k, den_mod (sd_var k) (me_var k)
| dm_alias : forall E, den_mod (sd_alias (st_mod E)) E
| dm_mem : forall E n, den_mod (sd_alias (st_mem E n)) (me_mem E n).

(** ** Scopes *)

(** A scope records what the imports of a frame, or the leading imports of a
    unit, bind.

    - [ss_alias] lists the aliases, latest first.
    - [ss_units] lists the imported units, which can be named by their full
      path. *)
Record sscope : Set := ss_mk
  { ss_alias : list (string * starget)
  ; ss_units : list fpath }.

(** The empty scope binds nothing. *)
Definition ss_empty : sscope := ss_mk nil nil.

(** [ss_binds sc y t] holds when [sc] has the alias [y] for [t]. *)
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

    While the body of [k] is elaborated, three frames are open, innermost
    first.

    - [N] has path [["M"; "N"]], parameter [B], and no commands yet.
    - [M] has path [["M"]], parameter [A], and the command for [id].
    - [Main] has path [nil], no parameters, and no commands yet.  The command
      for [M] is emitted only when [M] ends. *)
Record sframe : Set := sf_mk
  { sf_path : list string
  ; sf_params : list (string * typ)
  ; sf_cmds : list ccmd
  ; sf_scope : sscope }.

(** [sf_new ch ps] is an empty frame with member chain [ch] and parameters
    [ps]. *)
Definition sf_new (ch : list string) (ps : list (string * typ)) : sframe := sf_mk ch ps nil ss_empty.

(** [sf_emit F c] appends the command [c] to [F]. *)
Definition sf_emit (F : sframe) (c : ccmd) : sframe :=
  sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ c :: nil) (sf_scope F).

(** [ptele ps] is the parameter list [ps] as a core context, innermost
    first. *)
Definition ptele (ps : list (string * typ)) : ctx := rev (map (fun p => ce_ass (snd p)) ps).

(** [sf_taken F] lists the names that [F] binds as members or parameters. *)
Definition sf_taken (F : sframe) : list string := decl_names (sf_cmds F) ++ map fst (sf_params F).

(** [sf_names F] lists all the names that [F] binds: its aliases, its members
    and its parameters. *)
Definition sf_names (F : sframe) : list string := map fst (ss_alias (sf_scope F)) ++ sf_taken F.

(** [sf_binds F x] holds when [F] binds [x]. *)
Definition sf_binds (F : sframe) (x : string) : Prop := In x (sf_names F).

(** A member or alias may be declared in a frame only if the frame does not
    bind its name yet.  Names bound by enclosing frames may be shadowed. *)
Definition sf_fresh (F : sframe) (x : string) : Prop := ~ sf_binds F x.

(** [sf_wf F] states that [F] binds each name at most once. *)
Definition sf_wf (F : sframe) : Prop := NoDup (sf_names F).

(** ** Pre-application

    The parameters of the open frames are λ-variables.  Seen from a use site,
    the local binders come first, then the parameters of the innermost frame,
    then those of the next frame outward, and so on; within a frame, the last
    parameter is the nearest.  If [off] binders lie between the use site and
    the last of [n] parameters of a frame, then its parameters, in declaration
    order, are [vars_desc off n]:

<<
#(off + n - 1), …, #(off + 1), #off
>>

    A member is generalized over the parameters of its own frame and of every
    enclosing frame, outermost first, so a use applies it to those variables.
    [preapp off (F :: Fs) args] holds when [args] are these variables for a
    member of [F], where [Fs] encloses [F] and [off] binders lie between the
    use site and the last parameter of [F].  Frames nested inside [F]
    contribute no arguments; their parameters are among the [off] binders.

    In the body of [k], [id] is a member of [M], and [y], [x] and [B] lie
    between the use site and [A], so [preapp 3 [M; Main] [#3]] holds. *)
Definition vars_desc (off n : nat) : list exp :=
  map (fun i => a_var (off + (n - 1 - i))) (seq 0 n).

Inductive preapp : nat -> list sframe -> list exp -> Prop :=
| preapp_nil : forall off, preapp off nil nil
| preapp_cons : forall off F Fs args,
    preapp (off + List.length (sf_params F)) Fs args ->
    preapp off (F :: Fs) (args ++ vars_desc off (List.length (sf_params F))).

(** ** Name Resolution in the Open Frames *)

(** [fr_binds fp off Fs F x d] holds when the open frame [F] binds [x] to
    [d].  Here [fp] is the current unit, [Fs] are the frames enclosing [F],
    and [off] binders lie between the use site and the last parameter of
    [F]. *)
Inductive fr_binds (fp : fpath) (off : nat) (Fs : list sframe) (F : sframe) : string -> sden -> Prop :=
(** An alias was resolved outside these [off] binders. *)
| fr_alias : forall x t,
    ss_binds (sf_scope F) x t ->
    fr_binds fp off Fs F x (sd_alias (wk_starget off t))
(** A member, a definition or a module, is its absolute path applied to the
    variables given by [preapp]. *)
| fr_mem : forall x vs,
    declares (sf_cmds F) x ->
    preapp off (F :: Fs) vs ->
    fr_binds fp off Fs F x (sd_glob (p_abs fp (sf_path F ++ x :: nil)) vs)
(** A parameter lies [off] binders back, plus one for each later
    parameter. *)
| fr_param : forall x ps1 A ps2,
    sf_params F = ps1 ++ (x, A) :: ps2 ->
    fr_binds fp off Fs F x (sd_var (off + List.length ps2)).

(** [fbind fp O off Fs x d] holds when the name [x], which is not bound
    locally, denotes [d].  Here [O] is the scope of the unit's leading
    imports, and [off] binders lie between the use site and the last parameter
    of the first frame in [Fs].  The innermost frame that binds [x] decides;
    if none does, the aliases of [O] are used.

    In the body of [k], [N] does not bind [id], so the search moves to [M]
    with [off] increased from [2] to [3]; [M] binds [id], which denotes
    [Main.M.id $ #3]. *)
Inductive fbind (fp : fpath) (O : sscope) : nat -> list sframe -> string -> sden -> Prop :=
| fb_here : forall off F Fs x d,
    fr_binds fp off Fs F x d ->
    fbind fp O off (F :: Fs) x d
| fb_next : forall off F Fs x d,
    ~ sf_binds F x ->
    fbind fp O (off + List.length (sf_params F)) Fs x d ->
    fbind fp O off (F :: Fs) x d
| fb_outer : forall off x t,
    ss_binds O x t ->
    fbind fp O off nil x (sd_alias (wk_starget off t)).

(** ** Local Bindings *)

(** A local binding is a core binder, introduced by a λ, a Π, a recursor, a
    [let], a module parameter or an entry of a local body; or an alias, made
    by an import inside a local body, which introduces none. *)
Inductive lbind : Set :=
| lb_var : string -> lbind
| lb_alias : string -> starget -> lbind.

Definition lb_name (b : lbind) : string :=
  match b with lb_var x | lb_alias x _ => x end.

(** [lb_binders b] is the number of core binders that [b] introduces. *)
Definition lb_binders (b : lbind) : nat :=
  match b with lb_var _ => 1 | lb_alias _ _ => 0 end.

(** [nbinders L] is the number of core binders in [L], which is listed
    innermost first. *)
Definition nbinders (L : list lbind) : nat := fold_right (fun b n => lb_binders b + n) 0 L.

(** [lbound L x k b] holds when [b] is the innermost binding of [x] in [L],
    and [k] core binders lie between [b] and the use site. *)
Definition lbound (L : list lbind) (x : string) (k : nat) (b : lbind) : Prop :=
  exists L1 L2, L = L1 ++ b :: L2 /\ lb_name b = x /\ ~ In x (map lb_name L1) /\ k = nbinders L1.

(** [ldenote k b] is what [b] denotes [k] binders further in. *)
Definition ldenote (k : nat) (b : lbind) : sden :=
  match b with
  | lb_var _ => sd_var k
  | lb_alias _ t => sd_alias (wk_starget k t)
  end.

(** [lparams ps] are the binders of the parameters [ps], innermost first. *)
Definition lparams (ps : list (string * Cst.obj)) : list lbind := rev (map (fun p => lb_var (fst p)) ps).

(** The names an import [use]s, which the core checks. *)
Definition ispec_names (spec : Cst.ispec) : list string :=
  match spec with
  | Cst.i_use ns => ns
  | _ => nil
  end.

(** The unit an import loads first, if any. *)
Definition ifile (fq : fpath) : option fpath :=
  match fq with
  | nil => None
  | _ => Some fq
  end.

(** ** Objects

    [sel fp O Fs L o M] holds when the surface object [o] denotes the term
    [M], and [selm fp O Fs L o H] when it denotes the module expression [H].
    Here [fp] is the current unit, [O] is the scope of its leading imports,
    [Fs] are the open frames, innermost first, and [L] are the local
    bindings.  [sunit] gives the unit of a local module, [sdef] its
    definition and [sbody] its body.

    The body of [k] is elaborated with [L = [lb_var "y"; lb_var "x"]], so [x]
    is [#1], [id] is resolved by [fbind] with [off = 2], and [id x] is
    [Main.M.id $ #3 $ #1]. *)

(** [unit_in fp O Fs] holds when the unit [fp] is imported, by a leading
    import or in an open frame, and so can be named by its full path. *)
Definition unit_in (fp : fpath) (O : sscope) (Fs : list sframe) : Prop :=
  In fp (ss_units O) \/ exists F, In F Fs /\ In fp (ss_units (sf_scope F)).

Section Objects.
  Variable (fp : fpath) (O : sscope) (Fs : list sframe).

  (** What an import inside a local body names: a module of this unit,
      reached by name, or the module of another unit at a member path. *)
  Inductive ltarget : list lbind -> fpath -> list string -> modexp -> Prop :=
  | lt_local : forall L x ip E,
      selm L (fold_left Cst.proj ip (Cst.var x)) E ->
      ltarget L nil (x :: ip) E
  | lt_unit : forall L fq ip,
      fq <> nil -> ltarget L fq ip (me_path (p_abs fq ip))

  with sel : list lbind -> Cst.obj -> exp -> Prop :=
  | sel_typ : forall L n, sel L (Cst.typ n) (Type@n)
  | sel_nat : forall L, sel L Cst.nat ℕ
  | sel_zero : forall L, sel L Cst.zero zero
  | sel_succ : forall L o M, sel L o M -> sel L (Cst.succ o) (succ M)
  | sel_natrec : forall L on mx om oz sx sr os N A MZ MS,
      sel L on N ->
      sel (lb_var mx :: L) om A ->
      sel L oz MZ ->
      sel (lb_var sr :: lb_var sx :: L) os MS ->
      sel L (Cst.natrec on mx om oz sx sr os) (rec N return A | zero -> MZ | succ -> MS end)
  | sel_true_ty : forall L, sel L Cst.true_ty ⊤
  | sel_true_tm : forall L, sel L Cst.true_tm ⋆
  | sel_false_ty : forall L, sel L Cst.false_ty ⊥
  | sel_exfalso : forall L om mx oA M A,
      sel L om M ->
      sel (lb_var mx :: L) oA A ->
      sel L (Cst.exfalso om mx oA) (efq M return A)
  | sel_pi : forall L x oA oB A B,
      sel L oA A -> sel (lb_var x :: L) oB B -> sel L (Cst.pi x oA oB) (Π A B)
  | sel_fn : forall L x oA oM A M,
      sel L oA A -> sel (lb_var x :: L) oM M -> sel L (Cst.fn x oA oM) (λ A M)
  | sel_app : forall L o1 o2 M N,
      sel L o1 M -> sel L o2 N -> sel L (Cst.app o1 o2) (M $ N)
  | sel_local : forall L x k b M,
      lbound L x k b -> den_term (ldenote k b) M -> sel L (Cst.var x) M
  | sel_frame : forall L x d M,
      ~ In x (map lb_name L) ->
      fbind fp O (nbinders L) Fs x d ->
      den_term d M ->
      sel L (Cst.var x) M
  (** A projection selects a member of the module its head denotes. *)
  | sel_proj : forall L o x H,
      selm L o H -> sel L (Cst.proj o x) (a_mem H x)
  (** [let x : A := M in B end] elaborates to the core [ℓ A ≔ M in B].
      Inside [B], [x] is the variable of the [let], which the core binds to
      [M]. *)
  | sel_let : forall L x oA oM ob A M B,
      sel L oA A -> sel L oM M -> sel (lb_var x :: L) ob B ->
      sel L (Cst.letb (Cst.d_def x oA oM) ob) (ℓ A ≔ M in B)
  (** [let module x (ps) md in B end] binds the slot of a local module. *)
  | sel_let_mod : forall L x ps md ob U B,
      sunit L ps md U -> sel (lb_var x :: L) ob B ->
      sel L (Cst.letb (Cst.d_mod x ps md) ob) (ℓₘ U in B)

  with selm : list lbind -> Cst.obj -> modexp -> Prop :=
  | selm_local : forall L x k b H,
      lbound L x k b -> den_mod (ldenote k b) H -> selm L (Cst.var x) H
  | selm_frame : forall L x d H,
      ~ In x (map lb_name L) ->
      fbind fp O (nbinders L) Fs x d ->
      den_mod d H ->
      selm L (Cst.var x) H
  | selm_glob : forall L fq,
      unit_in fq O Fs -> selm L (Cst.glob fq) (me_path (p_abs fq nil))
  | selm_proj : forall L o y H,
      selm L o H -> selm L (Cst.proj o y) (me_mem H y)
  | selm_app : forall L o1 o2 H N,
      selm L o1 H -> sel L o2 N -> selm L (Cst.app o1 o2) (me_app H N)

  (** [sparams] elaborates a parameter list.  Each type can refer to the
      earlier parameters as λ-variables. *)
  with sparams : list lbind -> list (string * Cst.obj) -> list (string * typ) -> Prop :=
  | sp_nil : forall L, sparams L nil nil
  | sp_cons : forall L x oA ps A tys,
      sel L oA A ->
      sparams (lb_var x :: L) ps tys ->
      sparams L ((x, oA) :: ps) ((x, A) :: tys)

  (** A local module: its parameters, then its definition under them. *)
  with sunit : list lbind -> list (string * Cst.obj) -> Cst.mdef -> gunit -> Prop :=
  | su_intro : forall L ps md tys D,
      NoDup (map fst ps) ->
      sparams L ps tys ->
      sdef (lparams ps ++ L) md D ->
      sunit L ps md (gu_mk (ptele tys) D)

  with sdef : list lbind -> Cst.mdef -> moddef -> Prop :=
  | sdf_alias : forall L oE E,
      selm L oE E -> sdef L (Cst.md_alias oE) (md_alias E)
  | sdf_where : forall L cs Φ,
      sbody L gm_nil cs Φ -> sdef L (Cst.md_where cs) (md_body Φ)

  (** [sbody L Φ cs Φ']: the commands [cs] extend the body [Φ], seen with the
      bindings [L], to [Φ'].  Each entry binds its name for the entries after
      it.  An import is a check entry, which binds its aliases but no core
      variable.  The core rejects what a local body may not contain, an
      opaque definition and an [eval]. *)
  with sbody : list lbind -> gmod -> list Cst.cmd -> gmod -> Prop :=
  | sb_nil : forall L Φ, sbody L Φ nil Φ
  | sb_def : forall L Φ m x oA oM A M cs Φ',
      sel L oA A -> sel L oM M ->
      sbody (lb_var x :: L) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs Φ' ->
      sbody L Φ (Cst.c_def m x oA oM :: cs) Φ'
  | sb_mod : forall L Φ x ps md U cs Φ',
      sunit L ps md U ->
      sbody (lb_var x :: L) (gm_ext Φ x (ge_mod U)) cs Φ' ->
      sbody L Φ (Cst.c_mod (x :: nil) ps md :: cs) Φ'
  (** [module x.p (ps) md] is a module [x] without parameters that contains
      [module p (ps) md]. *)
  | sb_mod_path : forall L Φ x p ps md U cs Φ',
      p <> nil ->
      sunit L nil (Cst.md_where (Cst.c_mod p ps md :: nil)) U ->
      sbody (lb_var x :: L) (gm_ext Φ x (ge_mod U)) cs Φ' ->
      sbody L Φ (Cst.c_mod (x :: p) ps md :: cs) Φ'
  | sb_import : forall L Φ fq ip spec E L' cs Φ',
      ltarget L fq ip E ->
      libinds E spec L L' ->
      sbody L' (gm_check Φ (bc_import E (ispec_names spec))) cs Φ' ->
      sbody L Φ (Cst.c_import fq ip spec :: cs) Φ'
  | sb_eval : forall L Φ oM M cs Φ',
      sel L oM M ->
      sbody L (gm_check Φ (bc_eval M None)) cs Φ' ->
      sbody L Φ (Cst.c_eval oM None :: cs) Φ'
  | sb_eval_typ : forall L Φ oM oA M A cs Φ',
      sel L oM M -> sel L oA A ->
      sbody L (gm_check Φ (bc_eval M (Some A))) cs Φ' ->
      sbody L Φ (Cst.c_eval oM (Some oA) :: cs) Φ'

  (** What an import binds in a local body: [as y] the module, [use (ns)]
      each of its members [ns]. *)
  with libinds : modexp -> Cst.ispec -> list lbind -> list lbind -> Prop :=
  | lib_open : forall E L, libinds E Cst.i_open L L
  | lib_as : forall E y L, libinds E (Cst.i_as y) L (lb_alias y (st_mod E) :: L)
  | lib_use : forall E ns L,
      libinds E (Cst.i_use ns) L (fold_left (fun L n => lb_alias n (st_mem E n) :: L) ns L).
End Objects.

(** ** Imports *)

(** [itarget fp O Fs fq ip E] holds when [import fq.ip] refers to the module
    expression [E].  If [fq] is [nil], the import names a module of the
    current unit, and the dotted name [ip] is resolved as a module expression
    with no local binders.  Otherwise it names the module of another unit at
    the member path [ip]. *)
Inductive itarget (fp : fpath) (O : sscope) (Fs : list sframe) : fpath -> list string -> modexp -> Prop :=
| it_local : forall x ip E,
    selm fp O Fs nil (fold_left Cst.proj ip (Cst.var x)) E ->
    itarget fp O Fs nil (x :: ip) E
| it_unit : forall fq ip,
    fq <> nil -> itarget fp O Fs fq ip (me_path (p_abs fq ip)).

(** [alias_fresh taken sc y] holds when [y] is neither one of the frame's
    members and parameters [taken] nor an alias in [sc].  For the leading
    imports, [taken] is empty. *)
Definition alias_fresh (taken : list string) (sc : sscope) (y : string) : Prop :=
  ~ In y taken /\ ss_free sc y.

(** [use (n₁; …)] binds each [nᵢ] to the member [E.nᵢ], in order; each name
    must be fresh, including against the earlier ones. *)
Inductive use_binds (E : modexp) (taken : list string) : list string -> sscope -> sscope -> Prop :=
| ub_nil : forall sc, use_binds E taken nil sc sc
| ub_cons : forall n ns sc sc',
    alias_fresh taken sc n ->
    use_binds E taken ns (ss_add n (st_mem E n) sc) sc' ->
    use_binds E taken (n :: ns) sc sc'.

(** [ibinds E taken spec sc sc'] holds when importing the module [E] with the
    specification [spec] extends the scope [sc] to [sc'].  A plain import
    binds nothing, [as y] binds [y] to [E], and [use] binds the listed
    members. *)
Inductive ibinds (E : modexp) (taken : list string) : Cst.ispec -> sscope -> sscope -> Prop :=
| ib_open : forall sc, ibinds E taken Cst.i_open sc sc
| ib_as : forall y sc, alias_fresh taken sc y -> ibinds E taken (Cst.i_as y) sc (ss_add y (st_mod E) sc)
| ib_use : forall ns sc sc', use_binds E taken ns sc sc' -> ibinds E taken (Cst.i_use ns) sc sc'.

(** [simport fp O Fs taken sc c sc' c']: the import [c], in a frame with
    scope [sc] and members and parameters [taken], changes the scope to [sc']
    and emits the core command [c'], which the core checks. *)
Inductive simport (fp : fpath) (O : sscope) (Fs : list sframe) (taken : list string)
  : sscope -> Cst.cmd -> sscope -> ccmd -> Prop :=
| si_intro : forall sc fq ip spec E sc',
    itarget fp O Fs fq ip E ->
    ibinds E taken spec (ss_add_unit fq sc) sc' ->
    simport fp O Fs taken sc (Cst.c_import fq ip spec) sc' (cc_import (ifile fq) E (ispec_names spec)).

(** ** Commands

    [scmd fp O Fs F c F'] holds when the command [c] takes the innermost open
    frame [F] to [F'].  Here [fp] is the current unit, [O] is the scope of its
    leading imports, and [Fs] are the frames enclosing [F]. *)
Inductive scmd (fp : fpath) (O : sscope) : list sframe -> sframe -> Cst.cmd -> sframe -> Prop :=
(** A definition sees the members declared before it, but not itself. *)
| sc_def : forall Fs F m x oA oM A M,
    sf_fresh F x ->
    sel fp O (F :: Fs) nil oA A ->
    sel fp O (F :: Fs) nil oM M ->
    scmd fp O Fs F (Cst.c_def m x oA oM)
      (sf_emit F (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A M))
| sc_eval : forall Fs F oM M,
    sel fp O (F :: Fs) nil oM M ->
    scmd fp O Fs F (Cst.c_eval oM None) (sf_emit F (cc_eval M None))
| sc_eval_typ : forall Fs F oM oA M A,
    sel fp O (F :: Fs) nil oM M ->
    sel fp O (F :: Fs) nil oA A ->
    scmd fp O Fs F (Cst.c_eval oM (Some oA)) (sf_emit F (cc_eval M (Some A)))
| sc_import : forall Fs F fq ip spec sc' c,
    simport fp O (F :: Fs) (sf_taken F) (sf_scope F) (Cst.c_import fq ip spec) sc' c ->
    scmd fp O Fs F (Cst.c_import fq ip spec) (sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ c :: nil) sc')
(** The parameters of [module x (ps) where body end] are elaborated in [F],
    and its body in a new frame nested in [F]. *)
| sc_mod : forall Fs F x ps body tys N,
    sf_fresh F x ->
    NoDup (map fst ps) ->
    sparams fp O (F :: Fs) nil ps tys ->
    scmds fp O (F :: Fs) (sf_new (sf_path F ++ x :: nil) tys) body N ->
    scmd fp O Fs F (Cst.c_mod (x :: nil) ps (Cst.md_where body)) (sf_emit F (cc_mod x (ptele tys) (sf_cmds N)))
(** [module x (ps) := E]: [E] is read under the parameters. *)
| sc_alias : forall Fs F x ps oE tys E,
    sf_fresh F x ->
    NoDup (map fst ps) ->
    sparams fp O (F :: Fs) nil ps tys ->
    selm fp O (F :: Fs) (lparams ps) oE E ->
    scmd fp O Fs F (Cst.c_mod (x :: nil) ps (Cst.md_alias oE)) (sf_emit F (cc_alias x (ptele tys) E))
(** [module x.p (ps) md] is a module [x] without parameters that contains
    [module p (ps) md]. *)
| sc_mod_path : forall Fs F x p ps md N,
    p <> nil ->
    sf_fresh F x ->
    scmd fp O (F :: Fs) (sf_new (sf_path F ++ x :: nil) nil) (Cst.c_mod p ps md) N ->
    scmd fp O Fs F (Cst.c_mod (x :: p) ps md) (sf_emit F (cc_mod x ⋅ (sf_cmds N)))

with scmds (fp : fpath) (O : sscope) : list sframe -> sframe -> list Cst.cmd -> sframe -> Prop :=
| scs_nil : forall Fs F, scmds fp O Fs F nil F
| scs_cons : forall Fs F c cs F1 F2,
    scmd fp O Fs F c F1 -> scmds fp O Fs F1 cs F2 -> scmds fp O Fs F (c :: cs) F2.

(** [simports] elaborates the imports that precede the unit's declaration,
    each in the scope built by the earlier ones. *)
Inductive simports (fp : fpath) : sscope -> list Cst.cmd -> sscope -> list ccmd -> Prop :=
| sis_nil : forall O, simports fp O nil O nil
| sis_cons : forall O fq ip spec O1 c cs O2 is,
    simport fp O nil nil O (Cst.c_import fq ip spec) O1 c ->
    simports fp O1 cs O2 is ->
    simports fp O (Cst.c_import fq ip spec :: cs) O2 (c :: is).

(** ** Units

    A unit [import …; module fp (ps) where cs end] elaborates to the commands
    of its leading imports, its parameter context, and the commands of its
    own frame, whose member chain is [nil]. *)
Inductive elab_spec : Cst.prog -> cunit -> Prop :=
| es_intro : forall imports fp ps cs O imps tys F,
    simports fp ss_empty imports O imps ->
    NoDup (map fst ps) ->
    sparams fp O nil nil ps tys ->
    scmds fp O nil (sf_new nil tys) cs F ->
    elab_spec (imports, (fp, ps, cs)) (imps, ptele tys, sf_cmds F).

(** ** The Invariant

    Elaboration keeps every name bound at most once in each frame and in the
    scope of the leading imports, so [fr_binds] gives each name at most one
    meaning. *)

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

Lemma ibinds_wf : forall E taken spec sc sc',
    ibinds E taken spec sc sc' ->
    NoDup (map fst (ss_alias sc) ++ taken) -> NoDup (map fst (ss_alias sc') ++ taken).
Proof.
  induction 1 as [| | ns sc sc' Hu]; intros Hw; [ assumption | eapply alias_fresh_wf; eassumption |].
  induction Hu; [ assumption |]. apply IHHu. eapply alias_fresh_wf; eassumption.
Qed.

Lemma ss_alias_add_unit : forall fq sc, ss_alias (ss_add_unit fq sc) = ss_alias sc.
Proof. intros [] ?; reflexivity. Qed.

Lemma simport_wf : forall fp O Fs taken sc c sc' c',
    simport fp O Fs taken sc c sc' c' ->
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
    replace (decl_names (c :: nil)) with (@nil string) by (inversion s; subst; reflexivity).
    rewrite app_nil_r. eapply simport_wf; eassumption.
  - apply sf_wf_emit; [ assumption |]. intros ? [=<-]; assumption.
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
