From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members Command.

Import Syntax_Notations.

(** * A Declarative Specification of Elaboration

    [elab_spec prg u] holds when the surface unit [prg] elaborates to the core
    unit [u].  [Frontend/ElabCorrect.v] proves that [elaborate_core] computes
    exactly this relation.

    Elaboration turns names into de Bruijn indices and paths, and decides
    from an object's position whether it is a term or a module expression.
    It never looks inside a module: what [M.x] names, and whether it may be
    named, is left to the core.

    - Everything in scope is one list of entries, innermost first ([scope_entry]):
      core binders, members of the open frames, imported units, and, in the
      unit's parameter types only, the names its leading opens declare.  A name denotes its innermost entry, so there is no priority
      between kinds of entries and no invariant on the scope.
    - The core binders lie in the list in de Bruijn order.  A member of an
      open frame is generalized over the parameters of its frame and of the
      frames enclosing it, which are exactly the binders outside its entry;
      a use applies it to those variables.
    - A member of a frame, an open's declarations included, does not take
      the name of a parameter of the frame ([fresh]); that the frame
      declares no member twice is the core's to check.  A name an
      enclosing frame binds may be shadowed.
    - Where an object stands decides what it is: the head of a projection,
      the head of an application there, an alias body and an open target
      are module expressions ([spec_modexp]), everything else is a term ([spec_exp]).

    The running example of this file is

<<
module Main where
  module M (A : Typeω@0) where
    def id (x : A) : A := x end
    module N (B : Typeω@0) where
      def k (x : A) (y : B) : A := id x end
    end
  end
  def j : forall (x : Nat) -> Nat := M.id Nat end
end
>>

    The body of [k] is read in the scope

<<
y, x, B, id ↦ Main.M.id, A
>>

    (innermost first).  [id] lies under three binders ([y], [x], [B]) and
    over one ([A]), so it denotes [Main.M.id $ #3], and [id x] is
    [Main.M.id $ #3 $ #1].  In [j], [M] is closed, so [M] is the module
    [⟨Main.M⟩] and [M.id Nat] selects its member [id] and applies it. *)

(** ** Entries *)

Inductive scope_entry : Set :=
(** A core binder that may hold a module: a local module, an entry of a
    local body (an open's declarations included). *)
| scope_entry_var : string -> scope_entry
(** A core binder of a term: a λ, a Π, a binder of a motive or a branch, a
    [let] definition, a parameter, an argument of a constructor, the type a
    declaration declares.  It is no module. *)
| scope_entry_tvar : string -> scope_entry
(** A member of an open frame (an open's declarations included), named by
    its qualified name, generalized over the [m] binders outside it: the
    parameters of its frame and of the frames enclosing it.  [m] is fixed
    when the member is declared ([binders] of the scope there). *)
| scope_entry_mem : string -> qname -> nat -> scope_entry
(** [import X::Y]: the unit [X::Y] may be named by its path. *)
| scope_entry_unit : path -> scope_entry
(** A name a leading open declares, as the unit's parameter types see it:
    [scope_entry_open d E (Some n)] is the member [n] of the module [E], [scope_entry_open d
    E None] is [E] itself.  [E] is read where no binder is in scope. *)
| scope_entry_open : string -> modexp -> option string -> scope_entry.

Definition scope_entry_name (e : scope_entry) : option string :=
  match e with
  | scope_entry_var x | scope_entry_tvar x | scope_entry_mem x _ _ | scope_entry_open x _ _ => Some x
  | scope_entry_unit _ => None
  end.

Definition scope_entry_binders (e : scope_entry) : nat :=
  match e with
  | scope_entry_var _ | scope_entry_tvar _ => 1
  | _ => 0
  end.

(** The names bound in [S], and the number of core binders in it. *)
Definition names (S : list scope_entry) : list string :=
  flat_map (fun e => match scope_entry_name e with Some x => x :: nil | None => nil end) S.

Definition binders (S : list scope_entry) : nat := fold_right (fun e n => scope_entry_binders e + n) 0 S.

(** [bound S x k e]: [e] is the innermost entry of [S] that binds [x], with
    [k] core binders inside it. *)
#[warnings="-cannot-define-projection"]
Record bound (S : list scope_entry) (x : string) (k : nat) (e : scope_entry) : Prop := mk_bound
  { (** The entries inside [e] *)
    bound_inner : list scope_entry
  ; (** The entries outside [e] *)
    bound_outer : list scope_entry
  ; (** [S] is the inner entries, [e], then the outer ones. *)
    bound_split : S = bound_inner ++ e :: bound_outer
  ; (** [e] binds [x]. *)
    bound_name : scope_entry_name e = Some x
  ; (** No inner entry binds [x]. *)
    bound_first : ~ In x (names bound_inner)
  ; (** [k] is the number of core binders inside [e]. *)
    bound_inner_binders : k = binders bound_inner }.

(** A member of a frame may not take the name of one of the frame's
    parameters, [P].  That a frame declares no member twice is the core's
    to check ([gs_fresh]); but the core's parameter contexts are nameless
    ([ptele]: assumptions only), so it cannot check this clash. *)
Definition fresh (x : string) (P : list string) : Prop := ~ In x P.

(** The entries of a parameter list, innermost first. *)
Definition param_scope_entries (ps : list (string * Cst.expression)) : list scope_entry := rev (map (fun p => scope_entry_tvar (fst p)) ps).

(** The entries of names bound in order, innermost first: the binders of
    an eliminator's motive and branches. *)
Definition variable_scope_entries (xs : list string) : list scope_entry := rev (map scope_entry_tvar xs).

(** ** What an Entry Denotes

    [k] binders lie inside the entry.  A member is generalized over the
    [n] binders outside it, which its entry records; those parameters, in
    declaration order, are [vars_desc k n]:

<<
#(k + n - 1), …, #(k + 1), #k
>>  *)
Definition vars_desc (k n : nat) : list exp :=
  map (fun i => a_var (k + (n - 1 - i))) (seq 0 n).

(** [mapps H args] applies the module expression [H] to each of [args] in
    turn. *)
Definition mapps (H : modexp) (args : list exp) : modexp := fold_left me_app args H.

(** What a leading open declares [d] as: the member [c] of [E], or [E]. *)
Definition open_mod (E : modexp) (oc : option string) : modexp :=
  match oc with
  | Some c => me_mem E c
  | None => E
  end.

(** As a term.  A module alias is not one.  A leading open's entry needs
    no weakening: its module is closed. *)
Inductive entry_denotes_term (k : nat) : scope_entry -> exp -> Prop :=
(** A binder that may hold a module: the variable *)
| entry_denotes_term_var : forall x, entry_denotes_term k (scope_entry_var x) #k
(** A term binder: the variable *)
| entry_denotes_term_tvar : forall x, entry_denotes_term k (scope_entry_tvar x) #k
(** A member: its qualified name applied to the parameters outside it *)
| entry_denotes_term_mem : forall x p m, entry_denotes_term k (scope_entry_mem x p m) (apps (qname_term p) (vars_desc k m))
(** A leading open's name of a member: that member of the module *)
| entry_denotes_term_open : forall x E c, entry_denotes_term k (scope_entry_open x E (Some c)) (a_mem E c).

(** As a module expression.  A variable that may hold a module is a module
    slot, which the core rejects if it holds a term; a term binder is the
    binder too: the core fills it, a term of a record type standing for
    the record's module at the term ([fill_mod_term]), and rejects any
    other. *)
Inductive entry_denotes_mod (k : nat) : scope_entry -> modexp -> Prop :=
(** A binder that may hold a module: the module slot *)
| entry_denotes_mod_var : forall x, entry_denotes_mod k (scope_entry_var x) (me_var k)
(** A term binder: the binder, which the core fills when the term is of a
    record type *)
| entry_denotes_mod_tvar : forall x, entry_denotes_mod k (scope_entry_tvar x) (me_var k)
(** A member: its qualified name applied to the parameters outside it *)
| entry_denotes_mod_mem : forall x p m, entry_denotes_mod k (scope_entry_mem x p m) (mapps (qname_mod p) (vars_desc k m))
(** A leading open's name: what it names in the module *)
| entry_denotes_mod_open : forall x E oc, entry_denotes_mod k (scope_entry_open x E oc) (open_mod E oc).

(** ** What an Open Declares

    The items of an open, [iitem]s, are generated by the core
    ([items_gen]): [(None, W, true)] declares [W] as a private
    alias of the module, [(Some c, d, pv)] declares [d] as its member [c],
    privately when [pv]. *)

(** In a local body, the items of an open are entries of the body, one
    core binder each, newest first. *)
Definition item_scope_entries (its : list iitem) : list scope_entry := rev (map (fun it => scope_entry_var (iitem_name it)) its).

(** In the open frame at member chain [ch] of the unit [fp], with [n]
    binders outside the frame's members, they are members of the frame. *)
Definition item_mems (fp : path) (ch : list string) (n : nat) (its : list iitem) : list scope_entry :=
  rev (map (fun it => scope_entry_mem (iitem_name it) (q_abs fp (ch ++ iitem_name it :: nil)) n) its).

(** Before the unit's header, in the scope of its parameter types, they
    denote what they name in the module [E]. *)
Definition open_scope_entries (E : modexp) (its : list iitem) : list scope_entry :=
  rev (map (fun it => scope_entry_open (iitem_name it) E (fst (fst it))) its).

(** What [open fq.ip args] names, as a module object: the unit [fq] at
    the member path [ip] if [fq] is not empty, the module [ip] in scope
    otherwise; applied to [args].  Read as any module object is, it needs
    the unit to be nameable. *)
Definition ihead (fq ip : path) : option Cst.expression :=
  match fq, ip with
  | nil, nil => None
  | nil, x :: ip' => Some (fold_left Cst.proj ip' (Cst.var x))
  | _, _ => Some (fold_left Cst.proj ip (Cst.glob fq))
  end.

Definition itarget (fq ip : path) (args : list Cst.expression) : option Cst.expression :=
  option_map (fold_left Cst.app args) (ihead fq ip).

(** ** Eliminators

    An eliminator's blocks come in member order, the one marked [at] the
    scrutinee's ([elim_at]); which member each block is for, and the
    group, are the core's to find ([Core.Syntactic.Builtin]).  A block's
    binders bind the non-uniform parameters, then the scrutinee; only the
    scrutinee's may carry a type, which the core reads the group and its
    uniform parameters off. *)

(** The position of the one block marked [at], if exactly one is. *)
Fixpoint elim_at (ks : list bool) : option nat :=
  match ks with
  | nil => None
  | true :: ks' => if List.existsb (fun k => k) ks' then None else Some 0
  | false :: ks' => option_map S (elim_at ks')
  end.

(** ** Objects

    [spec_exp S o M] holds when the surface object [o] denotes the term [M] in the
    scope [S], and [spec_modexp S o H] when it denotes the module expression [H].
    Every rule but the two for names, and the one for a projection from a
    head that is no path, is a homomorphism. *)

(** Whether an object is a path of module position: a name, a member of
    one, or one applied.  A projection from it is a member of the module
    it denotes; one from any other head is a member of a term's. *)
Fixpoint expression_path (o : Cst.expression) : bool :=
  match o with
  | Cst.var _ | Cst.glob _ => true
  | Cst.proj o' _ | Cst.app o' _ => expression_path o'
  | _ => false
  end.

(** [ptele ps] is the parameter list [ps] as a core context, innermost
    first. *)
Definition ptele (ps : list (string * typ)) : ctx := rev (map (fun p => ce_ass (snd p)) ps).

Inductive spec_exp : list scope_entry -> Cst.expression -> exp -> Prop :=
| spec_exp_typ : forall S n, spec_exp S (Cst.typ n) (Typeω@n)
| spec_exp_suniv : forall S o M, spec_exp S o M -> spec_exp S (Cst.suniv o) (Type⟨M⟩)
| spec_exp_level : forall S n, spec_exp S (Cst.level n) (Level@n)
| spec_exp_llit : forall S o, spec_exp S (Cst.llit o) (𝕃ᵒ o)
| spec_exp_succl : forall S o M, spec_exp S o M -> spec_exp S (Cst.succl o) (succl M)
| spec_exp_maxl : forall S o1 o2 M N, spec_exp S o1 M -> spec_exp S o2 N -> spec_exp S (Cst.maxl o1 o2) (maxl M N)
(** The token [ℕ] and a numeral are core literals: what they stand for is
    generated from the builtin bindings when the command runs. *)
| spec_exp_nat : forall S, spec_exp S Cst.nat ℕ
| spec_exp_num : forall S n, spec_exp S (Cst.num n) (a_nlit n)
| spec_exp_true_ty : forall S, spec_exp S Cst.true_ty ⊤
| spec_exp_true_tm : forall S, spec_exp S Cst.true_tm ⋆
| spec_exp_false_ty : forall S, spec_exp S Cst.false_ty ⊥
| spec_exp_exfalso : forall S om mx oA M A,
    spec_exp S om M -> spec_exp (scope_entry_tvar mx :: S) oA A -> spec_exp S (Cst.exfalso om mx oA) (efq M return A)
| spec_exp_pi : forall S x oA oB A B,
    spec_exp S oA A -> spec_exp (scope_entry_tvar x :: S) oB B -> spec_exp S (Cst.pi x oA oB) (Π A B)
| spec_exp_fn : forall S x oA oM A M,
    spec_exp S oA A -> spec_exp (scope_entry_tvar x :: S) oM M -> spec_exp S (Cst.fn x oA oM) (λ A M)
| spec_exp_app : forall S o1 o2 M N,
    spec_exp S o1 M -> spec_exp S o2 N -> spec_exp S (Cst.app o1 o2) (M $ N)
| spec_exp_var : forall S x k e M,
    bound S x k e -> entry_denotes_term k e M -> spec_exp S (Cst.var x) M
(** A projection selects a member of the module its head denotes, a
    name, a member of one, or one applied ([expression_path]). *)
| spec_exp_proj : forall S o x H,
    expression_path o = true -> spec_modexp S o H -> spec_exp S (Cst.proj o x) (a_mem H x)
(** A projection from any other head, a term, selects the member of the
    module of a [let] bound to it, which the core fills
    ([fill_mod_term]). *)
| spec_exp_proj_let : forall S o x M,
    expression_path o = false -> spec_exp S o M -> spec_exp S (Cst.proj o x) (ℓ ≔ M in a_mem (me_var 0) x)
| spec_exp_let : forall S x oA oM ob A M B,
    spec_exp S oA A -> spec_exp S oM M -> spec_exp (scope_entry_tvar x :: S) ob B ->
    spec_exp S (Cst.letb (Cst.d_def x (Some oA) oM) ob) (ℓ A ≔ M in B)
(** Without an annotation, none is emitted: the core infers it. *)
| spec_exp_let_infer : forall S x oM ob M B,
    spec_exp S oM M -> spec_exp (scope_entry_tvar x :: S) ob B ->
    spec_exp S (Cst.letb (Cst.d_def x None oM) ob) (ℓ ≔ M in B)
(** [let module x (ps) md in B end]: [x] is the slot of the local module. *)
| spec_exp_let_mod : forall S x ps md ob U B,
    spec_unit S ps md U -> spec_exp (scope_entry_var x :: S) ob B ->
    spec_exp S (Cst.letb (Cst.d_mod x ps md) ob) (ℓₘ U in B)
(** An eliminator: its blocks, the one marked [at] the scrutinee's.  It
    carries no group and no uniform parameters: the core fills them from
    the annotations.  How many binders and branches there must be, and
    which constructor a branch is for, is the core's to check. *)
| spec_exp_elim : forall S om bks M Bks m,
    spec_exp S om M -> spec_blocks S bks Bks -> elim_at (List.map (fun bk => fst (fst (fst bk))) bks) = Some m ->
    spec_exp S (Cst.elim om bks) (a_elim None nil m Bks M)
(** A record value: its type and its fields, as written.  Whether the type
    is a record type and the fields are its own, in order, is the core's
    to check. *)
| spec_exp_tuple : forall S oT fs T Ms,
    spec_exp S oT T -> spec_tuple_fields S fs Ms -> spec_exp S (Cst.tuple oT fs) (a_tuple T Ms)

with spec_modexp : list scope_entry -> Cst.expression -> modexp -> Prop :=
| spec_modexp_var : forall S x k e H,
    bound S x k e -> entry_denotes_mod k e H -> spec_modexp S (Cst.var x) H
| spec_modexp_glob : forall S fq,
    In (scope_entry_unit fq) S -> spec_modexp S (Cst.glob fq) (me_unit fq)
(** A name no binding in scope has is the imported unit of that one-segment
    path. *)
| spec_modexp_unit1 : forall S x,
    ~ In x (names S) -> In (scope_entry_unit (x :: nil)) S -> spec_modexp S (Cst.var x) (me_unit (x :: nil))
| spec_modexp_proj : forall S o y H,
    spec_modexp S o H -> spec_modexp S (Cst.proj o y) (me_mem H y)
| spec_modexp_app : forall S o1 o2 H N,
    spec_modexp S o1 H -> spec_exp S o2 N -> spec_modexp S (Cst.app o1 o2) (me_app H N)

(** The fields of a record value, each its name and its value, all in the
    scope of the value. *)
with spec_tuple_fields : list scope_entry -> list (string * Cst.expression) -> list (string * exp) -> Prop :=
(** No field *)
| spec_tuple_fields_nil : forall S, spec_tuple_fields S nil nil
(** The first field, its name and its value, then the rest *)
| spec_tuple_fields_cons : forall S y oM fs M Ms,
    spec_exp S oM M -> spec_tuple_fields S fs Ms -> spec_tuple_fields S ((y, oM) :: fs) ((y, M) :: Ms)

with spec_branches : list scope_entry -> list (string * list string * Cst.expression) -> list (string * nat * exp) -> Prop :=
| spec_branches_nil : forall S, spec_branches S nil nil
| spec_branches_cons : forall S c ys oB bs B Bs,
    spec_exp (variable_scope_entries ys ++ S) oB B -> spec_branches S bs Bs ->
    spec_branches S ((c, ys, oB) :: bs) ((c, List.length ys, B) :: Bs)

(** The blocks of an eliminator: each its binders, the scrutinee's type
    under the binders before it, its motive under all of them, and its
    branches. *)
with spec_blocks : list scope_entry -> list (bool * list (string * option Cst.expression) * Cst.expression * list (string * list string * Cst.expression)) ->
    list eblock -> Prop :=
| spec_blocks_nil : forall S, spec_blocks S nil nil
| spec_blocks_cons : forall S k xs oA bs bks oZ A Bs Bks,
    spec_binders S nil xs oZ ->
    spec_exp (variable_scope_entries (List.map fst xs) ++ S) oA A -> spec_branches S bs Bs -> spec_blocks S bks Bks ->
    spec_blocks S ((k, xs, oA, bs) :: bks) (eb_mk (List.length xs) oZ A Bs :: Bks)

(** [spec_binders S pre xs oZ]: the binders [xs] of a block, after the binders
    [pre], carry no type but the last, whose type, if written, is [oZ],
    read under the binders before it. *)
with spec_binders : list scope_entry -> list string -> list (string * option Cst.expression) -> option exp -> Prop :=
| spec_binders_nil : forall S pre, spec_binders S pre nil None
| spec_binders_last_bare : forall S pre x, spec_binders S pre ((x, None) :: nil) None
| spec_binders_last_typed : forall S pre x o Z,
    spec_exp (variable_scope_entries pre ++ S) o Z -> spec_binders S pre ((x, Some o) :: nil) (Some Z)
| spec_binders_cons : forall S pre x y xs oZ,
    spec_binders S (pre ++ x :: nil) (y :: xs) oZ -> spec_binders S pre ((x, None) :: y :: xs) oZ

(** Each parameter's type sees the earlier parameters. *)
with spec_params : list scope_entry -> list (string * Cst.expression) -> list (string * typ) -> Prop :=
| spec_params_nil : forall S, spec_params S nil nil
| spec_params_cons : forall S x oA ps A tys,
    spec_exp S oA A ->
    spec_params (scope_entry_tvar x :: S) ps tys ->
    spec_params S ((x, oA) :: ps) ((x, A) :: tys)

(** A local module: its parameters, then its definition under them. *)
with spec_unit : list scope_entry -> list (string * Cst.expression) -> Cst.mdef -> gunit -> Prop :=
| spec_unit_intro : forall S ps md tys D,
    NoDup (map fst ps) ->
    spec_params S ps tys ->
    spec_def (param_scope_entries ps ++ S) md D ->
    spec_unit S ps md (gu_mk (ptele tys) D)

with spec_def : list scope_entry -> Cst.mdef -> moddef -> Prop :=
| spec_def_alias : forall S oE E,
    spec_modexp S oE E -> spec_def S (Cst.md_alias oE) (md_alias E)
| spec_def_where : forall S cs Φ,
    spec_body S gm_nil cs Φ -> spec_def S (Cst.md_where cs) (md_body sm_open Φ)

(** [spec_body S Φ cs Φ']: the commands [cs] of a local body extend [Φ] to [Φ'].
    Each entry is a core binder for the entries after it.  An open is a
    pre-form the core expands ([gm_open]); each of its items is a core
    binder.  The names of a body are checked fresh by the core.  A local
    body has no [import]s, no [eval]s and no axioms. *)
with spec_body : list scope_entry -> gmod -> list Cst.cmd -> gmod -> Prop :=
| spec_body_nil : forall S Φ, spec_body S Φ nil Φ
| spec_body_def : forall S Φ m x oA oM A M cs Φ',
    spec_exp S oA A -> spec_exp S oM M ->
    spec_body (scope_entry_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs Φ' ->
    spec_body S Φ (Cst.c_def m x oA oM :: cs) Φ'
| spec_body_mod : forall S Φ pv x ps md U cs Φ',
    spec_unit S ps md U ->
    spec_body (scope_entry_var x :: S) (gm_ext Φ x (ge_mod pv U)) cs Φ' ->
    spec_body S Φ (Cst.c_mod pv x ps md :: cs) Φ'
(** It loads nothing, so a unit it names must be nameable already. *)
| spec_body_open : forall S Φ fq ip args its o E cs Φ',
    itarget fq ip args = Some o ->
    spec_modexp S o E ->
    spec_body (item_scope_entries its ++ S) (gm_open Φ E its) cs Φ' ->
    spec_body S Φ (Cst.c_open fq ip args its :: cs) Φ'.

(** ** Inductive Declarations

    The type of a declaration binds its non-uniform parameters in front of
    its sort ([split_pis]).  The declared name is in scope in the
    constructors' argument types as an ordinary variable, [Self], outside
    the declaration's parameters, so a recursive occurrence is written with
    all of them, and every argument binds its name for the ones after it.  Which arguments are recursive is the core's to decide
    ([Core.Syntactic.Inductives.Group]). *)
Fixpoint split_pis (o : Cst.expression) : (list (string * Cst.expression) * Cst.expression)%type :=
  match o with
  | Cst.pi y oA oB => let (ps, oS) := split_pis oB in ((y, oA) :: ps, oS)
  | _ => (nil, o)
  end.

Inductive spec_constructor_args : list scope_entry -> list (string * Cst.expression) -> list (string * exp) -> Prop :=
| spec_constructor_args_nil : forall S, spec_constructor_args S nil nil
| spec_constructor_args_cons : forall S y oA args A args',
    spec_exp S oA A -> spec_constructor_args (scope_entry_tvar y :: S) args args' ->
    spec_constructor_args S ((y, oA) :: args) ((y, A) :: args').

Inductive spec_constructors (S : list scope_entry) :
    list (string * list (string * Cst.expression)) -> list (string * list (string * exp)) -> Prop :=
| spec_constructors_nil : spec_constructors S nil nil
| spec_constructors_cons : forall c args cs args' cs',
    spec_constructor_args S args args' -> spec_constructors S cs cs' ->
    spec_constructors S ((c, args) :: cs) ((c, args') :: cs').

(** The names of the members of a group. *)
Definition member_names (ms : list (string * Cst.expression * list (string * list (string * Cst.expression)))) : list string :=
  List.map (fun m => fst (fst m)) ms.

(** The members of a group, under its uniform parameters [ups] in the
    scope [S], the members' names [xs] in scope in every argument outside
    the parameters: each its non-uniform parameters, its sort and its
    constructors. *)
Inductive spec_members (S : list scope_entry) (ups : list (string * Cst.expression)) (xs : list string) :
    list (string * Cst.expression * list (string * list (string * Cst.expression))) -> list raw_member -> Prop :=
| spec_members_nil : spec_members S ups xs nil nil
| spec_members_cons : forall x oT cs ms nps oS ntys A cs' rms,
    split_pis oT = (nps, oS) ->
    NoDup (map fst (ups ++ nps)) ->
    spec_params (param_scope_entries ups ++ S) nps ntys ->
    spec_exp (param_scope_entries ups ++ S) oS A ->
    spec_constructors (param_scope_entries (ups ++ nps) ++ variable_scope_entries xs ++ S) cs cs' ->
    spec_members S ups xs ms rms ->
    spec_members S ups xs ((x, oT, cs) :: ms) (mk_rmem x (ptele ntys) A cs' :: rms).

(** ** Mutual Definitions

    A function's parameters are its non-uniform ones, then its scrutinee,
    last; its result type sees all of them, its clauses only the common
    parameters, as an eliminator's branches see only what is outside it. *)

(** The names of the functions. *)
Definition fun_names (fs : list (string * list (string * Cst.expression) * Cst.expression * list (string * list string * Cst.expression))) :
    list string :=
  List.map (fun f => fst (fst (fst f))) fs.

Inductive spec_functions (S : list scope_entry) :
    list (string * list (string * Cst.expression) * Cst.expression * list (string * list string * Cst.expression)) -> list raw_fun -> Prop :=
| spec_functions_nil : spec_functions S nil nil
| spec_functions_cons : forall f ys z oZ oA bs fs ytys Z A Bs rfs,
    NoDup (map fst (ys ++ (z, oZ) :: nil)) ->
    spec_params S ys ytys ->
    spec_exp (param_scope_entries ys ++ S) oZ Z ->
    spec_exp (scope_entry_tvar z :: param_scope_entries ys ++ S) oA A ->
    spec_branches S bs Bs ->
    spec_functions S fs rfs ->
    spec_functions S ((f, ys ++ (z, oZ) :: nil, oA, bs) :: fs) (mk_rfun f (ptele ytys) Z A Bs :: rfs).

(** The entries of names filed in order in the open frame at member chain
    [ch] of the unit [fp], with [n] binders outside the frame's members,
    innermost first. *)
Definition filed_mems (fp : path) (ch : list string) (n : nat) (xs : list string) : list scope_entry :=
  rev (map (fun x => scope_entry_mem x (q_abs fp (ch ++ x :: nil)) n) xs).

(** ** Record Types

    A record type's module is a frame over the record's parameters and,
    bound last, a value of the record ([Core.Syntactic.Members.record_mod_tele]),
    whose members are the fields, then the with-area.  The value has no
    name: a member of the with-area reaches it through the fields, which
    are members of the frame, so [snd] is the field of the value the
    module is at. *)

(** The value a record's module is at: a term binder no name denotes. *)
Definition scope_entry_self : scope_entry := scope_entry_tvar "".

(** The entries of the frame of the record [x] with the parameters [ps]
    and the fields [fs], declared at member chain [ch] of the unit [fp]
    with [n] binders outside the record, before its with-area: the fields,
    the value, then the parameters, innermost first.  The fields lie under
    the value and the parameters. *)
Definition record_scope_entries (fp : path) (ch : list string) (n : nat) (x : string) (ps fs : list (string * Cst.expression)) : list scope_entry :=
  filed_mems fp (ch ++ x :: nil) (binders (scope_entry_self :: param_scope_entries ps) + n) (map fst fs) ++ scope_entry_self :: param_scope_entries ps.

(** The names a command declares in its frame. *)
Definition cmd_decls (c : Cst.cmd) : list string :=
  match c with
  | Cst.c_mod _ x _ _ | Cst.c_def _ x _ _ | Cst.c_axiom x _ | Cst.c_ind_alias _ x _ _
  | Cst.c_record_alias _ x _ _ | Cst.c_record _ x _ _ _ _ => x :: nil
  | Cst.c_open _ _ _ its => map iitem_name its
  | Cst.c_ind _ _ _ ms => member_names ms
  | Cst.c_mdef _ _ fs => fun_names fs
  | Cst.c_import _ | Cst.c_error _ | Cst.c_eval _ _ | Cst.c_builtin _ _ => nil
  end.

(** ** Commands

    [spec_cmd fp ch P S c S' c']: the command [c], in the open frame at member
    chain [ch] of the unit [fp], whose parameters are named [P], read in
    the scope [S] (the frame's entries so far, innermost first, then
    everything outside the frame), extends the scope to [S'] and emits the
    core commands [c'].  [spec_cmds] runs the commands of a body in order.  A
    definition keyword with a modifier it implies ([Cst.c_error]) has no
    rule. *)
Inductive spec_cmd (fp : path) : list string -> list string -> list scope_entry -> Cst.cmd -> list scope_entry -> list core_cmd -> Prop :=
(** A definition: its type and its body, read in the scope. *)
| spec_cmd_def : forall ch P S m x oA oM A M,
    fresh x P ->
    spec_exp S oA A ->
    spec_exp S oM M ->
    spec_cmd fp ch P S (Cst.c_def m x oA oM) (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
      (core_cmd_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M) :: nil)
(** An axiom is opaque, and has no body. *)
| spec_cmd_axiom : forall ch P S x oA A,
    fresh x P ->
    spec_exp S oA A ->
    spec_cmd fp ch P S (Cst.c_axiom x oA) (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
      (core_cmd_def x false false A None :: nil)
(** The parameters of [module x (ps) where body end] are read in the
    scope, its body in a new frame inside, whose parameters are [ps]. *)
| spec_cmd_mod : forall ch P S pv x ps body tys bcs,
    fresh x P ->
    NoDup (map fst ps) ->
    spec_params S ps tys ->
    spec_cmds fp (ch ++ x :: nil) (map fst ps) (param_scope_entries ps ++ S) body bcs ->
    spec_cmd fp ch P S (Cst.c_mod pv x ps (Cst.md_where body)) (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
      (core_cmd_mod x pv (ptele tys) bcs :: nil)
(** [module x (ps) := E]: [E] is read under the parameters. *)
| spec_cmd_alias : forall ch P S pv x ps oE tys E,
    fresh x P ->
    NoDup (map fst ps) ->
    spec_params S ps tys ->
    spec_modexp (param_scope_entries ps ++ S) oE E ->
    spec_cmd fp ch P S (Cst.c_mod pv x ps (Cst.md_alias oE)) (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
      (core_cmd_alias x pv (ptele tys) E :: nil)
(** [import X::Y] loads the unit, which may be named from then on. *)
| spec_cmd_import : forall ch P S fq,
    spec_cmd fp ch P S (Cst.c_import fq) (scope_entry_unit fq :: S) (core_cmd_load fq :: nil)
(** An open loads nothing, so a unit it names must be nameable already.
    No name it declares is a parameter's; whether it declares one twice,
    or one the frame has declared, is the core's to check. *)
| spec_cmd_open : forall ch P S fq ip args its o E,
    itarget fq ip args = Some o ->
    spec_modexp S o E ->
    Forall (fun d => fresh d P) (map iitem_name its) ->
    spec_cmd fp ch P S (Cst.c_open fq ip args its) (item_mems fp ch (binders S) its ++ S) (core_cmd_open E its :: nil)
(** An evaluation, read in the scope; it declares nothing. *)
| spec_cmd_eval : forall ch P S oM M,
    spec_exp S oM M ->
    spec_cmd fp ch P S (Cst.c_eval oM None) S (core_cmd_eval M None :: nil)
(** An evaluation at a type written out *)
| spec_cmd_eval_typ : forall ch P S oM oA M A,
    spec_exp S oM M ->
    spec_exp S oA A ->
    spec_cmd fp ch P S (Cst.c_eval oM (Some oA)) S (core_cmd_eval M (Some A) :: nil)
(** [inductive x (ups) : T where cs with y : U where … end]: the uniform
    parameters are read in the scope, each member's non-uniform ones and
    sort under them, the constructors' arguments under all, with the
    members' names in scope.  It declares each member, a module whose
    members are the constructors.  The group files its recursor module as
    written ([wr]). *)
| spec_cmd_inductive : forall ch P S pv wr ups ms tys rms,
    NoDup (member_names ms) ->
    Forall (fun x => fresh x P) (member_names ms) ->
    spec_params S ups tys ->
    spec_members S ups (member_names ms) ms rms ->
    spec_cmd fp ch P S (Cst.c_ind pv wr ups ms) (filed_mems fp ch (binders S) (member_names ms) ++ S)
      (core_cmd_inductive pv (mk_raw (ptele tys) rms wr) :: nil)
(** [mutual def (ps) f … with g … end]: the common parameters are read in
    the scope, the functions under them.  It declares each function. *)
| spec_cmd_mdef : forall ch P S m ps fs tys rfs,
    NoDup (map fst ps) ->
    NoDup (fun_names fs) ->
    Forall (fun x => fresh x P) (fun_names fs) ->
    spec_params S ps tys ->
    spec_functions (param_scope_entries ps ++ S) fs rfs ->
    spec_cmd fp ch P S (Cst.c_mdef m ps fs) (filed_mems fp ch (binders S) (fun_names fs) ++ S)
      (core_cmd_mdef (negb (Cst.md_abstract m)) (Cst.md_private m) (ptele tys) rfs :: nil)
(** [inductive x (ps) := E]: [E] is read under the parameters, as an
    alias's target is; whether it names an inductive type, and its
    arguments the type's, is the core's to check. *)
| spec_cmd_inductive_alias : forall ch P S pv x ps oE tys E,
    fresh x P ->
    NoDup (map fst ps) ->
    spec_params S ps tys ->
    spec_modexp (param_scope_entries ps ++ S) oE E ->
    spec_cmd fp ch P S (Cst.c_ind_alias pv x ps oE) (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
      (core_cmd_inductive_alias x pv (ptele tys) E :: nil)
(** [record x (ps) := E]: as an inductive alias; whether [E] names a record
    type is the core's to check. *)
| spec_cmd_record_alias : forall ch P S pv x ps oE tys E,
    fresh x P ->
    NoDup (map fst ps) ->
    spec_params S ps tys ->
    spec_modexp (param_scope_entries ps ++ S) oE E ->
    spec_cmd fp ch P S (Cst.c_record_alias pv x ps oE) (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
      (core_cmd_record_alias x pv (ptele tys) E :: nil)
(** [builtin k := X]: [X] is a module, as written; whether it is an
    inductive type of the right shape is the core's to check. *)
| spec_cmd_builtin : forall ch P S k oX H,
    spec_modexp S oX H ->
    spec_cmd fp ch P S (Cst.c_builtin k oX) S (core_cmd_builtin k H :: nil)
(** [record x (ps) : S where f : A ; … with cs end]: the parameters are
    read in the scope, the sort under them, each field's type under them
    and the fields before it.  The with-area is read in the record's frame
    ([record_scope_entries]), whose parameters are [ps], with [x] in scope outside
    it; no name it declares is a field's.  It declares [x], a type and a
    module. *)
| spec_cmd_record : forall ch P S pv x ps oS fs cs tys Srt fs' bcs,
    fresh x P ->
    NoDup (map fst ps) ->
    spec_params S ps tys ->
    spec_exp (param_scope_entries ps ++ S) oS Srt ->
    spec_constructor_args (param_scope_entries ps ++ S) fs fs' ->
    Forall (fun y => ~ In y (map fst fs)) (flat_map cmd_decls cs) ->
    spec_cmds fp (ch ++ x :: nil) (map fst ps)
      (record_scope_entries fp ch (binders S) x ps fs ++ scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S) cs bcs ->
    spec_cmd fp ch P S (Cst.c_record pv x ps oS fs cs) (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
      (core_cmd_record x pv (ptele tys) Srt fs' bcs :: nil)

with spec_cmds (fp : path) : list string -> list string -> list scope_entry -> list Cst.cmd -> list core_cmd -> Prop :=
(** No command *)
| spec_cmds_nil : forall ch P S, spec_cmds fp ch P S nil nil
(** The first command, then the rest in the scope it leaves *)
| spec_cmds_cons : forall ch P S c S' c' cs cs',
    spec_cmd fp ch P S c S' c' ->
    spec_cmds fp ch P S' cs cs' ->
    spec_cmds fp ch P S (c :: cs) (c' ++ cs').

(** ** Units

    The leading imports and opens of a unit are read twice.

    - Before the unit's header, they give the scope [L] of its parameter
      types ([spec_lead]): their units, and the names their opens declare, as
      what they name ([open_scope_entries]).  No parameter is in scope there.  Their
      loads run before the unit.
    - After its parameters, they are the first commands of the unit's own
      frame, where their names are members ([spec_cmds]), read in the scope
      [param_scope_entries ps ++ L].

    The unit's member chain is [nil]. *)
Inductive spec_lead : list scope_entry -> list Cst.cmd -> list scope_entry -> list core_cmd -> Prop :=
| spec_lead_nil : forall L, spec_lead L nil L nil
| spec_lead_import : forall L fq cs L' lds,
    spec_lead (scope_entry_unit fq :: L) cs L' lds ->
    spec_lead L (Cst.c_import fq :: cs) L' (core_cmd_load fq :: lds)
| spec_lead_open : forall L fq ip args its o E cs L' lds,
    itarget fq ip args = Some o ->
    spec_modexp L o E ->
    spec_lead (open_scope_entries E its ++ L) cs L' lds ->
    spec_lead L (Cst.c_open fq ip args its :: cs) L' lds.

Inductive elab_spec : Cst.prog -> cunit -> Prop :=
| elab_spec_intro : forall leads fp ps cs L lds tys ccs,
    spec_lead nil leads L lds ->
    NoDup (map fst ps) ->
    spec_params L ps tys ->
    spec_cmds fp nil (map fst ps) (param_scope_entries ps ++ L) (leads ++ cs) ccs ->
    elab_spec (leads, (fp, ps, cs)) (lds, ptele tys, ccs).

(** ** Elaborated Commands Are Written

    No rule emits a generated command ([core_cmd_gen]): the privacy check the
    core skips for those is never skipped for what the user writes. *)

Scheme spec_cmd_mind := Minimality for spec_cmd Sort Prop
with spec_cmds_mind := Minimality for spec_cmds Sort Prop.

Lemma spec_cmds_written : forall fp ch P S cs ccs, spec_cmds fp ch P S cs ccs -> cmds_written ccs.
Proof.
  intros fp.
  apply (spec_cmds_mind fp (fun _ _ _ _ _ c' => cmds_written c') (fun _ _ _ _ ccs => cmds_written ccs));
    intros; unfold cmds_written in *; repeat constructor; try assumption.
  - apply cmd_written_mod; assumption.
  - apply cmd_written_record; assumption.
  - apply List.Forall_app; split; assumption.
Qed.

Lemma spec_lead_written : forall L cs L' lds, spec_lead L cs L' lds -> cmds_written lds.
Proof. induction 1; unfold cmds_written in *; repeat constructor; assumption. Qed.

Lemma elab_spec_written : forall prg u, elab_spec prg u -> unit_written u.
Proof.
  intros * []; cbn; split; [ eapply spec_lead_written | eapply spec_cmds_written ]; eassumption.
Qed.
