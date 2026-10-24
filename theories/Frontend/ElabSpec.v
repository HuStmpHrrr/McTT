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

    - Everything in scope is one list of entries, innermost first ([ent]):
      core binders, members of the open frames, imported units, and, in the
      unit's parameter types only, the names its leading opens declare.  A name denotes its innermost entry, so there is no priority
      between kinds of entries and no invariant on the scope.
    - The core binders lie in the list in de Bruijn order.  A member of an
      open frame is generalized over the parameters of its frame and of the
      frames enclosing it, which are exactly the binders outside its entry;
      a use applies it to those variables.
    - A frame binds each name at most once ([fresh]): a parameter or a
      member, an open's declarations included.  A name an enclosing frame
      binds may be shadowed.
    - Where an object stands decides what it is: the head of a projection,
      the head of an application there, an alias body and an open target
      are module expressions ([selm]), everything else is a term ([sel]).

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

Inductive ent : Set :=
(** A core binder that may hold a module: a local module, an entry of a
    local body (an open's declarations included). *)
| en_var : string -> ent
(** A core binder of a term: a λ, a Π, a binder of a motive or a branch, a
    [let] definition, a parameter, an argument of a constructor, the type a
    declaration declares.  It is no module. *)
| en_tvar : string -> ent
(** A member of an open frame (an open's declarations included), named by
    its qualified name. *)
| en_mem : string -> qname -> ent
(** [import X::Y]: the unit [X::Y] may be named by its path. *)
| en_unit : path -> ent
(** A name a leading open declares, as the unit's parameter types see it:
    [en_open d E (Some n)] is the member [n] of the module [E], [en_open d
    E None] is [E] itself.  [E] is read where no binder is in scope. *)
| en_open : string -> modexp -> option string -> ent.

Definition ent_name (e : ent) : option string :=
  match e with
  | en_var x | en_tvar x | en_mem x _ | en_open x _ _ => Some x
  | en_unit _ => None
  end.

Definition ent_binders (e : ent) : nat :=
  match e with
  | en_var _ | en_tvar _ => 1
  | _ => 0
  end.

(** The names bound in [S], and the number of core binders in it. *)
Definition names (S : list ent) : list string :=
  flat_map (fun e => match ent_name e with Some x => x :: nil | None => nil end) S.

Definition binders (S : list ent) : nat := fold_right (fun e n => ent_binders e + n) 0 S.

(** [bound S x k e n]: [e] is the innermost entry of [S] that binds [x], with
    [k] core binders inside it and [n] outside. *)
#[warnings="-cannot-define-projection"]
Record bound (S : list ent) (x : string) (k : nat) (e : ent) (n : nat) : Prop := mk_bound
  { bd_inner : list ent
  ; bd_outer : list ent
  ; bd_split : S = bd_inner ++ e :: bd_outer
  ; bd_name : ent_name e = Some x
  ; bd_first : ~ In x (names bd_inner)
  ; bd_inner_binders : k = binders bd_inner
  ; bd_outer_binders : n = binders bd_outer }.

(** A frame may bind a name once. *)
Definition fresh (x : string) (F : list ent) : Prop := ~ In x (names F).

(** The entries of a parameter list, innermost first. *)
Definition pents (ps : list (string * Cst.obj)) : list ent := rev (map (fun p => en_tvar (fst p)) ps).

(** The entries of names bound in order, innermost first: the binders of
    an eliminator's motive and branches. *)
Definition vents (xs : list string) : list ent := rev (map en_tvar xs).

(** ** What an Entry Denotes

    [k] binders lie inside the entry and [n] outside it.  The parameters
    outside a member, in declaration order, are [vars_desc k n]:

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
Inductive den_term (k n : nat) : ent -> exp -> Prop :=
| dt_var : forall x, den_term k n (en_var x) #k
| dt_tvar : forall x, den_term k n (en_tvar x) #k
| dt_mem : forall x p, den_term k n (en_mem x p) (apps (qname_term p) (vars_desc k n))
| dt_open : forall x E c, den_term k n (en_open x E (Some c)) (a_mem E c).

(** As a module expression.  A variable that may hold a module is a module
    slot, which the core rejects if it holds a term; a term binder is the
    binder too: the core fills it, a term of a record type standing for
    the record's module at the term ([fill_mod_term]), and rejects any
    other. *)
Inductive den_mod (k n : nat) : ent -> modexp -> Prop :=
| dm_var : forall x, den_mod k n (en_var x) (me_var k)
(** A term binder: the binder, which the core fills when the term is of a
    record type *)
| dm_tvar : forall x, den_mod k n (en_tvar x) (me_var k)
| dm_mem : forall x p, den_mod k n (en_mem x p) (mapps (qname_mod p) (vars_desc k n))
| dm_open : forall x E oc, den_mod k n (en_open x E oc) (open_mod E oc).

(** ** What an Open Declares

    The items of an open, [iitem]s, are generated by the core
    ([items_gen]): [(None, W, true)] declares [W] as a private
    alias of the module, [(Some c, d, pv)] declares [d] as its member [c],
    privately when [pv]. *)

(** In a local body, the items of an open are entries of the body, one
    core binder each, newest first. *)
Definition item_ents (its : list iitem) : list ent := rev (map (fun it => en_var (iitem_name it)) its).

(** In the open frame at member chain [ch] of the unit [fp], they are
    members of the frame. *)
Definition item_mems (fp : path) (ch : list string) (its : list iitem) : list ent :=
  rev (map (fun it => en_mem (iitem_name it) (q_abs fp (ch ++ iitem_name it :: nil))) its).

(** Before the unit's header, in the scope of its parameter types, they
    denote what they name in the module [E]. *)
Definition open_ents (E : modexp) (its : list iitem) : list ent :=
  rev (map (fun it => en_open (iitem_name it) E (fst (fst it))) its).

(** What [open fq.ip args] names, as a module object: the unit [fq] at
    the member path [ip] if [fq] is not empty, the module [ip] in scope
    otherwise; applied to [args].  Read as any module object is, it needs
    the unit to be nameable. *)
Definition ihead (fq ip : path) : option Cst.obj :=
  match fq, ip with
  | nil, nil => None
  | nil, x :: ip' => Some (fold_left Cst.proj ip' (Cst.var x))
  | _, _ => Some (fold_left Cst.proj ip (Cst.glob fq))
  end.

Definition itarget (fq ip : path) (args : list Cst.obj) : option Cst.obj :=
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

    [sel S o M] holds when the surface object [o] denotes the term [M] in the
    scope [S], and [selm S o H] when it denotes the module expression [H].
    Every rule but the two for names, and the one for a projection from a
    head that is no path, is a homomorphism. *)

(** Whether an object is a path of module position: a name, a member of
    one, or one applied.  A projection from it is a member of the module
    it denotes; one from any other head is a member of a term's. *)
Fixpoint obj_path (o : Cst.obj) : bool :=
  match o with
  | Cst.var _ | Cst.glob _ => true
  | Cst.proj o' _ | Cst.app o' _ => obj_path o'
  | _ => false
  end.

(** [ptele ps] is the parameter list [ps] as a core context, innermost
    first. *)
Definition ptele (ps : list (string * typ)) : ctx := rev (map (fun p => ce_ass (snd p)) ps).

Inductive sel : list ent -> Cst.obj -> exp -> Prop :=
| sel_typ : forall S n, sel S (Cst.typ n) (Typeω@n)
| sel_suniv : forall S o M, sel S o M -> sel S (Cst.suniv o) (Type⟨M⟩)
| sel_level : forall S n, sel S (Cst.level n) (Level@n)
| sel_llit : forall S o, sel S (Cst.llit o) (𝕃ᵒ o)
| sel_succl : forall S o M, sel S o M -> sel S (Cst.succl o) (succl M)
| sel_maxl : forall S o1 o2 M N, sel S o1 M -> sel S o2 N -> sel S (Cst.maxl o1 o2) (maxl M N)
(** The token [ℕ] and a numeral are core literals: what they stand for is
    generated from the builtin bindings when the command runs. *)
| sel_nat : forall S, sel S Cst.nat ℕ
| sel_num : forall S n, sel S (Cst.num n) (a_nlit n)
| sel_true_ty : forall S, sel S Cst.true_ty ⊤
| sel_true_tm : forall S, sel S Cst.true_tm ⋆
| sel_false_ty : forall S, sel S Cst.false_ty ⊥
| sel_exfalso : forall S om mx oA M A,
    sel S om M -> sel (en_tvar mx :: S) oA A -> sel S (Cst.exfalso om mx oA) (efq M return A)
| sel_pi : forall S x oA oB A B,
    sel S oA A -> sel (en_tvar x :: S) oB B -> sel S (Cst.pi x oA oB) (Π A B)
| sel_fn : forall S x oA oM A M,
    sel S oA A -> sel (en_tvar x :: S) oM M -> sel S (Cst.fn x oA oM) (λ A M)
| sel_app : forall S o1 o2 M N,
    sel S o1 M -> sel S o2 N -> sel S (Cst.app o1 o2) (M $ N)
| sel_var : forall S x k e n M,
    bound S x k e n -> den_term k n e M -> sel S (Cst.var x) M
(** A projection selects a member of the module its head denotes, a
    name, a member of one, or one applied ([obj_path]). *)
| sel_proj : forall S o x H,
    obj_path o = true -> selm S o H -> sel S (Cst.proj o x) (a_mem H x)
(** A projection from any other head, a term, selects the member of the
    module of a [let] bound to it, which the core fills
    ([fill_mod_term]). *)
| sel_proj_let : forall S o x M,
    obj_path o = false -> sel S o M -> sel S (Cst.proj o x) (ℓ ≔ M in a_mem (me_var 0) x)
| sel_let : forall S x oA oM ob A M B,
    sel S oA A -> sel S oM M -> sel (en_tvar x :: S) ob B ->
    sel S (Cst.letb (Cst.d_def x (Some oA) oM) ob) (ℓ A ≔ M in B)
(** Without an annotation, none is emitted: the core infers it. *)
| sel_let_infer : forall S x oM ob M B,
    sel S oM M -> sel (en_tvar x :: S) ob B ->
    sel S (Cst.letb (Cst.d_def x None oM) ob) (ℓ ≔ M in B)
(** [let module x (ps) md in B end]: [x] is the slot of the local module. *)
| sel_let_mod : forall S x ps md ob U B,
    sunit S ps md U -> sel (en_var x :: S) ob B ->
    sel S (Cst.letb (Cst.d_mod x ps md) ob) (ℓₘ U in B)
(** An eliminator: its blocks, the one marked [at] the scrutinee's.  It
    carries no group and no uniform parameters: the core fills them from
    the annotations.  How many binders and branches there must be, and
    which constructor a branch is for, is the core's to check. *)
| sel_elim : forall S om bks M Bks m,
    sel S om M -> sblocks S bks Bks -> elim_at (List.map (fun bk => fst (fst (fst bk))) bks) = Some m ->
    sel S (Cst.elim om bks) (a_elim None nil m Bks M)
(** A record value: its type and its fields, as written.  Whether the type
    is a record type and the fields are its own, in order, is the core's
    to check. *)
| sel_tuple : forall S oT fs T Ms,
    sel S oT T -> stfields S fs Ms -> sel S (Cst.tuple oT fs) (a_tuple T Ms)

with selm : list ent -> Cst.obj -> modexp -> Prop :=
| selm_var : forall S x k e n H,
    bound S x k e n -> den_mod k n e H -> selm S (Cst.var x) H
| selm_glob : forall S fq,
    In (en_unit fq) S -> selm S (Cst.glob fq) (me_unit fq)
(** A name no binding in scope has is the imported unit of that one-segment
    path. *)
| selm_unit1 : forall S x,
    ~ In x (names S) -> In (en_unit (x :: nil)) S -> selm S (Cst.var x) (me_unit (x :: nil))
| selm_proj : forall S o y H,
    selm S o H -> selm S (Cst.proj o y) (me_mem H y)
| selm_app : forall S o1 o2 H N,
    selm S o1 H -> sel S o2 N -> selm S (Cst.app o1 o2) (me_app H N)

(** The fields of a record value, each its name and its value, all in the
    scope of the value. *)
with stfields : list ent -> list (string * Cst.obj) -> list (string * exp) -> Prop :=
(** No field *)
| stf_nil : forall S, stfields S nil nil
(** The first field, its name and its value, then the rest *)
| stf_cons : forall S y oM fs M Ms,
    sel S oM M -> stfields S fs Ms -> stfields S ((y, oM) :: fs) ((y, M) :: Ms)

with sbrs : list ent -> list (string * list string * Cst.obj) -> list (string * nat * exp) -> Prop :=
| sbr_nil : forall S, sbrs S nil nil
| sbr_cons : forall S c ys oB bs B Bs,
    sel (vents ys ++ S) oB B -> sbrs S bs Bs ->
    sbrs S ((c, ys, oB) :: bs) ((c, List.length ys, B) :: Bs)

(** The blocks of an eliminator: each its binders, the scrutinee's type
    under the binders before it, its motive under all of them, and its
    branches. *)
with sblocks : list ent -> list (bool * list (string * option Cst.obj) * Cst.obj * list (string * list string * Cst.obj)) ->
    list eblock -> Prop :=
| sbk_nil : forall S, sblocks S nil nil
| sbk_cons : forall S k xs oA bs bks oZ A Bs Bks,
    sbinders S nil xs oZ ->
    sel (vents (List.map fst xs) ++ S) oA A -> sbrs S bs Bs -> sblocks S bks Bks ->
    sblocks S ((k, xs, oA, bs) :: bks) (eb_mk (List.length xs) oZ A Bs :: Bks)

(** [sbinders S pre xs oZ]: the binders [xs] of a block, after the binders
    [pre], carry no type but the last, whose type, if written, is [oZ],
    read under the binders before it. *)
with sbinders : list ent -> list string -> list (string * option Cst.obj) -> option exp -> Prop :=
| sbd_nil : forall S pre, sbinders S pre nil None
| sbd_last_bare : forall S pre x, sbinders S pre ((x, None) :: nil) None
| sbd_last_typed : forall S pre x o Z,
    sel (vents pre ++ S) o Z -> sbinders S pre ((x, Some o) :: nil) (Some Z)
| sbd_cons : forall S pre x y xs oZ,
    sbinders S (pre ++ x :: nil) (y :: xs) oZ -> sbinders S pre ((x, None) :: y :: xs) oZ

(** Each parameter's type sees the earlier parameters. *)
with sparams : list ent -> list (string * Cst.obj) -> list (string * typ) -> Prop :=
| sp_nil : forall S, sparams S nil nil
| sp_cons : forall S x oA ps A tys,
    sel S oA A ->
    sparams (en_tvar x :: S) ps tys ->
    sparams S ((x, oA) :: ps) ((x, A) :: tys)

(** A local module: its parameters, then its definition under them. *)
with sunit : list ent -> list (string * Cst.obj) -> Cst.mdef -> gunit -> Prop :=
| su_intro : forall S ps md tys D,
    NoDup (map fst ps) ->
    sparams S ps tys ->
    sdef (pents ps ++ S) md D ->
    sunit S ps md (gu_mk (ptele tys) D)

with sdef : list ent -> Cst.mdef -> moddef -> Prop :=
| sdf_alias : forall S oE E,
    selm S oE E -> sdef S (Cst.md_alias oE) (md_alias E)
| sdf_where : forall S cs Φ,
    sbody S gm_nil cs Φ -> sdef S (Cst.md_where cs) (md_body sm_open Φ)

(** [sbody S Φ cs Φ']: the commands [cs] of a local body extend [Φ] to [Φ'].
    Each entry is a core binder for the entries after it.  An open is a
    pre-form the core expands ([gm_open]); each of its items is a core
    binder.  The names of a body are checked fresh by the core.  A local
    body has no [import]s, no [eval]s and no axioms. *)
with sbody : list ent -> gmod -> list Cst.cmd -> gmod -> Prop :=
| sb_nil : forall S Φ, sbody S Φ nil Φ
| sb_def : forall S Φ m x oA oM A M cs Φ',
    sel S oA A -> sel S oM M ->
    sbody (en_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs Φ' ->
    sbody S Φ (Cst.c_def m x oA oM :: cs) Φ'
| sb_mod : forall S Φ pv x ps md U cs Φ',
    sunit S ps md U ->
    sbody (en_var x :: S) (gm_ext Φ x (ge_mod pv U)) cs Φ' ->
    sbody S Φ (Cst.c_mod pv x ps md :: cs) Φ'
(** It loads nothing, so a unit it names must be nameable already. *)
| sb_open : forall S Φ fq ip args its o E cs Φ',
    itarget fq ip args = Some o ->
    selm S o E ->
    sbody (item_ents its ++ S) (gm_open Φ E its) cs Φ' ->
    sbody S Φ (Cst.c_open fq ip args its :: cs) Φ'.

(** ** Inductive Declarations

    The type of a declaration binds its non-uniform parameters in front of
    its sort ([split_pis]).  The declared name is in scope in the
    constructors' argument types as an ordinary variable, [Self], outside
    the declaration's parameters, so a recursive occurrence is written with
    all of them, and every argument binds its name for the ones after it.  Which arguments are recursive is the core's to decide
    ([Core.Syntactic.Inductives.Group]). *)
Fixpoint split_pis (o : Cst.obj) : (list (string * Cst.obj) * Cst.obj)%type :=
  match o with
  | Cst.pi y oA oB => let (ps, oS) := split_pis oB in ((y, oA) :: ps, oS)
  | _ => (nil, o)
  end.

Inductive srargs : list ent -> list (string * Cst.obj) -> list (string * exp) -> Prop :=
| sra_nil : forall S, srargs S nil nil
| sra_cons : forall S y oA args A args',
    sel S oA A -> srargs (en_tvar y :: S) args args' ->
    srargs S ((y, oA) :: args) ((y, A) :: args').

Inductive srcons (S : list ent) :
    list (string * list (string * Cst.obj)) -> list (string * list (string * exp)) -> Prop :=
| src_nil : srcons S nil nil
| src_cons : forall c args cs args' cs',
    srargs S args args' -> srcons S cs cs' ->
    srcons S ((c, args) :: cs) ((c, args') :: cs').

(** The names of the members of a group. *)
Definition member_names (ms : list (string * Cst.obj * list (string * list (string * Cst.obj)))) : list string :=
  List.map (fun m => fst (fst m)) ms.

(** The members of a group, under its uniform parameters [ups] in the
    scope [S], the members' names [xs] in scope in every argument outside
    the parameters: each its non-uniform parameters, its sort and its
    constructors. *)
Inductive smembers (S : list ent) (ups : list (string * Cst.obj)) (xs : list string) :
    list (string * Cst.obj * list (string * list (string * Cst.obj))) -> list raw_member -> Prop :=
| sm_nil : smembers S ups xs nil nil
| sm_cons : forall x oT cs ms nps oS ntys A cs' rms,
    split_pis oT = (nps, oS) ->
    NoDup (map fst (ups ++ nps)) ->
    sparams (pents ups ++ S) nps ntys ->
    sel (pents ups ++ S) oS A ->
    srcons (pents (ups ++ nps) ++ vents xs ++ S) cs cs' ->
    smembers S ups xs ms rms ->
    smembers S ups xs ((x, oT, cs) :: ms) (mk_rmem x (ptele ntys) A cs' :: rms).

(** ** Mutual Definitions

    A function's parameters are its non-uniform ones, then its scrutinee,
    last; its result type sees all of them, its clauses only the common
    parameters, as an eliminator's branches see only what is outside it. *)

(** The names of the functions. *)
Definition fun_names (fs : list (string * list (string * Cst.obj) * Cst.obj * list (string * list string * Cst.obj))) :
    list string :=
  List.map (fun f => fst (fst (fst f))) fs.

Inductive sfuns (S : list ent) :
    list (string * list (string * Cst.obj) * Cst.obj * list (string * list string * Cst.obj)) -> list raw_fun -> Prop :=
| sf_nil : sfuns S nil nil
| sf_cons : forall f ys z oZ oA bs fs ytys Z A Bs rfs,
    NoDup (map fst (ys ++ (z, oZ) :: nil)) ->
    sparams S ys ytys ->
    sel (pents ys ++ S) oZ Z ->
    sel (en_tvar z :: pents ys ++ S) oA A ->
    sbrs S bs Bs ->
    sfuns S fs rfs ->
    sfuns S ((f, ys ++ (z, oZ) :: nil, oA, bs) :: fs) (mk_rfun f (ptele ytys) Z A Bs :: rfs).

(** The entries of names filed in order in the open frame at member chain
    [ch] of the unit [fp], innermost first. *)
Definition filed_mems (fp : path) (ch : list string) (xs : list string) : list ent :=
  rev (map (fun x => en_mem x (q_abs fp (ch ++ x :: nil))) xs).

(** ** Record Types

    A record type's module is a frame over the record's parameters and,
    bound last, a value of the record ([Core.Syntactic.Members.record_mod_tele]),
    whose members are the fields, then the with-area.  The value has no
    name: a member of the with-area reaches it through the fields, which
    are members of the frame, so [snd] is the field of the value the
    module is at. *)

(** The value a record's module is at: a term binder no name denotes. *)
Definition en_self : ent := en_tvar "".

(** The entries of the frame of the record [x] with the parameters [ps]
    and the fields [fs], declared at member chain [ch] of the unit [fp],
    before its with-area: the fields, the value, then the parameters,
    innermost first. *)
Definition record_ents (fp : path) (ch : list string) (x : string) (ps fs : list (string * Cst.obj)) : list ent :=
  filed_mems fp (ch ++ x :: nil) (map fst fs) ++ en_self :: pents ps.

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

    [scmd fp ch O F c F' c']: the command [c], in the open frame at member
    chain [ch] of the unit [fp], which binds [F] so far inside the scope
    [O], binds [F'] after it and emits the core commands [c'].  [scmds]
    runs the commands of a body in order.  A definition keyword with a
    modifier it implies ([Cst.c_error]) has no rule. *)
Inductive scmd (fp : path) : list string -> list ent -> list ent -> Cst.cmd -> list ent -> list ccmd -> Prop :=
| sc_def : forall ch O F m x oA oM A M,
    fresh x F ->
    sel (F ++ O) oA A ->
    sel (F ++ O) oM M ->
    scmd fp ch O F (Cst.c_def m x oA oM) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M) :: nil)
(** An axiom is opaque, and has no body. *)
| sc_axiom : forall ch O F x oA A,
    fresh x F ->
    sel (F ++ O) oA A ->
    scmd fp ch O F (Cst.c_axiom x oA) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_def x false false A None :: nil)
(** The parameters of [module x (ps) where body end] are read in [F], its
    body in a new frame inside. *)
| sc_mod : forall ch O F pv x ps body tys bcs,
    fresh x F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    scmds fp (ch ++ x :: nil) (F ++ O) (pents ps) body bcs ->
    scmd fp ch O F (Cst.c_mod pv x ps (Cst.md_where body)) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_mod x pv (ptele tys) bcs :: nil)
(** [module x (ps) := E]: [E] is read under the parameters. *)
| sc_alias : forall ch O F pv x ps oE tys E,
    fresh x F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    selm (pents ps ++ F ++ O) oE E ->
    scmd fp ch O F (Cst.c_mod pv x ps (Cst.md_alias oE)) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_alias x pv (ptele tys) E :: nil)
(** [import X::Y] loads the unit, which may be named from then on. *)
| sc_import : forall ch O F fq,
    scmd fp ch O F (Cst.c_import fq) (en_unit fq :: F) (cc_load fq :: nil)
(** An open loads nothing, so a unit it names must be nameable already.
    Each name it declares is fresh in the frame before it; whether it
    declares one twice is the core's to check. *)
| sc_open : forall ch O F fq ip args its o E,
    itarget fq ip args = Some o ->
    selm (F ++ O) o E ->
    Forall (fun d => fresh d F) (map iitem_name its) ->
    scmd fp ch O F (Cst.c_open fq ip args its) (item_mems fp ch its ++ F) (cc_open E its :: nil)
| sc_eval : forall ch O F oM M,
    sel (F ++ O) oM M ->
    scmd fp ch O F (Cst.c_eval oM None) F (cc_eval M None :: nil)
| sc_eval_typ : forall ch O F oM oA M A,
    sel (F ++ O) oM M ->
    sel (F ++ O) oA A ->
    scmd fp ch O F (Cst.c_eval oM (Some oA)) F (cc_eval M (Some A) :: nil)
(** [inductive x (ups) : T where cs with y : U where … end]: the uniform
    parameters are read in [F], each member's non-uniform ones and sort
    under them, the constructors' arguments under all, with the members'
    names in scope.  It declares each member, a module whose members are
    the constructors.  The group files its recursor module as written
    ([wr]). *)
| sc_ind : forall ch O F pv wr ups ms tys rms,
    NoDup (member_names ms) ->
    Forall (fun x => fresh x F) (member_names ms) ->
    sparams (F ++ O) ups tys ->
    smembers (F ++ O) ups (member_names ms) ms rms ->
    scmd fp ch O F (Cst.c_ind pv wr ups ms) (filed_mems fp ch (member_names ms) ++ F)
      (cc_ind pv (mk_raw (ptele tys) rms wr) :: nil)
(** [mutual def (ps) f … with g … end]: the common parameters are read in
    [F], the functions under them.  It declares each function. *)
| sc_mdef : forall ch O F m ps fs tys rfs,
    NoDup (map fst ps) ->
    NoDup (fun_names fs) ->
    Forall (fun x => fresh x F) (fun_names fs) ->
    sparams (F ++ O) ps tys ->
    sfuns (pents ps ++ F ++ O) fs rfs ->
    scmd fp ch O F (Cst.c_mdef m ps fs) (filed_mems fp ch (fun_names fs) ++ F)
      (cc_mdef (negb (Cst.md_abstract m)) (Cst.md_private m) (ptele tys) rfs :: nil)
(** [inductive x (ps) := E]: [E] is read under the parameters, as an
    alias's target is; whether it names an inductive type, and its
    arguments the type's, is the core's to check. *)
| sc_ind_alias : forall ch O F pv x ps oE tys E,
    fresh x F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    selm (pents ps ++ F ++ O) oE E ->
    scmd fp ch O F (Cst.c_ind_alias pv x ps oE) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_ind_alias x pv (ptele tys) E :: nil)
(** [record x (ps) := E]: as an inductive alias; whether [E] names a record
    type is the core's to check. *)
| sc_record_alias : forall ch O F pv x ps oE tys E,
    fresh x F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    selm (pents ps ++ F ++ O) oE E ->
    scmd fp ch O F (Cst.c_record_alias pv x ps oE) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_record_alias x pv (ptele tys) E :: nil)
(** [builtin k := X]: [X] is a module, as written; whether it is an
    inductive type of the right shape is the core's to check. *)
| sc_builtin : forall ch O F k oX H,
    selm (F ++ O) oX H ->
    scmd fp ch O F (Cst.c_builtin k oX) F (cc_builtin k H :: nil)
(** [record x (ps) : S where f : A ; … with cs end]: the parameters are
    read in [F], the sort under them, each field's type under them and the
    fields before it.  The with-area is read in the record's frame
    ([record_ents]), with [x] in scope outside it; no name it declares is
    a field's.  It declares [x], a type and a module. *)
| sc_record : forall ch O F pv x ps oS fs cs tys Srt fs' bcs,
    fresh x F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    sel (pents ps ++ F ++ O) oS Srt ->
    srargs (pents ps ++ F ++ O) fs fs' ->
    Forall (fun y => ~ In y (map fst fs)) (flat_map cmd_decls cs) ->
    scmds fp (ch ++ x :: nil) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F ++ O) (record_ents fp ch x ps fs) cs bcs ->
    scmd fp ch O F (Cst.c_record pv x ps oS fs cs) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_record x pv (ptele tys) Srt fs' bcs :: nil)

with scmds (fp : path) : list string -> list ent -> list ent -> list Cst.cmd -> list ccmd -> Prop :=
| scs_nil : forall ch O F, scmds fp ch O F nil nil
| scs_cons : forall ch O F c F' c' cs cs',
    scmd fp ch O F c F' c' ->
    scmds fp ch O F' cs cs' ->
    scmds fp ch O F (c :: cs) (c' ++ cs').

(** ** Units

    The leading imports and opens of a unit are read twice.

    - Before the unit's header, they give the scope [L] of its parameter
      types ([slead]): their units, and the names their opens declare, as
      what they name ([open_ents]).  No parameter is in scope there.  Their
      loads run before the unit.
    - After its parameters, they are the first commands of the unit's own
      frame, where their names are members ([scmds]).

    The unit's member chain is [nil]. *)
Inductive slead : list ent -> list Cst.cmd -> list ent -> list ccmd -> Prop :=
| sl_nil : forall L, slead L nil L nil
| sl_import : forall L fq cs L' lds,
    slead (en_unit fq :: L) cs L' lds ->
    slead L (Cst.c_import fq :: cs) L' (cc_load fq :: lds)
| sl_open : forall L fq ip args its o E cs L' lds,
    itarget fq ip args = Some o ->
    selm L o E ->
    slead (open_ents E its ++ L) cs L' lds ->
    slead L (Cst.c_open fq ip args its :: cs) L' lds.

Inductive elab_spec : Cst.prog -> cunit -> Prop :=
| es_intro : forall leads fp ps cs L lds tys ccs,
    slead nil leads L lds ->
    NoDup (map fst ps) ->
    sparams L ps tys ->
    scmds fp nil L (pents ps) (leads ++ cs) ccs ->
    elab_spec (leads, (fp, ps, cs)) (lds, ptele tys, ccs).

(** ** Elaborated Commands Are Written

    No rule emits a generated command ([cc_gen]): the privacy check the
    core skips for those is never skipped for what the user writes. *)

Scheme scmd_mind := Minimality for scmd Sort Prop
with scmds_mind := Minimality for scmds Sort Prop.

Lemma scmds_written : forall fp ch O F cs ccs, scmds fp ch O F cs ccs -> cmds_written ccs.
Proof.
  intros fp.
  apply (scmds_mind fp (fun _ _ _ _ _ c' => cmds_written c') (fun _ _ _ _ ccs => cmds_written ccs));
    intros; unfold cmds_written in *; repeat constructor; try assumption.
  - apply cmd_written_mod; assumption.
  - apply cmd_written_record; assumption.
  - apply List.Forall_app; split; assumption.
Qed.

Lemma slead_written : forall L cs L' lds, slead L cs L' lds -> cmds_written lds.
Proof. induction 1; unfold cmds_written in *; repeat constructor; assumption. Qed.

Lemma elab_spec_written : forall prg u, elab_spec prg u -> unit_written u.
Proof.
  intros * []; cbn; split; [ eapply slead_written | eapply scmds_written ]; eassumption.
Qed.
