From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members Command.

Import Syntax_Notations.

(** * A Declarative Specification of Elaboration

    [elab_spec prg u] holds when the surface unit [prg] elaborates to the core
    unit [u].  [Frontend/ElabCorrect.v] proves that [elaborate_core] computes
    exactly this relation.

    Elaboration turns names into de Bruijn indices, and decides from an
    object's position whether it is a term or a module expression.  It never
    looks inside a module, nor into another unit: what [M.x] names, and
    whether it may be named, is left to the core.  A unit may be named once
    this unit imports it.

    - Everything in scope is one list of entries, innermost first ([ent]):
      core binders, the self slots of the bodies being read, the members of
      those bodies, and imported units.  A name denotes its innermost entry,
      so there is no priority between kinds of entries and no invariant on
      the scope.
    - The core binders and self slots lie in the list in de Bruijn order.
      A member [y] of a body is read from that body's self slot: it denotes
      [a_mem (me_var k) y], where [k] is the index of the nearest self slot
      outside its entry ([self_index]).  Global and local bodies are read
      alike, and a member is never applied to anything.
    - A frame binds each name at most once ([fresh]): a parameter or a
      member, an open's declarations included; a unit's frame also the
      names its leading opens declare.  A name an enclosing frame binds may
      be shadowed.
    - Where an object stands decides what it is: the head of a projection,
      the head of an application there, an alias body and an open target
      are module expressions ([selm]), everything else is a term ([sel]).

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

    The body of [k] is read in the scope

<<
y, x, self, B, id, self, A, self
>>

    (innermost first).  [id] is a member of the body of [M], whose self slot
    lies under four binders ([y], [x], the self slot of [N], [B]), so it
    denotes [a_mem (me_var 4) id], and [id x] is [a_mem (me_var 4) id $ #1].
    In [j], [M] is a member of [Main]'s own body, read from its self slot
    [#0]: [M.id Nat] is [a_mem (me_mem (me_var 0) M) id $ ℕ]. *)

(** ** Entries *)

Inductive ent : Set :=
(** A core binder: a λ, a Π, a recursor, a [let], a parameter, a module
    slot, a name a leading open declares. *)
| en_var : string -> ent
(** The self slot of a body being read: it holds the entries before the
    one being read, and binds no name. *)
| en_self : ent
(** [en_mem x c]: the name [x] of the member [c] of the module in the
    nearest self slot outside it.  A body's members, an open's declarations
    included, are named by themselves; the names a leading open declares
    are read from the slot of its target. *)
| en_mem : string -> string -> ent
(** [import X::Y]: the unit [X::Y] may be opened. *)
| en_unit : path -> ent.

Definition ent_name (e : ent) : option string :=
  match e with
  | en_var x | en_mem x _ => Some x
  | en_self | en_unit _ => None
  end.

Definition ent_binders (e : ent) : nat :=
  match e with
  | en_var _ | en_self => 1
  | _ => 0
  end.

(** The names bound in [S], and the number of core binders in it. *)
Definition names (S : list ent) : list string :=
  flat_map (fun e => match ent_name e with Some x => x :: nil | None => nil end) S.

Definition binders (S : list ent) : nat := fold_right (fun e n => ent_binders e + n) 0 S.

(** The index of the nearest self slot of [S]. *)
Fixpoint self_index (S : list ent) : option nat :=
  match S with
  | nil => None
  | en_self :: _ => Some 0
  | e :: S' => option_map (plus (ent_binders e)) (self_index S')
  end.

(** [bound S x k e S2]: [e] is the innermost entry of [S] that binds [x],
    with [k] core binders inside it and the entries [S2] outside it. *)
Definition bound (S : list ent) (x : string) (k : nat) (e : ent) (S2 : list ent) : Prop :=
  exists S1, S = S1 ++ e :: S2 /\ ent_name e = Some x /\ ~ In x (names S1) /\ k = binders S1.

(** A frame may bind a name once: not among the names [X] it reserves, its
    parameters', nor among its members [F]. *)
Definition fresh (x : string) (X : list string) (F : list ent) : Prop := ~ In x (X ++ names F).

(** The entries of a parameter list, innermost first. *)
Definition pents (ps : list (string * Cst.obj)) : list ent := rev (map (fun p => en_var (fst p)) ps).

(** ** What an Entry Denotes

    [k] binders lie inside the entry, [S2] is the scope outside it. *)

(** As a term.  A member is read from the nearest self slot outside it. *)
Inductive den_term (k : nat) (S2 : list ent) : ent -> exp -> Prop :=
| dt_var : forall x, den_term k S2 (en_var x) #k
| dt_mem : forall x c j, self_index S2 = Some j -> den_term k S2 (en_mem x c) (a_mem (me_var (k + j)) c).

(** As a module expression.  A variable is a module slot; the core rejects
    it if it is a term variable. *)
Inductive den_mod (k : nat) (S2 : list ent) : ent -> modexp -> Prop :=
| dm_var : forall x, den_mod k S2 (en_var x) (me_var k)
| dm_mem : forall x c j, self_index S2 = Some j -> den_mod k S2 (en_mem x c) (me_mem (me_var (k + j)) c).

(** [mapps H args] applies the module expression [H] to each of [args] in
    turn. *)
Definition mapps (H : modexp) (args : list exp) : modexp := fold_left me_app args H.

(** ** What an Open Declares

    The core generates an open's declarations ([Core.Syntactic.Imports]):
    an open [cc_open E oz its] declares the private alias [z] of [E] if [oz =
    Some z], then each item [(n, d, pv)] of [its] as the member [n],
    privately when [pv].  The surface items say the same ([Cst.iitem]): the
    item [(None, W, true)] is the alias [W], and an open declares either the
    alias or members ([Cst.open_cmds]). *)
Definition open_items (its : list Cst.iitem) : option (option string * list iitem)%type :=
  match its with
  | (None, W, true) :: nil => Some (Some W, nil)
  | _ =>
      option_map (fun its' => (None, its'))
        ((fix go (its : list Cst.iitem) : option (list iitem) :=
            match its with
            | nil => Some nil
            | (Some n, d, pv) :: its' => option_map (cons (n, d, pv)) (go its')
            | (None, _, _) :: _ => None
            end) its)
  end.

(** The name an item declares. *)
Definition citem_name (it : Cst.iitem) : string := let '(_, d, _) := it in d.

(** In a body, what an open declares are members of the body, newest
    first. *)
Definition item_mems (its : list Cst.iitem) : list ent :=
  rev (map (fun it => en_mem (citem_name it) (citem_name it)) its).

(** Before the unit's header, an open declares the slot of its target in
    the leading context ([lead_slot]): named, if it is [as W], or read from
    by the names it declares, newest first. *)
Definition lead_ents (its : list Cst.iitem) : list ent :=
  match its with
  | (None, W, _) :: nil => en_var W :: nil
  | _ =>
      rev (map (fun it => let '(on, d, _) := it in en_mem d (match on with Some n => n | None => d end)) its)
        ++ en_self :: nil
  end.

(** What [open fq.ip args] names, as a module object: the unit [fq] at
    the member path [ip] if [fq] is not empty, the module [ip] in scope
    otherwise; applied to [args].  It loads nothing, so the unit must be
    imported. *)
Definition ihead (fq ip : path) : option Cst.obj :=
  match fq, ip with
  | nil, nil => None
  | nil, x :: ip' => Some (fold_left Cst.proj ip' (Cst.var x))
  | _, _ => Some (fold_left Cst.proj ip (Cst.glob fq))
  end.

Definition itarget (fq ip : path) (args : list Cst.obj) : option Cst.obj :=
  option_map (fold_left Cst.app args) (ihead fq ip).

(** ** Objects

    [sel S o M] holds when the surface object [o] denotes the term [M] in the
    scope [S], and [selm S o H] when it denotes the module expression [H].
    Every rule but the two for names is a homomorphism. *)

(** [ptele ps] is the parameter list [ps] as a core context, innermost
    first. *)
Definition ptele (ps : list (string * typ)) : ctx := rev (map (fun p => ce_ass (snd p)) ps).

Inductive sel : list ent -> Cst.obj -> exp -> Prop :=
| sel_typ : forall S n, sel S (Cst.typ n) (Type@n)
| sel_nat : forall S, sel S Cst.nat ℕ
| sel_zero : forall S, sel S Cst.zero zero
| sel_succ : forall S o M, sel S o M -> sel S (Cst.succ o) (succ M)
| sel_natrec : forall S on mx om oz sx sr os N A MZ MS,
    sel S on N ->
    sel (en_var mx :: S) om A ->
    sel S oz MZ ->
    sel (en_var sr :: en_var sx :: S) os MS ->
    sel S (Cst.natrec on mx om oz sx sr os) (rec N return A | zero -> MZ | succ -> MS end)
| sel_true_ty : forall S, sel S Cst.true_ty ⊤
| sel_true_tm : forall S, sel S Cst.true_tm ⋆
| sel_false_ty : forall S, sel S Cst.false_ty ⊥
| sel_exfalso : forall S om mx oA M A,
    sel S om M -> sel (en_var mx :: S) oA A -> sel S (Cst.exfalso om mx oA) (efq M return A)
| sel_pi : forall S x oA oB A B,
    sel S oA A -> sel (en_var x :: S) oB B -> sel S (Cst.pi x oA oB) (Π A B)
| sel_fn : forall S x oA oM A M,
    sel S oA A -> sel (en_var x :: S) oM M -> sel S (Cst.fn x oA oM) (λ A M)
| sel_app : forall S o1 o2 M N,
    sel S o1 M -> sel S o2 N -> sel S (Cst.app o1 o2) (M $ N)
| sel_var : forall S x k e S2 M,
    bound S x k e S2 -> den_term k S2 e M -> sel S (Cst.var x) M
(** A projection selects a member of the module its head denotes. *)
| sel_proj : forall S o x H,
    selm S o H -> sel S (Cst.proj o x) (a_mem H x)
| sel_let : forall S x oA oM ob A M B,
    sel S oA A -> sel S oM M -> sel (en_var x :: S) ob B ->
    sel S (Cst.letb (Cst.d_def x (Some oA) oM) ob) (ℓ A ≔ M in B)
(** Without an annotation, none is emitted: the core infers it. *)
| sel_let_infer : forall S x oM ob M B,
    sel S oM M -> sel (en_var x :: S) ob B ->
    sel S (Cst.letb (Cst.d_def x None oM) ob) (ℓ ≔ M in B)
(** [let module x (ps) md in B end]: [x] is the slot of the local module. *)
| sel_let_mod : forall S x ps md ob U B,
    sunit S ps md U -> sel (en_var x :: S) ob B ->
    sel S (Cst.letb (Cst.d_mod x ps md) ob) (ℓₘ U in B)

with selm : list ent -> Cst.obj -> modexp -> Prop :=
| selm_var : forall S x k e S2 H,
    bound S x k e S2 -> den_mod k S2 e H -> selm S (Cst.var x) H
(** A unit may be named once imported. *)
| selm_glob : forall S fq, In (en_unit fq) S -> selm S (Cst.glob fq) (me_unit fq)
| selm_proj : forall S o y H,
    selm S o H -> selm S (Cst.proj o y) (me_mem H y)
| selm_app : forall S o1 o2 H N,
    selm S o1 H -> sel S o2 N -> selm S (Cst.app o1 o2) (me_app H N)

(** Each parameter's type sees the earlier parameters. *)
with sparams : list ent -> list (string * Cst.obj) -> list (string * typ) -> Prop :=
| sp_nil : forall S, sparams S nil nil
| sp_cons : forall S x oA ps A tys,
    sel S oA A ->
    sparams (en_var x :: S) ps tys ->
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
(** A body is read under its self slot. *)
| sdf_where : forall S cs Φ,
    sbody (en_self :: S) gm_nil cs Φ -> sdef S (Cst.md_where cs) (md_body Φ)

(** [sbody S Φ cs Φ']: the commands [cs] of a local body extend [Φ] to [Φ'].
    Each entry is a member of the body for the entries after it.  An open is
    a pre-form the core expands ([gm_open]); each of its declarations is a
    member.  The names of a body are checked fresh by the core.  A local
    body has no [import]s, no [eval]s, no axioms and no abstract
    definitions. *)
with sbody : list ent -> gmod -> list Cst.cmd -> gmod -> Prop :=
| sb_nil : forall S Φ, sbody S Φ nil Φ
| sb_def : forall S Φ m x oA oM A M cs Φ',
    Cst.md_abstract m = false ->
    sel S oA A -> sel S oM M ->
    sbody (en_mem x x :: S) (gm_ext Φ x (ge_def (Cst.md_private m) A (Some M))) cs Φ' ->
    sbody S Φ (Cst.c_def m x oA oM :: cs) Φ'
| sb_mod : forall S Φ pv x ps md U cs Φ',
    sunit S ps md U ->
    sbody (en_mem x x :: S) (gm_ext Φ x (ge_mod pv U)) cs Φ' ->
    sbody S Φ (Cst.c_mod pv x ps md :: cs) Φ'
| sb_open : forall S Φ fq ip args its o E oz its' cs Φ',
    itarget fq ip args = Some o ->
    selm S o E ->
    open_items its = Some (oz, its') ->
    sbody (item_mems its ++ S) (gm_open Φ E oz its') cs Φ' ->
    sbody S Φ (Cst.c_open fq ip args its :: cs) Φ'.

(** ** Commands

    [scmd X O F c F' c']: the command [c], in the open frame which reserves
    the names [X] and binds the members [F] so far, inside the scope [O]
    whose head is the frame's self slot, binds [F'] after it and emits the
    core commands [c'].  [scmds] runs the commands of a body in order.  A definition keyword with a modifier it
    implies ([Cst.c_error]) has no rule. *)
Inductive scmd : list string -> list ent -> list ent -> Cst.cmd -> list ent -> list ccmd -> Prop :=
| sc_def : forall X O F m x oA oM A M,
    fresh x X F ->
    sel (F ++ O) oA A ->
    sel (F ++ O) oM M ->
    scmd X O F (Cst.c_def m x oA oM) (en_mem x x :: F)
      (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M) :: nil)
(** An axiom has no body. *)
| sc_axiom : forall X O F x oA A,
    fresh x X F ->
    sel (F ++ O) oA A ->
    scmd X O F (Cst.c_axiom x oA) (en_mem x x :: F) (cc_def x false false A None :: nil)
(** The parameters of [module x (ps) where body end] are read in [F], its
    body in a new frame inside, under its own self slot. *)
| sc_mod : forall X O F pv x ps body tys bcs,
    fresh x X F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    scmds (map fst ps) (en_self :: pents ps ++ F ++ O) nil body bcs ->
    scmd X O F (Cst.c_mod pv x ps (Cst.md_where body)) (en_mem x x :: F) (cc_mod x pv (ptele tys) bcs :: nil)
(** [module x (ps) := E]: [E] is read under the parameters. *)
| sc_alias : forall X O F pv x ps oE tys E,
    fresh x X F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    selm (pents ps ++ F ++ O) oE E ->
    scmd X O F (Cst.c_mod pv x ps (Cst.md_alias oE)) (en_mem x x :: F) (cc_alias x pv (ptele tys) E :: nil)
(** [import X::Y] loads the unit, which may be opened from then on. *)
| sc_import : forall X O F fq,
    scmd X O F (Cst.c_import fq) (en_unit fq :: F) (cc_load fq :: nil)
(** Each name an open declares is fresh in the frame before it; whether it
    declares one twice is the core's to check. *)
| sc_open : forall X O F fq ip args its o E oz its',
    itarget fq ip args = Some o ->
    selm (F ++ O) o E ->
    open_items its = Some (oz, its') ->
    Forall (fun d => fresh d X F) (map citem_name its) ->
    scmd X O F (Cst.c_open fq ip args its) (item_mems its ++ F) (cc_open E oz its' :: nil)
| sc_eval : forall X O F oM M,
    sel (F ++ O) oM M ->
    scmd X O F (Cst.c_eval oM None) F (cc_eval M None :: nil)
| sc_eval_typ : forall X O F oM oA M A,
    sel (F ++ O) oM M ->
    sel (F ++ O) oA A ->
    scmd X O F (Cst.c_eval oM (Some oA)) F (cc_eval M (Some A) :: nil)

with scmds : list string -> list ent -> list ent -> list Cst.cmd -> list ccmd -> Prop :=
| scs_nil : forall X O F, scmds X O F nil nil
| scs_cons : forall X O F c F' c' cs cs',
    scmd X O F c F' c' ->
    scmds X O F' cs cs' ->
    scmds X O F (c :: cs) (c' ++ cs').

(** ** Units

    The leading imports and opens of a unit come before its header
    ([slead]).  An import makes its unit nameable, an open declares a slot
    of the leading context, in which the unit's parameters are read and
    which its body sees.  The body is read under the unit's self slot;
    its frame reserves the names of the parameters and of the leading
    context. *)
Inductive slead : list ent -> list Cst.cmd -> list ent -> list ccmd -> Prop :=
| sl_nil : forall L, slead L nil L nil
| sl_import : forall L fq cs L' lds,
    slead (en_unit fq :: L) cs L' lds ->
    slead L (Cst.c_import fq :: cs) L' (cc_load fq :: lds)
| sl_open : forall L fq ip args its o E oz its' cs L' lds,
    itarget fq ip args = Some o ->
    selm L o E ->
    open_items its = Some (oz, its') ->
    Forall (fun d => fresh d nil L) (map citem_name its) ->
    slead (lead_ents its ++ L) cs L' lds ->
    slead L (Cst.c_open fq ip args its :: cs) L' (cc_open E oz its' :: lds).

Inductive elab_spec : Cst.prog -> cunit -> Prop :=
| es_intro : forall leads fp ps cs L lds tys ccs,
    slead nil leads L lds ->
    NoDup (map fst ps) ->
    Forall (fun x => fresh x nil L) (map fst ps) ->
    sparams L ps tys ->
    scmds (map fst ps ++ names L) (en_self :: pents ps ++ L) nil cs ccs ->
    elab_spec (leads, (fp, ps, cs)) (lds, ptele tys, ccs).
