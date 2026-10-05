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
y, x, B, id ↦ Main.M.id, A
>>

    (innermost first).  [id] lies under three binders ([y], [x], [B]) and
    over one ([A]), so it denotes [Main.M.id $ #3], and [id x] is
    [Main.M.id $ #3 $ #1].  In [j], [M] is closed, so [M] is the module
    [⟨Main.M⟩] and [M.id Nat] selects its member [id] and applies it. *)

(** ** Entries *)

Inductive ent : Set :=
(** A core binder: a λ, a Π, a recursor, a [let], a parameter, an entry of a
    local body (an open's declarations included). *)
| en_var : string -> ent
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
  | en_var x | en_mem x _ | en_open x _ _ => Some x
  | en_unit _ => None
  end.

Definition ent_binders (e : ent) : nat :=
  match e with
  | en_var _ => 1
  | _ => 0
  end.

(** The names bound in [S], and the number of core binders in it. *)
Definition names (S : list ent) : list string :=
  flat_map (fun e => match ent_name e with Some x => x :: nil | None => nil end) S.

Definition binders (S : list ent) : nat := fold_right (fun e n => ent_binders e + n) 0 S.

(** [bound S x k e n]: [e] is the innermost entry of [S] that binds [x], with
    [k] core binders inside it and [n] outside. *)
Definition bound (S : list ent) (x : string) (k : nat) (e : ent) (n : nat) : Prop :=
  exists S1 S2, S = S1 ++ e :: S2 /\ ent_name e = Some x /\ ~ In x (names S1) /\
           k = binders S1 /\ n = binders S2.

(** A frame may bind a name once. *)
Definition fresh (x : string) (F : list ent) : Prop := ~ In x (names F).

(** The entries of a parameter list, innermost first. *)
Definition pents (ps : list (string * Cst.obj)) : list ent := rev (map (fun p => en_var (fst p)) ps).

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
| dt_mem : forall x p, den_term k n (en_mem x p) (apps (qname_term p) (vars_desc k n))
| dt_open : forall x E c, den_term k n (en_open x E (Some c)) (a_mem E c).

(** As a module expression.  A variable is a module slot; the core rejects
    it if it is a term variable. *)
Inductive den_mod (k n : nat) : ent -> modexp -> Prop :=
| dm_var : forall x, den_mod k n (en_var x) (me_var k)
| dm_mem : forall x p, den_mod k n (en_mem x p) (mapps (qname_mod p) (vars_desc k n))
| dm_open : forall x E oc, den_mod k n (en_open x E oc) (open_mod E oc).

(** ** What an Open Declares

    The items of an open, [iitem]s, are generated by the core
    ([Core.Syntactic.Imports]): [(None, W, true)] declares [W] as a private
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
| sel_var : forall S x k e n M,
    bound S x k e n -> den_term k n e M -> sel S (Cst.var x) M
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
| selm_var : forall S x k e n H,
    bound S x k e n -> den_mod k n e H -> selm S (Cst.var x) H
| selm_glob : forall S fq,
    In (en_unit fq) S -> selm S (Cst.glob fq) (me_unit fq)
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
| sdf_where : forall S cs Φ,
    sbody S gm_nil cs Φ -> sdef S (Cst.md_where cs) (md_body Φ)

(** [sbody S Φ cs Φ']: the commands [cs] of a local body extend [Φ] to [Φ'].
    Each entry is a core binder for the entries after it.  An open is a
    pre-form the core expands ([gm_open]); each of its items is a core
    binder.  The names of a body are checked fresh by the core.  A local
    body has no [import]s and no [eval]s. *)
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
      (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A M :: nil)
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
