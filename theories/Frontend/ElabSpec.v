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
      core binders, members of the open frames, import aliases and imported
      units.  A name denotes its innermost entry, so there is no priority
      between kinds of entries and no invariant on the scope.
    - The core binders lie in the list in de Bruijn order.  A member of an
      open frame is generalized over the parameters of its frame and of the
      frames enclosing it, which are exactly the binders outside its entry;
      a use applies it to those variables.
    - A frame binds each name at most once ([fresh]): a parameter, a member
      or an import alias.  A name an enclosing frame binds may be shadowed.
    - Where an object stands decides what it is: the head of a projection,
      the head of an application there, an alias body and an import target
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
    local body. *)
| en_var : string -> ent
(** A member of an open frame, named by its qualified name. *)
| en_mem : string -> qname -> ent
(** [import E as y]: [y] is the module [E]. *)
| en_as : string -> modexp -> ent
(** [import E use (n)]: [n] is the member [E.n], whatever it is. *)
| en_use : string -> modexp -> ent
(** [import X::Y]: the unit [X::Y] may be named by its path. *)
| en_unit : path -> ent.

Definition ent_name (e : ent) : option string :=
  match e with
  | en_var x | en_mem x _ | en_as x _ | en_use x _ => Some x
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

(** What an import of the unit [fq] puts in scope: nothing for this unit. *)
Definition uents (fq : path) : list ent :=
  match fq with
  | nil => nil
  | _ => en_unit fq :: nil
  end.

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

(** [E] seen [k] binders further in. *)
Abbreviation mwk E k := (modexp_wk E (wk_shiftn k)).

(** As a term.  A module alias is not one. *)
Inductive den_term (k n : nat) : ent -> exp -> Prop :=
| dt_var : forall x, den_term k n (en_var x) #k
| dt_mem : forall x p, den_term k n (en_mem x p) (apps (qname_term p) (vars_desc k n))
| dt_use : forall x E, den_term k n (en_use x E) (a_mem (mwk E k) x).

(** As a module expression.  A variable is a module slot; the core rejects
    it if it is a term variable. *)
Inductive den_mod (k n : nat) : ent -> modexp -> Prop :=
| dm_var : forall x, den_mod k n (en_var x) (me_var k)
| dm_mem : forall x p, den_mod k n (en_mem x p) (mapps (qname_mod p) (vars_desc k n))
| dm_as : forall x E, den_mod k n (en_as x E) (mwk E k)
| dm_use : forall x E, den_mod k n (en_use x E) (me_mem (mwk E k) x).

(** ** What an Import Binds

    What an import binds in the frame [F]: nothing, [y] for the module, or
    each [n] for its member, in order; each name fresh in [F]. *)
Inductive ibinds (E : modexp) : Cst.ispec -> list ent -> list ent -> Prop :=
| ib_open : forall F, ibinds E Cst.i_open F F
| ib_as : forall y F, fresh y F -> ibinds E (Cst.i_as y) F (en_as y E :: F)
| ib_use_nil : forall F, ibinds E (Cst.i_use nil) F F
| ib_use_cons : forall n ns F F',
    fresh n F -> ibinds E (Cst.i_use ns) (en_use n E :: F) F' -> ibinds E (Cst.i_use (n :: ns)) F F'.

(** The names an import [use]s, which the core checks. *)
Definition ispec_names (spec : Cst.ispec) : list string :=
  match spec with
  | Cst.i_use ns => ns
  | _ => nil
  end.

(** An import in a local body loads nothing, so the unit it names, if any,
    must be one the scope [S] may name already. *)
Definition loaded (S : list ent) (fq : path) : Prop :=
  match fq with
  | nil => True
  | _ => In (en_unit fq) S
  end.

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
    sel S (Cst.letb (Cst.d_def x oA oM) ob) (ℓ A ≔ M in B)
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
    Each entry is a core binder for the entries after it.  An import binds
    its aliases for the entries after it, as a frame of its own, and is kept
    as a check entry for the core; a local body has no [eval]s. *)
with sbody : list ent -> gmod -> list Cst.cmd -> gmod -> Prop :=
| sb_nil : forall S Φ, sbody S Φ nil Φ
| sb_def : forall S Φ m x oA oM A M cs Φ',
    sel S oA A -> sel S oM M ->
    sbody (en_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs Φ' ->
    sbody S Φ (Cst.c_def m x oA oM :: cs) Φ'
| sb_mod : forall S Φ x ps md U cs Φ',
    sunit S ps md U ->
    sbody (en_var x :: S) (gm_ext Φ x (ge_mod U)) cs Φ' ->
    sbody S Φ (Cst.c_mod x ps md :: cs) Φ'
| sb_import : forall S Φ fq ip spec E F cs Φ',
    loaded S fq ->
    itarget S fq ip E ->
    ibinds E spec nil F ->
    sbody (F ++ S) (gm_check Φ (bc_import E (ispec_names spec))) cs Φ' ->
    sbody S Φ (Cst.c_import fq ip spec :: cs) Φ'

(** [import fq.ip] names a module of this unit, by name, if [fq] is empty,
    and otherwise the module of the unit [fq] at the member path [ip]. *)
with itarget : list ent -> path -> list string -> modexp -> Prop :=
| it_local : forall S x ip E,
    selm S (fold_left Cst.proj ip (Cst.var x)) E -> itarget S nil (x :: ip) E
| it_unit : forall S fq ip,
    fq <> nil -> itarget S fq ip (qname_mod (q_abs fq ip)).

(** ** Imports *)

(** The unit an import loads first, if any. *)
Definition ifile (fq : path) : option path :=
  match fq with
  | nil => None
  | _ => Some fq
  end.

(** [simport O F c F' c']: the import [c] in the frame [F], inside the scope
    [O], changes the frame to [F'] and emits the core command [c']. *)
Inductive simport (O F : list ent) : Cst.cmd -> list ent -> ccmd -> Prop :=
| si_intro : forall fq ip spec E F',
    itarget (F ++ O) fq ip E ->
    ibinds E spec (uents fq ++ F) F' ->
    simport O F (Cst.c_import fq ip spec) F' (cc_import (ifile fq) E (ispec_names spec)).

(** ** Commands

    [scmd fp ch O F c F' c']: the command [c], in the open frame at member
    chain [ch] of the unit [fp], which binds [F] so far inside the scope
    [O], binds [F'] after it and emits the core command [c'].  [scmds] runs
    the commands of a body in order. *)
Inductive scmd (fp : path) : list string -> list ent -> list ent -> Cst.cmd -> list ent -> ccmd -> Prop :=
| sc_def : forall ch O F m x oA oM A M,
    fresh x F ->
    sel (F ++ O) oA A ->
    sel (F ++ O) oM M ->
    scmd fp ch O F (Cst.c_def m x oA oM) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A M)
(** The parameters of [module x (ps) where body end] are read in [F], its
    body in a new frame inside. *)
| sc_mod : forall ch O F x ps body tys bcs,
    fresh x F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    scmds fp (ch ++ x :: nil) (F ++ O) (pents ps) body bcs ->
    scmd fp ch O F (Cst.c_mod x ps (Cst.md_where body)) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_mod x (ptele tys) bcs)
(** [module x (ps) := E]: [E] is read under the parameters. *)
| sc_alias : forall ch O F x ps oE tys E,
    fresh x F ->
    NoDup (map fst ps) ->
    sparams (F ++ O) ps tys ->
    selm (pents ps ++ F ++ O) oE E ->
    scmd fp ch O F (Cst.c_mod x ps (Cst.md_alias oE)) (en_mem x (q_abs fp (ch ++ x :: nil)) :: F)
      (cc_alias x (ptele tys) E)
| sc_import : forall ch O F fq ip spec F' c,
    simport O F (Cst.c_import fq ip spec) F' c ->
    scmd fp ch O F (Cst.c_import fq ip spec) F' c
| sc_eval : forall ch O F oM M,
    sel (F ++ O) oM M ->
    scmd fp ch O F (Cst.c_eval oM None) F (cc_eval M None)
| sc_eval_typ : forall ch O F oM oA M A,
    sel (F ++ O) oM M ->
    sel (F ++ O) oA A ->
    scmd fp ch O F (Cst.c_eval oM (Some oA)) F (cc_eval M (Some A))

with scmds (fp : path) : list string -> list ent -> list ent -> list Cst.cmd -> list ccmd -> Prop :=
| scs_nil : forall ch O F, scmds fp ch O F nil nil
| scs_cons : forall ch O F c F' c' cs cs',
    scmd fp ch O F c F' c' ->
    scmds fp ch O F' cs cs' ->
    scmds fp ch O F (c :: cs) (c' :: cs').

(** The imports before the unit's declaration form a frame of their own. *)
Inductive simports : list ent -> list Cst.cmd -> list ent -> list ccmd -> Prop :=
| sis_nil : forall O, simports O nil O nil
| sis_cons : forall O fq ip spec O1 c cs O2 is,
    simport nil O (Cst.c_import fq ip spec) O1 c ->
    simports O1 cs O2 is ->
    simports O (Cst.c_import fq ip spec :: cs) O2 (c :: is).

(** ** Units

    A unit [import …; module fp (ps) where cs end] elaborates to the commands
    of its leading imports, its parameter context, and the commands of its
    own frame, whose member chain is [nil]. *)
Inductive elab_spec : Cst.prog -> cunit -> Prop :=
| es_intro : forall imports fp ps cs O imps tys ccs,
    simports nil imports O imps ->
    NoDup (map fst ps) ->
    sparams O ps tys ->
    scmds fp nil O (pents ps) cs ccs ->
    elab_spec (imports, (fp, ps, cs)) (imps, ptele tys, ccs).
