From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members GlobalCtx Command.
From Mctt.Frontend Require Import ElabSpec.

Import Syntax_Notations.

Open Scope string_scope.

(** * Elaboration

    A unit elaborates into core commands without reading any other unit, and
    without looking inside any module.  The elaborator computes the relation
    of [Frontend.ElabSpec], on the same scope of entries: one function per
    relation, one clause per rule. *)

(** ** Results *)

Inductive eres (A : Type) : Type :=
| eok : A -> eres A
| eerr : string -> eres A.

Arguments eok {A}.
Arguments eerr {A}.

Definition ebind {A B} (m : eres A) (f : A -> eres B) : eres B :=
  match m with
  | eok a => f a
  | eerr e => eerr e
  end.

Notation "'let*' x ':=' m 'in' f" := (ebind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Definition echeck (b : bool) (e : string) : eres unit := if b then eok tt else eerr e.

(** ** Names *)

Definition mem_b (x : string) (xs : list string) : bool := List.existsb (String.eqb x) xs.

Definition binds_b (x : string) (e : ent) : bool :=
  match ent_name e with
  | Some y => String.eqb x y
  | None => false
  end.

(** The innermost entry binding [x], with the binders inside and outside it. *)
Fixpoint lookup (x : string) (S : list ent) : option (nat * ent * nat) :=
  match S with
  | nil => None
  | e :: S' =>
      if binds_b x e then Some (0, e, binders S')
      else option_map (fun '(k, e', n) => (ent_binders e + k, e', n)) (lookup x S')
  end.

Definition den_to_term (k n : nat) (e : ent) : eres exp :=
  match e with
  | en_var _ => eok #k
  | en_mem _ p => eok (apps (a_glob p) (vars_desc k n))
  | en_use x E => eok (a_mem (mwk E k) x)
  | _ => eerr "a module is not a term"
  end.

Definition den_to_mod (k n : nat) (e : ent) : eres modexp :=
  match e with
  | en_var _ => eok (me_var k)
  | en_mem _ p => eok (mapps (me_path p) (vars_desc k n))
  | en_as _ E => eok (mwk E k)
  | en_use x E => eok (me_mem (mwk E k) x)
  | en_unit _ => eerr "not a module"
  end.

Definition check_fresh (x : string) (F : list ent) : eres unit :=
  echeck (negb (mem_b x (names F))) (x ++ " is already declared").

(** A name repeated in a parameter telescope. *)
Fixpoint first_dup (xs : list string) : option string :=
  match xs with
  | nil => None
  | x :: xs' => if mem_b x xs' then Some x else first_dup xs'
  end.

Definition check_params (ps : list (string * Cst.obj)) : eres unit :=
  match first_dup (List.map fst ps) with
  | None => eok tt
  | Some x => eerr ("duplicate parameter " ++ x)
  end.

Definition unit_in_b (fq : fpath) (S : list ent) : bool :=
  List.existsb (fun e => match e with en_unit fq' => path_beq fq fq' | _ => false end) S.

(** ** Objects *)

Definition elab_params_with (f : list ent -> Cst.obj -> eres exp) :=
  fix go (S : list ent) (ps : list (string * Cst.obj)) : eres (list (string * typ)) :=
    match ps with
    | nil => eok nil
    | (x, oA) :: ps' =>
        let* A := f S oA in
        let* tys := go (en_var x :: S) ps' in
        eok ((x, A) :: tys)
    end.

Fixpoint elab (S : list ent) (o : Cst.obj) {struct o} : eres exp :=
  match o with
  | Cst.typ n => eok (Type@n)
  | Cst.nat => eok ℕ
  | Cst.zero => eok zero
  | Cst.succ o =>
      let* M := elab S o in
      eok (succ M)
  | Cst.natrec on mx om oz sx sr os =>
      let* N := elab S on in
      let* A := elab (en_var mx :: S) om in
      let* MZ := elab S oz in
      let* MS := elab (en_var sr :: en_var sx :: S) os in
      eok (rec N return A | zero -> MZ | succ -> MS end)
  | Cst.true_ty => eok ⊤
  | Cst.true_tm => eok ⋆
  | Cst.false_ty => eok ⊥
  | Cst.exfalso om mx oA =>
      let* M := elab S om in
      let* A := elab (en_var mx :: S) oA in
      eok (efq M return A)
  | Cst.pi x oA oB =>
      let* A := elab S oA in
      let* B := elab (en_var x :: S) oB in
      eok (Π A B)
  | Cst.fn x oA oM =>
      let* A := elab S oA in
      let* M := elab (en_var x :: S) oM in
      eok (λ A M)
  | Cst.app o1 o2 =>
      let* M := elab S o1 in
      let* N := elab S o2 in
      eok (M $ N)
  | Cst.var x =>
      match lookup x S with
      | Some (k, e, n) => den_to_term k n e
      | None => eerr ("unbound name " ++ x)
      end
  | Cst.glob _ => eerr "a unit is not a term"
  | Cst.proj o x =>
      let* H := elab_mod S o in
      eok (a_mem H x)
  | Cst.letb (Cst.d_def x oA oM) ob =>
      let* A := elab S oA in
      let* M := elab S oM in
      let* B := elab (en_var x :: S) ob in
      eok (ℓ A ≔ M in B)
  | Cst.letb (Cst.d_mod x ps md) ob =>
      let* _ := check_params ps in
      let* tys := elab_params_with elab S ps in
      let* D := elab_mdef (pents ps ++ S) md in
      let* B := elab (en_var x :: S) ob in
      eok (ℓₘ (gu_mk (ptele tys) D) in B)
  end

with elab_mod (S : list ent) (o : Cst.obj) {struct o} : eres modexp :=
  match o with
  | Cst.var x =>
      match lookup x S with
      | Some (k, e, n) => den_to_mod k n e
      | None => eerr ("unbound name " ++ x)
      end
  | Cst.glob fq =>
      let* _ := echeck (unit_in_b fq S) "the unit is not imported" in
      eok (me_path (p_abs fq nil))
  | Cst.proj o y =>
      let* H := elab_mod S o in
      eok (me_mem H y)
  | Cst.app o1 o2 =>
      let* H := elab_mod S o1 in
      let* N := elab S o2 in
      eok (me_app H N)
  | _ => eerr "not a module"
  end

with elab_mdef (S : list ent) (md : Cst.mdef) {struct md} : eres moddef :=
  match md with
  | Cst.md_alias oE =>
      let* E := elab_mod S oE in
      eok (md_alias E)
  | Cst.md_where cs =>
      let* Φ :=
        (fix go (S : list ent) (Φ : gmod) (cs : list Cst.cmd) {struct cs} : eres gmod :=
           match cs with
           | nil => eok Φ
           | Cst.c_def m x oA oM :: cs' =>
               let* A := elab S oA in
               let* M := elab S oM in
               go (en_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs'
           | Cst.c_mod x ps md' :: cs' =>
               let* _ := check_params ps in
               let* tys := elab_params_with elab S ps in
               let* D := elab_mdef (pents ps ++ S) md' in
               go (en_var x :: S) (gm_ext Φ x (ge_mod (gu_mk (ptele tys) D))) cs'
           | Cst.c_import _ _ _ :: _ => eerr "a local module has no imports"
           | Cst.c_eval _ _ :: _ => eerr "a local module has no evals"
           end) S gm_nil cs in
      eok (md_body Φ)
  end.

Definition elab_params := elab_params_with elab.

(** ** Imports *)

Definition elab_itarget (S : list ent) (fq ip : list string) : eres modexp :=
  match fq, ip with
  | nil, x :: ip' => elab_mod S (fold_left Cst.proj ip' (Cst.var x))
  | nil, nil => eerr "nothing to import"
  | _, _ => eok (me_path (p_abs fq ip))
  end.

Fixpoint use_binds (E : modexp) (ns : list string) (F : list ent) : eres (list ent) :=
  match ns with
  | nil => eok F
  | n :: ns' =>
      let* _ := check_fresh n F in
      use_binds E ns' (en_use n E :: F)
  end.

Definition elab_ibinds (E : modexp) (spec : Cst.ispec) (F : list ent) : eres (list ent) :=
  match spec with
  | Cst.i_open => eok F
  | Cst.i_as y =>
      let* _ := check_fresh y F in
      eok (en_as y E :: F)
  | Cst.i_use ns => use_binds E ns F
  end.

(** An import in the frame [F] inside [O]: the frame after it, and its core
    command. *)
Definition elab_import (O F : list ent) (fq ip : list string) (spec : Cst.ispec)
  : eres (list ent * ccmd)%type :=
  let* E := elab_itarget (F ++ O) fq ip in
  let* F' := elab_ibinds E spec (uents fq ++ F) in
  eok (F', cc_import (ifile fq) E (ispec_names spec)).

(** ** Commands

    A module body is elaborated where it stands: the body of [module x …
    where body end] is elaborated by [elab_cmd] itself, so no stack of frames
    is needed.  A command takes the frame's entries [F] to [F'] and emits one
    core command. *)
Definition elab_cmds_with (f : list string -> list ent -> list ent -> Cst.cmd -> eres (list ent * ccmd)%type)
  (ch : list string) (O : list ent) :=
  fix go (F : list ent) (cs : list Cst.cmd) : eres (list ccmd) :=
    match cs with
    | nil => eok nil
    | c :: cs' =>
        let* r := f ch O F c in
        let* ccs := go (fst r) cs' in
        eok (snd r :: ccs)
    end.

Fixpoint elab_cmd (fp : fpath) (ch : list string) (O F : list ent) (c : Cst.cmd) {struct c}
  : eres (list ent * ccmd)%type :=
  match c with
  | Cst.c_def m x oA oM =>
      let* _ := check_fresh x F in
      let* A := elab (F ++ O) oA in
      let* M := elab (F ++ O) oM in
      eok (en_mem x (p_abs fp (ch ++ x :: nil)) :: F, cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A M)
  | Cst.c_mod x ps (Cst.md_where body) =>
      let* _ := check_fresh x F in
      let* _ := check_params ps in
      let* tys := elab_params (F ++ O) ps in
      let* bcs := elab_cmds_with (elab_cmd fp) (ch ++ x :: nil) (F ++ O) (pents ps) body in
      eok (en_mem x (p_abs fp (ch ++ x :: nil)) :: F, cc_mod x (ptele tys) bcs)
  | Cst.c_mod x ps (Cst.md_alias oE) =>
      let* _ := check_fresh x F in
      let* _ := check_params ps in
      let* tys := elab_params (F ++ O) ps in
      let* E := elab_mod (pents ps ++ F ++ O) oE in
      eok (en_mem x (p_abs fp (ch ++ x :: nil)) :: F, cc_alias x (ptele tys) E)
  | Cst.c_import fq ip spec => elab_import O F fq ip spec
  | Cst.c_eval oM None =>
      let* M := elab (F ++ O) oM in
      eok (F, cc_eval M None)
  | Cst.c_eval oM (Some oA) =>
      let* M := elab (F ++ O) oM in
      let* A := elab (F ++ O) oA in
      eok (F, cc_eval M (Some A))
  end.

Definition elab_cmds (fp : fpath) := elab_cmds_with (elab_cmd fp).

Fixpoint elab_imports (O : list ent) (cs : list Cst.cmd) : eres (list ent * list ccmd)%type :=
  match cs with
  | nil => eok (O, nil)
  | Cst.c_import fq ip spec :: cs' =>
      let* r := elab_import nil O fq ip spec in
      let* r' := elab_imports (fst r) cs' in
      eok (fst r', snd r :: snd r')
  | _ :: _ => eerr "outside of any module"
  end.

(** ** Units *)

Definition elaborate_core (prg : Cst.prog) : eres cunit :=
  let '(imports, (fp, ps, cs)) := prg in
  let* r := elab_imports nil imports in
  let* _ := check_params ps in
  let* tys := elab_params (fst r) ps in
  let* ccs := elab_cmds fp nil (fst r) (pents ps) cs in
  eok (snd r, ptele tys, ccs).

Definition to_core (prg : Cst.prog) : option cunit :=
  match elaborate_core prg with
  | eok u => Some u
  | eerr _ => None
  end.
