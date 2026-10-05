From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members Command.
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

Definition eopt {A} (o : option A) (e : string) : eres A :=
  match o with
  | Some a => eok a
  | None => eerr e
  end.

(** ** Names *)

Definition mem_b (x : string) (xs : list string) : bool := List.existsb (String.eqb x) xs.

Definition binds_b (x : string) (e : ent) : bool :=
  match ent_name e with
  | Some y => String.eqb x y
  | None => false
  end.

(** The innermost entry binding [x], with the binders inside it and the
    entries outside it. *)
Fixpoint lookup (x : string) (S : list ent) : option (nat * ent * list ent) :=
  match S with
  | nil => None
  | e :: S' =>
      if binds_b x e then Some (0, e, S')
      else option_map (fun '(k, e', S2) => (ent_binders e + k, e', S2)) (lookup x S')
  end.

Definition den_to_term (k : nat) (S2 : list ent) (e : ent) : eres exp :=
  match e with
  | en_var _ => eok #k
  | en_mem _ c =>
      let* j := eopt (self_index S2) "internal error: a member outside any body" in
      eok (a_mem (me_var (k + j)) c)
  | _ => eerr "internal error: an entry without a name"
  end.

Definition den_to_mod (k : nat) (S2 : list ent) (e : ent) : eres modexp :=
  match e with
  | en_var _ => eok (me_var k)
  | en_mem _ c =>
      let* j := eopt (self_index S2) "internal error: a member outside any body" in
      eok (me_mem (me_var (k + j)) c)
  | _ => eerr "internal error: an entry without a name"
  end.

Definition check_fresh (x : string) (X : list string) (F : list ent) : eres unit :=
  echeck (negb (mem_b x (X ++ names F))) (x ++ " is already declared").

Fixpoint check_fresh_all (xs : list string) (X : list string) (F : list ent) : eres unit :=
  match xs with
  | nil => eok tt
  | x :: xs' =>
      let* _ := check_fresh x X F in
      check_fresh_all xs' X F
  end.

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

Definition unit_in_b (fq : path) (S : list ent) : bool :=
  List.existsb (fun e => match e with en_unit fq' => path_beq fq fq' | _ => false end) S.

Definition check_items (its : list Cst.iitem) : eres (option string * list iitem)%type :=
  eopt (open_items its) "internal error: an open both of a module and of its members".

(** ** Open Targets

    [elab_mod] on [itarget fq ip args], computed without building the
    object, so that a local body may use it: the head of the target, then
    its arguments by [f]. *)

Definition elab_ihead (S : list ent) (fq ip : list string) : eres modexp :=
  match fq, ip with
  | nil, x :: ip' =>
      let* H := match lookup x S with
                | Some (k, e, S2) => den_to_mod k S2 e
                | None => eerr ("unbound name " ++ x)
                end in
      eok (fold_left me_mem ip' H)
  | nil, nil => eerr "nothing to open"
  | _, _ =>
      let* _ := echeck (unit_in_b fq S) "the unit is not imported" in
      eok (fold_left me_mem ip (me_unit fq))
  end.

Definition elab_args_with (f : list ent -> Cst.obj -> eres exp) (S : list ent) :=
  fix go (os : list Cst.obj) : eres (list exp) :=
    match os with
    | nil => eok nil
    | o :: os' =>
        let* N := f S o in
        let* Ns := go os' in
        eok (N :: Ns)
    end.

Definition elab_target_with (f : list ent -> Cst.obj -> eres exp) (S : list ent) (fq ip : list string)
  (args : list Cst.obj) : eres modexp :=
  let* H := elab_ihead S fq ip in
  let* Ns := elab_args_with f S args in
  eok (mapps H Ns).

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
      | Some (k, e, S2) => den_to_term k S2 e
      | None => eerr ("unbound name " ++ x)
      end
  | Cst.glob _ => eerr "a unit is not a term"
  | Cst.proj o x =>
      let* H := elab_mod S o in
      eok (a_mem H x)
  | Cst.letb (Cst.d_def x (Some oA) oM) ob =>
      let* A := elab S oA in
      let* M := elab S oM in
      let* B := elab (en_var x :: S) ob in
      eok (ℓ A ≔ M in B)
  | Cst.letb (Cst.d_def x None oM) ob =>
      let* M := elab S oM in
      let* B := elab (en_var x :: S) ob in
      eok (ℓ ≔ M in B)
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
      | Some (k, e, S2) => den_to_mod k S2 e
      | None => eerr ("unbound name " ++ x)
      end
  | Cst.glob fq =>
      let* _ := echeck (unit_in_b fq S) "the unit is not imported" in
      eok (me_unit fq)
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
               let* _ := echeck (negb (Cst.md_abstract m)) "abstract definitions are not allowed in a local module" in
               let* A := elab S oA in
               let* M := elab S oM in
               go (en_mem x x :: S) (gm_ext Φ x (ge_def (Cst.md_private m) A (Some M))) cs'
           | Cst.c_mod pv x ps md' :: cs' =>
               let* _ := check_params ps in
               let* tys := elab_params_with elab S ps in
               let* D := elab_mdef (pents ps ++ S) md' in
               go (en_mem x x :: S) (gm_ext Φ x (ge_mod pv (gu_mk (ptele tys) D))) cs'
           | Cst.c_open fq ip args its :: cs' =>
               let* E := elab_target_with elab S fq ip args in
               let* r := check_items its in
               go (item_mems its ++ S)%list (gm_open Φ E (fst r) (snd r)) cs'
           | Cst.c_axiom _ _ :: _ => eerr "axioms are not allowed in a local module"
           | Cst.c_import _ :: _ => eerr "import is not allowed in a local module; use open"
           | Cst.c_error e :: _ => eerr e
           | Cst.c_eval _ _ :: _ => eerr "eval is not allowed in a local module"
           end) (en_self :: S) gm_nil cs in
      eok (md_body Φ)
  end.

Definition elab_params := elab_params_with elab.

(** ** Commands

    A module body is elaborated where it stands: the body of [module x …
    where body end] is elaborated by [elab_cmd] itself, under its own self
    slot, so no stack of frames is needed.  A command takes the frame's
    entries [F] to [F'] and emits its core commands. *)
Definition elab_cmds_with (f : list string -> list ent -> list ent -> Cst.cmd -> eres (list ent * list ccmd)%type)
  (X : list string) (O : list ent) :=
  fix go (F : list ent) (cs : list Cst.cmd) : eres (list ccmd) :=
    match cs with
    | nil => eok nil
    | c :: cs' =>
        let* r := f X O F c in
        let* ccs := go (fst r) cs' in
        eok (snd r ++ ccs)%list
    end.

Fixpoint elab_cmd (X : list string) (O F : list ent) (c : Cst.cmd) {struct c} : eres (list ent * list ccmd)%type :=
  match c with
  | Cst.c_def m x oA oM =>
      let* _ := check_fresh x X F in
      let* A := elab (F ++ O) oA in
      let* M := elab (F ++ O) oM in
      eok (en_mem x x :: F, cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M) :: nil)
  | Cst.c_axiom x oA =>
      let* _ := check_fresh x X F in
      let* A := elab (F ++ O) oA in
      eok (en_mem x x :: F, cc_def x false false A None :: nil)
  | Cst.c_mod pv x ps (Cst.md_where body) =>
      let* _ := check_fresh x X F in
      let* _ := check_params ps in
      let* tys := elab_params (F ++ O) ps in
      let* bcs := elab_cmds_with elab_cmd (map fst ps) (en_self :: pents ps ++ F ++ O) nil body in
      eok (en_mem x x :: F, cc_mod x pv (ptele tys) bcs :: nil)
  | Cst.c_mod pv x ps (Cst.md_alias oE) =>
      let* _ := check_fresh x X F in
      let* _ := check_params ps in
      let* tys := elab_params (F ++ O) ps in
      let* E := elab_mod (pents ps ++ F ++ O) oE in
      eok (en_mem x x :: F, cc_alias x pv (ptele tys) E :: nil)
  | Cst.c_import fq => eok (en_unit fq :: F, cc_load fq :: nil)
  | Cst.c_open fq ip args its =>
      let* E := elab_target_with elab (F ++ O) fq ip args in
      let* r := check_items its in
      let* _ := check_fresh_all (map citem_name its) X F in
      eok (item_mems its ++ F, cc_open E (fst r) (snd r) :: nil)%list
  | Cst.c_error e => eerr e
  | Cst.c_eval oM None =>
      let* M := elab (F ++ O) oM in
      eok (F, cc_eval M None :: nil)
  | Cst.c_eval oM (Some oA) =>
      let* M := elab (F ++ O) oM in
      let* A := elab (F ++ O) oA in
      eok (F, cc_eval M (Some A) :: nil)
  end.

Definition elab_cmds := elab_cmds_with elab_cmd.

(** The leading imports and opens, before the unit's header: the scope of
    its parameter types and its body, and their commands. *)
Fixpoint elab_lead (L : list ent) (cs : list Cst.cmd) : eres (list ent * list ccmd)%type :=
  match cs with
  | nil => eok (L, nil)
  | Cst.c_import fq :: cs' =>
      let* r := elab_lead (en_unit fq :: L) cs' in
      eok (fst r, cc_load fq :: snd r)
  | Cst.c_open fq ip args its :: cs' =>
      let* E := elab_target_with elab L fq ip args in
      let* oi := check_items its in
      let* _ := check_fresh_all (map citem_name its) nil L in
      let* r := elab_lead (lead_ents its ++ L)%list cs' in
      eok (fst r, cc_open E (fst oi) (snd oi) :: snd r)
  | Cst.c_error e :: _ => eerr e
  | _ :: _ => eerr "outside of any module"
  end.

(** ** Units *)

Definition elaborate_core (prg : Cst.prog) : eres cunit :=
  let '(leads, (fp, ps, cs)) := prg in
  let* r := elab_lead nil leads in
  let '(L, lds) := r in
  let* _ := check_params ps in
  let* _ := check_fresh_all (map fst ps) nil L in
  let* tys := elab_params L ps in
  let* ccs := elab_cmds (map fst ps ++ names L) (en_self :: pents ps ++ L) nil cs in
  eok (lds, ptele tys, ccs).

Definition to_core (prg : Cst.prog) : option cunit :=
  match elaborate_core prg with
  | eok u => Some u
  | eerr _ => None
  end.
