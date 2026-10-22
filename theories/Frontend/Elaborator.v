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

(** The error for a unit, named by its path as the driver prints paths,
    that the program does not import. *)
Definition unit_not_imported_msg (fq : list string) : string :=
  "the unit " ++ String.concat "›" fq ++ " is not imported".

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
  | en_var _ | en_tvar _ => eok #k
  | en_mem _ p => eok (apps (qname_term p) (vars_desc k n))
  | en_unit _ => eerr "a unit is not a term"
  | en_open _ E (Some c) => eok (a_mem E c)
  | en_open _ _ None => eerr "a module is not a term"
  end.

Definition den_to_mod (k n : nat) (e : ent) : eres modexp :=
  match e with
  | en_var _ => eok (me_var k)
  | en_tvar x => eerr (x ++ " is a variable, not a module")
  | en_mem _ p => eok (mapps (qname_mod p) (vars_desc k n))
  | en_unit _ => eerr "not a module"
  | en_open _ E oc => eok (open_mod E oc)
  end.

Definition check_fresh (x : string) (F : list ent) : eres unit :=
  echeck (negb (mem_b x (names F))) (x ++ " is already declared").

Fixpoint check_fresh_all (xs : list string) (F : list ent) : eres unit :=
  match xs with
  | nil => eok tt
  | x :: xs' =>
      let* _ := check_fresh x F in
      check_fresh_all xs' F
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

(** A name no binding in scope has, as a module: the imported unit of
    that one-segment path. *)
Definition unit_mod (x : string) (S : list ent) : eres modexp :=
  if unit_in_b (x :: nil) S then eok (me_unit (x :: nil)) else eerr ("unbound name " ++ x).

(** ** Open Targets

    [elab_mod] on [itarget fq ip args], computed without building the
    object, so that a local body may use it: the head of the target, then
    its arguments by [f]. *)

Definition elab_ihead (S : list ent) (fq ip : list string) : eres modexp :=
  match fq, ip with
  | nil, x :: ip' =>
      let* H := match lookup x S with
                | Some (k, e, n) => den_to_mod k n e
                | None => unit_mod x S
                end in
      eok (fold_left me_mem ip' H)
  | nil, nil => eerr "nothing to open"
  | _, _ =>
      let* _ := echeck (unit_in_b fq S) (unit_not_imported_msg fq) in
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
        let* tys := go (en_tvar x :: S) ps' in
        eok ((x, A) :: tys)
    end.

Definition elab_brs_with (f : list ent -> Cst.obj -> eres exp) (S : list ent) :=
  fix go (bs : list (string * list string * Cst.obj)) : eres (list (string * nat * exp)) :=
    match bs with
    | nil => eok nil
    | (c, ys, oB) :: bs' =>
        let* B := f (vents ys ++ S)%list oB in
        let* Bs := go bs' in
        eok ((c, List.length ys, B) :: Bs)
    end.

(** The rejection of a type on a binder before the last. *)
Definition blk_ann_msg : string := "only the last binder of a block (the scrutinee) may carry a type".

(** The rejection of an eliminator with no block, or more than one,
    marked [at]. *)
Definition elim_at_msg : string := "exactly one block of an eliminator is marked at, the scrutinee's".

(** The type written on the last binder of a block ([sbinders]), under the
    binders [pre] before it; a type on any other binder is rejected. *)
Definition elab_binders_with (f : list ent -> Cst.obj -> eres exp) (S : list ent) :=
  fix go (pre : list string) (xs : list (string * option Cst.obj)) : eres (option exp) :=
    match xs with
    | nil => eok None
    | (_, None) :: nil => eok None
    | (_, Some o) :: nil => let* Z := f (vents pre ++ S)%list o in eok (Some Z)
    | (_, Some _) :: _ :: _ => eerr blk_ann_msg
    | (x, None) :: ((_ :: _) as xs') => go (pre ++ x :: nil)%list xs'
    end.

Definition elab_blocks_with (f : list ent -> Cst.obj -> eres exp) (S : list ent) :=
  fix go (bks : list (bool * list (string * option Cst.obj) * Cst.obj * list (string * list string * Cst.obj)))
      : eres (list eblock) :=
    match bks with
    | nil => eok nil
    | (k, xs, oA, bs) :: bks' =>
        let* oZ := elab_binders_with f S nil xs in
        let* A := f (vents (List.map fst xs) ++ S)%list oA in
        let* Bs := elab_brs_with f S bs in
        let* Bks := go bks' in
        eok (eb_mk (List.length xs) oZ A Bs :: Bks)
    end.

Fixpoint elab (S : list ent) (o : Cst.obj) {struct o} : eres exp :=
  match o with
  | Cst.typ n => eok (Typeω@n)
  | Cst.suniv o =>
      let* M := elab S o in
      eok (Type⟨M⟩)
  | Cst.level n => eok (Level@n)
  | Cst.llit o => eok (𝕃ᵒ o)
  | Cst.succl o =>
      let* M := elab S o in
      eok (succl M)
  | Cst.maxl o1 o2 =>
      let* M := elab S o1 in
      let* N := elab S o2 in
      eok (maxl M N)
  | Cst.nat => eok ℕ
  | Cst.num n => eok (a_nlit n)
  | Cst.true_ty => eok ⊤
  | Cst.true_tm => eok ⋆
  | Cst.false_ty => eok ⊥
  | Cst.exfalso om mx oA =>
      let* M := elab S om in
      let* A := elab (en_tvar mx :: S) oA in
      eok (efq M return A)
  | Cst.pi x oA oB =>
      let* A := elab S oA in
      let* B := elab (en_tvar x :: S) oB in
      eok (Π A B)
  | Cst.fn x oA oM =>
      let* A := elab S oA in
      let* M := elab (en_tvar x :: S) oM in
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
  | Cst.letb (Cst.d_def x (Some oA) oM) ob =>
      let* A := elab S oA in
      let* M := elab S oM in
      let* B := elab (en_tvar x :: S) ob in
      eok (ℓ A ≔ M in B)
  | Cst.letb (Cst.d_def x None oM) ob =>
      let* M := elab S oM in
      let* B := elab (en_tvar x :: S) ob in
      eok (ℓ ≔ M in B)
  | Cst.letb (Cst.d_mod x ps md) ob =>
      let* _ := check_params ps in
      let* tys := elab_params_with elab S ps in
      let* D := elab_mdef (pents ps ++ S) md in
      let* B := elab (en_var x :: S) ob in
      eok (ℓₘ (gu_mk (ptele tys) D) in B)
  | Cst.elim om bks =>
      let* M := elab S om in
      let* Bks := elab_blocks_with elab S bks in
      match elim_at (List.map (fun bk => fst (fst (fst bk))) bks) with
      | Some m => eok (a_elim None nil m Bks M)
      | None => eerr elim_at_msg
      end
  end

with elab_mod (S : list ent) (o : Cst.obj) {struct o} : eres modexp :=
  match o with
  | Cst.var x =>
      match lookup x S with
      | Some (k, e, n) => den_to_mod k n e
      | None => unit_mod x S
      end
  | Cst.glob fq =>
      let* _ := echeck (unit_in_b fq S) (unit_not_imported_msg fq) in
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
               let* A := elab S oA in
               let* M := elab S oM in
               go (en_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs'
           | Cst.c_mod pv x ps md' :: cs' =>
               let* _ := check_params ps in
               let* tys := elab_params_with elab S ps in
               let* D := elab_mdef (pents ps ++ S) md' in
               go (en_var x :: S) (gm_ext Φ x (ge_mod pv (gu_mk (ptele tys) D))) cs'
           | Cst.c_open fq ip args its :: cs' =>
               let* E := elab_target_with elab S fq ip args in
               go (item_ents its ++ S)%list (gm_open Φ E its) cs'
           | Cst.c_axiom _ _ :: _ => eerr "axioms are not allowed in a local module"
           | Cst.c_import _ :: _ => eerr "import is not allowed in a local module; use open"
           | Cst.c_error e :: _ => eerr e
           | Cst.c_eval _ _ :: _ => eerr "eval is not allowed in a local module"
           | Cst.c_ind _ _ _ _ :: _ => eerr "an inductive type is not allowed in a local module"
           | Cst.c_mdef _ _ _ :: _ => eerr "a mutual definition is not allowed in a local module"
           | Cst.c_builtin _ _ :: _ => eerr "builtin is not allowed in a local module"
           | Cst.c_ind_alias _ _ _ _ :: _ => eerr "an inductive alias is not allowed in a local module"
           end) S gm_nil cs in
      eok (md_body sm_open Φ)
  end.

Definition elab_params := elab_params_with elab.

(** The arguments of a constructor, each binding its name for the ones
    after it; the declared type is a variable in scope. *)
Fixpoint elab_rargs (S : list ent) (args : list (string * Cst.obj)) : eres (list (string * exp)) :=
  match args with
  | nil => eok nil
  | (y, oA) :: args' =>
      let* A := elab S oA in
      let* args'' := elab_rargs (en_tvar y :: S) args' in
      eok ((y, A) :: args'')
  end.

Fixpoint elab_rcons (S : list ent) (cs : list (string * list (string * Cst.obj)))
  : eres (list (string * list (string * exp))) :=
  match cs with
  | nil => eok nil
  | (c, args) :: cs' =>
      let* args' := elab_rargs S args in
      let* cs'' := elab_rcons S cs' in
      eok ((c, args') :: cs'')
  end.

(** The members of a group, under its uniform parameters [ups], the
    members' names [xs] in scope in the arguments ([smembers]). *)
Fixpoint elab_members (S : list ent) (ups : list (string * Cst.obj)) (xs : list string)
    (ms : list (string * Cst.obj * list (string * list (string * Cst.obj)))) : eres (list raw_member) :=
  match ms with
  | nil => eok nil
  | (x, oT, cs) :: ms' =>
      let '(nps, oS) := split_pis oT in
      let* _ := check_params (ups ++ nps)%list in
      let* ntys := elab_params (pents ups ++ S)%list nps in
      let* A := elab (pents ups ++ S)%list oS in
      let* cs' := elab_rcons (pents (ups ++ nps) ++ vents xs ++ S)%list cs in
      let* rms := elab_members S ups xs ms' in
      eok (mk_rmem x (ptele ntys) A cs' :: rms)
  end.

(** The functions of a mutual definition ([sfuns]): each its parameters,
    the last its scrutinee. *)
Fixpoint elab_funs (S : list ent)
    (fs : list (string * list (string * Cst.obj) * Cst.obj * list (string * list string * Cst.obj))) :
    eres (list raw_fun) :=
  match fs with
  | nil => eok nil
  | (f, ps, oA, bs) :: fs' =>
      match List.rev ps with
      | nil => eerr ("the function " ++ f ++ " of a mutual definition has no scrutinee")
      | (z, oZ) :: rys =>
          let ys := List.rev rys in
          let* _ := check_params ps in
          let* ytys := elab_params S ys in
          let* Z := elab (pents ys ++ S)%list oZ in
          let* A := elab (en_tvar z :: pents ys ++ S)%list oA in
          let* Bs := elab_brs_with elab S bs in
          let* rfs := elab_funs S fs' in
          eok (mk_rfun f (ptele ytys) Z A Bs :: rfs)
      end
  end.

(** Names declared together twice. *)
Definition check_distinct (what : string) (xs : list string) : eres unit :=
  match first_dup xs with
  | None => eok tt
  | Some x => eerr (x ++ " is declared twice in " ++ what)
  end.

(** ** Commands

    A module body is elaborated where it stands: the body of [module x …
    where body end] is elaborated by [elab_cmd] itself, so no stack of frames
    is needed.  A command takes the frame's entries [F] to [F'] and emits its
    core commands. *)
Definition elab_cmds_with (f : list string -> list ent -> list ent -> Cst.cmd -> eres (list ent * list ccmd)%type)
  (ch : list string) (O : list ent) :=
  fix go (F : list ent) (cs : list Cst.cmd) : eres (list ccmd) :=
    match cs with
    | nil => eok nil
    | c :: cs' =>
        let* r := f ch O F c in
        let* ccs := go (fst r) cs' in
        eok (snd r ++ ccs)%list
    end.

Fixpoint elab_cmd (fp : path) (ch : list string) (O F : list ent) (c : Cst.cmd) {struct c}
  : eres (list ent * list ccmd)%type :=
  match c with
  | Cst.c_def m x oA oM =>
      let* _ := check_fresh x F in
      let* A := elab (F ++ O) oA in
      let* M := elab (F ++ O) oM in
      eok (en_mem x (q_abs fp (ch ++ x :: nil)) :: F, cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M) :: nil)
  (** An axiom is opaque: it has no body to unfold. *)
  | Cst.c_axiom x oA =>
      let* _ := check_fresh x F in
      let* A := elab (F ++ O) oA in
      eok (en_mem x (q_abs fp (ch ++ x :: nil)) :: F, cc_def x false false A None :: nil)
  | Cst.c_mod pv x ps (Cst.md_where body) =>
      let* _ := check_fresh x F in
      let* _ := check_params ps in
      let* tys := elab_params (F ++ O) ps in
      let* bcs := elab_cmds_with (elab_cmd fp) (ch ++ x :: nil) (F ++ O) (pents ps) body in
      eok (en_mem x (q_abs fp (ch ++ x :: nil)) :: F, cc_mod x pv (ptele tys) bcs :: nil)
  | Cst.c_mod pv x ps (Cst.md_alias oE) =>
      let* _ := check_fresh x F in
      let* _ := check_params ps in
      let* tys := elab_params (F ++ O) ps in
      let* E := elab_mod (pents ps ++ F ++ O) oE in
      eok (en_mem x (q_abs fp (ch ++ x :: nil)) :: F, cc_alias x pv (ptele tys) E :: nil)
  | Cst.c_import fq => eok (en_unit fq :: F, cc_load fq :: nil)
  | Cst.c_open fq ip args its =>
      let* E := elab_target_with elab (F ++ O) fq ip args in
      let* _ := check_fresh_all (map iitem_name its) F in
      eok (item_mems fp ch its ++ F, cc_open E its :: nil)%list
  | Cst.c_error e => eerr e
  | Cst.c_eval oM None =>
      let* M := elab (F ++ O) oM in
      eok (F, cc_eval M None :: nil)
  | Cst.c_eval oM (Some oA) =>
      let* M := elab (F ++ O) oM in
      let* A := elab (F ++ O) oA in
      eok (F, cc_eval M (Some A) :: nil)
  | Cst.c_ind pv wr ups ms =>
      let* _ := check_distinct "a group" (member_names ms) in
      let* _ := check_fresh_all (member_names ms) F in
      let* tys := elab_params (F ++ O) ups in
      let* rms := elab_members (F ++ O) ups (member_names ms) ms in
      eok (filed_mems fp ch (member_names ms) ++ F, cc_ind pv (mk_raw (ptele tys) rms wr) :: nil)%list
  | Cst.c_mdef m ps fs =>
      let* _ := check_params ps in
      let* _ := check_distinct "a mutual definition" (fun_names fs) in
      let* _ := check_fresh_all (fun_names fs) F in
      let* tys := elab_params (F ++ O) ps in
      let* rfs := elab_funs (pents ps ++ F ++ O) fs in
      eok (filed_mems fp ch (fun_names fs) ++ F,
           cc_mdef (negb (Cst.md_abstract m)) (Cst.md_private m) (ptele tys) rfs :: nil)%list
  (** The type is a module, as written; the command declares nothing. *)
  | Cst.c_builtin k oX =>
      let* H := elab_mod (F ++ O) oX in
      eok (F, cc_builtin k H :: nil)
  (** The target is a module, read under the parameters, as an alias's
      is. *)
  | Cst.c_ind_alias pv x ps oE =>
      let* _ := check_fresh x F in
      let* _ := check_params ps in
      let* tys := elab_params (F ++ O) ps in
      let* E := elab_mod (pents ps ++ F ++ O) oE in
      eok (en_mem x (q_abs fp (ch ++ x :: nil)) :: F, cc_ind_alias x pv (ptele tys) E :: nil)
  end.

Definition elab_cmds (fp : path) := elab_cmds_with (elab_cmd fp).

(** The leading imports and opens, before the unit's header: the scope of
    its parameter types, and their loads. *)
Fixpoint elab_lead (L : list ent) (cs : list Cst.cmd) : eres (list ent * list ccmd)%type :=
  match cs with
  | nil => eok (L, nil)
  | Cst.c_import fq :: cs' =>
      let* r := elab_lead (en_unit fq :: L) cs' in
      eok (fst r, cc_load fq :: snd r)
  | Cst.c_open fq ip args its :: cs' =>
      let* E := elab_target_with elab L fq ip args in
      elab_lead (open_ents E its ++ L)%list cs'
  | Cst.c_error e :: _ => eerr e
  | _ :: _ => eerr "outside of any module"
  end.

(** ** Units

    The leading imports and opens are read before the unit's header, for
    its parameter types, then as the first commands of its frame. *)

Definition elaborate_core (prg : Cst.prog) : eres cunit :=
  let '(leads, (fp, ps, cs)) := prg in
  let* r := elab_lead nil leads in
  let '(L, lds) := r in
  let* _ := check_params ps in
  let* tys := elab_params L ps in
  let* ccs := elab_cmds fp nil L (pents ps) (leads ++ cs) in
  eok (lds, ptele tys, ccs).

Definition to_core (prg : Cst.prog) : option cunit :=
  match elaborate_core prg with
  | eok u => Some u
  | eerr _ => None
  end.
