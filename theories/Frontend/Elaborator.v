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

Inductive elab_result (A : Type) : Type :=
| elab_success : A -> elab_result A
| elab_failure : string -> elab_result A.

Arguments elab_success {A}.
Arguments elab_failure {A}.

Definition elab_bind {A B} (m : elab_result A) (f : A -> elab_result B) : elab_result B :=
  match m with
  | elab_success a => f a
  | elab_failure e => elab_failure e
  end.

Notation "'let*' x ':=' m 'in' f" := (elab_bind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Definition elab_check (b : bool) (e : string) : elab_result unit := if b then elab_success tt else elab_failure e.

(** The error for a unit, named by its path as the driver prints paths,
    that the program does not import. *)
Definition unit_not_imported_msg (fq : list string) : string :=
  "the unit " ++ String.concat "›" fq ++ " is not imported".

(** ** Names *)

Definition mem_b (x : string) (xs : list string) : bool := List.existsb (String.eqb x) xs.

Definition binds_b (x : string) (e : scope_entry) : bool :=
  match scope_entry_name e with
  | Some y => String.eqb x y
  | None => false
  end.

(** The innermost entry binding [x], with the binders inside it.  The walk
    stops there: nothing outside the entry is read. *)
Fixpoint lookup (x : string) (S : list scope_entry) : option (nat * scope_entry) :=
  match S with
  | nil => None
  | e :: S' =>
      if binds_b x e then Some (0, e)
      else option_map (fun '(k, e') => (scope_entry_binders e + k, e')) (lookup x S')
  end.

(** What an entry, under [k] binders, denotes as a term ([entry_denotes_term]) *)
Definition entry_to_term (k : nat) (e : scope_entry) : elab_result exp :=
  match e with
  | scope_entry_var _ | scope_entry_tvar _ => elab_success #k
  | scope_entry_mem _ p m => elab_success (apps (qname_term p) (vars_desc k m))
  | scope_entry_unit _ => elab_failure "a unit is not a term"
  | scope_entry_open _ E (Some c) => elab_success (a_mem E c)
  | scope_entry_open _ _ None => elab_failure "a module is not a term"
  end.

(** What an entry, under [k] binders, denotes as a module ([entry_denotes_mod]) *)
Definition entry_to_mod (k : nat) (e : scope_entry) : elab_result modexp :=
  match e with
  | scope_entry_var _ => elab_success (me_var k)
  | scope_entry_tvar _ => elab_success (me_var k)
  | scope_entry_mem _ p m => elab_success (mapps (qname_mod p) (vars_desc k m))
  | scope_entry_unit _ => elab_failure "not a module"
  | scope_entry_open _ E oc => elab_success (open_mod E oc)
  end.

(** A declared name is not one of the frame's parameters [P] ([fresh]). *)
Definition check_fresh (x : string) (P : list string) : elab_result unit :=
  elab_check (negb (mem_b x P)) (x ++ " is already declared").

(** Alike for each of several declared names *)
Fixpoint check_fresh_all (xs : list string) (P : list string) : elab_result unit :=
  match xs with
  | nil => elab_success tt
  | x :: xs' =>
      let* _ := check_fresh x P in
      check_fresh_all xs' P
  end.

(** A name repeated in a parameter telescope. *)
Fixpoint first_dup (xs : list string) : option string :=
  match xs with
  | nil => None
  | x :: xs' => if mem_b x xs' then Some x else first_dup xs'
  end.

Definition check_params (ps : list (string * Cst.expression)) : elab_result unit :=
  match first_dup (List.map fst ps) with
  | None => elab_success tt
  | Some x => elab_failure ("duplicate parameter " ++ x)
  end.

Definition unit_in_b (fq : path) (S : list scope_entry) : bool :=
  List.existsb (fun e => match e with scope_entry_unit fq' => path_beq fq fq' | _ => false end) S.

(** A name no binding in scope has, as a module: the imported unit of
    that one-segment path. *)
Definition unit_mod (x : string) (S : list scope_entry) : elab_result modexp :=
  if unit_in_b (x :: nil) S then elab_success (me_unit (x :: nil)) else elab_failure ("unbound name " ++ x).

(** ** Open Targets

    [elab_mod] on [itarget fq ip args], computed without building the
    object, so that a local body may use it: the head of the target, then
    its arguments by [f]. *)

Definition elab_ihead (S : list scope_entry) (fq ip : list string) : elab_result modexp :=
  match fq, ip with
  | nil, x :: ip' =>
      let* H := match lookup x S with
                | Some (k, e) => entry_to_mod k e
                | None => unit_mod x S
                end in
      elab_success (fold_left me_mem ip' H)
  | nil, nil => elab_failure "nothing to open"
  | _, _ =>
      let* _ := elab_check (unit_in_b fq S) (unit_not_imported_msg fq) in
      elab_success (fold_left me_mem ip (me_unit fq))
  end.

Definition elab_args_with (f : list scope_entry -> Cst.expression -> elab_result exp) (S : list scope_entry) :=
  fix go (os : list Cst.expression) : elab_result (list exp) :=
    match os with
    | nil => elab_success nil
    | o :: os' =>
        let* N := f S o in
        let* Ns := go os' in
        elab_success (N :: Ns)
    end.

Definition elab_target_with (f : list scope_entry -> Cst.expression -> elab_result exp) (S : list scope_entry) (fq ip : list string)
  (args : list Cst.expression) : elab_result modexp :=
  let* H := elab_ihead S fq ip in
  let* Ns := elab_args_with f S args in
  elab_success (mapps H Ns).

(** ** Objects *)

Definition elab_params_with (f : list scope_entry -> Cst.expression -> elab_result exp) :=
  fix go (S : list scope_entry) (ps : list (string * Cst.expression)) : elab_result (list (string * typ)) :=
    match ps with
    | nil => elab_success nil
    | (x, oA) :: ps' =>
        let* A := f S oA in
        let* tys := go (scope_entry_tvar x :: S) ps' in
        elab_success ((x, A) :: tys)
    end.

Definition elab_brs_with (f : list scope_entry -> Cst.expression -> elab_result exp) (S : list scope_entry) :=
  fix go (bs : list (string * list string * Cst.expression)) : elab_result (list (string * nat * exp)) :=
    match bs with
    | nil => elab_success nil
    | (c, ys, oB) :: bs' =>
        let* B := f (variable_scope_entries ys ++ S)%list oB in
        let* Bs := go bs' in
        elab_success ((c, List.length ys, B) :: Bs)
    end.

(** The rejection of a type on a binder before the last. *)
Definition blk_ann_msg : string := "only the last binder of a block (the scrutinee) may carry a type".

(** The rejection of an eliminator with no block, or more than one,
    marked [at]. *)
Definition elim_at_msg : string := "exactly one block of an eliminator is marked at, the scrutinee's".

(** The type written on the last binder of a block ([sbinders]), under the
    binders [pre] before it; a type on any other binder is rejected. *)
Definition elab_binders_with (f : list scope_entry -> Cst.expression -> elab_result exp) (S : list scope_entry) :=
  fix go (pre : list string) (xs : list (string * option Cst.expression)) : elab_result (option exp) :=
    match xs with
    | nil => elab_success None
    | (_, None) :: nil => elab_success None
    | (_, Some o) :: nil => let* Z := f (variable_scope_entries pre ++ S)%list o in elab_success (Some Z)
    | (_, Some _) :: _ :: _ => elab_failure blk_ann_msg
    | (x, None) :: ((_ :: _) as xs') => go (pre ++ x :: nil)%list xs'
    end.

Definition elab_blocks_with (f : list scope_entry -> Cst.expression -> elab_result exp) (S : list scope_entry) :=
  fix go (bks : list (bool * list (string * option Cst.expression) * Cst.expression * list (string * list string * Cst.expression)))
      : elab_result (list eblock) :=
    match bks with
    | nil => elab_success nil
    | (k, xs, oA, bs) :: bks' =>
        let* oZ := elab_binders_with f S nil xs in
        let* A := f (variable_scope_entries (List.map fst xs) ++ S)%list oA in
        let* Bs := elab_brs_with f S bs in
        let* Bks := go bks' in
        elab_success (eb_mk (List.length xs) oZ A Bs :: Bks)
    end.

(** A module path as written, for messages: a name, a unit, or a member of
    one. *)
Fixpoint path_text (o : Cst.expression) : option string :=
  match o with
  | Cst.var x => Some x
  | Cst.glob fq => Some (String.concat "›" fq)
  | Cst.proj o' y => option_map (fun p => p ++ "." ++ y) (path_text o')
  | _ => None
  end.

(** The rejection of an alias [x] of a type in a local module, [what]
    being "an inductive alias" or "a record alias": at no parameter and a
    member path [P.n], the open that names the type there instead; else
    the general form of that open. *)
Definition local_alias_error (what x : string) (ps : list (string * Cst.expression)) (oE : Cst.expression) : string :=
  let general := what ++ " is not allowed in a local module; open the type by name, `open M use (T as "
                   ++ x ++ ")`, instead" in
  match ps, oE with
  | nil, Cst.proj o n =>
      match path_text o with
      | Some p => what ++ " is not allowed in a local module; write `open " ++ p ++ " use (" ++ n ++ " as "
                    ++ x ++ ")` instead"
      | None => general
      end
  | _, _ => general
  end.

(** The fields of a record value, each its name and its value. *)
Definition elab_tfields_with (f : list scope_entry -> Cst.expression -> elab_result exp) (S : list scope_entry) :=
  fix go (fs : list (string * Cst.expression)) : elab_result (list (string * exp)) :=
    match fs with
    | nil => elab_success nil
    | (y, oM) :: fs' =>
        let* M := f S oM in
        let* Ms := go fs' in
        elab_success ((y, M) :: Ms)
    end.

Fixpoint elab (S : list scope_entry) (o : Cst.expression) {struct o} : elab_result exp :=
  match o with
  | Cst.typ n => elab_success (Typeω@n)
  | Cst.suniv o =>
      let* M := elab S o in
      elab_success (Type⟨M⟩)
  | Cst.level n => elab_success (Level@n)
  | Cst.llit o => elab_success (𝕃ᵒ o)
  | Cst.succl o =>
      let* M := elab S o in
      elab_success (succl M)
  | Cst.maxl o1 o2 =>
      let* M := elab S o1 in
      let* N := elab S o2 in
      elab_success (maxl M N)
  | Cst.nat => elab_success ℕ
  | Cst.num n => elab_success (a_nlit n)
  | Cst.true_ty => elab_success ⊤
  | Cst.true_tm => elab_success ⋆
  | Cst.false_ty => elab_success ⊥
  | Cst.exfalso om mx oA =>
      let* M := elab S om in
      let* A := elab (scope_entry_tvar mx :: S) oA in
      elab_success (efq M return A)
  | Cst.pi x oA oB =>
      let* A := elab S oA in
      let* B := elab (scope_entry_tvar x :: S) oB in
      elab_success (Π A B)
  | Cst.fn x oA oM =>
      let* A := elab S oA in
      let* M := elab (scope_entry_tvar x :: S) oM in
      elab_success (λ A M)
  | Cst.app o1 o2 =>
      let* M := elab S o1 in
      let* N := elab S o2 in
      elab_success (M $ N)
  | Cst.var x =>
      match lookup x S with
      | Some (k, e) => entry_to_term k e
      | None => elab_failure ("unbound name " ++ x)
      end
  | Cst.glob _ => elab_failure "a unit is not a term"
  | Cst.proj o x =>
      if expression_path o then
        let* H := elab_mod S o in
        elab_success (a_mem H x)
      else
        let* M := elab S o in
        elab_success (ℓ ≔ M in a_mem (me_var 0) x)
  | Cst.letb (Cst.d_def x (Some oA) oM) ob =>
      let* A := elab S oA in
      let* M := elab S oM in
      let* B := elab (scope_entry_tvar x :: S) ob in
      elab_success (ℓ A ≔ M in B)
  | Cst.letb (Cst.d_def x None oM) ob =>
      let* M := elab S oM in
      let* B := elab (scope_entry_tvar x :: S) ob in
      elab_success (ℓ ≔ M in B)
  | Cst.letb (Cst.d_mod x ps md) ob =>
      let* _ := check_params ps in
      let* tys := elab_params_with elab S ps in
      let* D := elab_mdef (param_scope_entries ps ++ S) md in
      let* B := elab (scope_entry_var x :: S) ob in
      elab_success (ℓₘ (gu_mk (ptele tys) D) in B)
  | Cst.elim om bks =>
      let* M := elab S om in
      let* Bks := elab_blocks_with elab S bks in
      match elim_at (List.map (fun bk => fst (fst (fst bk))) bks) with
      | Some m => elab_success (a_elim None nil m Bks M)
      | None => elab_failure elim_at_msg
      end
  | Cst.tuple oT fs =>
      let* T := elab S oT in
      let* Ms := elab_tfields_with elab S fs in
      elab_success (a_tuple T Ms)
  end

with elab_mod (S : list scope_entry) (o : Cst.expression) {struct o} : elab_result modexp :=
  match o with
  | Cst.var x =>
      match lookup x S with
      | Some (k, e) => entry_to_mod k e
      | None => unit_mod x S
      end
  | Cst.glob fq =>
      let* _ := elab_check (unit_in_b fq S) (unit_not_imported_msg fq) in
      elab_success (me_unit fq)
  | Cst.proj o y =>
      let* H := elab_mod S o in
      elab_success (me_mem H y)
  | Cst.app o1 o2 =>
      let* H := elab_mod S o1 in
      let* N := elab S o2 in
      elab_success (me_app H N)
  | _ => elab_failure "not a module"
  end

with elab_mdef (S : list scope_entry) (md : Cst.mdef) {struct md} : elab_result moddef :=
  match md with
  | Cst.md_alias oE =>
      let* E := elab_mod S oE in
      elab_success (md_alias E)
  | Cst.md_where cs =>
      let* Φ :=
        (fix go (S : list scope_entry) (Φ : gmod) (cs : list Cst.cmd) {struct cs} : elab_result gmod :=
           match cs with
           | nil => elab_success Φ
           | Cst.c_def m x oA oM :: cs' =>
               let* A := elab S oA in
               let* M := elab S oM in
               go (scope_entry_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs'
           | Cst.c_mod pv x ps md' :: cs' =>
               let* _ := check_params ps in
               let* tys := elab_params_with elab S ps in
               let* D := elab_mdef (param_scope_entries ps ++ S) md' in
               go (scope_entry_var x :: S) (gm_ext Φ x (ge_mod pv (gu_mk (ptele tys) D))) cs'
           | Cst.c_open fq ip args its :: cs' =>
               let* E := elab_target_with elab S fq ip args in
               go (item_scope_entries its ++ S)%list (gm_open Φ E its) cs'
           | Cst.c_axiom _ _ :: _ => elab_failure "axioms are not allowed in a local module"
           | Cst.c_import _ :: _ => elab_failure "import is not allowed in a local module; use open"
           | Cst.c_error e :: _ => elab_failure e
           | Cst.c_eval _ _ :: _ => elab_failure "eval is not allowed in a local module"
           | Cst.c_ind _ _ _ _ :: _ => elab_failure "an inductive type is not allowed in a local module"
           | Cst.c_mdef _ _ _ :: _ => elab_failure "a mutual definition is not allowed in a local module"
           | Cst.c_builtin _ _ :: _ => elab_failure "builtin is not allowed in a local module"
           | Cst.c_ind_alias _ x ps oE :: _ => elab_failure (local_alias_error "an inductive alias" x ps oE)
           | Cst.c_record_alias _ x ps oE :: _ => elab_failure (local_alias_error "a record alias" x ps oE)
           | Cst.c_record _ _ _ _ _ _ :: _ => elab_failure "a record type is not allowed in a local module"
           end) S gm_nil cs in
      elab_success (md_body sm_open Φ)
  end.

Definition elab_params := elab_params_with elab.

(** The arguments of a constructor, each binding its name for the ones
    after it; the declared type is a variable in scope. *)
Fixpoint elab_rargs (S : list scope_entry) (args : list (string * Cst.expression)) : elab_result (list (string * exp)) :=
  match args with
  | nil => elab_success nil
  | (y, oA) :: args' =>
      let* A := elab S oA in
      let* args'' := elab_rargs (scope_entry_tvar y :: S) args' in
      elab_success ((y, A) :: args'')
  end.

Fixpoint elab_rcons (S : list scope_entry) (cs : list (string * list (string * Cst.expression)))
  : elab_result (list (string * list (string * exp))) :=
  match cs with
  | nil => elab_success nil
  | (c, args) :: cs' =>
      let* args' := elab_rargs S args in
      let* cs'' := elab_rcons S cs' in
      elab_success ((c, args') :: cs'')
  end.

(** The members of a group, under its uniform parameters [ups], the
    members' names [xs] in scope in the arguments ([smembers]). *)
Fixpoint elab_members (S : list scope_entry) (ups : list (string * Cst.expression)) (xs : list string)
    (ms : list (string * Cst.expression * list (string * list (string * Cst.expression)))) : elab_result (list raw_member) :=
  match ms with
  | nil => elab_success nil
  | (x, oT, cs) :: ms' =>
      let '(nps, oS) := split_pis oT in
      let* _ := check_params (ups ++ nps)%list in
      let* ntys := elab_params (param_scope_entries ups ++ S)%list nps in
      let* A := elab (param_scope_entries ups ++ S)%list oS in
      let* cs' := elab_rcons (param_scope_entries (ups ++ nps) ++ variable_scope_entries xs ++ S)%list cs in
      let* rms := elab_members S ups xs ms' in
      elab_success (mk_rmem x (ptele ntys) A cs' :: rms)
  end.

(** The functions of a mutual definition ([sfuns]): each its parameters,
    the last its scrutinee. *)
Fixpoint elab_funs (S : list scope_entry)
    (fs : list (string * list (string * Cst.expression) * Cst.expression * list (string * list string * Cst.expression))) :
    elab_result (list raw_fun) :=
  match fs with
  | nil => elab_success nil
  | (f, ps, oA, bs) :: fs' =>
      match List.rev ps with
      | nil => elab_failure ("the function " ++ f ++ " of a mutual definition has no scrutinee")
      | (z, oZ) :: rys =>
          let ys := List.rev rys in
          let* _ := check_params ps in
          let* ytys := elab_params S ys in
          let* Z := elab (param_scope_entries ys ++ S)%list oZ in
          let* A := elab (scope_entry_tvar z :: param_scope_entries ys ++ S)%list oA in
          let* Bs := elab_brs_with elab S bs in
          let* rfs := elab_funs S fs' in
          elab_success (mk_rfun f (ptele ytys) Z A Bs :: rfs)
      end
  end.

(** Names declared together twice. *)
Definition check_distinct (what : string) (xs : list string) : elab_result unit :=
  match first_dup xs with
  | None => elab_success tt
  | Some x => elab_failure (x ++ " is declared twice in " ++ what)
  end.

(** A name the with-area [cs] of the record [x] declares that is one of its
    fields [fs]: the field took it. *)
Definition check_no_field (x : string) (fs : list string) (cs : list Cst.cmd) : elab_result unit :=
  match List.find (fun y => mem_b y fs) (flat_map cmd_decls cs) with
  | Some f => elab_failure (f ++ " is a field of record " ++ x)
  | None => elab_success tt
  end.

(** ** Commands

    A module body is elaborated where it stands: the body of [module x …
    where body end] is elaborated by [elab_cmd] itself, so no stack of frames
    is needed.  A command, in a frame whose parameters are named [P], takes
    the scope [S] (the frame's entries so far, then everything outside it)
    to [S'] and emits its core commands; a new entry is pushed on the front
    of the scope, so no command copies it.  [nb] is the number of binders
    of the scope, [binders S], which a member's entry records; a frame's
    members add none, so [nb] is the frame's, and is never recounted. *)
Definition elab_cmds_with (f : list string -> list string -> nat -> list scope_entry -> Cst.cmd -> elab_result (list scope_entry * list core_cmd)%type)
  (ch : list string) (P : list string) (nb : nat) :=
  fix go (S : list scope_entry) (cs : list Cst.cmd) : elab_result (list core_cmd) :=
    match cs with
    | nil => elab_success nil
    | c :: cs' =>
        let* r := f ch P nb S c in
        let* ccs := go (fst r) cs' in
        elab_success (snd r ++ ccs)%list
    end.

Fixpoint elab_cmd (fp : path) (ch : list string) (P : list string) (nb : nat) (S : list scope_entry) (c : Cst.cmd) {struct c}
  : elab_result (list scope_entry * list core_cmd)%type :=
  match c with
  | Cst.c_def m x oA oM =>
      let* _ := check_fresh x P in
      let* A := elab S oA in
      let* M := elab S oM in
      elab_success (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S, core_cmd_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M) :: nil)
  (** An axiom is opaque: it has no body to unfold. *)
  | Cst.c_axiom x oA =>
      let* _ := check_fresh x P in
      let* A := elab S oA in
      elab_success (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S, core_cmd_def x false false A None :: nil)
  | Cst.c_mod pv x ps (Cst.md_where body) =>
      let* _ := check_fresh x P in
      let* _ := check_params ps in
      let* tys := elab_params S ps in
      let* bcs := elab_cmds_with (elab_cmd fp) (ch ++ x :: nil) (map fst ps) (binders (param_scope_entries ps) + nb) (param_scope_entries ps ++ S) body in
      elab_success (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S, core_cmd_mod x pv (ptele tys) bcs :: nil)
  | Cst.c_mod pv x ps (Cst.md_alias oE) =>
      let* _ := check_fresh x P in
      let* _ := check_params ps in
      let* tys := elab_params S ps in
      let* E := elab_mod (param_scope_entries ps ++ S) oE in
      elab_success (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S, core_cmd_alias x pv (ptele tys) E :: nil)
  | Cst.c_import fq => elab_success (scope_entry_unit fq :: S, core_cmd_load fq :: nil)
  | Cst.c_open fq ip args its =>
      let* E := elab_target_with elab S fq ip args in
      let* _ := check_fresh_all (map iitem_name its) P in
      elab_success (item_mems fp ch nb its ++ S, core_cmd_open E its :: nil)%list
  | Cst.c_error e => elab_failure e
  | Cst.c_eval oM None =>
      let* M := elab S oM in
      elab_success (S, core_cmd_eval M None :: nil)
  | Cst.c_eval oM (Some oA) =>
      let* M := elab S oM in
      let* A := elab S oA in
      elab_success (S, core_cmd_eval M (Some A) :: nil)
  | Cst.c_ind pv wr ups ms =>
      let* _ := check_distinct "a group" (member_names ms) in
      let* _ := check_fresh_all (member_names ms) P in
      let* tys := elab_params S ups in
      let* rms := elab_members S ups (member_names ms) ms in
      elab_success (filed_mems fp ch nb (member_names ms) ++ S, core_cmd_inductive pv (mk_raw (ptele tys) rms wr) :: nil)%list
  | Cst.c_mdef m ps fs =>
      let* _ := check_params ps in
      let* _ := check_distinct "a mutual definition" (fun_names fs) in
      let* _ := check_fresh_all (fun_names fs) P in
      let* tys := elab_params S ps in
      let* rfs := elab_funs (param_scope_entries ps ++ S) fs in
      elab_success (filed_mems fp ch nb (fun_names fs) ++ S,
           core_cmd_mdef (negb (Cst.md_abstract m)) (Cst.md_private m) (ptele tys) rfs :: nil)%list
  (** The type is a module, as written; the command declares nothing. *)
  | Cst.c_builtin k oX =>
      let* H := elab_mod S oX in
      elab_success (S, core_cmd_builtin k H :: nil)
  (** The target is a module, read under the parameters, as an alias's
      is. *)
  | Cst.c_ind_alias pv x ps oE =>
      let* _ := check_fresh x P in
      let* _ := check_params ps in
      let* tys := elab_params S ps in
      let* E := elab_mod (param_scope_entries ps ++ S) oE in
      elab_success (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S, core_cmd_inductive_alias x pv (ptele tys) E :: nil)
  (** A record alias, as an inductive alias is. *)
  | Cst.c_record_alias pv x ps oE =>
      let* _ := check_fresh x P in
      let* _ := check_params ps in
      let* tys := elab_params S ps in
      let* E := elab_mod (param_scope_entries ps ++ S) oE in
      elab_success (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S, core_cmd_record_alias x pv (ptele tys) E :: nil)
  (** The parameters, the sort and the fields' types are read as an
      inductive type's are; the with-area in the record's frame, the record
      in scope outside it. *)
  | Cst.c_record pv x ps oS fs cs =>
      let* _ := check_fresh x P in
      let* _ := check_params ps in
      let* tys := elab_params S ps in
      let* Srt := elab (param_scope_entries ps ++ S) oS in
      let* fs' := elab_rargs (param_scope_entries ps ++ S) fs in
      let* _ := check_no_field x (map fst fs) cs in
      let* bcs := elab_cmds_with (elab_cmd fp) (ch ++ x :: nil) (map fst ps) (binders (scope_entry_self :: param_scope_entries ps) + nb)
                    (record_scope_entries fp ch nb x ps fs ++ scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S) cs in
      elab_success (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) nb :: S, core_cmd_record x pv (ptele tys) Srt fs' bcs :: nil)
  end.

Definition elab_cmds (fp : path) := elab_cmds_with (elab_cmd fp).

(** The leading imports and opens, before the unit's header: the scope of
    its parameter types, and their loads. *)
Fixpoint elab_lead (L : list scope_entry) (cs : list Cst.cmd) : elab_result (list scope_entry * list core_cmd)%type :=
  match cs with
  | nil => elab_success (L, nil)
  | Cst.c_import fq :: cs' =>
      let* r := elab_lead (scope_entry_unit fq :: L) cs' in
      elab_success (fst r, core_cmd_load fq :: snd r)
  | Cst.c_open fq ip args its :: cs' =>
      let* E := elab_target_with elab L fq ip args in
      elab_lead (open_scope_entries E its ++ L)%list cs'
  | Cst.c_error e :: _ => elab_failure e
  | _ :: _ => elab_failure "outside of any module"
  end.

(** ** Units

    The leading imports and opens are read before the unit's header, for
    its parameter types, then as the first commands of its frame. *)

Definition elaborate_core (prg : Cst.prog) : elab_result cunit :=
  let '(leads, (fp, ps, cs)) := prg in
  let* r := elab_lead nil leads in
  let '(L, lds) := r in
  let* _ := check_params ps in
  let* tys := elab_params L ps in
  let* ccs := elab_cmds fp nil (map fst ps) (binders (param_scope_entries ps ++ L)) (param_scope_entries ps ++ L) (leads ++ cs) in
  elab_success (lds, ptele tys, ccs).

Definition to_core (prg : Cst.prog) : option cunit :=
  match elaborate_core prg with
  | elab_success u => Some u
  | elab_failure _ => None
  end.
