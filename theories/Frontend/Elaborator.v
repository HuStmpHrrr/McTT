From Stdlib Require Import Lia List ListDec PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members GlobalCtx Command.
From Mctt.Frontend Require Import Resolve ElabSpec.

Import Syntax_Notations.

Open Scope string_scope.

(** * Elaboration

    A unit elaborates into core commands without reading any other unit, and
    without looking inside any module.  A name becomes a λ-variable (a local
    binder or a parameter of an open frame), a member of an open frame
    [a_glob], named by its absolute path and applied to the parameters of the
    frames enclosing it, or an import alias.  A projection is the core's
    member selection of the module expression its head denotes.  The
    elaborator computes the relation of [Frontend.ElabSpec] on the same data
    structures. *)

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

Fixpoint alias_lookup (x : string) (al : list (string * starget)) : option starget :=
  match al with
  | nil => None
  | (y, t) :: al' => if String.eqb x y then Some t else alias_lookup x al'
  end.

(** The innermost local binding of [x], [k] binders further in. *)
Fixpoint lb_lookup (k : nat) (x : string) (L : list lbind) : option sden :=
  match L with
  | nil => None
  | b :: L' => if String.eqb x (lb_name b) then Some (ldenote k b) else lb_lookup (lb_binders b + k) x L'
  end.

(** The number of parameters of the frames [Fs]. *)
Definition tele (Fs : list sframe) : nat := fold_right (fun F n => List.length (sf_params F) + n) 0 Fs.

(** A name looked up in the open frames: an alias, then a member, then a
    parameter.  [off] counts the binders between the use site and the
    parameters of the first frame. *)
Fixpoint fr_lookup (fp : fpath) (O : sscope) (off : nat) (x : string) (Fs : list sframe) : option sden :=
  match Fs with
  | nil =>
      match alias_lookup x (ss_alias O) with
      | Some t => Some (sd_alias (wk_starget off t))
      | None => None
      end
  | F :: Fs' =>
      match alias_lookup x (ss_alias (sf_scope F)) with
      | Some t => Some (sd_alias (wk_starget off t))
      | None =>
          if mem_b x (decl_names (sf_cmds F))
          then Some (sd_glob (p_abs fp (sf_path F ++ x :: nil)) (vars_desc off (tele (F :: Fs'))))
          else match index_of x (rev (map fst (sf_params F))) with
               | Some k => Some (sd_var (off + k))
               | None => fr_lookup fp O (off + List.length (sf_params F)) x Fs'
               end
      end
  end.

(** A unit is named by its full path only where it has been imported. *)
Definition unit_reachable (O : sscope) (Fs : list sframe) (fq : fpath) : bool :=
  List.existsb (path_beq fq) (ss_units O) ||
  List.existsb (fun F => List.existsb (path_beq fq) (ss_units (sf_scope F))) Fs.

Definition den_to_term (d : sden) : eres exp :=
  match d with
  | sd_glob p vs => eok (apps (a_glob p) vs)
  | sd_var k => eok #k
  | sd_alias (st_mem E n) => eok (a_mem E n)
  | sd_alias (st_mod _) => eerr "a module is not a term"
  end.

Definition den_to_mod (d : sden) : modexp :=
  match d with
  | sd_glob p vs => mapps (me_path p) vs
  | sd_var k => me_var k
  | sd_alias (st_mod E) => E
  | sd_alias (st_mem E n) => me_mem E n
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

(** What an import in a local body binds. *)
Definition libinds_of (E : modexp) (spec : Cst.ispec) (L : list lbind) : list lbind :=
  match spec with
  | Cst.i_open => L
  | Cst.i_as y => lb_alias y (st_mod E) :: L
  | Cst.i_use ns => fold_left (fun L n => lb_alias n (st_mem E n) :: L) ns L
  end.

(** ** Objects

    [elab] elaborates a term, [elab_mod] a module expression and [elab_mdef]
    the definition of a module under its parameters.  A parameter list is
    elaborated where it occurs, by [elab_params]. *)

Definition elab_params_with (f : list lbind -> Cst.obj -> eres exp) :=
  fix go (L : list lbind) (ps : list (string * Cst.obj)) : eres (list (string * typ)) :=
    match ps with
    | nil => eok nil
    | (x, oA) :: ps' =>
        let* A := f L oA in
        let* tys := go (lb_var x :: L) ps' in
        eok ((x, A) :: tys)
    end.

Section Objects.
  Variable (fp : fpath) (O : sscope) (Fs : list sframe).

  Definition lookup (L : list lbind) (x : string) : option sden :=
    match lb_lookup 0 x L with
    | Some d => Some d
    | None => fr_lookup fp O (nbinders L) x Fs
    end.

  (** A dotted name [x.ip] in module position, as [elab_mod] reads it. *)
  Definition elab_dotted (L : list lbind) (x : string) (ip : list string) : eres modexp :=
    match lookup L x with
    | Some d => eok (fold_left me_mem ip (den_to_mod d))
    | None => eerr ("unbound name " ++ x)
    end.

  Fixpoint elab (L : list lbind) (o : Cst.obj) {struct o} : eres exp :=
    match o with
    | Cst.typ n => eok (Type@n)
    | Cst.nat => eok ℕ
    | Cst.zero => eok zero
    | Cst.succ o =>
        let* M := elab L o in
        eok (succ M)
    | Cst.natrec on mx om oz sx sr os =>
        let* N := elab L on in
        let* A := elab (lb_var mx :: L) om in
        let* MZ := elab L oz in
        let* MS := elab (lb_var sr :: lb_var sx :: L) os in
        eok (rec N return A | zero -> MZ | succ -> MS end)
    | Cst.true_ty => eok ⊤
    | Cst.true_tm => eok ⋆
    | Cst.false_ty => eok ⊥
    | Cst.exfalso om mx oA =>
        let* M := elab L om in
        let* A := elab (lb_var mx :: L) oA in
        eok (efq M return A)
    | Cst.pi x oA oB =>
        let* A := elab L oA in
        let* B := elab (lb_var x :: L) oB in
        eok (Π A B)
    | Cst.fn x oA oM =>
        let* A := elab L oA in
        let* M := elab (lb_var x :: L) oM in
        eok (λ A M)
    | Cst.app o1 o2 =>
        let* M := elab L o1 in
        let* N := elab L o2 in
        eok (M $ N)
    | Cst.var x =>
        match lookup L x with
        | Some d => den_to_term d
        | None => eerr ("unbound name " ++ x)
        end
    | Cst.glob _ => eerr "a unit is not a term"
    | Cst.proj o x =>
        let* H := elab_mod L o in
        eok (a_mem H x)
    | Cst.letb (Cst.d_def x oA oM) ob =>
        let* A := elab L oA in
        let* M := elab L oM in
        let* B := elab (lb_var x :: L) ob in
        eok (ℓ A ≔ M in B)
    | Cst.letb (Cst.d_mod x ps md) ob =>
        let* _ := check_params ps in
        let* tys := elab_params_with elab L ps in
        let* D := elab_mdef (lparams ps ++ L) md in
        let* B := elab (lb_var x :: L) ob in
        eok (ℓₘ (gu_mk (ptele tys) D) in B)
    end

  with elab_mod (L : list lbind) (o : Cst.obj) {struct o} : eres modexp :=
    match o with
    | Cst.var x =>
        match lookup L x with
        | Some d => eok (den_to_mod d)
        | None => eerr ("unbound name " ++ x)
        end
    | Cst.glob fq =>
        let* _ := echeck (unit_reachable O Fs fq) "the unit is not imported" in
        eok (me_path (p_abs fq nil))
    | Cst.proj o y =>
        let* H := elab_mod L o in
        eok (me_mem H y)
    | Cst.app o1 o2 =>
        let* H := elab_mod L o1 in
        let* N := elab L o2 in
        eok (me_app H N)
    | _ => eerr "not a module"
    end

  with elab_mdef (L : list lbind) (md : Cst.mdef) {struct md} : eres moddef :=
    match md with
    | Cst.md_alias oE =>
        let* E := elab_mod L oE in
        eok (md_alias E)
    | Cst.md_where cs =>
        let* Φ :=
          (fix go (L : list lbind) (Φ : gmod) (cs : list Cst.cmd) {struct cs} : eres gmod :=
             match cs with
             | nil => eok Φ
             | c :: cs' =>
                 match c with
                 | Cst.c_def m x oA oM =>
                     let* A := elab L oA in
                     let* M := elab L oM in
                     go (lb_var x :: L)
                        (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs'
                 | Cst.c_mod p ps md' =>
                     let* U :=
                       (fix path_unit (p : list string) : eres (string * gunit)%type :=
                          match p with
                          | nil => eerr "empty module name"
                          | x :: nil =>
                              let* _ := check_params ps in
                              let* tys := elab_params_with elab L ps in
                              let* D := elab_mdef (lparams ps ++ L) md' in
                              eok (x, gu_mk (ptele tys) D)
                          | x :: p' =>
                              let* yU := path_unit p' in
                              eok (x, gu_mk ⋅ (md_body (gm_ext gm_nil (fst yU) (ge_mod (snd yU)))))
                          end) p in
                     go (lb_var (fst U) :: L) (gm_ext Φ (fst U) (ge_mod (snd U))) cs'
                 | Cst.c_import fq ip spec =>
                     let* E :=
                       match fq, ip with
                       | nil, x :: ip' => elab_dotted L x ip'
                       | nil, nil => eerr "nothing to import"
                       | _, _ => eok (me_path (p_abs fq ip))
                       end in
                     go (libinds_of E spec L) (gm_check Φ (bc_import E (ispec_names spec))) cs'
                 | Cst.c_eval oM oA =>
                     let* M := elab L oM in
                     match oA with
                     | None => go L (gm_check Φ (bc_eval M None)) cs'
                     | Some oA =>
                         let* A := elab L oA in
                         go L (gm_check Φ (bc_eval M (Some A))) cs'
                     end
                 end
             end) L gm_nil cs in
        eok (md_body Φ)
    end.

  Definition elab_params := elab_params_with elab.
End Objects.

(** ** Commands

    The state of a unit being elaborated: the open frames, innermost first,
    and the commands emitted before the unit's declaration. *)
Record ustate : Set := us_mk
  { us_unit : fpath
  ; us_outer : sscope
  ; us_frames : list sframe
  ; us_imps : list ccmd }.

(** A name not bound in a frame by a member, an alias or a parameter. *)
Definition sf_fresh_b (F : sframe) (x : string) : bool := negb (mem_b x (sf_names F)).

(** The innermost frame is updated by [f], which sees the frames outside. *)
Definition us_top (st : ustate) (f : sframe -> list sframe -> eres sframe) : eres ustate :=
  match us_frames st with
  | F :: Fs => let* F' := f F Fs in eok (us_mk (us_unit st) (us_outer st) (F' :: Fs) (us_imps st))
  | nil => eerr "outside of any module"
  end.

Definition elab_def (st : ustate) (m : Cst.mods) (x : string) (oA oM : Cst.obj) : eres ustate :=
  us_top st (fun F Fs =>
    let* _ := echeck (sf_fresh_b F x) (x ++ " is already declared") in
    let* A := elab (us_unit st) (us_outer st) (F :: Fs) nil oA in
    let* M := elab (us_unit st) (us_outer st) (F :: Fs) nil oM in
    eok (sf_emit F (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A M))).

Definition elab_eval (st : ustate) (oM : Cst.obj) (oA : option Cst.obj) : eres ustate :=
  us_top st (fun F Fs =>
    let* M := elab (us_unit st) (us_outer st) (F :: Fs) nil oM in
    match oA with
    | None => eok (sf_emit F (cc_eval M None))
    | Some oA =>
        let* A := elab (us_unit st) (us_outer st) (F :: Fs) nil oA in
        eok (sf_emit F (cc_eval M (Some A)))
    end).

Definition elab_alias (st : ustate) (x : string) (ps : list (string * Cst.obj)) (oE : Cst.obj) : eres ustate :=
  us_top st (fun F Fs =>
    let* _ := echeck (sf_fresh_b F x) (x ++ " is already declared") in
    let* _ := check_params ps in
    let* tys := elab_params (us_unit st) (us_outer st) (F :: Fs) nil ps in
    let* E := elab_mod (us_unit st) (us_outer st) (F :: Fs) (lparams ps) oE in
    eok (sf_emit F (cc_alias x (ptele tys) E))).

(** ** Imports *)

Definition alias_fresh_b (taken : list string) (sc : sscope) (y : string) : bool :=
  negb (mem_b y taken) && negb (mem_b y (map fst (ss_alias sc))).

Definition use_bind (E : modexp) (taken : list string) (acc : eres sscope) (n : string) : eres sscope :=
  let* sc := acc in
  let* _ := echeck (alias_fresh_b taken sc n) (n ++ " is already declared") in
  eok (ss_add n (st_mem E n) sc).

Definition ibinds_of (E : modexp) (taken : list string) (spec : Cst.ispec) (sc : sscope) : eres sscope :=
  match spec with
  | Cst.i_open => eok sc
  | Cst.i_as y =>
      let* _ := echeck (alias_fresh_b taken sc y) (y ++ " is already declared") in
      eok (ss_add y (st_mod E) sc)
  | Cst.i_use ns => fold_left (use_bind E taken) ns (eok sc)
  end.

Definition itarget_of (fp : fpath) (O : sscope) (Fs : list sframe) (fq : fpath) (ip : list string) : eres modexp :=
  match fq, ip with
  | nil, x :: ip' => elab_dotted fp O Fs nil x ip'
  | nil, nil => eerr "nothing to import"
  | _, _ => eok (me_path (p_abs fq ip))
  end.

(** An import is checked by the core where it stands: it goes into the
    innermost frame, or, before the unit's declaration, into the imports. *)
Definition elab_import (st : ustate) (fq ip : list string) (spec : Cst.ispec) : eres ustate :=
  match us_frames st with
  | F :: Fs =>
      let* E := itarget_of (us_unit st) (us_outer st) (F :: Fs) fq ip in
      let* sc := ibinds_of E (sf_taken F) spec (ss_add_unit fq (sf_scope F)) in
      eok (us_mk (us_unit st) (us_outer st)
             (sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ cc_import (ifile fq) E (ispec_names spec) :: nil) sc :: Fs)
             (us_imps st))
  | nil =>
      let* E := itarget_of (us_unit st) (us_outer st) nil fq ip in
      let* sc := ibinds_of E nil spec (ss_add_unit fq (us_outer st)) in
      eok (us_mk (us_unit st) sc nil (us_imps st ++ cc_import (ifile fq) E (ispec_names spec) :: nil))
  end.

(** Opening a module pushes its frame; closing it pops the frame and makes the
    module a member of the frame outside. *)
Definition us_open (st : ustate) (F : sframe) : ustate :=
  us_mk (us_unit st) (us_outer st) (F :: us_frames st) (us_imps st).

Definition us_close (x : string) (st : ustate) : eres ustate :=
  match us_frames st with
  | N :: F :: Fs =>
      eok (us_mk (us_unit st) (us_outer st)
             (sf_emit F (cc_mod x (ptele (sf_params N)) (sf_cmds N)) :: Fs) (us_imps st))
  | _ => eerr "no module to close"
  end.

Definition us_path (st : ustate) : list string :=
  match us_frames st with
  | F :: _ => sf_path F
  | nil => nil
  end.

Definition check_fresh (st : ustate) (x : string) : eres unit :=
  let* _ := us_top st (fun F _ => let* _ := echeck (sf_fresh_b F x) (x ++ " is already declared") in eok F) in
  eok tt.

(** The loop over a module body is an inner [fix], since the body is nested
    in a [list].  [module A.B] opens [A], without parameters, and [B] inside
    it.  A declared module cannot be reopened, because later commands may
    depend on its members. *)
Fixpoint elab_cmd (st : ustate) (c : Cst.cmd) : eres ustate :=
  match c with
  | Cst.c_mod p ps md =>
      (fix open_path (p : list string) (st : ustate) : eres ustate :=
         match p with
         | nil => eerr "empty module name"
         | x :: nil =>
             match md with
             | Cst.md_alias oE => elab_alias st x ps oE
             | Cst.md_where body =>
                 let* _ := check_fresh st x in
                 let* _ := check_params ps in
                 let* tys := elab_params (us_unit st) (us_outer st) (us_frames st) nil ps in
                 let* st1 :=
                   (fix go (st : ustate) (cs : list Cst.cmd) : eres ustate :=
                      match cs with
                      | nil => eok st
                      | c :: cs' => let* st' := elab_cmd st c in go st' cs'
                      end) (us_open st (sf_new (us_path st ++ x :: nil) tys)) body in
                 us_close x st1
             end
         | x :: p' =>
             let* _ := check_fresh st x in
             let* st1 := open_path p' (us_open st (sf_new (us_path st ++ x :: nil) nil)) in
             us_close x st1
         end) p st
  | Cst.c_def m x oA oM => elab_def st m x oA oM
  | Cst.c_eval oM oA => elab_eval st oM oA
  | Cst.c_import fq ip spec => elab_import st fq ip spec
  end.

Fixpoint elab_cmds (st : ustate) (cs : list Cst.cmd) : eres ustate :=
  match cs with
  | nil => eok st
  | c :: cs' => let* st' := elab_cmd st c in elab_cmds st' cs'
  end.

(** ** Units

    A unit's imports are elaborated outside its frame, then its parameters,
    then its body in its own frame. *)
Definition elaborate_core (prg : Cst.prog) : eres cunit :=
  let '(imports, (fp, ps, cs)) := prg in
  let* st0 := elab_cmds (us_mk fp ss_empty nil nil) imports in
  let* _ := check_params ps in
  let* tys := elab_params fp (us_outer st0) nil nil ps in
  let* st := elab_cmds (us_open st0 (sf_new nil tys)) cs in
  match us_frames st with
  | F :: nil => eok (us_imps st, ptele (sf_params F), sf_cmds F)
  | _ => eerr "unbalanced modules"
  end.

Definition to_core (prg : Cst.prog) : option cunit :=
  match elaborate_core prg with
  | eok u => Some u
  | eerr _ => None
  end.
