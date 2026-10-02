From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax GlobalCtx Command.
From Mctt.Frontend Require Import Resolve.

Import Syntax_Notations.

Open Scope string_scope.

(** * Elaboration

    A unit elaborates into core commands without reading any other unit.  A
    name becomes a λ-variable (a local binder or a parameter of an open frame)
    or a member [a_glob], named by its absolute path.  A member is generalized
    over the parameters of the modules enclosing it, so a member of an open
    frame is applied to the parameter variables of its frame and the frames
    outside it.  A path into an imported unit is left to typing. *)

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

(** ** Open Frames

    A frame being elaborated: its names, its parameters, the commands emitted
    so far (last first), and its imports' aliases and units.  The imports that
    precede a unit's declaration have an [oscope] of their own. *)
Record oscope : Set := os_mk
  { os_alias : list (string * target)
  ; os_units : list (list string) }.

Record oframe : Set := of_mk
  { of_names : eframe
  ; of_params : ctx
  ; of_cmds : list ccmd
  ; of_scope : oscope
  (** The member chain from the unit's root to this frame. *)
  ; of_path : list string }.

Definition of_alias (f : oframe) : list (string * target) := os_alias (of_scope f).

Fixpoint alias_lookup (x : string) (al : list (string * target)) : option target :=
  match al with
  | nil => None
  | (y, t) :: al' => if String.eqb x y then Some t else alias_lookup x al'
  end.

Fixpoint ls_lookup (x : string) (ls : lscope) : option lent :=
  match ls with
  | nil => None
  | (y, e) :: ls' => if String.eqb x y then Some e else ls_lookup x ls'
  end.

(** A name taken in a frame by a member or a parameter. *)
Definition of_taken (x : string) (f : oframe) : bool :=
  match em_lookup x (ef_mod (of_names f)), index_of x (ef_params (of_names f)) with
  | None, None => false
  | _, _ => true
  end.

(** A name not bound in a frame by a member, an alias or a parameter. *)
Definition of_fresh (x : string) (f : oframe) : bool :=
  match alias_lookup x (of_alias f) with
  | None => negb (of_taken x f)
  | Some _ => false
  end.

(** A name repeated in a parameter telescope. *)
Fixpoint first_dup (xs : list string) : option string :=
  match xs with
  | nil => None
  | x :: xs' => if List.existsb (String.eqb x) xs' then Some x else first_dup xs'
  end.

Definition check_params (ps : list (string * Cst.obj)) : eres unit :=
  match first_dup (List.map fst ps) with
  | None => eok tt
  | Some x => eerr ("duplicate parameter " ++ x)
  end.

(** A new member [x], declared by the command [c]. *)
Definition of_add (x : string) (en : ename) (c : ccmd) (f : oframe) : oframe :=
  {| of_names := ef_mk (ef_params (of_names f)) (em_ext (ef_mod (of_names f)) x en)
   ; of_params := of_params f
   ; of_cmds := c :: of_cmds f
   ; of_scope := of_scope f
   ; of_path := of_path f |}.

Definition os_fresh (x : string) (sc : oscope) : bool :=
  match alias_lookup x (os_alias sc) with None => true | Some _ => false end.

Definition os_alias_add (x : string) (t : target) (sc : oscope) : oscope :=
  os_mk ((x, t) :: os_alias sc) (os_units sc).

Definition os_unit_add (fp : list string) (sc : oscope) : oscope :=
  os_mk (os_alias sc) (fp :: os_units sc).

Definition os_has_unit (fp : list string) (sc : oscope) : bool :=
  List.existsb (path_beq fp) (os_units sc).

Definition of_new (xs : list string) (Δ : ctx) (ip : list string) : oframe :=
  {| of_names := ef_mk xs em_nil; of_params := Δ; of_cmds := nil; of_scope := os_mk nil nil;
     of_path := ip |}.

(** The parameter variables of the frames [fs], outermost first, seen [off]
    binders in.  A member of the innermost frame is applied to them. *)
Definition fr_tele_len (fs : list oframe) : nat :=
  List.fold_right (fun f n => List.length (of_params f) + n) 0 fs.

Definition param_vars (off n : nat) : list exp :=
  List.map (fun i => a_var (off + (n - 1 - i))) (List.seq 0 n).

(** ** Terms *)

(** A path into an imported unit, with the arguments supplied so far. *)
Definition mr_opaque (fp mems : list string) (args : list exp) : mref :=
  {| mr_unit := fp; mr_mems := mems; mr_mod := None;
     mr_public := true; mr_args := args |}.

(** A dotted name resolves to a term or to a module. *)
Inductive res : Set :=
| r_exp : exp -> res
| r_mod : mref -> res.

(** An opaque path is a term if it names a member at all. *)
Definition res_term (r : eres res) : eres exp :=
  match r with
  | eok (r_exp M) => eok M
  | eok (r_mod mr) =>
      match mr_mod mr, mr_mems mr with
      | None, _ :: _ => eok (sc_apply (a_glob {| p_unit := mr_unit mr; p_mems := mr_mems mr |}) (mr_args mr))
      | None, nil => eerr "a unit is not a term"
      | Some _, _ => eerr "a module is not a term"
      end
  | eerr e => eerr e
  end.

Definition res_mod (r : eres res) : eres mref :=
  match r with
  | eok (r_mod mr) => eok mr
  | eok (r_exp _) => eerr "a term is not a module"
  | eerr e => eerr e
  end.

(** The definition [x] of the module [mr], with [args] more arguments.  It is
    a closed constant, so any number of arguments is allowed. *)
Definition mr_def (mr : mref) (x : string) (args : list exp) : eres res :=
  let args' := List.app (mr_args mr) args in
  eok (r_exp (sc_apply (a_glob {| p_unit := mr_unit mr; p_mems := List.app (mr_mems mr) (x :: nil) |}) args')).

(** A member of a module that is not open; only a public one can be named. *)
Definition mr_member (mr : mref) (x : string) (args : list exp) : eres res :=
  let args' := List.app (mr_args mr) args in
  let mems' := List.app (mr_mems mr) (x :: nil) in
  match mr_mod mr with
  | None =>
      (* REVISIT: privacy of imported members *)
      eok (r_mod {| mr_unit := mr_unit mr; mr_mems := mems'; mr_mod := None;
                    mr_public := true; mr_args := args' |})
  | Some Φ =>
      match em_lookup x Φ with
      | None => eerr ("no member " ++ x)
      | Some (en_def pv) =>
          let* _ := echeck (negb (mr_public mr && pv)) (x ++ " is private") in
          mr_def mr x args
      | Some (en_mod n Φx) =>
          eok (r_mod {| mr_unit := mr_unit mr; mr_mems := mems'; mr_mod := Some Φx;
                        mr_public := true; mr_args := args' |})
      end
  end.

Definition mr_apply (mr : mref) (args : list exp) : mref :=
  {| mr_unit := mr_unit mr; mr_mems := mr_mems mr; mr_mod := mr_mod mr;
     mr_public := mr_public mr; mr_args := List.app (mr_args mr) args |}.

Definition tg_use (t : target) (args : list exp) : eres res :=
  match t with
  | tg_mod mr => eok (r_mod (mr_apply mr args))
  (** [x] was checked to be a public definition when the alias was made. *)
  | tg_mem mr x => mr_def mr x args
  end.

(** A name looked up in the open frames: an alias, then any member, then a
    parameter.  [off] counts the binders between the use site and the
    current frame's parameters, past which an alias's arguments are weakened.
    [fp] is the unit's own path. *)
Definition tg_local (off : nat) (t : target) : target :=
  match t with
  | tg_mod mr => tg_mod (mr_weaken off 0 mr)
  | tg_mem mr y => tg_mem (mr_weaken off 0 mr) y
  end.

Fixpoint fr_lookup (fp : list string) (os : oscope) (off : nat) (x : string) (fs : list oframe) (args : list exp)
  : eres res :=
  match fs with
  | nil =>
      match alias_lookup x (os_alias os) with
      | Some t => tg_use (tg_local off t) args
      | None => eerr ("unbound name " ++ x)
      end
  | f :: fs' =>
      match alias_lookup x (of_alias f) with
      | Some t => tg_use (tg_local off t) args
      | None =>
          let vs := param_vars off (fr_tele_len fs) in
          match em_lookup x (ef_mod (of_names f)) with
          | Some (en_def _) =>
              eok (r_exp (sc_apply (a_glob (p_abs fp (List.app (of_path f) (x :: nil)))) (List.app vs args)))
          | Some (en_mod n Φ) =>
              eok (r_mod {| mr_unit := fp; mr_mems := List.app (of_path f) (x :: nil); mr_mod := Some Φ;
                            mr_public := true; mr_args := List.app vs args |})
          | None =>
              match index_of x (ef_params (of_names f)) with
              | Some k => eok (r_exp (sc_apply (a_var (off + k)) args))
              | None => fr_lookup fp os (off + List.length (of_params f)) x fs' args
              end
          end
      end
  end.

(** A unit is named by its full path only where it has been imported. *)
Definition unit_reachable (os : oscope) (fs : list oframe) (fp : list string) : bool :=
  os_has_unit fp os || List.existsb (fun f => os_has_unit fp (of_scope f)) fs.

Section Terms.
  Variable (fp : list string) (os : oscope) (fs : list oframe).

  (** [args] are the arguments the object is applied to, outermost last; the
      head of the spine decides whether they are module arguments. *)
  Fixpoint elab_res (ls : lscope) (d : nat) (o : Cst.obj) (args : list exp) : eres res :=
    match o with
    | Cst.typ n => eok (r_exp (sc_apply Type@n args))
    | Cst.nat => eok (r_exp (sc_apply ℕ args))
    | Cst.zero => eok (r_exp (sc_apply zero args))
    | Cst.succ o =>
        let* M := res_term (elab_res ls d o nil) in
        eok (r_exp (sc_apply (succ M) args))
    | Cst.natrec on mx om oz sx sr os =>
        let* N := res_term (elab_res ls d on nil) in
        let* A := res_term (elab_res (ls_push mx d ls) (S d) om nil) in
        let* MZ := res_term (elab_res ls d oz nil) in
        let* MS := res_term (elab_res (ls_push sr (S d) (ls_push sx d ls)) (S (S d)) os nil) in
        eok (r_exp (sc_apply (rec N return A | zero -> MZ | succ -> MS end) args))
    | Cst.true_ty => eok (r_exp (sc_apply ⊤ args))
    | Cst.true_tm => eok (r_exp (sc_apply ⋆ args))
    | Cst.false_ty => eok (r_exp (sc_apply ⊥ args))
    | Cst.exfalso om mx oA =>
        let* M := res_term (elab_res ls d om nil) in
        let* A := res_term (elab_res (ls_push mx d ls) (S d) oA nil) in
        eok (r_exp (sc_apply (efq M return A) args))
    | Cst.pi x oA oB =>
        let* A := res_term (elab_res ls d oA nil) in
        let* B := res_term (elab_res (ls_push x d ls) (S d) oB nil) in
        eok (r_exp (sc_apply (Π A B) args))
    | Cst.fn x oA oM =>
        let* A := res_term (elab_res ls d oA nil) in
        let* M := res_term (elab_res (ls_push x d ls) (S d) oM nil) in
        eok (r_exp (sc_apply (λ A M) args))
    | Cst.app o1 o2 =>
        let* N := res_term (elab_res ls d o2 nil) in
        elab_res ls d o1 (N :: args)
    | Cst.var x =>
        match ls_lookup x ls with
        | Some (le_term M n) => eok (r_exp (sc_apply (sc_shift d n M) args))
        | Some (le_mod mr n) => eok (r_mod (mr_apply (mr_weaken d n mr) args))
        | None => fr_lookup fp os d x fs args
        end
    | Cst.glob fp =>
        let* _ := echeck (unit_reachable os fs fp) "the unit is not imported" in
        eok (r_mod (mr_opaque fp nil args))
    | Cst.proj o1 x =>
        let* mr := res_mod (elab_res ls d o1 nil) in
        mr_member mr x args
    | Cst.letb (Cst.d_def m x oA oM) obody =>
        let* A := res_term (elab_res ls d oA nil) in
        let* M := res_term (elab_res ls d oM nil) in
        let e := if Cst.md_abstract m then le_term #0 (S d) else le_term M d in
        let* B := res_term (elab_res ((x, e) :: ls) (S d) obody nil) in
        eok (r_exp (sc_apply ((λ A B) $ M) args))
    (** A local module binding names the module and emits nothing. *)
    | Cst.letb (Cst.d_mod x oE) obody =>
        let* mr := res_mod (elab_res ls d oE nil) in
        let* M := res_term (elab_res ((x, le_mod mr d) :: ls) d obody nil) in
        eok (r_exp (sc_apply M args))
    end.

  Definition elab (o : Cst.obj) : eres exp := res_term (elab_res nil 0 o nil).

  (** A parameter telescope: each type sees the parameters before it as
      λ-variables. *)
  Fixpoint elab_params (ls : lscope) (d : nat) (ps : list (string * Cst.obj)) (Δ : ctx) : eres ctx :=
    match ps with
    | nil => eok Δ
    | (x, oA) :: ps' =>
        let* A := res_term (elab_res ls d oA nil) in
        elab_params (ls_push x d ls) (S d) ps' (Δ ▹ A)
    end.
End Terms.

(** ** Commands

    The state of a unit being elaborated: the open frames, innermost first,
    and the commands emitted before the unit's declaration, last first. *)
Record ustate : Set := us_mk
  { us_unit : list string
  ; us_outer : oscope
  ; us_frames : list oframe
  ; us_imps : list ccmd }.

Definition us_top (st : ustate) (f : oframe -> eres oframe) : eres ustate :=
  match us_frames st with
  | g :: gs => let* g' := f g in eok (us_mk (us_unit st) (us_outer st) (g' :: gs) (us_imps st))
  | nil => eerr "outside of any module"
  end.

(** The member chain of the innermost frame. *)
Definition us_path (st : ustate) : list string :=
  match us_frames st with
  | g :: _ => of_path g
  | nil => nil
  end.

(** An import goes into the innermost frame, or, before the unit's
    declaration, into the scope outside it. *)
Definition us_scope (st : ustate) (oc : option ccmd) (f : oscope -> eres oscope) : eres ustate :=
  let cons_opt cs := match oc with Some c => c :: cs | None => cs end in
  match us_frames st with
  | g :: gs =>
      let* sc := f (of_scope g) in
      eok (us_mk (us_unit st) (us_outer st)
             ({| of_names := of_names g; of_params := of_params g;
                 of_cmds := cons_opt (of_cmds g); of_scope := sc; of_path := of_path g |} :: gs)
             (us_imps st))
  | nil => let* sc := f (us_outer st) in eok (us_mk (us_unit st) sc nil (cons_opt (us_imps st)))
  end.

(** A definition is elaborated against the members before it, and becomes one. *)
Definition elab_def (st : ustate) (m : Cst.mods) (x : string) (oA oM : Cst.obj) : eres ustate :=
  us_top st (fun f =>
    let* _ := echeck (of_fresh x f) (x ++ " is already declared") in
    let* A := elab (us_unit st) (us_outer st) (us_frames st) oA in
    let* M := elab (us_unit st) (us_outer st) (us_frames st) oM in
    eok (of_add x (en_def (Cst.md_private m))
           (cc_def x (negb (Cst.md_abstract m)) (Cst.md_private m) A M) f)).

Definition elab_eval (st : ustate) (oM : Cst.obj) (oA : option Cst.obj) : eres ustate :=
  us_top st (fun f =>
    let* M := elab (us_unit st) (us_outer st) (us_frames st) oM in
    let* A := match oA with
              | None => eok None
              | Some oA => let* A := elab (us_unit st) (us_outer st) (us_frames st) oA in eok (Some A)
              end in
    eok {| of_names := of_names f; of_params := of_params f;
           of_cmds := cc_eval M A :: of_cmds f; of_scope := of_scope f; of_path := of_path f |}).

(** An import binds names: a unit's full path, and the names given with
    [as] or [use].  Only an import of another unit emits a command. *)
Definition import_target (st : ustate) (fp ip : list string) : eres mref :=
  match fp, ip with
  | nil, x :: ip' =>
      res_mod (elab_res (us_unit st) (us_outer st) (us_frames st) nil 0
                 (List.fold_left Cst.proj ip' (Cst.var x)) nil)
  | nil, nil => eerr "nothing to import"
  | _, _ => eok (mr_opaque fp ip nil)
  end.

(** [use n]: the name [n] for the member [n] of [mr]. *)
Definition use_bind (taken : string -> bool) (mr : mref) (acc : eres oscope) (n : string) : eres oscope :=
  let* sc := acc in
  let* _ := echeck (negb (taken n) && os_fresh n sc) (n ++ " is already declared") in
  match mr_mod mr with
  | None =>
      (* REVISIT: privacy of imported members *)
      eok (os_alias_add n
             (tg_mod {| mr_unit := mr_unit mr; mr_mems := List.app (mr_mems mr) (n :: nil);
                        mr_mod := None; mr_public := true;
                        mr_args := mr_args mr |}) sc)
  | Some Φ =>
      match em_lookup n Φ with
      | Some (en_def pv) =>
          let* _ := echeck (negb (mr_public mr && pv)) (n ++ " is private") in
          eok (os_alias_add n (tg_mem mr n) sc)
      | Some (en_mod k Φn) =>
          eok (os_alias_add n
                 (tg_mod {| mr_unit := mr_unit mr; mr_mems := List.app (mr_mems mr) (n :: nil);
                            mr_mod := Some Φn; mr_public := true;
                            mr_args := mr_args mr |}) sc)
      | None => eerr ("no member " ++ n)
      end
  end.

(** What an import of [mr] from the unit [fp] binds in the scope [sc].  Each
    name must be neither an alias of [sc] nor [taken]. *)
Definition import_binds (taken : string -> bool) (fp : list string) (mr : mref) (spec : Cst.ispec)
  (sc : oscope) : eres oscope :=
  let sc := match fp with nil => sc | _ => os_unit_add fp sc end in
  match spec with
  | Cst.i_open => eok sc
  | Cst.i_as y =>
      let* _ := echeck (negb (taken y) && os_fresh y sc) (y ++ " is already declared") in
      eok (os_alias_add y (tg_mod mr) sc)
  | Cst.i_use ns => List.fold_left (use_bind taken mr) ns (eok sc)
  end.

Definition elab_import (st : ustate) (fp ip : list string) (spec : Cst.ispec) : eres ustate :=
  let* mr := import_target st fp ip in
  let oc := match fp with nil => None | _ => Some (cc_import fp ip) end in
  (* before the unit's declaration there is no frame, so nothing is taken but
     the earlier aliases *)
  let taken := match us_frames st with g :: _ => fun y => of_taken y g | nil => fun _ => false end in
  us_scope st oc (import_binds taken fp mr spec).

(** Opening a module pushes its frame; closing it pops the frame and makes the
    module a member of the frame outside. *)
Definition us_open (st : ustate) (f : oframe) : ustate :=
  us_mk (us_unit st) (us_outer st) (f :: us_frames st) (us_imps st).

Definition us_close (x : string) (st : ustate) : eres ustate :=
  match us_frames st with
  | f :: g :: gs =>
      let en := en_mod (List.length (ef_params (of_names f))) (ef_mod (of_names f)) in
      let c := cc_mod x (of_params f) (List.rev (of_cmds f)) in
      eok (us_mk (us_unit st) (us_outer st) (of_add x en c g :: gs) (us_imps st))
  | _ => eerr "no module to close"
  end.

(** The loop over a module body is an inner [fix], since the body is nested
    in a [list].  [module A.B] opens [A], without parameters, and [B] inside
    it.  A declared module cannot be reopened, because later commands may
    depend on its members. *)
Fixpoint elab_cmd (st : ustate) (c : Cst.cmd) : eres ustate :=
  match c with
  | Cst.c_mod p ps body =>
      let go := fix go (st : ustate) (cs : list Cst.cmd) : eres ustate :=
                  match cs with
                  | nil => eok st
                  | c :: cs' => let* st' := elab_cmd st c in go st' cs'
                  end in
      (fix open_path (p : list string) (st : ustate) : eres ustate :=
         match p with
         | nil => eerr "empty module name"
         | x :: p' =>
             let* _ := us_top st (fun f =>
                         let* _ := echeck (of_fresh x f) (x ++ " is already declared") in eok f) in
             let* f := match p' with
                       | nil =>
                           let* _ := check_params ps in
                           let* Δ := elab_params (us_unit st) (us_outer st) (us_frames st) nil 0 ps ⋅ in
                           eok (of_new (List.rev (List.map fst ps)) Δ (List.app (us_path st) (x :: nil)))
                       | _ => eok (of_new nil ⋅ (List.app (us_path st) (x :: nil)))
                       end in
             let* st1 := match p' with
                         | nil => go (us_open st f) body
                         | _ => open_path p' (us_open st f)
                         end in
             us_close x st1
         end) p st
  | Cst.c_def m x oA oM => elab_def st m x oA oM
  | Cst.c_eval oM oA => elab_eval st oM oA
  | Cst.c_import fp ip spec => elab_import st fp ip spec
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
  let* st0 := elab_cmds (us_mk fp (os_mk nil nil) nil nil) imports in
  let* _ := check_params ps in
  let* Δ := elab_params fp (us_outer st0) nil nil 0 ps ⋅ in
  let* st := elab_cmds (us_open st0 (of_new (List.rev (List.map fst ps)) Δ nil)) cs in
  match us_frames st with
  | f :: nil => eok (List.rev (us_imps st), of_params f, List.rev (of_cmds f))
  | _ => eerr "unbalanced modules"
  end.

Definition to_core (prg : Cst.prog) : option cunit :=
  match elaborate_core prg with
  | eok u => Some u
  | eerr _ => None
  end.


