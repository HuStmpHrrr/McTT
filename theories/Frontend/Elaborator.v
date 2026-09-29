From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax GlobalCtx.
From Mctt.Frontend Require Import Resolve.

Import Syntax_Notations GlobalCtx_Notations.

Open Scope string_scope.

(** * Elaboration

    A compilation unit elaborates into the global context: given the units
    already filed, [Θ], it produces its own [gunit], to be filed next, and one
    obligation per [eval].  A definition becomes a [ge_def] of the frame it is
    declared in, a nested module a [ge_mod]; a name becomes a parameter
    [$[n, k]], a member [a_glob] (relative for the open frames, absolute for a
    filed unit), or a λ-variable.  An [eval] is checked where it stands: on the
    stack of frames as they are at that point. *)

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

    A frame being elaborated: its names, the frame itself, and what [import]
    declared in it — aliases, and the units it made reachable by their full
    path.  The imports that precede a unit's declaration are outside all of its
    frames, in an [oscope] of their own. *)
Record oscope : Set := os_mk
  { os_alias : list (string * target)
  ; os_units : list (list string) }.

Record oframe : Set := of_mk
  { of_names : eframe
  ; of_unit : gunit
  ; of_scope : oscope }.

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

(** A name not yet taken in a frame, by a member or an alias. *)
Definition of_fresh (x : string) (f : oframe) : bool :=
  match em_lookup x (ef_mod (of_names f)), alias_lookup x (of_alias f) with
  | None, None => true
  | _, _ => false
  end.

Definition of_add (x : string) (E : gentry) (en : ename) (f : oframe) : oframe :=
  {| of_names := ef_mk (ef_params (of_names f)) (em_ext (ef_mod (of_names f)) x en)
   ; of_unit := gu_mk (gu_params (of_unit f)) (gu_mod (of_unit f) ⊳ x ↦ E)
   ; of_scope := of_scope f |}.

Definition os_fresh (x : string) (sc : oscope) : bool :=
  match alias_lookup x (os_alias sc) with None => true | Some _ => false end.

Definition os_alias_add (x : string) (t : target) (sc : oscope) : oscope :=
  os_mk ((x, t) :: os_alias sc) (os_units sc).

Definition os_unit_add (fp : list string) (sc : oscope) : oscope :=
  os_mk (os_alias sc) (fp :: os_units sc).

Definition os_has_unit (fp : list string) (sc : oscope) : bool :=
  List.existsb (path_beq fp) (os_units sc).

Definition of_new (xs : list string) (Δ : ctx) : oframe :=
  {| of_names := ef_mk xs em_nil; of_unit := gu_mk Δ gm_nil; of_scope := os_mk nil nil |}.

(** ** Terms *)

(** Resolving a dotted name gives a term or a module, the latter with the
    module arguments supplied so far. *)
Inductive res : Set :=
| r_exp : exp -> res
| r_mod : mref -> res.

Definition res_term (r : eres res) : eres exp :=
  match r with
  | eok (r_exp M) => eok M
  | eok (r_mod _) => eerr "a module is not a term"
  | eerr e => eerr e
  end.

Definition res_mod (r : eres res) : eres mref :=
  match r with
  | eok (r_mod mr) => eok mr
  | eok (r_exp _) => eerr "a term is not a module"
  | eerr e => eerr e
  end.

(** A member of a module that is not open: only a public one can be named, and
    only once the closed modules crossed have their arguments. *)
Definition mr_member (mr : mref) (x : string) (args : list exp) : eres res :=
  match em_lookup x (mr_mod mr) with
  | None => eerr ("no member " ++ x)
  | Some (en_def pv) =>
      let args' := List.app (mr_args mr) args in
      let* _ := echeck (negb (mr_public mr && pv)) (x ++ " is private") in
      let* _ := echeck (Nat.leb (mr_arity mr) (List.length args'))
                  ("module arguments missing for " ++ x) in
      eok (r_exp (sc_apply (a_glob {| p_qual := mr_qual mr; p_mems := List.app (mr_mems mr) (x :: nil) |}) args'))
  | Some (en_mod n Φ) =>
      eok (r_mod {| mr_qual := mr_qual mr; mr_mems := List.app (mr_mems mr) (x :: nil); mr_mod := Φ;
                    mr_public := true; mr_arity := mr_arity mr + n; mr_args := List.app (mr_args mr) args |})
  end.

Definition mr_apply (mr : mref) (args : list exp) : mref :=
  {| mr_qual := mr_qual mr; mr_mems := mr_mems mr; mr_mod := mr_mod mr;
     mr_public := mr_public mr; mr_arity := mr_arity mr; mr_args := List.app (mr_args mr) args |}.

Definition tg_use (t : target) (args : list exp) : eres res :=
  match t with
  | tg_mod mr => eok (r_mod (mr_apply mr args))
  | tg_mem mr x => mr_member mr x args
  end.

(** A name looked up in the open frames, from [i] frames in: an alias, then a
    member — any member, private or not, the frame being open — then a
    parameter. *)
Definition tg_local (d i : nat) (t : target) : target :=
  match tg_shift i t with
  | tg_mod mr => tg_mod (mr_weaken d 0 mr)
  | tg_mem mr y => tg_mem (mr_weaken d 0 mr) y
  end.

Fixpoint fr_lookup (os : oscope) (d : nat) (x : string) (i : nat) (fs : list oframe) (args : list exp)
  : eres res :=
  match fs with
  | nil =>
      match alias_lookup x (os_alias os) with
      | Some t => tg_use (tg_local d i t) args
      | None => eerr ("unbound name " ++ x)
      end
  | f :: fs' =>
      match alias_lookup x (of_alias f) with
      | Some t => tg_use (tg_local d i t) args
      | None =>
          match em_lookup x (ef_mod (of_names f)) with
          | Some (en_def _) => eok (r_exp (sc_apply (a_glob (p_rel i (x :: nil))) args))
          | Some (en_mod n Φ) =>
              eok (r_mod {| mr_qual := qu_rel i; mr_mems := x :: nil; mr_mod := Φ;
                            mr_public := true; mr_arity := n; mr_args := args |})
          | None =>
              match index_of x (ef_params (of_names f)) with
              | Some k => eok (r_exp (sc_apply $[i, k] args))
              | None => fr_lookup os d x (S i) fs' args
              end
          end
      end
  end.

(** A filed unit is closed: its parameters are among what a use of its
    members has to supply. *)
Definition unit_mref (Θ : gdeps) (fp : list string) (args : list exp) : eres mref :=
  match gds_lookup Θ fp with
  | Some U =>
      eok {| mr_qual := qu_abs fp; mr_mems := nil; mr_mod := gm_erase (gu_mod U);
             mr_public := true; mr_arity := List.length (gu_params U); mr_args := args |}
  | None => eerr "unknown unit"
  end.

(** A unit is named by its full path only where it has been imported. *)
Definition unit_reachable (os : oscope) (fs : list oframe) (fp : list string) : bool :=
  os_has_unit fp os || List.existsb (fun f => os_has_unit fp (of_scope f)) fs.

Section Terms.
  Variable (Θ : gdeps) (os : oscope) (fs : list oframe).

  (** [args] are the arguments the object is applied to, outermost last, so
      that the head of a spine decides whether they are module arguments. *)
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
        | None => fr_lookup os d x 0 fs args
        end
    | Cst.glob fp =>
        let* _ := echeck (unit_reachable os fs fp) "the unit is not imported" in
        let* mr := unit_mref Θ fp args in
        eok (r_mod mr)
    | Cst.proj o1 x =>
        let* mr := res_mod (elab_res ls d o1 nil) in
        mr_member mr x args
    | Cst.letb (Cst.d_def m x oA oM) obody =>
        let* A := res_term (elab_res ls d oA nil) in
        let* M := res_term (elab_res ls d oM nil) in
        let e := if Cst.md_abstract m then le_term #0 (S d) else le_term M d in
        let* B := res_term (elab_res ((x, e) :: ls) (S d) obody nil) in
        eok (r_exp (sc_apply ((λ A B) $ M) args))
    (** A local module binding emits nothing: it names the module, with its
        arguments. *)
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
    and the [eval] obligations so far, each with the stack it is checked on. *)
Definition eval_obl : Set := (gstack * exp * option typ)%type.

Record ustate : Set := us_mk
  { us_outer : oscope
  ; us_frames : list oframe
  ; us_evals : list eval_obl }.

Definition us_stack (st : ustate) : gstack := List.map of_unit (us_frames st).

Definition us_top (st : ustate) (f : oframe -> eres oframe) : eres ustate :=
  match us_frames st with
  | g :: gs => let* g' := f g in eok (us_mk (us_outer st) (g' :: gs) (us_evals st))
  | nil => eerr "outside of any module"
  end.

(** What [import] declares goes into the innermost frame, or before the unit's
    declaration into the scope outside it. *)
Definition us_scope (st : ustate) (f : oscope -> eres oscope) : eres ustate :=
  match us_frames st with
  | g :: gs =>
      let* sc := f (of_scope g) in
      eok (us_mk (us_outer st) ({| of_names := of_names g; of_unit := of_unit g; of_scope := sc |} :: gs)
             (us_evals st))
  | nil => let* sc := f (us_outer st) in eok (us_mk sc nil (us_evals st))
  end.

(** A definition is checked against the members before it, and becomes one. *)
Definition elab_def (Θ : gdeps) (st : ustate) (m : Cst.mods) (x : string) (oA oM : Cst.obj)
  : eres ustate :=
  us_top st (fun f =>
    let* _ := echeck (of_fresh x f) (x ++ " is already declared") in
    let* A := elab Θ (us_outer st) (us_frames st) oA in
    let* M := elab Θ (us_outer st) (us_frames st) oM in
    eok (of_add x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))
           (en_def (Cst.md_private m)) f)).

Definition elab_eval (Θ : gdeps) (st : ustate) (oM : Cst.obj) (oA : option Cst.obj) : eres ustate :=
  let* M := elab Θ (us_outer st) (us_frames st) oM in
  let* A := match oA with
            | None => eok None
            | Some oA => let* A := elab Θ (us_outer st) (us_frames st) oA in eok (Some A)
            end in
  eok (us_mk (us_outer st) (us_frames st) (List.app (us_evals st) ((us_stack st, M, A) :: nil))).

(** [import] binds names only: the module's full path, for a unit, and with
    [as] or [use] the names given. *)
Definition elab_import (Θ : gdeps) (st : ustate) (fp ip : list string) (spec : Cst.ispec)
  : eres ustate :=
  let* mr := match fp, ip with
             | nil, x :: ip' =>
                 res_mod (elab_res Θ (us_outer st) (us_frames st) nil 0
                            (List.fold_left Cst.proj ip' (Cst.var x)) nil)
             | nil, nil => eerr "nothing to import"
             | _, _ =>
                 let* mr := unit_mref Θ fp nil in
                 List.fold_left (fun acc x => let* mr := acc in res_mod (mr_member mr x nil))
                   ip (eok mr)
             end in
  us_scope st (fun sc =>
    let sc := match fp with nil => sc | _ => os_unit_add fp sc end in
    match spec with
    | Cst.i_open => eok sc
    | Cst.i_as y =>
        let* _ := echeck (os_fresh y sc) (y ++ " is already declared") in
        eok (os_alias_add y (tg_mod mr) sc)
    | Cst.i_use ns =>
        List.fold_left
          (fun acc n =>
             let* sc := acc in
             let* _ := echeck (os_fresh n sc) (n ++ " is already declared") in
             match em_lookup n (mr_mod mr) with
             | Some (en_def pv) =>
                 let* _ := echeck (negb (mr_public mr && pv)) (n ++ " is private") in
                 eok (os_alias_add n (tg_mem mr n) sc)
             | Some (en_mod k Φ) =>
                 eok (os_alias_add n
                        (tg_mod {| mr_qual := mr_qual mr; mr_mems := List.app (mr_mems mr) (n :: nil);
                                   mr_mod := Φ; mr_public := true; mr_arity := mr_arity mr + k;
                                   mr_args := mr_args mr |}) sc)
             | None => eerr ("no member " ++ n)
             end)
          ns (eok sc)
    end).

(** Opening a module pushes its frame; closing it pops the frame and files it
    as a member of the one outside. *)
Definition us_open (st : ustate) (f : oframe) : ustate :=
  us_mk (us_outer st) (f :: us_frames st) (us_evals st).

Definition us_close (x : string) (st : ustate) : eres ustate :=
  match us_frames st with
  | f :: g :: gs =>
      let E := ge_mod (gu_params (of_unit f)) (gu_mod (of_unit f)) in
      let en := en_mod (List.length (gu_params (of_unit f))) (ef_mod (of_names f)) in
      eok (us_mk (us_outer st) (of_add x E en g :: gs) (us_evals st))
  | _ => eerr "no module to close"
  end.

(** The loop over a module body is an inner [fix]: the body sits under a
    [list], which neither mutual recursion nor a recursion on the list gets
    past the guard condition.  [module A.B] opens [A], with no parameters, and
    [B] inside it; a name already declared cannot be reopened, since what
    follows it may already depend on its members. *)
Fixpoint elab_cmd (Θ : gdeps) (st : ustate) (c : Cst.cmd) : eres ustate :=
  match c with
  | Cst.c_mod p ps body =>
      let go := fix go (st : ustate) (cs : list Cst.cmd) : eres ustate :=
                  match cs with
                  | nil => eok st
                  | c :: cs' => let* st' := elab_cmd Θ st c in go st' cs'
                  end in
      (fix open_path (p : list string) (st : ustate) : eres ustate :=
         match p with
         | nil => eerr "empty module name"
         | x :: p' =>
             let* _ := us_top st (fun f =>
                         let* _ := echeck (of_fresh x f) (x ++ " is already declared") in eok f) in
             let* f := match p' with
                       | nil =>
                           let* Δ := elab_params Θ (us_outer st) (us_frames st) nil 0 ps ⋅ in
                           eok (of_new (List.rev (List.map fst ps)) Δ)
                       | _ => eok (of_new nil ⋅)
                       end in
             let* st1 := match p' with
                         | nil => go (us_open st f) body
                         | _ => open_path p' (us_open st f)
                         end in
             us_close x st1
         end) p st
  | Cst.c_def m x oA oM => elab_def Θ st m x oA oM
  | Cst.c_eval oM oA => elab_eval Θ st oM oA
  | Cst.c_import fp ip spec => elab_import Θ st fp ip spec
  end.

Fixpoint elab_cmds (Θ : gdeps) (st : ustate) (cs : list Cst.cmd) : eres ustate :=
  match cs with
  | nil => eok st
  | c :: cs' => let* st' := elab_cmd Θ st c in elab_cmds Θ st' cs'
  end.

(** ** Units

    A unit, elaborated against the units filed so far: its imports, outside
    of its frame; its parameters, which see them; then its body in its frame,
    which is what is filed under its path. *)
Definition elaborate_prog (Θ : gdeps) (prg : Cst.prog)
  : eres ((list string * gunit) * list eval_obl)%type :=
  let '(imports, (fp, ps, cs)) := prg in
  let* _ := echeck (match gds_lookup Θ fp with None => true | Some _ => false end)
              "the unit is already filed" in
  let* st0 := elab_cmds Θ (us_mk (os_mk nil nil) nil nil) imports in
  let* Δ := elab_params Θ (us_outer st0) nil nil 0 ps ⋅ in
  let* st := elab_cmds Θ (us_open st0 (of_new (List.rev (List.map fst ps)) Δ)) cs in
  match us_frames st with
  | f :: nil => eok ((fp, of_unit f), us_evals st)
  | _ => eerr "unbalanced modules"
  end.

(** ** User Expressions

    The expressions the type checker is willing to be given.  Every [exp] is one:
    the distinction the predicate used to make disappeared when substitution
    stopped being a constructor, and it is kept only because [type_check_closed]
    is indexed by it. *)
Generalizable All Variables.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp (a_typ i) )
| user_exp_nat :
  `( user_exp a_nat )
| user_exp_zero :
  `( user_exp a_zero )
| user_exp_succ :
  `( user_exp M ->
     user_exp (a_succ M) )
| user_exp_natrec :
  `( user_exp A ->
     user_exp MZ ->
     user_exp MS ->
     user_exp M ->
     user_exp (a_natrec A MZ MS M) )
| user_exp_pi :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_pi A B) )
| user_exp_fn :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_fn A M) )
| user_exp_app :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_app M N) )
| user_exp_vlookup :
  `( user_exp (a_var x) )
| user_exp_param :
  `( user_exp (a_param lp) )
| user_exp_glob :
  `( user_exp (a_glob p) ).

#[export]
Hint Constructors user_exp : mctt.

Lemma user_exp_all : forall M, user_exp M.
Proof.
  induction M; mauto 3.
Qed.

#[export]
Hint Resolve user_exp_all : mctt.

Lemma user_exp_nf : forall M, user_exp (nf_to_exp M)
with user_exp_ne : forall M, user_exp (ne_to_exp M).
Proof.
  - clear user_exp_nf; induction M; mauto 3.
  - clear user_exp_ne; induction M; mauto 3.
Qed.

