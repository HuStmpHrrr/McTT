From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Frontend Require Import Resolve.

Import Syntax_Notations.

Open Scope string_scope.

(** * Elaboration

    Elaboration turns a whole compilation unit into a single closed expression
    together with its type; see [Frontend.Resolve] for the two things a name can
    resolve to and for how the definition telescope is used. *)

(** ** Objects

    Resolving a dotted name gives either a term or a module, and in the latter
    case the module arguments supplied so far still have to be carried along, to
    be prepended to the arguments of whichever member is eventually selected. *)
Inductive res : Set :=
| r_exp : exp -> res
| r_ent : entry -> list exp -> res.

(** A module is not a term, and an under-applied member is not one either. *)
Definition res_term (d : nat) (r : option res) : option exp :=
  match r with
  | Some (r_exp M) => Some M
  | Some (r_ent (e_val v) args) => sc_use d v args
  | _ => None
  end.

(** [args] are the arguments the elaborated object is applied to, outermost
    last; they are threaded through so that the head of an application spine can
    decide whether they are module arguments or ordinary ones. *)
Fixpoint elab_res (s : scope) (d : nat) (o : Cst.obj) (args : list exp) : option res :=
  match o with
  | Cst.typ n => Some (r_exp (sc_apply Type@n args))
  | Cst.nat => Some (r_exp (sc_apply ℕ args))
  | Cst.zero => Some (r_exp (sc_apply zero args))
  | Cst.succ o =>
      match res_term d (elab_res s d o nil) with
      | Some M => Some (r_exp (sc_apply (succ M) args))
      | None => None
      end
  | Cst.natrec on mx om oz sx sr os =>
      match res_term d (elab_res s d on nil),
            res_term (S d) (elab_res (sc_push mx d s) (S d) om nil),
            res_term d (elab_res s d oz nil),
            res_term (S (S d)) (elab_res (sc_push sr (S d) (sc_push sx d s)) (S (S d)) os nil) with
      | Some N, Some A, Some MZ, Some MS =>
          Some (r_exp (sc_apply (rec N return A | zero -> MZ | succ -> MS end) args))
      | _, _, _, _ => None
      end
  | Cst.pi x oA oB =>
      match res_term d (elab_res s d oA nil),
            res_term (S d) (elab_res (sc_push x d s) (S d) oB nil) with
      | Some A, Some B => Some (r_exp (sc_apply (Π A B) args))
      | _, _ => None
      end
  | Cst.fn x oA oM =>
      match res_term d (elab_res s d oA nil),
            res_term (S d) (elab_res (sc_push x d s) (S d) oM nil) with
      | Some A, Some M => Some (r_exp (sc_apply (λ A M) args))
      | _, _ => None
      end
  | Cst.app o1 o2 =>
      match res_term d (elab_res s d o2 nil) with
      | Some N => elab_res s d o1 (N :: args)
      | None => None
      end
  | Cst.var x =>
      match sc_lookup x s with
      | Some e => Some (r_ent e args)
      | None => None
      end
  (** Only a module has members, and the arguments it was given come first. *)
  | Cst.proj o1 x =>
      match elab_res s d o1 nil with
      | Some (r_ent (e_mod _ ms) margs) =>
          match sc_lookup x ms with
          | Some e => Some (r_ent e (List.app margs args))
          | None => None
          end
      | _ => None
      end
  | Cst.letb (Cst.d_def m x oA oM) obody =>
      match res_term d (elab_res s d oA nil), res_term d (elab_res s d oM nil) with
      | Some A, Some M =>
          let v := v_bind (Cst.md_abstract m) d 0 false M in
          match res_term (S d) (elab_res (sc_cons x (e_val v) s) (S d) obody nil) with
          | Some B => Some (r_exp (sc_apply ((λ A B) $ M) args))
          | None => None
          end
      | _, _ => None
      end
  (** A local module binding emits nothing at all: the arguments are baked into
      the members and the alias is recorded. *)
  | Cst.letb (Cst.d_mod x oE) obody =>
      match elab_res s d oE nil with
      | Some (r_ent (e_mod n ms) margs) =>
          match sc_fix d margs ms with
          | Some ms' =>
              match res_term d (elab_res (sc_cons x (e_mod n ms') s) d obody nil) with
              | Some M => Some (r_exp (sc_apply M args))
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  end.

Definition elab (s : scope) (d : nat) (o : Cst.obj) : option exp :=
  res_term d (elab_res s d o nil).

(** ** Commands

    A unit is elaborated left to right.  [u_frame] holds what the module
    currently being elaborated has declared, [u_outer] what it inherited; the
    telescope and the depth are shared by the whole unit, since every definition
    anywhere in it contributes one binder to the same nest. *)
Record ustate : Set :=
  { u_outer : scope
  ; u_frame : scope
  ; u_depth : nat
  ; u_tele : list (exp * exp)
  ; u_evals : list ((option typ * exp)%type)
  ; u_idepth : nat }.

Definition u_init : ustate :=
  {| u_outer := sc_nil; u_frame := sc_nil; u_depth := 0; u_tele := nil;
     u_evals := nil; u_idepth := 0 |}.

Definition u_view (st : ustate) : scope := sc_app (u_frame st) (u_outer st).

(** Starting the body of a module: what the enclosing scope declared becomes
    inherited, and the import depth restarts at [0]. *)
Definition u_enter (st : ustate) : ustate :=
  {| u_outer := u_view st; u_frame := sc_nil; u_depth := u_depth st;
     u_tele := u_tele st; u_evals := u_evals st; u_idepth := 0 |}.

Definition u_push_eval (st : ustate) (e : (option typ * exp)%type) : ustate :=
  {| u_outer := u_outer st; u_frame := u_frame st; u_depth := u_depth st;
     u_tele := u_tele st; u_evals := List.app (u_evals st) (cons e nil);
     u_idepth := u_idepth st |}.

Definition u_refit (st : ustate) (fr : scope) (n : nat) : ustate :=
  {| u_outer := u_outer st; u_frame := fr; u_depth := u_depth st;
     u_tele := u_tele st; u_evals := u_evals st; u_idepth := n |}.

(** The parameters of the enclosing modules, prepended to a member's type and
    body as ordinary binders.  This is the whole of parameterization: a member of
    a parameterized module is a function, and [(X.Y.Z a b).foo] is [foo] applied
    to [a] and [b]. *)
Definition tele_pi (ps : list (string * Cst.obj)) (o : Cst.obj) : Cst.obj :=
  List.fold_right (fun p acc => Cst.pi (fst p) (snd p) acc) o ps.

Definition tele_fn (ps : list (string * Cst.obj)) (o : Cst.obj) : Cst.obj :=
  List.fold_right (fun p acc => Cst.fn (fst p) (snd p) acc) o ps.

(** The telescope becomes the nest [(λ A₁ (λ A₂ … $ M₂) $ M₁], entry [i] having
    been elaborated at depth [i].  A type mentioned inside the nest lives at its
    far end, so to be reported it has to be closed by the substitution the nest
    performs. *)
Definition tele_nest (t : list (exp * exp)) (M : exp) : exp :=
  List.fold_right (fun p body => (λ (fst p) body) $ (snd p)) M t.

Definition tele_close (t : list (exp * exp)) : sub :=
  List.fold_left (fun σ p => σ ,, (snd p)[σ]) t Id.

(** An identity function at [A], which is how an ascribed [eval] gets checked
    against its type *inside* the nest.  Doing it outside would check it against
    [A[tele_close]] instead, where every [abstract] definition [A] mentions has
    already been unfolded — the reported type does leak that way, but the check
    must not. *)
Definition ascribe (A M : exp) : exp := (λ A #0) $ M.

(** Leaving the body of a module: its members become reachable under [p], while
    the depth, the telescope and the obligations it accumulated stay. *)
Definition u_close (p : list string) (st st' : ustate) : ustate :=
  {| u_outer := u_outer st
   ; u_frame := sc_insert p (e_mod (u_idepth st') (u_frame st')) (u_frame st)
   ; u_depth := u_depth st'
   ; u_tele := u_tele st'
   ; u_evals := u_evals st'
   ; u_idepth := u_idepth st |}.

(** A definition contributes one telescope entry, and binds a name to it at the
    depth the entry was elaborated at. *)
Definition elab_def (ps : list (string * Cst.obj)) (st : ustate)
  (m : Cst.mods) (x : string) (oA oM : Cst.obj) : option ustate :=
  let d := u_depth st in
  match elab (u_view st) d (tele_pi ps oA), elab (u_view st) d (tele_fn ps oM) with
  | Some A, Some M =>
      Some {| u_outer := u_outer st
            ; u_frame :=
                sc_cons x
                  (e_val (v_bind (Cst.md_abstract m) d (List.length ps) (Cst.md_private m) M))
                  (u_frame st)
            ; u_depth := S d
            ; u_tele := List.app (u_tele st) (cons (A, M) nil)
            ; u_evals := u_evals st
            ; u_idepth := u_idepth st |}
  | _, _ => None
  end.

(** An [eval] declares nothing; it records one closed obligation, built from the
    definitions that precede it. *)
Definition elab_eval (st : ustate) (oM : Cst.obj) (oA : option Cst.obj) : option ustate :=
  let d := u_depth st in
  let t := u_tele st in
  match elab (u_view st) d oM with
  | Some M =>
      match oA with
      | None => Some (u_push_eval st (None, tele_nest t M))
      | Some oA =>
          match elab (u_view st) d oA with
          | Some A =>
              Some (u_push_eval st (Some A[tele_close t], tele_nest t (ascribe A M)))
          | None => None
          end
      end
  | None => None
  end.

(** [i_open] binds nothing: within one unit an imported module is already
    reachable under its full path.  All three forms do update the import depth,
    and both aliasing forms hide the private members. *)
Definition elab_import (st : ustate) (p : list string) (spec : Cst.ispec) : option ustate :=
  match sc_lookup_path p (u_view st) with
  | Some (e_mod n ms) =>
      let n' := Nat.max (u_idepth st) (S n) in
      match spec with
      | Cst.i_open => Some (u_refit st (u_frame st) n')
      | Cst.i_as y => Some (u_refit st (sc_cons y (e_mod n (sc_public ms)) (u_frame st)) n')
      | Cst.i_use ns =>
          match sc_take ns (sc_public ms) (u_frame st) with
          | Some fr => Some (u_refit st fr n')
          | None => None
          end
      end
  | _ => None
  end.

(** The loop over the members of a module is an inner [fix] rather than a call to
    [elab_cmds]: the body of a module sits under a [list], and neither mutual
    recursion (which would ask the guard condition to compare [Cst.cmd] with
    [list Cst.cmd]) nor a recursion on the list (which would ask it to see
    through the [list]) is accepted.  [elab_cmd_mod] discharges the duplication
    the inner [fix] creates. *)
Fixpoint elab_cmd (ps : list (string * Cst.obj)) (st : ustate) (c : Cst.cmd) : option ustate :=
  match c with
  | Cst.c_mod p params body =>
      match (fix go (st : ustate) (cs : list Cst.cmd) : option ustate :=
               match cs with
               | nil => Some st
               | c :: cs' =>
                   match elab_cmd (List.app ps params) st c with
                   | Some st' => go st' cs'
                   | None => None
                   end
               end) (u_enter st) body with
      | Some st' => Some (u_close p st st')
      | None => None
      end
  | Cst.c_def m x oA oM => elab_def ps st m x oA oM
  | Cst.c_eval oM oA => elab_eval st oM oA
  | Cst.c_import p spec => elab_import st p spec
  end.

Fixpoint elab_cmds (ps : list (string * Cst.obj)) (st : ustate) (cs : list Cst.cmd)
  : option ustate :=
  match cs with
  | nil => Some st
  | c :: cs' =>
      match elab_cmd ps st c with
      | Some st' => elab_cmds ps st' cs'
      | None => None
      end
  end.

(** The inner [fix] of [elab_cmd] and [elab_cmds] are the same loop, so a module
    is elaborated by elaborating its body in the entered state. *)
Lemma elab_cmds_go : forall cs ps st,
    (fix go (st : ustate) (cs : list Cst.cmd) : option ustate :=
       match cs with
       | nil => Some st
       | c :: cs' =>
           match elab_cmd ps st c with
           | Some st' => go st' cs'
           | None => None
           end
       end) st cs = elab_cmds ps st cs.
Proof.
  induction cs as [| c cs IHcs]; intros; simpl; [ reflexivity |].
  destruct (elab_cmd ps st c); [ apply IHcs | reflexivity ].
Qed.

Lemma elab_cmd_mod : forall ps st p params body,
    elab_cmd ps st (Cst.c_mod p params body) =
      match elab_cmds (List.app ps params) (u_enter st) body with
      | Some st' => Some (u_close p st st')
      | None => None
      end.
Proof.
  intros. rewrite <- elab_cmds_go. reflexivity.
Qed.

Lemma elab_cmd_def : forall ps st m x oA oM,
    elab_cmd ps st (Cst.c_def m x oA oM) = elab_def ps st m x oA oM.
Proof. reflexivity. Qed.

Lemma elab_cmd_eval : forall ps st oM oA,
    elab_cmd ps st (Cst.c_eval oM oA) = elab_eval st oM oA.
Proof. reflexivity. Qed.

Lemma elab_cmd_import : forall ps st p spec,
    elab_cmd ps st (Cst.c_import p spec) = elab_import st p spec.
Proof. reflexivity. Qed.

Lemma elab_cmds_cons : forall ps st c cs,
    elab_cmds ps st (cons c cs) =
      match elab_cmd ps st c with
      | Some st' => elab_cmds ps st' cs
      | None => None
      end.
Proof. reflexivity. Qed.

(** ** Compilation Units

    An [eval] is closed off where it stands, against the definitions in scope
    there. *)
Definition elaborate_prog (prg : Cst.prog) : option (list ((option typ * exp)%type)) :=
  let (imports, top) := prg in
  let (p, cs) := top in
  match elab_cmds nil u_init imports with
  | Some st0 =>
      match elab_cmds nil (u_enter st0) cs with
      | Some st => Some (u_evals st)
      | None => None
      end
  | None => None
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
  `( user_exp (a_var x) ).

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

(** ** Closedness

    Elaboration success used to be characterized by a *set* of free names
    ([cst_variables] and [well_scoped]).  That characterization does not survive
    modules: whether [X.Y.Z] elaborates depends on whether [X] is a module and on
    how many parameters it has, and no set of names records that.  What is left
    of it, and what the pipeline actually needs, is the other half of the old
    statement — that a successful elaboration at depth [d] produces a term with
    no index beyond [d], so a whole unit produces a closed one. *)
Inductive closed_at : exp -> nat -> Prop :=
 | ca_var : forall x n, x < n -> closed_at (a_var x) n
 | ca_lam : forall t b n, closed_at t n -> closed_at b (1+n) -> closed_at (a_fn t b) n
 | ca_pi : forall t b n, closed_at t n -> closed_at b (1+n) -> closed_at (a_pi t b) n
 | ca_app : forall a1 a2 n, closed_at a1 n -> closed_at a2 n ->
            closed_at (a_app a1 a2) n
 | ca_nat : forall n, closed_at (a_nat) n
 | ca_zero : forall n, closed_at (a_zero) n
 | ca_type : forall n m, closed_at (a_typ m) n
 | ca_succ : forall a n, closed_at a n -> closed_at (a_succ a) n
 | ca_natrec : forall n m z s l, closed_at n l -> closed_at m (1+l) -> closed_at z l -> closed_at s (2+l) -> closed_at (a_natrec m z s n) l
.

#[export]
Hint Constructors closed_at : mctt.

(** *** Bounded Weakenings and Substitutions

    Closedness is preserved by any weakening or substitution that respects the
    bound, which is all the elaborator ever applies. *)
Definition wk_bounded (φ : wk) (n n' : nat) : Prop := forall x, x < n -> φ x < n'.

Definition sb_bounded (σ : sub) (n n' : nat) : Prop := forall x, x < n -> closed_at (σ x) n'.

Lemma closed_at_le : forall M n,
    closed_at M n ->
    forall n', n <= n' -> closed_at M n'.
Proof.
  induction 1; intros ? Hle; econstructor; solve [ lia | eauto with arith ].
Qed.

Lemma wk_bounded_q : forall φ n n',
    wk_bounded φ n n' ->
    wk_bounded (wk_q φ) (S n) (S n').
Proof.
  intros ? ? ? Hφ [| x] ?; simpl; [ lia |].
  apply ->Nat.succ_lt_mono. apply Hφ. lia.
Qed.

Lemma closed_at_wk : forall M n,
    closed_at M n ->
    forall φ n', wk_bounded φ n n' -> closed_at M⟨φ⟩ n'.
Proof.
  induction 1; intros; simpl; econstructor; eauto using wk_bounded_q.
Qed.

Lemma closed_at_shiftn : forall M n k,
    closed_at M n ->
    closed_at M⟨wk_shiftn k⟩ (n + k).
Proof.
  intros. eapply closed_at_wk; [ eassumption |]. intros ? ?. simpl. lia.
Qed.

Lemma sb_bounded_q : forall σ n n',
    sb_bounded σ n n' ->
    sb_bounded (sb_q σ) (S n) (S n').
Proof.
  intros ? ? ? Hσ [| x] ?; unfold sb_q; simpl.
  - constructor. lia.
  - eapply closed_at_wk; [ apply Hσ; lia |]. intros ? ?. simpl. lia.
Qed.

Lemma closed_at_sub : forall M n,
    closed_at M n ->
    forall σ n', sb_bounded σ n n' -> closed_at M[σ] n'.
Proof.
  induction 1; intros ? ? Hσ; simpl; try (apply Hσ; assumption);
    econstructor; eauto 6 using sb_bounded_q with mctt.
Qed.

(** *** Well-formed Scopes

    The invariant a scope satisfies during elaboration: the term a name resolves
    to is closed at the depth it was elaborated at, and that depth has already
    been reached. *)
Inductive ent_wf : nat -> entry -> Prop :=
| ew_val : forall d v,
    v_depth v <= d ->
    closed_at (v_term v) (v_depth v) ->
    ent_wf d (e_val v)
| ew_mod : forall d n ms,
    sc_wf d ms ->
    ent_wf d (e_mod n ms)
with sc_wf : nat -> scope -> Prop :=
| sw_nil : forall d, sc_wf d sc_nil
| sw_cons : forall d x e s,
    ent_wf d e ->
    sc_wf d s ->
    sc_wf d (sc_cons x e s).

#[export]
Hint Constructors ent_wf sc_wf : mctt.

Lemma ent_wf_le : forall d e, ent_wf d e -> forall d', d <= d' -> ent_wf d' e
with sc_wf_le : forall d s, sc_wf d s -> forall d', d <= d' -> sc_wf d' s.
Proof.
  - destruct 1; intros.
    + econstructor; [ lia | assumption ].
    + econstructor. eapply sc_wf_le; eassumption.
  - destruct 1; intros; [ constructor |].
    econstructor; [ eapply ent_wf_le | eapply sc_wf_le ]; eassumption.
Qed.

Lemma sc_lookup_wf : forall s d x e,
    sc_wf d s ->
    sc_lookup x s = Some e ->
    ent_wf d e.
Proof.
  induction s; intros * Hs Hl; simpl in *; [ discriminate |].
  inversion_clear Hs. destruct (string_dec _ _); mauto 3.
  inversion Hl; subst; assumption.
Qed.

Lemma sc_lookup_path_wf : forall p s d e,
    sc_wf d s ->
    sc_lookup_path p s = Some e ->
    ent_wf d e.
Proof.
  induction p as [| x [| y p] IHp]; intros * Hs Hl; simpl in *; try discriminate.
  - mauto 3 using sc_lookup_wf.
  - destruct (sc_lookup x s) as [[| n ms] |] eqn:Hx; try discriminate.
    assert (ent_wf d (e_mod n ms)) as Hm by mauto 3 using sc_lookup_wf.
    inversion_clear Hm. eapply IHp; eassumption.
Qed.

Lemma sc_app_wf : forall s t d,
    sc_wf d s ->
    sc_wf d t ->
    sc_wf d (sc_app s t).
Proof.
  induction s; intros * Hs Ht; simpl; [ assumption |].
  inversion_clear Hs. mauto 3.
Qed.

Lemma sc_app_wf_inv : forall s t d,
    sc_wf d (sc_app s t) ->
    sc_wf d s /\ sc_wf d t.
Proof.
  induction s; intros * Hst; simpl in *; [ mauto 3 |].
  inversion_clear Hst. firstorder mauto 3.
Qed.

Lemma sc_insert_wf : forall p e s d,
    ent_wf d e ->
    sc_wf d s ->
    sc_wf d (sc_insert p e s).
Proof.
  induction p as [| x [| y p] IHp]; intros * He Hs; simpl; [ assumption | mauto 3 |].
  destruct (sc_lookup x s) as [[v | n ms] |] eqn:Hx; [ mauto 4 | | mauto 4 ].
  assert (ent_wf d (e_mod n ms)) as Hm by mauto 3 using sc_lookup_wf.
  inversion_clear Hm. mauto 4.
Qed.

Lemma ent_public_wf : forall e d e',
    ent_wf d e ->
    ent_public e = Some e' ->
    ent_wf d e'
with sc_public_wf : forall s d,
    sc_wf d s ->
    sc_wf d (sc_public s).
Proof.
  - destruct e; intros * He Hp; simpl in *.
    + destruct (v_private v); [ discriminate |].
      inversion Hp; subst; assumption.
    + inversion_clear He. inversion Hp; subst.
      econstructor. apply sc_public_wf. assumption.
  - destruct s; intros * Hs; simpl; [ constructor |].
    inversion_clear Hs.
    destruct (ent_public e) eqn:Hp.
    + econstructor; [ eapply ent_public_wf | apply sc_public_wf ]; eassumption.
    + apply sc_public_wf. assumption.
Qed.

Lemma sc_take_wf : forall ns ms s d s',
    sc_wf d ms ->
    sc_wf d s ->
    sc_take ns ms s = Some s' ->
    sc_wf d s'.
Proof.
  induction ns; intros * Hms Hs Ht; simpl in *.
  - inversion Ht; subst; assumption.
  - destruct (sc_lookup a ms) as [e |] eqn:Hl; [| discriminate].
    pose proof (sc_lookup_wf ms d a e Hms Hl).
    eapply (IHns ms (sc_cons a e s) d); mauto 3.
Qed.

(** *** Using an Entry *)

Lemma closed_at_sc_shift : forall M n d,
    closed_at M n ->
    n <= d ->
    closed_at (sc_shift d n M) d.
Proof.
  unfold sc_shift. intros.
  remember (d - n) as k eqn:Hk.
  replace d with (n + k) by lia.
  apply closed_at_shiftn. assumption.
Qed.

Lemma closed_at_sc_apply : forall args M d,
    closed_at M d ->
    List.Forall (fun N => closed_at N d) args ->
    closed_at (sc_apply M args) d.
Proof.
  unfold sc_apply. induction args; intros * HM Hargs; simpl; [ assumption |].
  inversion_clear Hargs. mauto 3.
Qed.

Lemma closed_at_sc_use : forall d v args M,
    ent_wf d (e_val v) ->
    List.Forall (fun N => closed_at N d) args ->
    sc_use d v args = Some M ->
    closed_at M d.
Proof.
  unfold sc_use. intros * Hv Hargs Hu.
  destruct (Nat.leb _ _); [| discriminate].
  inversion Hu; subst. inversion_clear Hv.
  apply closed_at_sc_apply; [ apply closed_at_sc_shift |]; assumption.
Qed.

Lemma ent_fix_wf : forall e d args e',
    ent_wf d e ->
    List.Forall (fun N => closed_at N d) args ->
    ent_fix d args e = Some e' ->
    ent_wf d e'
with sc_fix_wf : forall s d args s',
    sc_wf d s ->
    List.Forall (fun N => closed_at N d) args ->
    sc_fix d args s = Some s' ->
    sc_wf d s'.
Proof.
  - destruct e as [v | n ms]; intros * He Hargs Hf; simpl in *.
    + destruct (Nat.leb _ _); [| discriminate].
      inversion Hf; subst. inversion_clear He.
      econstructor; simpl; [ lia |].
      apply closed_at_sc_apply; [ apply closed_at_sc_shift |]; assumption.
    + inversion_clear He.
      destruct (sc_fix d args ms) as [ms' |] eqn:Hms; [| discriminate].
      inversion Hf; subst.
      econstructor. eapply (sc_fix_wf ms d args ms'); eassumption.
  - destruct s as [| x en t]; intros * Hs Hargs Hf; simpl in *.
    + inversion Hf; subst; constructor.
    + inversion_clear Hs.
      destruct (ent_fix d args en) as [en' |] eqn:Hen; [| discriminate].
      destruct (sc_fix d args t) as [t' |] eqn:Ht; [| discriminate].
      inversion Hf; subst.
      econstructor;
        [ eapply (ent_fix_wf en d args en') | eapply (sc_fix_wf t d args t') ];
        eassumption.
Qed.

(** *** Elaboration of Objects

    What [elab_res] returns is well formed at the current depth: a term is
    closed there, and a module is a well-formed scope together with arguments
    closed there. *)
Definition res_wf (d : nat) (r : res) : Prop :=
  match r with
  | r_exp M => closed_at M d
  | r_ent e args => ent_wf d e /\ List.Forall (fun N => closed_at N d) args
  end.

Lemma res_term_closed : forall d r M,
    res_wf d r ->
    res_term d (Some r) = Some M ->
    closed_at M d.
Proof.
  destruct r as [| [] ?]; intros * Hr Ht; simpl in *; try discriminate.
  - inversion Ht; subst; assumption.
  - destruct Hr. mauto 3 using closed_at_sc_use.
Qed.

Lemma sc_push_wf : forall x d s,
    sc_wf d s ->
    sc_wf (S d) (sc_push x d s).
Proof.
  unfold sc_push. intros. econstructor.
  - econstructor; simpl; [ lia | constructor; lia ].
  - eapply sc_wf_le; [ eassumption | lia ].
Qed.

(** A local definition binds either the λ it emits or the term itself; either
    way the entry lives one binder deeper. *)
Lemma ent_wf_bind : forall ab d ar priv M,
    closed_at M d ->
    ent_wf (S d) (e_val (v_bind ab d ar priv M)).
Proof.
  unfold v_bind, v_bound, v_inline. intros * HM.
  destruct ab; econstructor; simpl; [ lia | constructor; lia | lia | assumption ].
Qed.

#[local]
Hint Resolve sc_push_wf ent_wf_bind : mctt.

(** The statements of the mutual induction over [Cst.obj] and [Cst.decl]:
    [elab_res] matches on a declaration inline, so the declaration's part of the
    statement is just its objects'. *)
Definition elab_res_wf_stmt (o : Cst.obj) : Prop :=
  forall s d args r,
    sc_wf d s ->
    List.Forall (fun N => closed_at N d) args ->
    elab_res s d o args = Some r ->
    res_wf d r.

Definition elab_decl_wf_stmt (dcl : Cst.decl) : Prop :=
  match dcl with
  | Cst.d_def _ _ oA oM => elab_res_wf_stmt oA /\ elab_res_wf_stmt oM
  | Cst.d_mod _ oE => elab_res_wf_stmt oE
  end.

Scheme obj_mut := Induction for Cst.obj Sort Prop
  with decl_mut := Induction for Cst.decl Sort Prop.

(** Every premise of [elab_res] is a sub-elaboration that produced a term.  The
    induction hypothesis is spelled out rather than folded so that it unifies,
    and it comes last so that the sub-elaboration itself fixes the scope and the
    object. *)
Lemma elab_sub_closed : forall s d o M,
    res_term d (elab_res s d o nil) = Some M ->
    sc_wf d s ->
    (forall s' d' args r,
        sc_wf d' s' ->
        List.Forall (fun N => closed_at N d') args ->
        elab_res s' d' o args = Some r ->
        res_wf d' r) ->
    closed_at M d.
Proof.
  intros * Ht Hs Ho.
  destruct (elab_res s d o nil) as [r |] eqn:He; [| discriminate].
  eapply res_term_closed; [| eassumption].
  eapply Ho; mauto 3.
Qed.

(** [elab_res] only returns something when each of its sub-elaborations does:
    name every branch, and drop the impossible ones. *)
#[local]
Ltac elab_res_wf_tac :=
  repeat match goal with
    | H: context[res_term ?d (elab_res ?s ?d' ?o nil)] |- _ =>
        (* the equations this very tactic produces are not to be split again *)
        lazymatch type of H with
        | res_term _ _ = Some _ => fail
        | _ =>
            let Hc := fresh "Hc" in
            destruct (res_term d (elab_res s d' o nil)) as [? |] eqn:Hc;
            [| discriminate H]
        end
    end;
  match goal with
  | H: Some _ = Some _ |- _ => inversion_clear H
  end;
  simpl; apply closed_at_sc_apply; [| assumption].

(** The scope of a sub-elaboration is whatever [sc_push] made of the current
    one, and its induction hypothesis is in the context. *)
#[local]
Ltac elab_sub_closed_tac :=
  eapply elab_sub_closed; [ eassumption | mauto 3 | eassumption ].

Lemma elab_res_wf : forall o, elab_res_wf_stmt o.
Proof.
  apply (obj_mut elab_res_wf_stmt elab_decl_wf_stmt);
    unfold elab_res_wf_stmt, elab_decl_wf_stmt in *;
    intros; simpl in *; mauto 3.
  (* [typ], [nat], [zero]: a constant applied to the arguments *)
  1-3: inversion_clear H1; simpl; apply closed_at_sc_apply; mauto 3.
  (* [succ], [natrec], [pi], [fn]: a former applied to the arguments *)
  1-4: elab_res_wf_tac; econstructor; elab_sub_closed_tac.
  (* [app]: the argument joins the spine *)
  - destruct (res_term d (elab_res s d o0 nil)) as [N |] eqn:Hc; [| discriminate].
    eapply H; [ eassumption | | eassumption ].
    econstructor; [| assumption ]. elab_sub_closed_tac.
  (* [var]: whatever the name resolves to, still under-applied *)
  - destruct (sc_lookup s s0) as [e |] eqn:Hl; [| discriminate].
    inversion_clear H1. simpl. split; mauto 3 using sc_lookup_wf.
  (* [proj]: the module's arguments come before the member's *)
  - destruct (elab_res s0 d o nil) as [[| [v | n ms] margs] |] eqn:He; try discriminate.
    destruct (sc_lookup s ms) as [e |] eqn:Hl; [| discriminate].
    inversion_clear H2.
    assert (res_wf d (r_ent (e_mod n ms) margs)) as [Hm Hargs]
      by (eapply H; [ eassumption | constructor | eassumption ]).
    inversion_clear Hm. simpl. split; [ mauto 3 using sc_lookup_wf |].
    apply List.Forall_app. split; assumption.
  (* [letb]: the binding extends the scope the body is elaborated in *)
  - destruct d as [m x oA oM | x oE].
    (* a definition emits its own [λ], so the body is one binder deeper *)
    + destruct H as [HA HM]. elab_res_wf_tac.
      econstructor; [ econstructor; [ elab_sub_closed_tac |] | elab_sub_closed_tac ].
      eapply elab_sub_closed; [ eassumption | | eassumption ].
      econstructor;
        [ apply ent_wf_bind; elab_sub_closed_tac
        | eapply sc_wf_le; [ eassumption | lia ] ].
    (* a module binding emits nothing, but its members absorb the arguments *)
    + destruct (elab_res s d0 oE nil) as [[| [v | n ms] margs] |] eqn:He;
        try discriminate.
      destruct (sc_fix d0 margs ms) as [ms' |] eqn:Hf; [| discriminate].
      elab_res_wf_tac.
      assert (res_wf d0 (r_ent (e_mod n ms) margs)) as [Hm Hargs]
        by (eapply H; [ eassumption | constructor | eassumption ]).
      inversion_clear Hm.
      eapply elab_sub_closed; [ eassumption | | eassumption ].
      econstructor; [ econstructor; eapply sc_fix_wf | ]; eassumption.
Qed.

Corollary elab_closed : forall s d o M,
    sc_wf d s ->
    elab s d o = Some M ->
    closed_at M d.
Proof.
  unfold elab. intros.
  eapply elab_sub_closed; [ eassumption | eassumption | apply elab_res_wf ].
Qed.

(** ** Closedness of a Unit

    The telescope of a unit: entry [i] was elaborated at depth [i], so the nest
    it becomes is closed, and the substitution it performs takes a type living
    at its far end down to a closed one. *)
Inductive tele_wf : nat -> list (exp * exp) -> Prop :=
| tw_nil : forall k, tele_wf k nil
| tw_cons : forall k A M t,
    closed_at A k ->
    closed_at M k ->
    tele_wf (S k) t ->
    tele_wf k (cons (A, M) t).

#[export]
Hint Constructors tele_wf : mctt.

Lemma tele_wf_app : forall t k A M,
    tele_wf k t ->
    closed_at A (k + List.length t) ->
    closed_at M (k + List.length t) ->
    tele_wf k (List.app t (cons (A, M) nil)).
Proof.
  induction t as [| [A' M'] t IHt]; intros * Ht HA HM; simpl in *.
  - rewrite Nat.add_0_r in *. mauto 3.
  - inversion_clear Ht.
    replace (k + S (List.length t)) with (S k + List.length t) in HA by lia.
    replace (k + S (List.length t)) with (S k + List.length t) in HM by lia.
    econstructor; [ assumption | assumption | apply IHt; assumption ].
Qed.

Lemma closed_at_tele_nest : forall t k M,
    tele_wf k t ->
    closed_at M (k + List.length t) ->
    closed_at (tele_nest t M) k.
Proof.
  induction t as [| [A M'] t IHt]; intros * Ht HM; simpl in *.
  - rewrite Nat.add_0_r in HM. assumption.
  - inversion_clear Ht.
    replace (k + S (List.length t)) with (S k + List.length t) in HM by lia.
    econstructor; [ econstructor; [ assumption | apply IHt; assumption ] | assumption ].
Qed.

Lemma sb_bounded_tele_close : forall t k σ,
    tele_wf k t ->
    sb_bounded σ k 0 ->
    sb_bounded (List.fold_left (fun σ p => σ ,, (snd p)[σ]) t σ) (k + List.length t) 0.
Proof.
  induction t as [| [A M] t IHt]; intros * Ht Hσ; simpl in *.
  - rewrite Nat.add_0_r. assumption.
  - inversion_clear Ht.
    replace (k + S (List.length t)) with (S k + List.length t) by lia.
    apply IHt; [ assumption |].
    intros [| x] ?; simpl; [ mauto 3 using closed_at_sub | apply Hσ; lia ].
Qed.

Corollary closed_at_tele_close : forall t A,
    tele_wf 0 t ->
    closed_at A (List.length t) ->
    closed_at A[tele_close t] 0.
Proof.
  unfold tele_close. intros.
  eapply closed_at_sub; [ eassumption |].
  apply (sb_bounded_tele_close t 0 Id); [ assumption |].
  intros ? ?. lia.
Qed.

(** *** Well-formed Unit States

    A state is well formed when both of its scopes are well formed at the depth
    reached so far, its telescope accounts for exactly that depth, and every
    obligation it has collected is closed. *)
Definition eval_wf (e : (option typ * exp)%type) : Prop :=
  match fst e with
  | Some A => closed_at A 0
  | None => True
  end /\ closed_at (snd e) 0.

Definition u_wf (st : ustate) : Prop :=
  sc_wf (u_depth st) (u_outer st) /\
  sc_wf (u_depth st) (u_frame st) /\
  tele_wf 0 (u_tele st) /\
  List.length (u_tele st) = u_depth st /\
  List.Forall eval_wf (u_evals st).

Lemma u_wf_view : forall st, u_wf st -> sc_wf (u_depth st) (u_view st).
Proof.
  unfold u_view. intros ? [? [? ?]]. apply sc_app_wf; assumption.
Qed.

Lemma u_wf_init : u_wf u_init.
Proof. unfold u_wf, u_init; simpl. repeat split; mauto 3. Qed.

Lemma u_wf_enter : forall st, u_wf st -> u_wf (u_enter st).
Proof.
  intros ? Hst. pose proof (u_wf_view _ Hst).
  destruct Hst as [? [? [? [? ?]]]].
  unfold u_wf, u_enter; simpl. repeat split; mauto 3.
Qed.

Lemma u_wf_close : forall p st st',
    u_wf st ->
    u_wf st' ->
    u_depth st <= u_depth st' ->
    u_wf (u_close p st st').
Proof.
  intros * [Ho [Hf _]] [_ [Hf' [Ht' [Hlen' Hev']]]] Hle.
  unfold u_wf, u_close; simpl. repeat split; try assumption.
  - eapply sc_wf_le; eassumption.
  - apply sc_insert_wf; [ econstructor; eassumption | eapply sc_wf_le; eassumption ].
Qed.

Lemma u_wf_push_eval : forall st e,
    u_wf st ->
    eval_wf e ->
    u_wf (u_push_eval st e).
Proof.
  intros * [? [? [? [? ?]]]] ?.
  unfold u_wf, u_push_eval; simpl. repeat split; try assumption.
  apply List.Forall_app. split; [ assumption | econstructor; [ assumption | constructor ] ].
Qed.

Lemma u_wf_refit : forall st fr n,
    u_wf st ->
    sc_wf (u_depth st) fr ->
    u_wf (u_refit st fr n).
Proof.
  intros * [? [? [? [? ?]]]] ?.
  unfold u_wf, u_refit; simpl. repeat split; assumption.
Qed.

Lemma u_depth_enter : forall st, u_depth (u_enter st) = u_depth st.
Proof. reflexivity. Qed.

Lemma u_depth_close : forall p st st', u_depth (u_close p st st') = u_depth st'.
Proof. reflexivity. Qed.

(** *** Elaboration of Commands *)

Lemma u_wf_def : forall ps st m x oA oM st',
    u_wf st ->
    elab_def ps st m x oA oM = Some st' ->
    u_wf st' /\ u_depth st <= u_depth st'.
Proof.
  unfold elab_def. intros * Hst Hd.
  pose proof (u_wf_view _ Hst) as Hv.
  destruct (elab (u_view st) (u_depth st) (tele_pi ps oA)) as [A |] eqn:HA; [| discriminate].
  destruct (elab (u_view st) (u_depth st) (tele_fn ps oM)) as [M |] eqn:HM; [| discriminate].
  pose proof (elab_closed _ _ _ _ Hv HA).
  pose proof (elab_closed _ _ _ _ Hv HM).
  destruct Hst as [Ho [Hf [Ht [Hlen Hev]]]].
  inversion Hd; subst; clear Hd.
  unfold u_wf; simpl. repeat split.
  - eapply sc_wf_le; [ eassumption | lia ].
  - econstructor; [ apply ent_wf_bind; assumption | eapply sc_wf_le; [ eassumption | lia ] ].
  - apply tele_wf_app;
      [ assumption | simpl; rewrite Hlen; assumption | simpl; rewrite Hlen; assumption ].
  - rewrite List.length_app, Hlen. simpl. lia.
  - assumption.
  - lia.
Qed.

Lemma u_wf_eval : forall st oM oA st',
    u_wf st ->
    elab_eval st oM oA = Some st' ->
    u_wf st' /\ u_depth st <= u_depth st'.
Proof.
  unfold elab_eval. intros * Hst He.
  pose proof (u_wf_view _ Hst) as Hv.
  assert (Ht : tele_wf 0 (u_tele st)) by (destruct Hst as [? [? [? ?]]]; assumption).
  assert (Hlen : List.length (u_tele st) = u_depth st)
    by (destruct Hst as [? [? [? [? ?]]]]; assumption).
  assert (Hnest : forall N,
             closed_at N (u_depth st) -> closed_at (tele_nest (u_tele st) N) 0)
    by (intros; apply closed_at_tele_nest; [ assumption | simpl; rewrite Hlen; assumption ]).
  destruct (elab (u_view st) (u_depth st) oM) as [M |] eqn:HM; [| discriminate].
  pose proof (elab_closed _ _ _ _ Hv HM).
  destruct oA as [oA |].
  - destruct (elab (u_view st) (u_depth st) oA) as [A |] eqn:HA; [| discriminate].
    pose proof (elab_closed _ _ _ _ Hv HA).
    inversion He; subst; clear He.
    split; [| unfold u_push_eval; simpl; lia].
    apply u_wf_push_eval; [ assumption |].
    unfold eval_wf, ascribe; simpl. split.
    + apply closed_at_tele_close; [ assumption | rewrite Hlen; assumption ].
    + apply Hnest.
      econstructor; [ econstructor; [ assumption | constructor; lia ] | assumption ].
  - inversion He; subst; clear He.
    split; [| unfold u_push_eval; simpl; lia].
    apply u_wf_push_eval; [ assumption |].
    unfold eval_wf; simpl. split; [ exact I | apply Hnest; assumption ].
Qed.

Lemma u_wf_import : forall st p spec st',
    u_wf st ->
    elab_import st p spec = Some st' ->
    u_wf st' /\ u_depth st <= u_depth st'.
Proof.
  unfold elab_import. intros * Hst Hi.
  pose proof (u_wf_view _ Hst) as Hv.
  destruct (sc_lookup_path p (u_view st)) as [[| n ms] |] eqn:Hl; try discriminate.
  assert (ent_wf (u_depth st) (e_mod n ms)) as Hm by (eapply sc_lookup_path_wf; eassumption).
  inversion_clear Hm.
  assert (Hf : sc_wf (u_depth st) (u_frame st)) by (destruct Hst as [? [? ?]]; assumption).
  destruct spec as [| y | ns];
    [| | destruct (sc_take ns (sc_public ms) (u_frame st)) as [fr |] eqn:Ht; [| discriminate] ];
    inversion Hi; subst; clear Hi;
    (split; [| unfold u_refit; simpl; lia]); apply u_wf_refit; try assumption.
  - econstructor; [ econstructor; apply sc_public_wf; assumption | assumption ].
  (* the [sc_take] that produced the frame fixes what its premises are about *)
  - eapply sc_take_wf; [| | eassumption ];
      [ apply sc_public_wf; assumption | assumption ].
Qed.

(** *** Elaboration of a Unit

    [elab_cmds] recurses on a module's body, which [list]'s induction principle
    does not see, so the induction is on a measure instead. *)
Fixpoint cmd_size (c : Cst.cmd) : nat :=
  match c with
  | Cst.c_mod _ _ cs =>
      S ((fix sizes (cs : list Cst.cmd) : nat :=
            match cs with
            | nil => 0
            | c :: cs => cmd_size c + sizes cs
            end) cs)
  | _ => 1
  end.

Fixpoint cmds_size (cs : list Cst.cmd) : nat :=
  match cs with
  | nil => 0
  | c :: cs => cmd_size c + cmds_size cs
  end.

Lemma cmd_size_mod : forall p params cs,
    cmd_size (Cst.c_mod p params cs) = S (cmds_size cs).
Proof. reflexivity. Qed.

Lemma cmd_size_pos : forall c, 1 <= cmd_size c.
Proof. destruct c; simpl; lia. Qed.

Lemma elab_cmds_wf : forall n ps cs st st',
    cmds_size cs <= n ->
    u_wf st ->
    elab_cmds ps st cs = Some st' ->
    u_wf st' /\ u_depth st <= u_depth st'.
Proof.
  induction n as [| n IHn]; intros * Hn Hst Hcs;
    (destruct cs as [| c cs];
     [ simpl in Hcs; inversion Hcs; subst; split; [ assumption | lia ] |]);
    pose proof (cmd_size_pos c); simpl in Hn;
    [ lia |].
  assert (Hrest : cmds_size cs <= n) by lia.
  rewrite elab_cmds_cons in Hcs.
  destruct c as [p params body | m x oA oM | ip spec | oM oA].
  (* the body of a module is smaller, and its members become reachable under [p] *)
  - rewrite cmd_size_mod in Hn. rewrite elab_cmd_mod in Hcs.
    destruct (elab_cmds (List.app ps params) (u_enter st) body) as [st1 |] eqn:Hb;
      [| discriminate].
    pose proof (IHn (List.app ps params) body (u_enter st) st1
                  ltac:(lia) (u_wf_enter _ Hst) Hb) as [Hst1 Hle1].
    rewrite u_depth_enter in Hle1.
    pose proof (IHn ps cs (u_close p st st1) st' Hrest
                  (u_wf_close _ _ _ Hst Hst1 Hle1) Hcs) as [Hst2 Hle2].
    rewrite u_depth_close in Hle2. split; [ assumption | lia ].
  - rewrite elab_cmd_def in Hcs.
    destruct (elab_def ps st m x oA oM) as [st1 |] eqn:Hd; [| discriminate].
    pose proof (u_wf_def _ _ _ _ _ _ _ Hst Hd) as [Hst1 Hle1].
    pose proof (IHn ps cs st1 st' Hrest Hst1 Hcs) as [Hst2 Hle2].
    split; [ assumption | lia ].
  - rewrite elab_cmd_import in Hcs.
    destruct (elab_import st ip spec) as [st1 |] eqn:Hi; [| discriminate].
    pose proof (u_wf_import _ _ _ _ Hst Hi) as [Hst1 Hle1].
    pose proof (IHn ps cs st1 st' Hrest Hst1 Hcs) as [Hst2 Hle2].
    split; [ assumption | lia ].
  - rewrite elab_cmd_eval in Hcs.
    destruct (elab_eval st oM oA) as [st1 |] eqn:He; [| discriminate].
    pose proof (u_wf_eval _ _ _ _ Hst He) as [Hst1 Hle1].
    pose proof (IHn ps cs st1 st' Hrest Hst1 Hcs) as [Hst2 Hle2].
    split; [ assumption | lia ].
Qed.

(** Every obligation a unit elaborates to is closed, so [run_eval] may hand it
    to [type_check_closed] and to [nbe]. *)
Theorem elaborate_prog_wf : forall prg es,
    elaborate_prog prg = Some es ->
    List.Forall eval_wf es.
Proof.
  unfold elaborate_prog. intros [imports [p cs]] * He.
  destruct (elab_cmds nil u_init imports) as [st0 |] eqn:H0; [| discriminate].
  destruct (elab_cmds nil (u_enter st0) cs) as [st |] eqn:H1; [| discriminate].
  inversion He; subst; clear He.
  pose proof (elab_cmds_wf (cmds_size imports) nil imports u_init st0
                ltac:(lia) u_wf_init H0) as [Hst0 _].
  pose proof (elab_cmds_wf (cmds_size cs) nil cs (u_enter st0) st
                ltac:(lia) (u_wf_enter _ Hst0) H1) as [Hst _].
  destruct Hst as [? [? [? [? ?]]]]. assumption.
Qed.
