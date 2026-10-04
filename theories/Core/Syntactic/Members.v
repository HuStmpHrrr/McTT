(** * Members of Modules

    A module has no signature: the type of a member is computed from the
    module, when it is needed, by the relation [member_type], and its
    δ-reduct by the function [member_unfold].  Both read syntax, context
    lookup and global resolution only, so they sit outside the mutual block of
    judgments, which uses them. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution GlobalCtx.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** ** Module Slots *)

Reserved Notation "Γ ∋ '#' x ⇒ₘ U" (at level 70, x constr at level 0, U at level 69).

(** The unit of a module slot, weakened to the use site. *)
Inductive ctx_lookup_mod : nat -> gunit -> ctx -> Prop :=
(** The innermost slot *)
| mod_here : `(Γ ▹ₘ U ∋ #0 ⇒ₘ gunit_wk U wk_shift)
(** A slot under one more entry *)
| mod_there : `(Γ ∋ #n ⇒ₘ U -> e :: Γ ∋ #(S n) ⇒ₘ gunit_wk U wk_shift)
where "Γ ∋ '#' x ⇒ₘ U" := (ctx_lookup_mod x U Γ) : type_scope.

#[export]
Hint Constructors ctx_lookup_mod : mctt.

Fixpoint ctx_find_mod (Γ : ctx) (x : nat) : option gunit :=
  match Γ with
  | nil => None
  | e :: Γ' =>
      match x with
      | 0 => match e with ce_mod U => Some (gunit_wk U wk_shift) | _ => None end
      | S y => option_map (fun U => gunit_wk U wk_shift) (ctx_find_mod Γ' y)
      end
  end.

Lemma ctx_find_mod_sound : forall Γ x U, ctx_find_mod Γ x = Some U -> Γ ∋ #x ⇒ₘ U.
Proof.
  induction Γ as [| e Γ IH]; intros [| y] U H; cbn in H; try discriminate.
  - destruct e; cbn in H; try discriminate; injection H as <-; constructor.
  - destruct (ctx_find_mod Γ y) eqn:E; cbn in H; [| discriminate ].
    injection H as <-; constructor; apply IH; assumption.
Qed.

Lemma ctx_find_mod_complete : forall Γ x U, Γ ∋ #x ⇒ₘ U -> ctx_find_mod Γ x = Some U.
Proof. induction 1; cbn; [ reflexivity | rewrite IHctx_lookup_mod; reflexivity ]. Qed.

Lemma ctx_find_mod_spec : forall Γ x U, ctx_find_mod Γ x = Some U <-> Γ ∋ #x ⇒ₘ U.
Proof. split; auto using ctx_find_mod_sound, ctx_find_mod_complete. Qed.

Lemma ctx_lookup_mod_functional : forall Γ x U U', Γ ∋ #x ⇒ₘ U -> Γ ∋ #x ⇒ₘ U' -> U = U'.
Proof. intros * H H'; apply ctx_find_mod_spec in H, H'; congruence. Qed.

(** ** Syntactic Helpers *)

(** The body up to and including the entry named [x]. *)
Fixpoint gm_prefix_upto (Φ : gmod) (x : string) : option gmod :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' y _ => if String.eqb x y then Some Φ else gm_prefix_upto Φ' x
  | gm_check Φ' _ => gm_prefix_upto Φ' x
  end.

(** The check entries of a body, each with the body before it. *)
Fixpoint gm_checks (Φ : gmod) : list (gmod * bcheck) :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' _ _ => gm_checks Φ'
  | gm_check Φ' c => (Φ', c) :: gm_checks Φ'
  end.

(** [M] applied to [args], outermost first. *)
Fixpoint apps (M : exp) (args : list exp) : exp :=
  match args with
  | nil => M
  | N :: args' => apps (a_app M N) args'
  end.

(** The root of a module expression, its arguments, outermost first, and the
    chain of submodules selected.  Arguments and selections commute, since
    members are closed over the parameters they lie under. *)
Fixpoint modexp_spine (H : modexp) : (modexp * list exp * list string)%type :=
  match H with
  | me_mem H y => let '(R, args, pre) := modexp_spine H in (R, args, pre ++ y :: nil)
  | me_app H N => let '(R, args, pre) := modexp_spine H in (R, args ++ N :: nil, pre)
  | _ => (H, nil, nil)
  end.

(** A module expression with no argument. *)
Fixpoint me_noargs (H : modexp) : Prop :=
  match H with
  | me_mem H _ => me_noargs H
  | me_app _ _ => False
  | _ => True
  end.

(** The Π a type is, looking through local definitions and local modules. *)
Fixpoint pi_view (A : typ) : option (typ * typ)%type :=
  match A with
  | a_pi B C => Some (B, C)
  | a_let (b_def B N) T =>
      match pi_view T with
      | Some (B', C') => Some (B'[Id,,N], C'[q (Id,,N)])
      | None => None
      end
  | a_let (b_mod U) T =>
      match pi_view T with
      | Some (B', C') => Some (B'[Id ,,ₘ me_lit U], C'[q (Id ,,ₘ me_lit U)])
      | None => None
      end
  | _ => None
  end.

(** ** Arities

    A module's arity is the telescope of parameters it still takes, a [ctx]
    over the context of the module, innermost first.  Its entries may include
    local definitions and modules, from the bodies around the module; they
    are not parameters, and an argument goes to the outermost assumption,
    through them.

    [tele_view T] is that assumption's type and the rest of the telescope,
    over the context extended by it, the definitions and modules outside the
    assumption substituted away; [None] if [T] has no assumption left.  It is
    computed outermost first, on the reversed telescope, as [pi_view] is on a
    type: through a definition, the view inside it is moved out by
    substituting the definition. *)
Fixpoint tele_open (R : list centry) : option (typ * ctx)%type :=
  match R with
  | nil => None
  | ce_ass B :: R' => Some (B, rev R')
  | ce_def B N :: R' =>
      match tele_open R' with
      | Some (B', T') => Some (B'[Id,,N], tele_sub T' (q (Id,,N)))
      | None => None
      end
  | ce_mod U :: R' =>
      match tele_open R' with
      | Some (B', T') => Some (B'[Id ,,ₘ me_lit U], tele_sub T' (q (Id ,,ₘ me_lit U)))
      | None => None
      end
  end.

Definition tele_view (T : ctx) : option (typ * ctx)%type := tele_open (rev T).

(** The telescope left when the outermost parameter is instantiated with
    [N]: a module of arity [T], applied to [N], has arity [tele_inst T N]. *)
Definition tele_inst (T : ctx) (N : exp) : option ctx :=
  match tele_view T with
  | Some (_, T') => Some (tele_sub T' (Id,,N))
  | None => None
  end.

(** A module [F (A : Type@0) (f : forall (x : A) -> A)] takes [⋅ ▹ Type@0 ▹
    Π #0 #1]; applied to [ℕ], it takes [⋅ ▹ Π ℕ ℕ]. *)
Example tele_inst_example : tele_inst (⋅ ▹ Type@0 ▹ Π #0 #1) ℕ = Some (⋅ ▹ Π ℕ ℕ).
Proof. reflexivity. Qed.

(** ** Member Types

    [member_type Θ Ξ Γ H ch R] says that the chain [ch] of the module [H] is
    a definition of canonical type [A] ([R = mr_term A]), or a module that
    still takes the parameters [T] ([R = mr_mod T]).  A module is applied to
    an argument of the type of its outermost parameter, [tele_view]: it may be
    applied to fewer arguments than it has parameters, but not to more.

    A body member's type is its declared type, generalized over the unit's
    parameters and over the body before it, which become [ℓ]/[ℓₘ] binders; a
    module's arity is extended by them.  An alias member's type is its target
    member's type, instantiated with the alias's arguments and generalized over
    its parameters.  A chain from a unit is read off the global context;
    privacy is not a matter of typing (see [Command]). *)

(** The sort of a member. *)
Inductive mkind : Set :=
(** A definition *)
| mk_term
(** A module *)
| mk_mod.

(** The type of a member. *)
Inductive mres : Set :=
(** A definition, of this type. *)
| mr_term : typ -> mres
(** A module, with the parameters it still takes. *)
| mr_mod : ctx -> mres.

Definition mres_kind (R : mres) : mkind :=
  match R with
  | mr_term _ => mk_term
  | mr_mod _ => mk_mod
  end.

(** A member type as a type: a module's arity is the [Π] over its parameters,
    into [⊤].  The semantics reads member types through it. *)
Definition mres_ty (R : mres) : typ :=
  match R with
  | mr_term A => A
  | mr_mod T => ctx_pi T a_True
  end.

(** A member type generalized over a telescope it lives under. *)
Definition mres_gen (Δ : ctx) (R : mres) : mres :=
  match R with
  | mr_term A => mr_term (ctx_pi Δ A)
  | mr_mod T => mr_mod (T ++ Δ)
  end.

(** The type of a member of [H N], from the type [R] of the member of [H]:
    the outermost parameter of [R] instantiated with [N]. *)
Definition mres_app (R : mres) (N : exp) : option mres :=
  match R with
  | mr_term A =>
      match pi_view A with
      | Some (_, C) => Some (mr_term C[Id,,N])
      | None => None
      end
  | mr_mod T => option_map mr_mod (tele_inst T N)
  end.

Definition mres_wk (R : mres) (φ : wk) : mres :=
  match R with
  | mr_term A => mr_term A[φ]ʷ
  | mr_mod T => mr_mod (tele_wk T φ)
  end.

Definition mres_sub (R : mres) (σ : sub) : mres :=
  match R with
  | mr_term A => mr_term A[σ]
  | mr_mod T => mr_mod (tele_sub T σ)
  end.

Inductive member_type (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list string -> mres -> Prop :=
(** A definition reached from a unit, of its declared type. *)
| mt_unit_def : forall Γ fp ch b pv A B,
    ch <> nil ->
    gc_resolve Θ Ξ (q_abs fp ch) = Some (ge_def b pv A B) ->
    member_type Θ Ξ Γ (me_unit fp) ch (mr_term A)
(** A body module reached from a unit, taking the parameters it is filed
    with. *)
| mt_unit_mod : forall Γ fp ch T,
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_body T) ->
    member_type Θ Ξ Γ (me_unit fp) ch (mr_mod T)
(** A chain through an alias reached from a unit, read in the alias, past it. *)
| mt_unit_alias : forall Γ fp ch U r R,
    (mres_kind R = mk_term -> r <> nil) ->
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_alias U r) ->
    unit_member_type Θ Ξ nil U r R ->
    member_type Θ Ξ Γ (me_unit fp) ch R
(** A chain of a module slot, read in the unit it holds. *)
| mt_var : forall Γ x U ch R,
    Γ ∋ #x ⇒ₘ U ->
    unit_member_type Θ Ξ Γ U ch R ->
    member_type Θ Ξ Γ (me_var x) ch R
(** A chain of a literal module. *)
| mt_lit : forall Γ U ch R,
    unit_member_type Θ Ξ Γ U ch R ->
    member_type Θ Ξ Γ (me_lit U) ch R
(** A selection is read as a longer chain; a definition is not a module. *)
| mt_mem : forall Γ H y ch R,
    (mres_kind R = mk_term -> ch <> nil) ->
    member_type Θ Ξ Γ H (y :: ch) R ->
    member_type Θ Ξ Γ (me_mem H y) ch R
(** A member of an application: the member of the module, its outermost
    parameter instantiated with the argument. *)
| mt_app : forall Γ H N ch R R',
    member_type Θ Ξ Γ H ch R ->
    mres_app R N = Some R' ->
    member_type Θ Ξ Γ (me_app H N) ch R'
with unit_member_type (Θ : gdeps) (Ξ : gstack) : ctx -> gunit -> list string -> mres -> Prop :=
(** A body unit itself takes its parameters. *)
| umt_self : forall Γ Δ Φ,
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) nil (mr_mod Δ)
(** A definition of the body, generalized over the parameters and the body
    before it. *)
| umt_def : forall Γ Δ Φ Φ' x b pv A B,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (x :: nil) (mr_term (ctx_pi (body_ctx Φ' ++ Δ) A))
(** A chain through a module of the body, read in it, generalized over the
    parameters and the body before it. *)
| umt_mod : forall Γ Δ Φ Φ' y Uy ch R,
    (mres_kind R = mk_term -> ch <> nil) ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
    unit_member_type Θ Ξ (body_ctx Φ' ++ Δ ++ Γ) Uy ch R ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (y :: ch) (mres_gen (body_ctx Φ' ++ Δ) R)
(** A chain of an alias, read in its target, generalized over the alias's
    parameters. *)
| umt_alias : forall Γ Δ E ch R,
    member_type Θ Ξ (Δ ++ Γ) E ch R ->
    unit_member_type Θ Ξ Γ (gu_mk Δ (md_alias E)) ch (mres_gen Δ R).

Scheme member_type_mut_ind := Induction for member_type Sort Prop
with unit_member_type_mut_ind := Induction for unit_member_type Sort Prop.
Combined Scheme member_type_both_ind from member_type_mut_ind, unit_member_type_mut_ind.

#[export]
Hint Constructors member_type unit_member_type : mctt.

(** ** Expansions and the δ-Reduct

    The expansion of a member of a unit is a term of the unit's context: a
    body member is its body under the unit's parameters and the body before
    it; an alias member is its target member under the alias's parameters.
    The δ-reduct of [H.x] makes one lookup: a definition reached from a unit
    is its own reduct, the global, which unfolds by its own rule; otherwise it
    is the expansion of a member of an alias, or of a member of a slot or a
    literal.  It never follows an alias chain. *)

Definition member_expansion (U : gunit) (ch : list string) : option exp :=
  match U, ch with
  | _, nil => None
  | gu_mk Δ (md_alias E), _ => Some (ctx_fn Δ (member_ref E ch))
  | gu_mk Δ (md_body Φ), x :: ch' =>
      match gm_prefix_upto Φ x, ch' with
      | Some (gm_ext Φ' y (ge_def b pv A B)), nil =>
          Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_def b pv A B)) ++ Δ) (a_var 0))
      | Some (gm_ext Φ' y (ge_mod Uy)), _ :: _ =>
          Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_mod Uy)) ++ Δ) (member_ref (me_var 0) ch'))
      | _, _ => None
      end
  end.

Fixpoint member_unfold_ch (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (ch : list string) : option exp :=
  match H with
  | me_unit fp =>
      match gc_resolve Θ Ξ (q_abs fp ch) with
      | Some (ge_def _ _ _ _) => Some (member_ref (me_unit fp) ch)
      | _ =>
          match gc_module Θ Ξ (q_abs fp ch) with
          | Some (mr_alias U r) => member_expansion U r
          | _ => None
          end
      end
  | me_var x =>
      match ctx_find_mod Γ x with
      | Some U => member_expansion U ch
      | None => None
      end
  | me_lit U => member_expansion U ch
  | me_mem H y => member_unfold_ch Θ Ξ Γ H (y :: ch)
  | me_app H N => option_map (fun M => a_app M N) (member_unfold_ch Θ Ξ Γ H ch)
  end.

Definition member_unfold (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (x : string) : option exp :=
  member_unfold_ch Θ Ξ Γ H (x :: nil).
