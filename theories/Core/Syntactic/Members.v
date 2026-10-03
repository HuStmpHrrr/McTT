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
| mod_here : `(Γ ▹ₘ U ∋ #0 ⇒ₘ gunit_wk U wk_shift)
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

(** [H.y1. … .yn.x] as a term: submodule selections, then a member. *)
Fixpoint member_ref (H : modexp) (ch : list string) : exp :=
  match ch with
  | nil => exp_junk
  | x :: nil => a_mem H x
  | y :: ch' => member_ref (me_mem H y) ch'
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

(** ** Member Types

    [member_type Θ Ξ Γ H ch k A] says that the chain [ch] of the module [H] is
    a public definition of canonical type [A] ([k = mk_term]), or a module
    whose arity type is [A] ([k = mk_mod]).  The arity type of a module with
    parameters [T] is [ctx_pi T ⊤]: arguments are checked against it as
    against a [Π]-type, so a module may be applied to fewer arguments than it
    has parameters, but not to more.

    A body member's type is its declared type, generalized over the unit's
    parameters and over the body before it, which become [ℓ]/[ℓₘ] binders.  An
    alias member's type is its target member's type, instantiated with the
    alias's arguments and generalized over its parameters. *)

Inductive mkind : Set := mk_term | mk_mod.

Inductive member_type (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list string -> mkind -> typ -> Prop :=
| mt_path_def : forall Γ qp ch b A B,
    ch <> nil ->
    gc_resolve Θ Ξ (path_app qp ch) = Some (ge_def b false A B) ->
    member_type Θ Ξ Γ (me_path qp) ch mk_term A
| mt_path_mod : forall Γ qp ch T,
    gc_module Θ Ξ (path_app qp ch) = Some (mr_body T) ->
    member_type Θ Ξ Γ (me_path qp) ch mk_mod (ctx_pi T a_True)
| mt_path_alias : forall Γ qp ch U r k A,
    gc_module Θ Ξ (path_app qp ch) = Some (mr_alias U r) ->
    unit_member_type Θ Ξ nil U r k A ->
    member_type Θ Ξ Γ (me_path qp) ch k A
| mt_var : forall Γ x U ch k A,
    Γ ∋ #x ⇒ₘ U ->
    unit_member_type Θ Ξ Γ U ch k A ->
    member_type Θ Ξ Γ (me_var x) ch k A
| mt_lit : forall Γ U ch k A,
    unit_member_type Θ Ξ Γ U ch k A ->
    member_type Θ Ξ Γ (me_lit U) ch k A
| mt_mem : forall Γ H y ch k A,
    (k = mk_term -> ch <> nil) ->
    member_type Θ Ξ Γ H (y :: ch) k A ->
    member_type Θ Ξ Γ (me_mem H y) ch k A
| mt_app : forall Γ H N ch k A B C,
    member_type Θ Ξ Γ H ch k A ->
    pi_view A = Some (B, C) ->
    member_type Θ Ξ Γ (me_app H N) ch k C[Id,,N]
with unit_member_type (Θ : gdeps) (Ξ : gstack) : ctx -> gunit -> list string -> mkind -> typ -> Prop :=
| umt_self : forall Γ Δ Φ,
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) nil mk_mod (ctx_pi Δ a_True)
| umt_def : forall Γ Δ Φ Φ' x b A B,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b false A B)) ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (x :: nil) mk_term (ctx_pi (body_ctx Φ' ++ Δ) A)
| umt_mod : forall Γ Δ Φ Φ' y Uy ch k A,
    (k = mk_term -> ch <> nil) ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
    unit_member_type Θ Ξ (body_ctx Φ' ++ Δ ++ Γ) Uy ch k A ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (y :: ch) k (ctx_pi (body_ctx Φ' ++ Δ) A)
| umt_alias : forall Γ Δ E ch k A,
    member_type Θ Ξ (Δ ++ Γ) E ch k A ->
    unit_member_type Θ Ξ Γ (gu_mk Δ (md_alias E)) ch k (ctx_pi Δ A).

Scheme member_type_mut_ind := Induction for member_type Sort Prop
with unit_member_type_mut_ind := Induction for unit_member_type Sort Prop.
Combined Scheme member_type_both_ind from member_type_mut_ind, unit_member_type_mut_ind.

#[export]
Hint Constructors member_type unit_member_type : mctt.

(** ** Expansions and the δ-Reduct

    The expansion of a member of a unit is a term of the unit's context: a
    body member is its body under the unit's parameters and the body before
    it; an alias member is its target member under the alias's parameters.
    The δ-reduct of [H.x] makes one lookup: a filed definition, the expansion
    of a member of an alias, or the expansion of a member of a slot or a
    literal.  It never follows an alias chain. *)

Definition member_expansion (U : gunit) (ch : list string) : option exp :=
  match U, ch with
  | _, nil => None
  | gu_mk Δ (md_alias E), _ => Some (ctx_fn Δ (member_ref E ch))
  | gu_mk Δ (md_body Φ), x :: ch' =>
      match gm_prefix_upto Φ x, ch' with
      | Some (gm_ext Φ' y (ge_def b false A B)), nil =>
          Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_def b false A B)) ++ Δ) (a_var 0))
      | Some (gm_ext Φ' y (ge_mod Uy)), _ :: _ =>
          Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_mod Uy)) ++ Δ) (member_ref (me_var 0) ch'))
      | _, _ => None
      end
  end.

Fixpoint member_unfold_ch (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (ch : list string) : option exp :=
  match H with
  | me_path qp =>
      match gc_resolve Θ Ξ (path_app qp ch) with
      | Some (ge_def _ false _ _) => Some (a_glob (path_app qp ch))
      | _ =>
          match gc_module Θ Ξ (path_app qp ch) with
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
