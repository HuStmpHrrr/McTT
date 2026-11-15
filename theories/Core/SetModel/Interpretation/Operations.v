(** * Operations on Semantic Values

    Application of a value to arguments, application of a module to an
    argument, and selection of a member from a module, reading globals
    through a valuation only.  Which members of a module are proofs is
    read off the module ([module_member_proofs]): a function of a parameter
    carries it, as its domain may be empty. *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export Elements.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

(** A value applied to arguments, outermost first. *)
Definition apply_values (f : aczel_set) (args : list aczel_set) : aczel_set := fold_left set_apply args f.

(** The kind is a proof's. *)
Definition is_proof_kind (κ : abs_kind) : bool :=
  match κ with ak_propositional => true | _ => false end.

Section Modules.
  Variable γ : global_valuation.

(** A module applied to an argument: a parameter takes it, a global module
    records it.  The members' kinds stay. *)
Fixpoint apply_module (m : set_module) (x : aczel_set) : set_module :=
  match m with
  | set_module_params dom P f => set_module_cond (set_mem x (code_carrier dom)) P (f x)
  | set_module_global p args => set_module_global p (args ++ [x])
  | set_module_members ms => set_module_members ms
  | set_module_cond φ P m' => set_module_cond φ P (apply_module m' x)
  end.

(** A module applied to arguments, outermost first. *)
Definition apply_module_args (m : set_module) (args : list aczel_set) : set_module :=
  fold_left apply_module args m.

(** The entry of the member [x] of a table: the last one so named. *)
Fixpoint members_lookup (ms : list (string * set_entry)) (x : string) : option set_entry :=
  match ms with
  | nil => None
  | (y, e) :: ms' =>
      match members_lookup ms' x with
      | Some e' => Some e'
      | None => if String.eqb x y then Some e else None
      end
  end.

(** [module_member_proofs m ys x]: the member [x] of the submodule of [m]
    at the chain [ys] is a proof.  By recursion on the chain, so that a
    global module is read through the valuation's modules. *)
Fixpoint module_member_proofs (m : set_module) (ys : list string) (x : string) {struct ys} : bool :=
  match ys, m with
  (** A function of a parameter, or one applied, carries it *)
  | _, set_module_params _ P _ => P ys x
  | _, set_module_cond _ P _ => P ys x
  (** In a table: a proof's term entry *)
  | nil, set_module_members ms =>
      match members_lookup ms x with
      | Some (set_entry_term κ _) => is_proof_kind κ
      | _ => false
      end
  (** In a global module: the valuation's table at its path *)
  | nil, set_module_global p _ => global_proofs γ p x
  (** In a table's submodule: the entry's module part *)
  | y :: ys', set_module_members ms =>
      match members_lookup ms y with
      | Some e => module_member_proofs (set_entry_module_part e) ys' x
      | None => false
      end
  (** In a global module's submodule: the valuation's module there *)
  | y :: ys', set_module_global p _ => module_member_proofs (global_module γ (qname_in p y)) ys' x
  end.

Inductive set_entry_eq : set_entry -> set_entry -> Prop :=
(** Two terms of one kind *)
| set_entry_eq_term : forall κ v v', set_eq v v' -> set_entry_eq (set_entry_term κ v) (set_entry_term κ v')
(** Two modules *)
| set_entry_eq_module : forall m m', set_module_eq m m' -> set_entry_eq (set_entry_module m) (set_entry_module m')
(** Two definitions with module parts *)
| set_entry_eq_both : forall v v' m m', set_eq v v' -> set_module_eq m m' ->
    set_entry_eq (set_entry_both v m) (set_entry_both v' m')
(** [set_module_eq m m']: the modules [m] and [m'] are equal *)
with set_module_eq : set_module -> set_module -> Prop :=
(** Functions of a parameter: domains of equal carriers, the same proofs,
    equal at equal values of the domain.  Only a domain's carrier is ever
    read, and units over telescopes that are equal extensions have
    parameters of mutual subtypes, which give equal carriers, not equal
    codes *)
| set_module_eq_params : forall a a' P P' f f', set_eq (code_carrier a) (code_carrier a') -> (forall ys x, P ys x = P' ys x) ->
    (forall x x', set_mem x (code_carrier a) -> set_eq x x' -> set_module_eq (f x) (f' x')) ->
    set_module_eq (set_module_params a P f) (set_module_params a' P' f')
(** Tables with equal entries under the same names *)
| set_module_eq_members : forall ms ms', set_members_eq ms ms' ->
    set_module_eq (set_module_members ms) (set_module_members ms')
(** One global module at equal arguments *)
| set_module_eq_global : forall p args args', list_set_eq args args' ->
    set_module_eq (set_module_global p args) (set_module_global p args')
(** Equivalent conditions, the same proofs, equal modules where they hold *)
| set_module_eq_cond : forall (φ φ' : Prop) P P' m m', (φ <-> φ') -> (forall ys x, P ys x = P' ys x) ->
    (φ -> set_module_eq m m') -> set_module_eq (set_module_cond φ P m) (set_module_cond φ' P' m')
(** A condition that holds, on the left: the module under it, of the
    other side's proofness.  In [module M (n : ℕ) where def k : ℕ ≔ n
    end], [M 0] is [M]'s function applied, [set_module_cond (0 ∈ ℕ) P m],
    and its [β]-reduct [M[0]] is the table [m]: they are equal because
    the condition holds *)
| set_module_eq_cond_l : forall (φ : Prop) P m m', φ -> set_module_eq m m' ->
    (forall ys x, P ys x = module_member_proofs m' ys x) -> set_module_eq (set_module_cond φ P m) m'
(** A condition that holds, on the right: as [set_module_eq_cond_l], with
    the sides swapped ([M[0]] and [M 0] in the example there) *)
| set_module_eq_cond_r : forall (φ : Prop) P m m', φ -> set_module_eq m m' ->
    (forall ys x, P ys x = module_member_proofs m ys x) -> set_module_eq m (set_module_cond φ P m')
(** [set_members_eq ms ms']: the tables [ms] and [ms'] have the same names,
    in order, with equal entries *)
with set_members_eq : list (string * set_entry) -> list (string * set_entry) -> Prop :=
(** No member *)
| set_members_eq_nil : set_members_eq nil nil
(** A member, then the rest *)
| set_members_eq_cons : forall x e e' ms ms', set_entry_eq e e' -> set_members_eq ms ms' ->
    set_members_eq ((x, e) :: ms) ((x, e') :: ms').

(** [set_env_eq ρ ρ']: the environments [ρ] and [ρ'] have equal entries. *)
Definition set_env_eq (ρ ρ' : set_env) : Prop := forall x, set_entry_eq (ρ x) (ρ' x).

(** The term member [x] of a module: the closed value of a global one at
    the module's arguments, a table's entry, or, over a parameter, the
    member's closure: the empty set for a proof, otherwise the graph. *)
Fixpoint select_term (m : set_module) (x : string) : aczel_set :=
  match m with
  | set_module_params dom P f =>
      if P nil x then empty_set else graph_set (code_carrier dom) (fun v => select_term (f v) x)
  | set_module_members ms =>
      match members_lookup ms x with
      | Some e => set_entry_value e
      | None => empty_set
      end
  | set_module_global p args => apply_values (snd (global_term γ (qname_in p x))) args
  | set_module_cond φ _ m' => cond φ (select_term m' x)
  end.

(** The submodule [y] of a module: the closed module of a global one at
    the module's arguments, a table's entry, or, over a parameter, the
    submodule over it, with the submodule's members' kinds. *)
Fixpoint select_module (m : set_module) (y : string) : set_module :=
  match m with
  | set_module_params dom P f => set_module_params dom (fun ys => P (y :: ys)) (fun v => select_module (f v) y)
  | set_module_members ms =>
      match members_lookup ms y with
      | Some e => set_entry_module_part e
      | None => set_module_members nil
      end
  | set_module_global p args => apply_module_args (global_module γ (qname_in p y)) args
  | set_module_cond φ P m' => set_module_cond φ (fun ys => P (y :: ys)) (select_module m' y)
  end.

End Modules.
