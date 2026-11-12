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
  (** In a global module: by the kind of its global *)
  | nil, set_module_global p _ => is_proof_kind (fst (global_term γ (qname_in p x)))
  (** In a table's submodule: the entry's module part *)
  | y :: ys', set_module_members ms =>
      match members_lookup ms y with
      | Some e => module_member_proofs (set_entry_module_part e) ys' x
      | None => false
      end
  (** In a global module's submodule: the valuation's module there *)
  | y :: ys', set_module_global p _ => module_member_proofs (global_module γ (qname_in p y)) ys' x
  end.

(** The term member [x] of a module is a proof. *)
Definition member_is_proof (m : set_module) (x : string) : Prop := module_member_proofs m nil x = true.

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
