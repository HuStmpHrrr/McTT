(** * Operations on Semantic Values

    Application of a value to arguments, application of a module to an
    argument, and selection of a member from a module, reading globals
    through a valuation only. *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export Elements.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

(** A value applied to arguments, outermost first. *)
Definition apply_values (f : aczel_set) (args : list aczel_set) : aczel_set := fold_left set_apply args f.

Section Modules.
  Variable γ : global_valuation.

(** A module applied to an argument: a parameter takes it, a global module
    records it. *)
Definition apply_module (m : set_module) (x : aczel_set) : set_module :=
  match m with
  | set_module_params _ f => f x
  | set_module_global p args => set_module_global p (args ++ [x])
  | set_module_members ms => set_module_members ms
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

(** The term member [x] of a module is a proof: at every value of a
    parameter's type (a function of a parameter is fixed only there), in a
    table as a proposition's entry, in a global module by the kind of its
    global. *)
Fixpoint member_is_proof (m : set_module) (x : string) : Prop :=
  match m with
  | set_module_params dom f => forall v, set_mem v (code_carrier dom) -> member_is_proof (f v) x
  | set_module_members ms => exists v, members_lookup ms x = Some (set_entry_term ak_propositional v)
  | set_module_global p _ => fst (global_term γ (qname_in p x)) = ak_propositional
  end.

(** The term member [x] of a module: the closed value of a global one at
    the module's arguments, a table's entry, or, over a parameter, the
    member's closure: the empty set for a proof, otherwise the graph. *)
Fixpoint select_term (m : set_module) (x : string) : aczel_set :=
  match m with
  | set_module_params dom f =>
      cond (~ member_is_proof m x) (graph_set (code_carrier dom) (fun v => select_term (f v) x))
  | set_module_members ms =>
      match members_lookup ms x with
      | Some e => set_entry_value e
      | None => empty_set
      end
  | set_module_global p args => apply_values (snd (global_term γ (qname_in p x))) args
  end.

(** The submodule [y] of a module: the closed module of a global one at
    the module's arguments, a table's entry, or, over a parameter, the
    submodule over it. *)
Fixpoint select_module (m : set_module) (y : string) : set_module :=
  match m with
  | set_module_params dom f => set_module_params dom (fun v => select_module (f v) y)
  | set_module_members ms =>
      match members_lookup ms y with
      | Some e => set_entry_module_part e
      | None => set_module_members nil
      end
  | set_module_global p args => apply_module_args (global_module γ (qname_in p y)) args
  end.

End Modules.
