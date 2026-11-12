(** * Operations on Semantic Values

    Application of a value to arguments, application of a module to an
    argument, and selection of a member from a module, reading globals
    through a valuation only. *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export ElimGraph.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

(** A value applied to arguments, outermost first. *)
Definition apply_values (f : aczel_set) (args : list aczel_set) : aczel_set := fold_left set_apply args f.

(** The closure of a member of the kind [κ] over a parameter of the type
    code [dom]: a proof at [ak_propositional], otherwise the graph. *)
Definition close_value (κ : abs_kind) (dom : aczel_set) (F : aczel_set -> aczel_set) : aczel_set :=
  match κ with
  | ak_propositional => empty_set
  | _ => graph_set (code_carrier dom) F
  end.

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

(** The kind of the term member [x] of a module: at a parameter, read at
    any argument, the members' kinds not depending on it. *)
Fixpoint member_kind (m : set_module) (x : string) : abs_kind :=
  match m with
  | set_module_params _ f => member_kind (f empty_set) x
  | set_module_members ms =>
      match members_lookup ms x with
      | Some (set_entry_term κ _) => κ
      | _ => ak_relevant
      end
  | set_module_global p _ => fst (global_term γ (qname_in p x))
  end.

(** The term member [x] of a module: the closed value of a global one at
    the module's arguments, a table's entry, or, over a parameter, the
    member's closure. *)
Fixpoint select_term (m : set_module) (x : string) : aczel_set :=
  match m with
  | set_module_params dom f => close_value (member_kind (f empty_set) x) dom (fun v => select_term (f v) x)
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
