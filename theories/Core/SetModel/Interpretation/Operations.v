(** * Operations on Semantic Values

    Application of a term's meaning to an argument (value and type code
    together), application of a module to an argument, and selection of a
    member from a module, reading globals through a valuation only. *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export ElimGraph.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

(** The type code of an application of a term of the type code [C] to
    [x]: the codomain at [x] of a [Π], a proposition (any) at a proof. *)
Definition apply_type (C x : aczel_set) : aczel_set :=
  cond_either (is_relevant_code C) (pi_codomain C x) (is_prop_code C) (prop_code True).

(** A term's meaning applied to [x]. *)
Definition apply_meaning (m : set_meaning) (x : aczel_set) : set_meaning :=
  mk_set_meaning (set_apply (meaning_value m) x) (apply_type (meaning_type m) x).

(** A term's meaning applied to arguments, outermost first. *)
Definition apply_meaning_args (m : set_meaning) (args : list aczel_set) : set_meaning :=
  fold_left apply_meaning args m.

(** The closure of a member over a parameter of the type code [dom], at
    the kind of the member: a proof at [ak_propositional], with a
    [∀] for type, otherwise the graph with a [Π] for type. *)
Definition close_meaning (κ : abs_kind) (dom : aczel_set) (F : aczel_set -> set_meaning) : set_meaning :=
  match κ with
  | ak_propositional => mk_set_meaning empty_set (forall_code dom (fun v => meaning_type (F v)))
  | _ => mk_set_meaning (graph_set (code_carrier dom) (fun v => meaning_value (F v))) (pi_code dom (fun v => meaning_type (F v)))
  end.

Section Modules.
  Variables (T : universe_tower) (γ : global_valuation).

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
      | Some (set_entry_term κ _ _) => κ
      | _ => ak_relevant
      end
  | set_module_global _ _ => ak_relevant
  end.

(** The term member [x] of a module: the closed value of a global one at
    the module's arguments, a table's entry, or, over a parameter, the
    member's closure. *)
Fixpoint select_term (m : set_module) (x : string) : set_meaning :=
  match m with
  | set_module_params dom f => close_meaning (member_kind (f empty_set) x) dom (fun v => select_term (f v) x)
  | set_module_members ms =>
      match members_lookup ms x with
      | Some e => set_entry_meaning T e
      | None => mk_set_meaning empty_set empty_set
      end
  | set_module_global p args => apply_meaning_args (global_term γ (qname_in p x)) args
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
