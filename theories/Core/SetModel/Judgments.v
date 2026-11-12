(** * The Set Judgments

    The judgments of the set model, at a universe tower [T] and a
    valuation [γ] of the global context.  Environments of a context are
    related ([set_env_rel]) when their entries are equal and of the
    entries' types, definitions and units; a term denotes a function of
    the environment ([set_denotes]) when that function is its value at
    every environment of the context and every value of it at a related
    environment equals the function's.  Existence and uniqueness are thus
    proved together, by the fundamental theorem, for well-formed terms
    only.

    The judgments then follow the syntactic ones: equal terms of a type
    denote one function into the type's carriers ([set_exp_eq]), a subtype
    has the smaller carriers ([set_subtyp]), equal extensions relate the
    same environments ([set_ext_eq]), equal module expressions and units
    denote one module whose members are of their types ([set_modexp_eq],
    [set_unit_eq]). *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Respects.
From Mctt.Core.Syntactic Require Import Syntax Members.
Import ListNotations.

(** The environment without its variable [#0]. *)
Definition set_env_tail (ρ : set_env) : set_env := fun x => ρ (S x).

Section Judgments.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** ** Related Environments *)

(** [set_assumption_with Γ ρ κ A e e' x x' a]: the entries [e] and [e'] of
    an assumption of [A] of the kind [κ] are equal values [x] and [x'] of
    [A]'s value [a]. *)
Record set_assumption_with (Γ : ctx) (ρ : set_env) (κ : abs_kind) (A : exp) (e e' : set_entry) (x x' a : aczel_set) : Prop :=
  { (** The left entry is the term [x] *)
    set_assumption_left : e = set_entry_term κ x
    (** The right entry is the term [x'] *)
  ; set_assumption_right : e' = set_entry_term κ x'
    (** [A] denotes [a] *)
  ; set_assumption_type : set_interp T γ Γ ρ A a
    (** [x] is of [a] *)
  ; set_assumption_mem : set_mem x (code_carrier a)
    (** The two are equal *)
  ; set_assumption_eq : set_eq x x' }.

(** [set_definition_with Γ ρ M e e' v v' w]: the entries [e] and [e'] of a
    definition of [M] are values [v] and [v'] equal to [M]'s value [w]. *)
Record set_definition_with (Γ : ctx) (ρ : set_env) (M : exp) (e e' : set_entry) (v v' w : aczel_set) : Prop :=
  { (** The left entry is the relevant term [v] *)
    set_definition_left : e = set_entry_term ak_relevant v
    (** The right entry is the relevant term [v'] *)
  ; set_definition_right : e' = set_entry_term ak_relevant v'
    (** [M] denotes [w] *)
  ; set_definition_value : set_interp T γ Γ ρ M w
    (** [v] is [w] *)
  ; set_definition_left_eq : set_eq v w
    (** [v'] is [w] *)
  ; set_definition_right_eq : set_eq v' w }.

(** [set_module_slot_with Γ ρ U e e' m m' n]: the entries [e] and [e'] of
    a module slot of the unit [U] are modules [m] and [m'] equal to [U]'s
    module [n]. *)
Record set_module_slot_with (Γ : ctx) (ρ : set_env) (U : gunit) (e e' : set_entry) (m m' n : set_module) : Prop :=
  { (** The left entry is the module [m] *)
    set_module_slot_left : e = set_entry_module m
    (** The right entry is the module [m'] *)
  ; set_module_slot_right : e' = set_entry_module m'
    (** [U] denotes [n] *)
  ; set_module_slot_unit : set_interp_gunit T γ Γ ρ U n
    (** [m] is [n] *)
  ; set_module_slot_left_eq : set_module_eq m n
    (** [m'] is [n] *)
  ; set_module_slot_right_eq : set_module_eq m' n }.

(** [set_definition_module_with Γ ρ M U e e' v v' w m m' n]: the entries
    [e] and [e'] of a definition of [M] with the module part [U] are terms
    [v], [v'] equal to [M]'s value [w], with modules [m], [m'] equal to
    [U]'s module [n]. *)
Record set_definition_module_with (Γ : ctx) (ρ : set_env) (M : exp) (U : gunit) (e e' : set_entry)
    (v v' w : aczel_set) (m m' n : set_module) : Prop :=
  { (** The left entry is the term [v] with the module [m] *)
    set_definition_module_left : e = set_entry_both v m
    (** The right entry is the term [v'] with the module [m'] *)
  ; set_definition_module_right : e' = set_entry_both v' m'
    (** [M] denotes [w] *)
  ; set_definition_module_value : set_interp T γ Γ ρ M w
    (** [U] denotes [n] *)
  ; set_definition_module_unit : set_interp_gunit T γ Γ ρ U n
    (** [v] is [w] *)
  ; set_definition_module_left_eq : set_eq v w
    (** [v'] is [w] *)
  ; set_definition_module_right_eq : set_eq v' w
    (** [m] is [n] *)
  ; set_definition_module_left_module_eq : set_module_eq m n
    (** [m'] is [n] *)
  ; set_definition_module_right_module_eq : set_module_eq m' n }.

(** [set_entry_rel Γ ρ ce e e']: [e] and [e'] are related entries of the
    context entry [ce] of [Γ], at [ρ]. *)
Definition set_entry_rel (Γ : ctx) (ρ : set_env) (ce : centry) (e e' : set_entry) : Prop :=
  match ce with
  | ce_ass κ A => exists x x' a, set_assumption_with Γ ρ κ A e e' x x' a
  | ce_def _ M => exists v v' w, set_definition_with Γ ρ M e e' v v' w
  | ce_mod U => exists m m' n, set_module_slot_with Γ ρ U e e' m m' n
  | ce_dm _ M U => exists v v' w m m' n, set_definition_module_with Γ ρ M U e e' v v' w m m' n
  end.

(** [set_env_rel Γ ρ ρ']: [ρ] and [ρ'] are related environments of [Γ]. *)
Fixpoint set_env_rel (Γ : ctx) (ρ ρ' : set_env) : Prop :=
  match Γ with
  | nil => True
  | ce :: Γ' => set_env_rel Γ' (set_env_tail ρ) (set_env_tail ρ') /\ set_entry_rel Γ' (set_env_tail ρ) ce (ρ 0) (ρ' 0)
  end.

(** [ρ] is an environment of [Γ]. *)
Definition set_env_in (Γ : ctx) (ρ : set_env) : Prop := set_env_rel Γ ρ ρ.

(** ** Denotations *)

(** [set_denotes Γ M F]: [M] denotes [F] in [Γ]. *)
Record set_denotes (Γ : ctx) (M : exp) (F : set_env -> aczel_set) : Prop :=
  { (** [F ρ] is [M]'s value at every environment *)
    set_denotes_exists : forall ρ, set_env_in Γ ρ -> set_interp T γ Γ ρ M (F ρ)
    (** Every value of [M] at a related environment is [F]'s *)
  ; set_denotes_unique : forall ρ ρ' v, set_env_rel Γ ρ ρ' -> set_interp T γ Γ ρ' M v -> set_eq v (F ρ) }.

(** [set_modexp_denotes Γ H F]: the module expression [H] denotes [F] in
    [Γ]. *)
Record set_modexp_denotes (Γ : ctx) (H : modexp) (F : set_env -> set_module) : Prop :=
  { (** [F ρ] is [H]'s module at every environment *)
    set_modexp_denotes_exists : forall ρ, set_env_in Γ ρ -> set_interp_modexp T γ Γ ρ H (F ρ)
    (** Every module of [H] at a related environment is [F]'s *)
  ; set_modexp_denotes_unique : forall ρ ρ' m, set_env_rel Γ ρ ρ' -> set_interp_modexp T γ Γ ρ' H m -> set_module_eq m (F ρ) }.

(** The submodule at the chain [ys] of a module. *)
Definition select_modules (m : set_module) (ys : list string) : set_module := fold_left (select_module γ) ys m.

(** [set_members_valid Γ H F]: every term member of a submodule of [H],
    of [F]'s modules, is of its type, and is its δ-reduct when it has
    one. *)
Definition set_members_valid (Γ : ctx) (H : modexp) (F : set_env -> set_module) : Prop :=
  forall ys x R A FA, mdenote gc_deps gc_stack Γ (me_mem (me_mems H ys) x) R -> mdesc_type R = Some A ->
    set_denotes Γ A FA -> forall ρ, set_env_in Γ ρ ->
    set_mem (select_term γ (select_modules (F ρ) ys) x) (code_carrier (FA ρ)) /\
    (forall N FN, mdesc_reduct R = Some N -> set_denotes Γ N FN -> set_eq (select_term γ (select_modules (F ρ) ys) x) (FN ρ)).

(** ** The Judgments *)

(** [set_exp_eq_with Γ A M M' FA FM]: [A] denotes [FA], [M] and [M'] both
    [FM], of [FA]'s carriers. *)
Record set_exp_eq_with (Γ : ctx) (A M M' : exp) (FA FM : set_env -> aczel_set) : Prop :=
  { (** The type's denotation *)
    set_exp_eq_type : set_denotes Γ A FA
    (** The left term's *)
  ; set_exp_eq_left : set_denotes Γ M FM
    (** The right term's, the same *)
  ; set_exp_eq_right : set_denotes Γ M' FM
    (** Of the type *)
  ; set_exp_eq_mem : forall ρ, set_env_in Γ ρ -> set_mem (FM ρ) (code_carrier (FA ρ)) }.

(** [M] and [M'] are equal terms of the type [A] in [Γ]. *)
Definition set_exp_eq (Γ : ctx) (A M M' : exp) : Prop := exists FA FM, set_exp_eq_with Γ A M M' FA FM.

(** [set_subtyp_with Γ A A' FA FA']: [A] and [A'] denote [FA] and [FA'],
    the first's carriers in the second's. *)
Record set_subtyp_with (Γ : ctx) (A A' : exp) (FA FA' : set_env -> aczel_set) : Prop :=
  { (** The subtype's denotation *)
    set_subtyp_left : set_denotes Γ A FA
    (** The supertype's *)
  ; set_subtyp_right : set_denotes Γ A' FA'
    (** The subtype's carriers are in the supertype's *)
  ; set_subtyp_sub : forall ρ, set_env_in Γ ρ -> set_sub (code_carrier (FA ρ)) (code_carrier (FA' ρ)) }.

(** [A] is a subtype of [A'] in [Γ]. *)
Definition set_subtyp (Γ : ctx) (A A' : exp) : Prop := exists FA FA', set_subtyp_with Γ A A' FA FA'.

(** [set_modexp_eq_with Γ H H' F]: [H] and [H'] both denote [F], whose
    members are valid. *)
Record set_modexp_eq_with (Γ : ctx) (H H' : modexp) (F : set_env -> set_module) : Prop :=
  { (** The left expression's denotation *)
    set_modexp_eq_left : set_modexp_denotes Γ H F
    (** The right expression's, the same *)
  ; set_modexp_eq_right : set_modexp_denotes Γ H' F
    (** Its members are of their types *)
  ; set_modexp_eq_members : set_members_valid Γ H F }.

(** [H] and [H'] are equal module expressions in [Γ]. *)
Definition set_modexp_eq (Γ : ctx) (H H' : modexp) : Prop := exists F, set_modexp_eq_with Γ H H' F.

(** [U] and [U'] are equal units in [Γ]: as literal module expressions. *)
Definition set_unit_eq (Γ : ctx) (U U' : gunit) : Prop := set_modexp_eq Γ (me_lit U) (me_lit U').

(** [set_entry_valid Γ ce]: the context entry [ce] is valid in [Γ]: its
    type, definition or unit denotes. *)
Definition set_entry_valid (Γ : ctx) (ce : centry) : Prop :=
  match ce with
  | ce_ass _ A => exists FA, set_denotes Γ A FA
  | ce_def A M => set_exp_eq Γ A M M
  | ce_mod U => set_unit_eq Γ U U
  | ce_dm A M U => set_exp_eq Γ A M M /\ set_unit_eq Γ U U
  end.

(** [set_ctx Γ]: every entry of [Γ] is valid in the context before it. *)
Fixpoint set_ctx (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | ce :: Γ' => set_ctx Γ' /\ set_entry_valid Γ' ce
  end.

(** [set_ext_eq_with Γ Ψ Ψ']: the extensions [Ψ] and [Ψ'] of [Γ] are
    valid and relate the same environments. *)
Record set_ext_eq_with (Γ Ψ Ψ' : ctx) : Prop :=
  { (** The left extension is valid *)
    set_ext_eq_left : set_ctx (Ψ ++ Γ)
    (** The right extension is valid *)
  ; set_ext_eq_right : set_ctx (Ψ' ++ Γ)
    (** They relate the same environments *)
  ; set_ext_eq_rel : forall ρ ρ', set_env_rel (Ψ ++ Γ) ρ ρ' <-> set_env_rel (Ψ' ++ Γ) ρ ρ' }.

End Judgments.
