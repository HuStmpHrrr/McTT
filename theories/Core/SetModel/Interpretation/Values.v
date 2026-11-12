(** * The Values of the Set Model

    What a variable or a member denotes: a term, a module, or both
    ([set_entry]); a module is a function of its parameters' values, a
    table of members, or a global module at arguments ([set_module]).  An
    environment gives every variable an entry ([set_env]). *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Sets Require Export Encodings.
From Mctt.Core.SetModel.Interpretation Require Export Codes.
From Mctt.Core.Syntactic Require Import Syntax.

(** Which members of a module are proofs: [P ys x] says whether the member
    [x] of the submodule at the chain [ys] is. *)
Definition member_proofness : Type := list string -> string -> bool.

(** What a variable or a member denotes. *)
Inductive set_entry : Type :=
(** A term of the kind [kind], its value.  The kind is the one the syntax
    stores ([ce_ass], [ge_def]); it tells a member closure over a module's
    parameters whether it is a proof *)
| set_entry_term (kind : abs_kind) (value : aczel_set)
(** A module *)
| set_entry_module (m : set_module)
(** A definition with a module part: its term, relevant, and its module *)
| set_entry_both (value : aczel_set) (m : set_module)
with set_module : Type :=
(** A unit's parameter of the type code [domain]: a function of the
    parameter's value, with which of its members are proofs.  That is read
    off the unit's syntax ([unit_member_proofs]), not off [f]: [f] is
    fixed only on the domain, which may be empty, and an empty domain
    tells nothing.  In [module M (n : ℕ) (z : Empty) where def k : ℕ ≔ n
    end] the member [k] is no proof, so [M.k] is the function
    [n ↦ ∅] of [Π (n : ℕ) (z : Empty), ℕ]; in
    [module M (n : ℕ) (z : Empty) where def p : ⊤ ≔ tt end] the member
    [p] is one, so [M.p] is the empty set, as every proof is *)
| set_module_params (domain : aczel_set) (proofs : member_proofness) (f : aczel_set -> set_module)
(** A body: its members by name, in order *)
| set_module_members (members : list (string * set_entry))
(** The global module at the path [p], at the arguments [args],
    outermost first *)
| set_module_global (p : qname) (args : list aczel_set)
(** [m] where [condition] holds, nothing where it fails: a function of a
    parameter applied to an argument, guarded by the argument being of the
    parameter's type.  The function is fixed only there, so without the
    guard two derivations of an ill-typed [me_app U x], at an argument
    outside [U]'s parameter type, could give unrelated modules; the
    interpretation is then not functional, and the uniqueness of a
    substituted term such as [M[N]], whose derivations are not typed node
    by node, could not be derived.  Which members are proofs is kept
    besides, as the function's: outside the domain [m] is anything *)
| set_module_cond (condition : Prop) (proofs : member_proofness) (m : set_module).

(** An environment: an entry for every variable. *)
Definition set_env : Type := nat -> set_entry.

(** The entry of no binding: never read by a scoped term. *)
Definition absent_set_entry : set_entry := set_entry_term ak_relevant empty_set.

(** The environment of the empty context. *)
Definition empty_set_env : set_env := fun _ => absent_set_entry.

(** [ρ] extended by the entry [e] at the variable [#0]. *)
Definition set_env_extend (ρ : set_env) (e : set_entry) : set_env :=
  fun x => match x with 0 => e | S y => ρ y end.

(** The kind of a context entry's term: an assumption's own, a
    definition's relevant. *)
Definition centry_kind (ce : centry) : abs_kind :=
  match ce with
  | ce_ass κ _ => κ
  | _ => ak_relevant
  end.

(** The kinds of a context's entries, outermost first. *)
Definition ctx_kinds (Δ : ctx) : list abs_kind := List.rev (List.map centry_kind Δ).

(** [ρ] extended by the term values [vs] of the kinds [κs], both outermost
    first: the last is [#0]; a value with no kind left is relevant. *)
Fixpoint set_env_extend_kinded (ρ : set_env) (κs : list abs_kind) (vs : list aczel_set) : set_env :=
  match vs with
  | nil => ρ
  | v :: vs' => set_env_extend_kinded (set_env_extend ρ (set_entry_term (List.hd ak_relevant κs) v)) (List.tl κs) vs'
  end.

(** What an entry gives a term variable: its term, or at a module what
    the substitution's [se_mod] gives one, [Prop] ([sentry_exp]), so that
    interpretation commutes with substitution. *)
Definition set_entry_value (e : set_entry) : aczel_set :=
  match e with
  | set_entry_term _ v | set_entry_both v _ => v
  | set_entry_module _ => prop_universe_code
  end.

(** What an entry gives a module variable: its module, or at a term what
    the substitution's [se_exp] gives one, the empty unit at the empty path
    ([sentry_modexp]). *)
Definition set_entry_module_part (e : set_entry) : set_module :=
  match e with
  | set_entry_module m | set_entry_both _ m => m
  | set_entry_term _ _ => set_module_global (q_abs nil nil) nil
  end.

(** ** Equality of Values *)

(** [set_entry_eq e e']: the entries [e] and [e'] are equal: of one shape
    and kind, with equal parts. *)
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
(** Functions of a parameter: equal domains, the same proofs, equal at
    equal values of the domain *)
| set_module_eq_params : forall a a' P P' f f', set_eq a a' -> (forall ys x, P ys x = P' ys x) ->
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
