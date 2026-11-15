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
    denote one function into the type's carriers ([set_rel_exp_eq]), a
    subtype has the smaller carriers ([set_rel_subtyp]), equal extensions
    relate the same environments ([set_ext_eq_with]), equal module
    expressions and units denote one module and are valid
    ([set_rel_modexp_eq], [set_rel_unit_eq]): what they are built of
    denotes, so that their members are of their types.

    Those are read at one global context.  The valuations that model a
    global context come next ([set_gctx_ok]), then what it is for one to
    model a context at a bigger one ([set_gctx_embedding]), and last the
    judgments the fundamental theorem concludes ([set_exp_eq] and the
    rest), each its one-context judgment read at every context its own is
    modelled at, as the gluing model's are. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Functional.
From Mctt.Core.SetModel.Interpretation Require Import ContextRelation.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export Bound.
From Mctt.Core.Syntactic Require Import Syntax Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths Presup.
Import ListNotations.

(** The environment without its variable [#0]. *)
Definition set_env_tail (ρ : set_env) : set_env := fun x => ρ (S x).

(** [ρ] without its first [n] entries. *)
Definition set_env_drop (n : nat) (ρ : set_env) : set_env := fun x => ρ (n + x).

(** The universe of sets a universe's value is the code of. *)
Definition universe_shape (FU : set_env -> aczel_set) (ρ : set_env) (V : aczel_set) : Prop :=
  grothendieck V /\ exists l, set_eq (FU ρ) (universe_code l V).

(** [set_member_seen Ξ1 Rm1 x]: [x] is a member of the module part [Rm1]
    as the context with the stack [Ξ1] reads it: an entry of the part, or,
    for a filed module, a stored member, which counts the type former of
    an inductive type whose frame is open on [Ξ1]: in [module P where
    inductive V : Type where | mk : V → V end], [P.V] in [mk]'s type is
    read off the open frame, not off [P]'s body ([mdenote_ind_frame]). *)
Inductive set_member_seen (Ξ1 : gstack) : mdesc -> string -> Prop :=
(** An entry of the part *)
| set_member_seen_entry : forall Rm1 x e, mdesc_entry Rm1 x = Some e -> set_member_seen Ξ1 Rm1 x
(** A stored member of a filed module, its body's or an open frame's former *)
| set_member_seen_stored : forall Θ' p T Φ1 Ns x R0, stored_term_member Ξ1 Φ1 p x R0 ->
    set_member_seen Ξ1 (mdesc_closed Θ' p T Φ1 Ns) x
(** A frame open on [Ξ1] under a filed module, a submodule there before
    it is filed: in [module M where module N where … end end], [M.N] names
    the open frame while [N]'s body is checked *)
| set_member_seen_frame : forall Θ' p T Φ1 Ns y Ty Φy, gc_frame Ξ1 (qname_in p y) = Some (Ty, Φy) ->
    set_member_seen Ξ1 (mdesc_closed Θ' p T Φ1 Ns) y.

(** [set_member_at Θ1 Ξ1 Θ2 Ξ2 Rm x]: [x] is a member of the module part
    [Rm] read at [Θ2 ⍮ Ξ2] that the part it grew from at [Θ1 ⍮ Ξ1] already
    has.  A frame grows after a term is checked against it: in
    [module M where def a ≔ 0; def b ≔ … M.a …; def c ≔ 1 end], [b] is
    checked against [M = {a}], and the members a judgment about [b] may
    speak of are those. *)
Definition set_member_at (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Rm : mdesc) (x : string) : Prop :=
  exists Rm1, mdesc_grows Θ1 Ξ1 Θ2 Ξ2 Rm1 Rm /\ set_member_seen Ξ1 Rm1 x.

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

(** [set_definition_with Γ ρ M r e e' v v' w]: the entries [e] and [e'] of
    a definition of [M] are values [v] and [v'] of the tag [r], equal to
    [M]'s value [w].  The tag is any: the interpretation reads only the
    values, and a body stores each definition at its own tag
    ([set_interp_ge_def]), which [body_ctx] does not keep.  In
    [module M where def p : ⊤ ≔ tt; def q : ⊤ ≔ p end], [p]'s entry is a
    proof's, and [q] is read at it as at a definition of [body_ctx]. *)
Record set_definition_with (Γ : ctx) (ρ : set_env) (M : exp) (r : abs_kind) (e e' : set_entry) (v v' w : aczel_set) : Prop :=
  { (** The left entry is the term [v] *)
    set_definition_left : e = set_entry_term r v
    (** The right entry is the term [v'] *)
  ; set_definition_right : e' = set_entry_term r v'
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
  ; set_module_slot_left_eq : set_module_eq γ m n
    (** [m'] is [n] *)
  ; set_module_slot_right_eq : set_module_eq γ m' n }.

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
  ; set_definition_module_left_module_eq : set_module_eq γ m n
    (** [m'] is [n] *)
  ; set_definition_module_right_module_eq : set_module_eq γ m' n }.

(** [set_entry_rel Γ ρ ce e e']: [e] and [e'] are related entries of the
    context entry [ce] of [Γ], at [ρ]. *)
Definition set_entry_rel (Γ : ctx) (ρ : set_env) (ce : centry) (e e' : set_entry) : Prop :=
  match ce with
  | ce_ass κ A => exists x x' a, set_assumption_with Γ ρ κ A e e' x x' a
  | ce_def _ M => exists r v v' w, set_definition_with Γ ρ M r e e' v v' w
  | ce_mod U => exists m m' n, set_module_slot_with Γ ρ U e e' m m' n
  | ce_dm _ M U => exists v v' w m m' n, set_definition_module_with Γ ρ M U e e' v v' w m m' n
  end.

(** [set_env_rel Γ ρ ρ']: [ρ] and [ρ'] are related environments of [Γ];
    below the context their entries are equal, as a term read past its
    context would read them. *)
Fixpoint set_env_rel (Γ : ctx) (ρ ρ' : set_env) : Prop :=
  match Γ with
  | nil => set_env_eq γ ρ ρ'
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
  ; set_modexp_denotes_unique : forall ρ ρ' m, set_env_rel Γ ρ ρ' -> set_interp_modexp T γ Γ ρ' H m -> set_module_eq γ m (F ρ) }.

(** [set_member_known Θ1 Ξ1 Γ H x]: [x] is a member of [H]'s module part
    here that the context [Θ1 ⍮ Ξ1] this one grew from already has
    ([set_member_at]).  It is read off the module part, not off [H], as
    [H] and the unit it is equal to share their module part
    ([set_modexp_valid_with]): for [H = A.B] with [A ≔ C], the unit is
    [C.B], of which the smaller context need know nothing. *)
Definition set_member_known (Θ1 : gdeps) (Ξ1 : gstack) (Γ : ctx) (H : modexp) (x : string) : Prop :=
  forall R0 R0m, mdenote gc_deps gc_stack Γ H R0 -> mdesc_mod R0 = Some R0m -> set_member_at Θ1 Ξ1 gc_deps gc_stack R0m x.

(** [set_members_valid Θ1 Ξ1 Γ H F]: every term member of [H] that the
    context [Θ1 ⍮ Ξ1] already has, of [F]'s modules, is of its type, and
    is its δ-reduct when it has one.  A member of a submodule is one of
    the submodule's, valid in its turn. *)
Definition set_members_valid (Θ1 : gdeps) (Ξ1 : gstack) (Γ : ctx) (H : modexp) (F : set_env -> set_module) : Prop :=
  forall x R A FA, set_member_known Θ1 Ξ1 Γ H x -> mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    set_denotes Γ A FA -> forall ρ, set_env_in Γ ρ ->
    set_mem (select_term γ (F ρ) x) (code_carrier (FA ρ)) /\
    (forall N FN, mdesc_reduct R = Some N -> set_denotes Γ N FN -> set_eq (select_term γ (F ρ) x) (FN ρ)).

(** ** The Judgments *)

(** [set_exp_eq_with Γ A M M' FA FM FM']: [A] denotes [FA], [M] and [M']
    the equal [FM] and [FM'], of [FA]'s carriers.  The two are equal, not
    the same function: a denotation is a term's exact value, and equal terms
    such as [(λ A M) N] and [M[N]] have equal values, not the same. *)
Record set_exp_eq_with (Γ : ctx) (A M M' : exp) (FA FM FM' : set_env -> aczel_set) : Prop :=
  { (** The type's denotation *)
    set_exp_eq_type : set_denotes Γ A FA
    (** The left term's *)
  ; set_exp_eq_left : set_denotes Γ M FM
    (** The right term's *)
  ; set_exp_eq_right : set_denotes Γ M' FM'
    (** The two are equal *)
  ; set_exp_eq_eq : forall ρ, set_env_in Γ ρ -> set_eq (FM ρ) (FM' ρ)
    (** Of the type *)
  ; set_exp_eq_mem : forall ρ, set_env_in Γ ρ -> set_mem (FM ρ) (code_carrier (FA ρ)) }.

(** [M] and [M'] are equal terms of the type [A] in [Γ], at this one
    global context: the building block of [set_exp_eq]. *)
Definition set_rel_exp_eq (Γ : ctx) (A M M' : exp) : Prop := exists FA FM FM', set_exp_eq_with Γ A M M' FA FM FM'.

(** [set_subtyp_with Γ A A' FA FA']: [A] and [A'] denote [FA] and [FA'],
    the first's carriers in the second's. *)
Record set_subtyp_with (Γ : ctx) (A A' : exp) (FA FA' : set_env -> aczel_set) : Prop :=
  { (** The subtype's denotation *)
    set_subtyp_left : set_denotes Γ A FA
    (** The supertype's *)
  ; set_subtyp_right : set_denotes Γ A' FA'
    (** The subtype's carriers are in the supertype's *)
  ; set_subtyp_sub : forall ρ, set_env_in Γ ρ -> set_sub (code_carrier (FA ρ)) (code_carrier (FA' ρ)) }.

(** [A] is a subtype of [A'] in [Γ], at this one global context: the
    building block of [set_subtyp]. *)
Definition set_rel_subtyp (Γ : ctx) (A A' : exp) : Prop := exists FA FA', set_subtyp_with Γ A A' FA FA'.

(** [set_modexp_rel_with Γ H H' F F']: [H] and [H'] denote the equal [F]
    and [F'] in [Γ]. *)
Record set_modexp_rel_with (Γ : ctx) (H H' : modexp) (F F' : set_env -> set_module) : Prop :=
  { (** The left expression's denotation *)
    set_modexp_rel_left : set_modexp_denotes Γ H F
    (** The right expression's *)
  ; set_modexp_rel_right : set_modexp_denotes Γ H' F'
    (** The two are equal *)
  ; set_modexp_rel_eq : forall ρ, set_env_in Γ ρ -> set_module_eq γ (F ρ) (F' ρ) }.

(** [H] and [H'] denote equal modules in [Γ]. *)
Definition set_modexp_rel (Γ : ctx) (H H' : modexp) : Prop := exists F F', set_modexp_rel_with Γ H H' F F'.

(** [set_entry_valid Γ ce]: the context entry [ce] is valid in [Γ]: its
    type, definition or unit denotes.  A slot's unit is valid besides
    ([set_valid_slots]). *)
Definition set_entry_valid (Γ : ctx) (ce : centry) : Prop :=
  match ce with
  | ce_ass _ A => exists FA, set_denotes Γ A FA
  | ce_def A M => set_rel_exp_eq Γ A M M
  | ce_mod U => set_modexp_rel Γ (me_lit U) (me_lit U)
  | ce_dm A M U => set_rel_exp_eq Γ A M M /\ set_modexp_rel Γ (me_lit U) (me_lit U)
  end.

(** [set_ctx Γ]: every entry of [Γ] is valid in the context before it. *)
Fixpoint set_ctx (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | ce :: Γ' => set_ctx Γ' /\ set_entry_valid Γ' ce
  end.

(** ** Valid Units and Module Expressions

    A unit is valid when its parts are: a filed module at arguments valid
    against its telescope; a local body whose context denotes, whose
    submodules are valid units in the context the body before each makes,
    and whose opens' targets are valid; an alias whose target is.  A
    module expression is valid when it denotes a module equal to a valid
    unit's of the same module part.  The members of a valid module
    expression are of their types ([set_members_valid]). *)

(** [set_args_valid Γ T Tr Tf Ns]: the arguments [Ns] fill the outermost
    parameters [Tf] of the closed telescope [T = Tr ++ Tf], each of its
    parameter's type, instantiated by the arguments before it, of an
    evaluated sort. *)
Record set_args_valid (Γ T Tr Tf : ctx) (Ns : list exp) : Prop :=
  { (** The telescope splits at the arguments *)
    set_args_split : T = Tr ++ Tf
    (** One argument per filled parameter *)
  ; set_args_length : List.length Tf = List.length Ns
    (** The filled parameters are assumptions *)
  ; set_args_assumptions : all_assumptions Tf
    (** They are closed *)
  ; set_args_scoped : ctx_scoped 0 Tf
    (** Each argument is of its type *)
  ; set_args_typed : forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Tf sb_id Ns) k = Some A ->
      set_rel_exp_eq Γ A N N
    (** Each type is of an evaluated sort *)
  ; set_args_evaluated : forall k A, nth_error (tele_insts Tf sb_id Ns) k = Some A ->
      exists Srt, evaluated_sort Srt /\ set_rel_exp_eq Γ Srt A A }.

(** [set_params_evaluated Γ Δ l]: each parameter of [Δ] is a type of the
    universe at [l] or a type of levels, in the context after it. *)
Definition set_params_evaluated (Γ Δ : ctx) (l : nat) : Prop :=
  forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 ->
    set_rel_exp_eq (Δ2 ++ Γ) (a_typ l) A A \/ set_rel_exp_eq (Δ2 ++ Γ) a_level_sort A A.

(** [set_body_sorts_valid Φ D]: each term part of the body [Φ] over [D],
    filled in, is of the sort its kind tag says, in [D]: the typing of a
    body unit types its definitions filled in. *)
Fixpoint set_body_sorts_valid (Φ : gmod) (D : ctx) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ0 _ E =>
      set_body_sorts_valid Φ0 D /\
      forall A M σ, entry_tm E = Some (A, M) -> gm_fill Φ0 = Some σ ->
        exists i, set_rel_exp_eq D (abs_kind_sort (entry_kind E) (a_typ i)) (exp_sub A σ) (exp_sub A σ)
  (* read on expansions only, which have no open *)
  | gm_open Φ0 _ _ _ => set_body_sorts_valid Φ0 D
  end.

(** [set_body_ok Γ Δ Φ Φx]: the body [Φ] over the parameters [Δ],
    expanded to [Φx], is well formed and denotes, with its context and its
    opens' targets. *)
Record set_body_ok (Γ Δ : ctx) (Φ Φx : gmod) : Prop :=
  { (** The unit is well formed *)
    set_body_ok_wf : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ)
    (** Its expansion *)
  ; set_body_ok_xp : body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx
    (** Its parameters are assumptions *)
  ; set_body_ok_params : all_assumptions Δ
    (** Of evaluated sorts *)
  ; set_body_ok_evaluated : exists l, set_params_evaluated Γ Δ l
    (** The context denotes *)
  ; set_body_ok_ctx : set_ctx Γ
    (** So does the body's context *)
  ; set_body_ok_body_ctx : set_ctx (body_ctx Φx ++ Δ ++ Γ)
    (** Each entry is of its tag's sort *)
  ; set_body_ok_sorts : set_body_sorts_valid Φx (Δ ++ Γ)
    (** The body has its own shape *)
  ; set_body_ok_shape : body_shape Φ Φ
    (** So does its expansion *)
  ; set_body_ok_shape_xp : body_shape Φx Φx
    (** The unit denotes *)
  ; set_body_ok_rel : set_modexp_rel Γ (me_lit (gu_open Δ Φ)) (me_lit (gu_open Δ Φ))
    (** Each open's target denotes *)
  ; set_body_ok_opens : forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> set_modexp_rel (Ψ ++ Δ ++ Γ) H H }.

(** [set_alias_ok Γ Δ E]: the alias of [E] over the parameters [Δ] is well
    formed and denotes, and so does its target. *)
Record set_alias_ok (Γ Δ : ctx) (E : modexp) : Prop :=
  { (** The unit is well formed *)
    set_alias_ok_wf : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E))
    (** Its parameters are assumptions *)
  ; set_alias_ok_params : all_assumptions Δ
    (** Of evaluated sorts *)
  ; set_alias_ok_evaluated : exists l, set_params_evaluated Γ Δ l
    (** The context denotes *)
  ; set_alias_ok_ctx : set_ctx Γ
    (** So does the parameters' *)
  ; set_alias_ok_params_ctx : set_ctx (Δ ++ Γ)
    (** The unit denotes *)
  ; set_alias_ok_rel : set_modexp_rel Γ (me_lit (gu_mk Δ (md_alias E))) (me_lit (gu_mk Δ (md_alias E)))
    (** So does its target *)
  ; set_alias_ok_target : set_modexp_rel (Δ ++ Γ) E E }.

(** [set_slots_coherent Γ κs]: [κs] gives each slot of [Γ] the proofness
    of its unit, read past the slot.  An environment of [Γ] gives such
    slots ([env_slot_proofs]); so do slots pushed past assumptions, at
    which no environment need exist. *)
Fixpoint set_slots_coherent (Γ : ctx) (κs : nat -> member_proofness) : Prop :=
  match Γ with
  | nil => True
  | ce :: Γ' =>
      set_slots_coherent Γ' (fun s => κs (S s)) /\
      forall U, centry_unit ce = Some U -> forall ys x, κs 0 ys x = unit_member_proofs γ (fun s => κs (S s)) U ys x
  end.

(** [set_modexp_valid_with Γ H K R Rm RK]: [H], well formed and denoting
    [R] of the module part [Rm], is equal to [K], which denotes [RK] of the
    same module part, and has [K]'s proofness. *)
Record set_modexp_valid_with (Γ : ctx) (H K : modexp) (R Rm RK : mdesc) : Prop :=
  { (** [H] is well formed *)
    set_modexp_valid_wf : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H
    (** It denotes [R] *)
  ; set_modexp_valid_desc : mdenote gc_deps gc_stack Γ H R
    (** Of the module part [Rm] *)
  ; set_modexp_valid_mod : mdesc_mod R = Some Rm
    (** Its module is [K]'s *)
  ; set_modexp_valid_rel : set_modexp_rel Γ H K
    (** [K] denotes [RK] *)
  ; set_modexp_valid_unit_desc : mdenote gc_deps gc_stack Γ K RK
    (** Of the same module part *)
  ; set_modexp_valid_unit_mod : mdesc_mod RK = Some Rm
    (** Its members are proofs where [K]'s are, read off the syntax at
        slots coherent with [Γ], not at environments: in
        [module N where def k : ℕ ≔ 0 end] and
        [module M (n : ℕ) (z : Empty) ≔ N], [M.k] is the function
        [n ↦ ∅] of [Π ℕ (Π Empty ℕ)] only if [N]'s proofness says [k] is
        no proof, and [N] is read in [z : Empty, n : ℕ], which has no
        environment: there [N]'s equality to [K] says nothing *)
  ; set_modexp_valid_proofs : forall κs, set_slots_coherent Γ κs -> forall ys x,
      modexp_member_proofs γ κs H ys x = modexp_member_proofs γ κs K ys x }.

(** [set_valid_unit Γ K]: the unit [K] is valid in [Γ]. *)
Inductive set_valid_unit : ctx -> modexp -> Prop :=
(** A filed module at valid arguments *)
| set_valid_unit_filed : forall Γ p T Φ Tr Tf Ns,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc gc_deps gc_stack p = Some (T, Φ) -> set_ctx Γ -> set_args_valid Γ T Tr Tf Ns ->
    set_valid_unit Γ (me_apps (qname_mod p) Ns)
(** A local body: its parts denote, its submodules are valid units in the
    context the body before each makes, and its opens' targets are valid *)
| set_valid_unit_body : forall Γ Δ Φ Φx, set_body_ok Γ Δ Φ Φx ->
    (forall y Φ0 E U, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       set_valid_unit (body_ctx Φ0 ++ Δ ++ Γ) (me_lit U)) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> set_valid_modexp (Ψ ++ Δ ++ Γ) H) ->
    set_valid_unit Γ (me_lit (gu_open Δ Φ))
(** An alias, its target valid *)
| set_valid_unit_alias : forall Γ Δ E, set_alias_ok Γ Δ E -> set_valid_modexp (Δ ++ Γ) E ->
    set_valid_unit Γ (me_lit (gu_mk Δ (md_alias E)))
(** [set_valid_modexp Γ H]: the module expression [H] is valid in [Γ] *)
with set_valid_modexp : ctx -> modexp -> Prop :=
(** [H] is equal to a valid unit of the same module part *)
| set_valid_modexp_intro : forall Γ H K R Rm RK, set_modexp_valid_with Γ H K R Rm RK -> set_valid_unit Γ K ->
    set_valid_modexp Γ H.

Scheme set_valid_unit_mut_ind := Induction for set_valid_unit Sort Prop
with set_valid_modexp_mut_ind := Induction for set_valid_modexp Sort Prop.
Combined Scheme set_valid_unit_modexp_ind from set_valid_unit_mut_ind, set_valid_modexp_mut_ind.

(** [set_valid_slots Γ]: the unit of each slot of [Γ] is valid in the
    context before it. *)
Fixpoint set_valid_slots (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | ce :: Γ' => set_valid_slots Γ' /\ forall U, centry_unit ce = Some U -> set_valid_unit Γ' (me_lit U)
  end.

(** [set_modexp_eq_with Γ H H' F F']: [H] and [H'] denote the equal [F] and
    [F'], are valid, and have the same proofness. *)
Record set_modexp_eq_with (Γ : ctx) (H H' : modexp) (F F' : set_env -> set_module) : Prop :=
  { (** The left expression's denotation *)
    set_modexp_eq_left : set_modexp_denotes Γ H F
    (** The right expression's *)
  ; set_modexp_eq_right : set_modexp_denotes Γ H' F'
    (** The two are equal *)
  ; set_modexp_eq_eq : forall ρ, set_env_in Γ ρ -> set_module_eq γ (F ρ) (F' ρ)
    (** The left expression is valid *)
  ; set_modexp_eq_valid : set_valid_modexp Γ H
    (** So is the right one *)
  ; set_modexp_eq_valid' : set_valid_modexp Γ H'
    (** Their members are proofs at the same places, read off the syntax
        at slots coherent with [Γ], not at environments: in
        [module M (z : Empty) ≔ N] and [module M (z : Empty) ≔ N'], where
        the member [k] is a proof in [N] and not in [N'], the two units
        denote equal modules, as [z : Empty] has no environment, yet
        [M.k] is [∅] on one side and a graph on the other: equal
        denotations say nothing there *)
  ; set_modexp_eq_proofs : forall κs, set_slots_coherent Γ κs -> forall ys x,
      modexp_member_proofs γ κs H ys x = modexp_member_proofs γ κs H' ys x }.

(** [H] and [H'] are equal module expressions in [Γ], at this one global
    context: the building block of [set_modexp_eq]. *)
Definition set_rel_modexp_eq (Γ : ctx) (H H' : modexp) : Prop := exists F F', set_modexp_eq_with Γ H H' F F'.

(** [set_unit_eq_with Γ U U' F F']: the units [U] and [U'] denote the
    equal [F] and [F'] as literals, are valid, and have the same
    proofness. *)
Record set_unit_eq_with (Γ : ctx) (U U' : gunit) (F F' : set_env -> set_module) : Prop :=
  { (** The left unit's denotation *)
    set_unit_eq_left : set_modexp_denotes Γ (me_lit U) F
    (** The right unit's *)
  ; set_unit_eq_right : set_modexp_denotes Γ (me_lit U') F'
    (** The two are equal *)
  ; set_unit_eq_eq : forall ρ, set_env_in Γ ρ -> set_module_eq γ (F ρ) (F' ρ)
    (** The left unit is valid *)
  ; set_unit_eq_valid : set_valid_unit Γ (me_lit U)
    (** So is the right one *)
  ; set_unit_eq_valid' : set_valid_unit Γ (me_lit U')
    (** Their members are proofs at the same places, read off the syntax
        at slots coherent with [Γ] (why not at environments: see
        [set_modexp_eq_proofs]) *)
  ; set_unit_eq_proofs : forall κs, set_slots_coherent Γ κs -> forall ys x,
      unit_member_proofs γ κs U ys x = unit_member_proofs γ κs U' ys x }.

(** [U] and [U'] are equal units in [Γ], at this one global context: the
    building block of [set_unit_eq]. *)
Definition set_rel_unit_eq (Γ : ctx) (U U' : gunit) : Prop := exists F F', set_unit_eq_with Γ U U' F F'.

(** [set_ext_eq_with Γ Ψ Ψ']: the extensions [Ψ] and [Ψ'] of [Γ] are
    valid and relate the same environments. *)
Record set_ext_eq_with (Γ Ψ Ψ' : ctx) : Prop :=
  { (** The left extension is valid *)
    set_ext_eq_left : set_ctx (Ψ ++ Γ)
    (** The right extension is valid *)
  ; set_ext_eq_right : set_ctx (Ψ' ++ Γ)
    (** They relate the same environments *)
  ; set_ext_eq_rel : forall ρ ρ', set_env_rel (Ψ ++ Γ) ρ ρ' <-> set_env_rel (Ψ' ++ Γ) ρ ρ' }.

(** ** Denotations Respect Related Environments *)

Lemma set_denotes_rel : forall Γ M F ρ ρ', set_denotes Γ M F -> set_env_rel Γ ρ ρ' -> set_env_in Γ ρ' ->
    set_eq (F ρ') (F ρ).
Proof. intros * [Hex Hun] Hr Hin. exact (Hun _ _ _ Hr (Hex _ Hin)). Qed.

Lemma set_modexp_denotes_rel : forall Γ H F ρ ρ', set_modexp_denotes Γ H F -> set_env_rel Γ ρ ρ' -> set_env_in Γ ρ' ->
    set_module_eq γ (F ρ') (F ρ).
Proof. intros * [Hex Hun] Hr Hin. exact (Hun _ _ _ Hr (Hex _ Hin)). Qed.

(** A module expression's module is equal to itself. *)
Lemma set_modexp_denotes_refl : forall Γ H F ρ, set_modexp_denotes Γ H F -> set_env_in Γ ρ -> set_module_eq γ (F ρ) (F ρ).
Proof. intros * HF Hρ. exact (set_modexp_denotes_unique _ _ _ HF _ _ _ Hρ (set_modexp_denotes_exists _ _ _ HF _ Hρ)). Qed.

Lemma set_interp_me_lit_iff : forall Γ ρ U m, set_interp_modexp T γ Γ ρ (me_lit U) m <-> set_interp_gunit T γ Γ ρ U m.
Proof. intros. split; intros H; [inversion H; subst; assumption | constructor; exact H]. Qed.

(** Related environments extended by equal values of an assumption's
    type are related. *)
Lemma set_env_rel_extend_ass : forall Γ ρ ρ' κ A a x x', set_env_rel Γ ρ ρ' -> set_interp T γ Γ ρ A a ->
    set_mem x (code_carrier a) -> set_eq x x' ->
    set_env_rel (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ x)) (set_env_extend ρ' (set_entry_term κ x')).
Proof. intros * Hr Ha Hx E. split; [exact Hr |]. exists x, x', a. constructor; auto. Qed.

Lemma set_env_in_extend_ass : forall Γ ρ κ A a x, set_env_in Γ ρ -> set_interp T γ Γ ρ A a ->
    set_mem x (code_carrier a) -> set_env_in (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ x)).
Proof. intros * Hr Ha Hx. apply set_env_rel_extend_ass with (a := a); [exact Hr | exact Ha | exact Hx | apply set_eq_refl]. Qed.

(** Related environments of a valid context form a partial equivalence. *)
Lemma set_env_rel_per : forall Γ, set_ctx Γ ->
    (forall ρ ρ', set_env_rel Γ ρ ρ' -> set_env_rel Γ ρ' ρ) /\
    (forall ρ1 ρ2 ρ3, set_env_rel Γ ρ1 ρ2 -> set_env_rel Γ ρ2 ρ3 -> set_env_rel Γ ρ1 ρ3).
Proof.
  induction Γ as [| ce Γ IH]; intros HΓ.
  { split; cbn [set_env_rel].
    - intros ρ ρ' H x. apply set_entry_eq_sym. apply H.
    - intros ρ1 ρ2 ρ3 H1 H2 x. eapply set_entry_eq_trans; [apply H1 | apply H2]. }
  destruct HΓ as [HΓ Hce]. destruct (IH HΓ) as [Hsym Htrans].
  assert (Hin : forall ρ ρ', set_env_rel Γ ρ ρ' -> set_env_in Γ ρ /\ set_env_in Γ ρ')
    by (intros ρ ρ' H; split; [eapply Htrans; [exact H | apply Hsym; exact H] | eapply Htrans; [apply Hsym; exact H | exact H]]).
  split.
  - intros ρ ρ' [Ht He]. split; [apply Hsym; exact Ht |].
    destruct (Hin _ _ Ht) as [Hl Hr].
    destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel set_entry_valid] in He, Hce |- *.
    + destruct He as (x & x' & a & [E1 E2 Ha Hx Exx']). destruct Hce as [FA HFA].
      pose proof (set_denotes_exists _ _ _ HFA _ Hr) as Ha'.
      pose proof (set_denotes_unique _ _ _ HFA _ _ _ Hl Ha) as Ea.
      pose proof (set_denotes_rel _ _ _ _ _ HFA Ht Hr) as Ea'.
      exists x', x, (FA (set_env_tail ρ')). constructor; try assumption; [| apply set_eq_sym; exact Exx'].
      eapply set_mem_eq_l; [exact Exx' |]. eapply set_mem_eq_r; [| exact Hx]. apply code_carrier_resp.
      eapply set_eq_trans; [exact Ea | apply set_eq_sym; exact Ea'].
    + destruct He as (r & v & v' & w & [E1 E2 Hw Ev Ev']). destruct Hce as (FA & FM & FM' & [_ HFM _ _ _]).
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl Hw) as Ew.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht Hr) as Ew'.
      exists r, v', v, (FM (set_env_tail ρ')). constructor; try assumption; [exact (set_denotes_exists _ _ _ HFM _ Hr) | |].
      * eapply set_eq_trans; [exact Ev' |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
      * eapply set_eq_trans; [exact Ev |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
    + destruct He as (m & m' & n & [E1 E2 Hn Em Em']). destruct Hce as (FU & FU' & [HFU _ _]).
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht Hr) as En'.
      exists m', m, (FU (set_env_tail ρ')). constructor; try assumption;
        [exact (proj1 (set_interp_me_lit_iff _ _ _ _) (set_modexp_denotes_exists _ _ _ HFU _ Hr)) | |].
      * eapply set_module_eq_trans; [exact Em' |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
      * eapply set_module_eq_trans; [exact Em |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
    + destruct He as (v & v' & w & m & m' & n & [E1 E2 Hw Hn Ev Ev' Em Em']).
      destruct Hce as [(FA & FM & FM' & [_ HFM _ _ _]) (FU & FU' & [HFU _ _])].
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl Hw) as Ew.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht Hr) as Ew'.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht Hr) as En'.
      exists v', v, (FM (set_env_tail ρ')), m', m, (FU (set_env_tail ρ')). constructor; try assumption;
        [exact (set_denotes_exists _ _ _ HFM _ Hr)
        | exact (proj1 (set_interp_me_lit_iff _ _ _ _) (set_modexp_denotes_exists _ _ _ HFU _ Hr)) | | | |].
      * eapply set_eq_trans; [exact Ev' |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
      * eapply set_eq_trans; [exact Ev |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
      * eapply set_module_eq_trans; [exact Em' |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
      * eapply set_module_eq_trans; [exact Em |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
  - intros ρ1 ρ2 ρ3 [Ht12 He12] [Ht23 He23]. split; [eapply Htrans; eassumption |].
    destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel set_entry_valid] in He12, He23, Hce |- *.
    + destruct He12 as (x1 & x2 & a & [E1 E2 Ha Hx Ex]). destruct He23 as (y2 & y3 & b & [F2 F3 Hb Hy Ey]).
      rewrite E2 in F2. injection F2 as <-. exists x1, y3, a. constructor; try assumption. eapply set_eq_trans; eassumption.
    + destruct He12 as (r & v1 & v2 & w & [E1 E2 Hw Ev1 Ev2]). destruct He23 as (r' & u2 & u3 & w' & [F2 F3 Hw' Eu2 Eu3]).
      rewrite E2 in F2. injection F2 as <- <-. destruct Hce as (FA & FM & FM' & [_ HFM _ _ _]).
      destruct (Hin _ _ Ht12) as [Hl1 Hr2].
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl1 Hw) as Ew.
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hr2 Hw') as Ew'.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht12 Hr2) as E12.
      exists r, v1, u3, w. constructor; try assumption.
      eapply set_eq_trans; [exact Eu3 |]. eapply set_eq_trans; [exact Ew' |].
      eapply set_eq_trans; [exact E12 | apply set_eq_sym; exact Ew].
    + destruct He12 as (m1 & m2 & n & [E1 E2 Hn Em1 Em2]). destruct He23 as (k2 & k3 & n' & [F2 F3 Hn' Ek2 Ek3]).
      rewrite E2 in F2. injection F2 as <-. destruct Hce as (FU & FU' & [HFU _ _]).
      destruct (Hin _ _ Ht12) as [Hl1 Hr2].
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl1 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hr2 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn')) as En'.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht12 Hr2) as E12.
      exists m1, k3, n. constructor; try assumption.
      eapply set_module_eq_trans; [exact Ek3 |]. eapply set_module_eq_trans; [exact En' |].
      eapply set_module_eq_trans; [exact E12 | apply set_module_eq_sym; exact En].
    + destruct He12 as (v1 & v2 & w & m1 & m2 & n & [E1 E2 Hw Hn Ev1 Ev2 Em1 Em2]).
      destruct He23 as (u2 & u3 & w' & k2 & k3 & n' & [F2 F3 Hw' Hn' Eu2 Eu3 Ek2 Ek3]).
      rewrite E2 in F2. injection F2 as <- <-. destruct Hce as [(FA & FM & FM' & [_ HFM _ _ _]) (FU & FU' & [HFU _ _])].
      destruct (Hin _ _ Ht12) as [Hl1 Hr2].
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl1 Hw) as Ew.
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hr2 Hw') as Ew'.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht12 Hr2) as E12.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl1 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hr2 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn')) as En'.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht12 Hr2) as F12.
      exists v1, u3, w, m1, k3, n. constructor; try assumption.
      * eapply set_eq_trans; [exact Eu3 |]. eapply set_eq_trans; [exact Ew' |].
        eapply set_eq_trans; [exact E12 | apply set_eq_sym; exact Ew].
      * eapply set_module_eq_trans; [exact Ek3 |]. eapply set_module_eq_trans; [exact En' |].
        eapply set_module_eq_trans; [exact F12 | apply set_module_eq_sym; exact En].
Qed.

(** Two denotations of a term agree at an environment. *)
Lemma set_denotes_agree : forall Γ M F G ρ, set_denotes Γ M F -> set_denotes Γ M G -> set_env_in Γ ρ ->
    set_eq (F ρ) (G ρ).
Proof. intros * HF HG Hρ. exact (set_denotes_unique _ _ _ HG _ _ _ Hρ (set_denotes_exists _ _ _ HF _ Hρ)). Qed.

(** Equal terms are equal the other way round. *)
Lemma set_exp_eq_sym : forall Γ A M M', set_rel_exp_eq Γ A M M' -> set_rel_exp_eq Γ A M' M.
Proof.
  intros * (FA & FM & FM' & [HA HM HM' E Hm]). exists FA, FM', FM. constructor; try assumption.
  - intros ρ Hρ. apply set_eq_sym. exact (E ρ Hρ).
  - intros ρ Hρ. eapply set_mem_eq_l; [exact (E ρ Hρ) | exact (Hm ρ Hρ)].
Qed.

(** Equality of terms is transitive. *)
Lemma set_exp_eq_trans : forall Γ A M M' M'', set_rel_exp_eq Γ A M M' -> set_rel_exp_eq Γ A M' M'' -> set_rel_exp_eq Γ A M M''.
Proof.
  intros * (FA & FM & FM' & [HA HM HM' E Hm]) (FA2 & FM2 & FM3 & [_ HM2 HM3 E2 _]). exists FA, FM, FM3.
  constructor; try assumption. intros ρ Hρ. eapply set_eq_trans; [exact (E ρ Hρ) |].
  eapply set_eq_trans; [exact (set_denotes_agree _ _ _ _ _ HM' HM2 Hρ) | exact (E2 ρ Hρ)].
Qed.

(** Related environments have equal entries. *)
Lemma set_env_rel_eq : forall Γ ρ ρ', set_env_rel Γ ρ ρ' -> set_env_eq γ ρ ρ'.
Proof.
  induction Γ as [| ce Γ IH]; intros ρ ρ' H; [exact H |]. destruct H as [Ht He].
  pose proof (IH _ _ Ht) as Et. intros [| x]; [| exact (Et x)].
  destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel] in He.
  - destruct He as (x & x' & a & [-> -> _ _ E]). constructor. exact E.
  - destruct He as (r & v & v' & w & [-> -> _ E1 E2]). constructor. eapply set_eq_trans; [exact E1 | apply set_eq_sym; exact E2].
  - destruct He as (m & m' & n & [-> -> _ E1 E2]). constructor. eapply set_module_eq_trans; [exact E1 | apply set_module_eq_sym; exact E2].
  - destruct He as (v & v' & w & m & m' & n & [-> -> _ _ E1 E2 E3 E4]). constructor;
      [eapply set_eq_trans; [exact E1 | apply set_eq_sym; exact E2] | eapply set_module_eq_trans; [exact E3 | apply set_module_eq_sym; exact E4]].
Qed.

Section Functional.
  Hypothesis Hfn : fn_kinds_unique.
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** A term that has a value at every environment of a valid context
    denotes it: functionality gives the uniqueness. *)
Corollary set_denotes_of_exists : forall Γ M F, set_ctx Γ ->
    (forall ρ, set_env_in Γ ρ -> set_interp T γ Γ ρ M (F ρ)) -> set_denotes Γ M F.
Proof.
  intros * HΓ Hex. constructor; [exact Hex |]. intros ρ ρ' v Hr Hv.
  destruct (set_env_rel_per _ HΓ) as [Hsym Htrans].
  assert (Hρ : set_env_in Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
  apply set_eq_sym. exact (set_interp_functional T γ Hfn Hmods _ _ _ _ (Hex _ Hρ) _ _ (set_env_rel_eq _ _ _ Hr) Hv).
Qed.

Corollary set_modexp_denotes_of_exists : forall Γ H F, set_ctx Γ ->
    (forall ρ, set_env_in Γ ρ -> set_interp_modexp T γ Γ ρ H (F ρ)) -> set_modexp_denotes Γ H F.
Proof.
  intros * HΓ Hex. constructor; [exact Hex |]. intros ρ ρ' m Hr Hm.
  destruct (set_env_rel_per _ HΓ) as [Hsym Htrans].
  assert (Hρ : set_env_in Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
  apply set_module_eq_sym. exact (set_interp_modexp_functional T γ Hfn Hmods _ _ _ _ (Hex _ Hρ) _ _ (set_env_rel_eq _ _ _ Hr) Hm).
Qed.

End Functional.

(** ** Contexts, Universes and Extensions at One Context

    The other shapes the fundamental theorem concludes, at one global
    context: a context denotes with valid slots, a universe denotes as
    one, and equal extensions agree on suffixes of equal length. *)

(** [set_universe_with Γ U FU]: [U] denotes [FU], a universe at every
    environment of [Γ], which denotes. *)
Record set_universe_with (Γ : ctx) (U : exp) (FU : set_env -> aczel_set) : Prop :=
  { (** The context denotes *)
    set_universe_ctx : set_ctx Γ
    (** [U] denotes [FU] *)
  ; set_universe_denotes : set_denotes Γ U FU
    (** A universe at each environment *)
  ; set_universe_shape : forall ρ, set_env_in Γ ρ -> exists V, universe_shape FU ρ V }.

(** [U] is a universe in [Γ], at this one global context: the building
    block of [set_universe]. *)
Definition set_rel_universe (Γ : ctx) (U : exp) : Prop := exists FU, set_universe_with Γ U FU.

(** [set_rel_ext_eq_suffixes Γ Δ Δ']: suffixes of equal length of [Δ] and
    [Δ'] are equal extensions of [Γ], and both whole extensions have valid
    slots, at this one global context: the building block of
    [set_ext_eq_suffixes]. *)
Record set_rel_ext_eq_suffixes (Γ Δ Δ' : ctx) : Prop :=
  { (** Equal suffixes *)
    set_ext_eq_suffixes_eq : forall X Ψ X' Ψ', Δ = X ++ Ψ -> Δ' = X' ++ Ψ' -> List.length Ψ = List.length Ψ' ->
      set_ext_eq_with Γ Ψ Ψ'
    (** The left extension's slots *)
  ; set_ext_eq_suffixes_slots : set_valid_slots (Δ ++ Γ)
    (** The right extension's slots *)
  ; set_ext_eq_suffixes_slots' : set_valid_slots (Δ' ++ Γ) }.

(** [Γ] denotes and its slots are valid, at this one global context: the
    building block of [set_ctx_slots]. *)
Definition set_rel_ctx_slots (Γ : ctx) : Prop := set_ctx Γ /\ set_valid_slots Γ.

End Judgments.

(** * Valuations That Model a Global Context

    A valuation models the global context ([set_gctx_ok]) when what it
    gives each global is what the global's stored description denotes:

    - a filed module or frame reads its global module at its path, over a
      denoting closed telescope; a term member of it has its stored kind,
      is the empty set at a proof, and, applied to an environment of an
      outer part of the telescope, is of the [Π] over the rest and is its
      reduct's value ([set_filed_mod], [set_filed_term_with]);
    - a filed body or frame is its own global module, and an alias is the
      module its unit denotes;
    - a group of inductive types has the parameter and argument types its
      declaration's telescopes denote, the carriers of [Carriers], type
      formers and constructors of their closed types and values, and a
      view the carriers of what it views ([set_group_ok]);
    - a record type has the parameter and field types its declaration
      denotes, the tuples of its fields as elements, and a type former of
      its closed type and value ([set_record_ok]).

    A type read off the values of a telescope is a function of those
    values ([set_reads], [set_tele_types]), the value of the type at every
    environment of the telescope. *)

(** ** Telescopes *)

(** The term values of the first entries of [ρ], one per entry of [Δ],
    outermost first. *)
Fixpoint set_env_values (Δ : ctx) (ρ : set_env) : list aczel_set :=
  match Δ with
  | nil => nil
  | _ :: Δ' => set_env_values Δ' (set_env_tail ρ) ++ [set_entry_value (ρ 0)]
  end.

(** [l] with its [n]-th value replaced by the empty set: a recursive
    argument as the types after it read it ([arguments_fit]). *)
Definition erase_at (n : nat) (l : list aczel_set) : list aczel_set := List.firstn n l ++ empty_set :: List.skipn (S n) l.

(** The type code a constructor argument is read at. *)
Definition set_argument_type (g : set_argument) : list aczel_set -> aczel_set :=
  match g with
  | set_argument_plain _ type | set_argument_recursive type _ _ _ => type
  end.

(** The code of a recursive argument of a group [G] over the domains [ds]
    into the member [target] at the parameters [tparams], after the values
    [vals]: the [Π]s over the domains into the inductive type of the
    target's carrier, at the uniform parameters of [vals]. *)
Fixpoint shape_code (G : set_group) (ds : list (list aczel_set -> aczel_set)) (target : nat)
    (tparams : list aczel_set -> list aczel_set) (pre points : list aczel_set) : aczel_set :=
  match ds with
  | nil =>
      let nuniform := List.length (set_group_uniform_types G) in
      inductive_code (set_group_carrier G target (List.firstn nuniform pre ++ List.skipn nuniform (tparams (pre ++ points))))
  | d :: ds' => pi_code (d (pre ++ points)) (fun x => shape_code G ds' target tparams pre (points ++ [x]))
  end.

(** [argument_ignores n g pre]: the argument [g], after the values [pre],
    reads them alike with the [n]-th erased: its type, or its domains and
    its target's parameters at any points, not only at points of the
    domains: for [node : T → (⊥ → B → T) → T], no point of [⊥] extends to
    one of [B], and the code of the second argument still reads [B]. *)
Definition argument_ignores (n : nat) (g : set_argument) (pre : list aczel_set) : Prop :=
  match g with
  | set_argument_plain _ type => set_eq (type pre) (type (erase_at n pre))
  | set_argument_recursive _ ds _ tparams =>
      (forall k d pts, List.nth_error ds k = Some d -> List.length pts = k -> set_eq (d (pre ++ pts)) (d (erase_at n pre ++ pts))) /\
      (forall pts, List.length pts = List.length ds -> list_set_eq (tparams (pre ++ pts)) (tparams (erase_at n pre ++ pts)))
  end.

Section Model.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** [set_reads Γ M F]: [F] reads [M] off the values of [Γ]: it is [M]'s
    value at every environment of [Γ]. *)
Definition set_reads (Γ : ctx) (M : exp) (F : list aczel_set -> aczel_set) : Prop :=
  forall ρ, set_env_in T γ Γ ρ -> set_interp T γ Γ ρ M (F (set_env_values Γ ρ)).

(** [set_tele_types Γ0 Δ Fs]: [Fs] read the types of the telescope [Δ]
    over [Γ0], each off the values of the context before it. *)
Inductive set_tele_types (Γ0 : ctx) : ctx -> list (list aczel_set -> aczel_set) -> Prop :=
(** No entry *)
| set_tele_types_nil : set_tele_types Γ0 nil nil
(** An assumption, after the others *)
| set_tele_types_ass : forall κ A Δ Fs F, set_tele_types Γ0 Δ Fs -> set_reads (Δ ++ Γ0) A F ->
    set_tele_types Γ0 (ce_ass κ A :: Δ) (Fs ++ [F]).

(** ** Term Members and Modules *)

(** [set_filed_reduct_with p x R1 Ns T1 T2 r A0 M1]: the member [x] of the
    filed module [p], read as [R1] at the arguments [Ns] for the outer part
    [T2] of its telescope, has the reduct [M1] over [T2], instantiated: of
    the [Π] at [r] over the inner part [T1] into [A0], and the member's
    value applied at every environment of [T2]. *)
Record set_filed_reduct_with (p : qname) (x : string) (R1 : mdesc) (Ns : list exp) (T1 T2 : ctx) (r : abs_kind)
    (A0 M1 : exp) : Prop :=
  { (** The reduct read is [M1] instantiated *)
    set_filed_reduct_read : mdesc_reduct R1 = Some (exp_sub M1 (sb_of_list sb_id Ns))
    (** [M1] is of the [Π] over the inner part *)
  ; set_filed_reduct_valid : set_rel_exp_eq T γ T2 (ctx_pi_at r T1 A0) M1 M1
    (** [M1] is over the outer part only *)
  ; set_filed_reduct_scoped : exp_scoped (List.length T2) M1
    (** It is the member's value applied *)
  ; set_filed_reduct_value : forall ρ m, set_env_in T γ T2 ρ -> set_interp T γ T2 ρ M1 m ->
      set_eq m (apply_values (snd (global_term γ (qname_in p x))) (set_env_values T2 ρ)) }.

(** [set_filed_term_with p Tl x R0 A0 i]: the term member [x] of the filed
    module [p] over its telescope [Tl], read as [R0], of the type [A0] over
    [Tl], of its kind's sort at the index [i]: read at arguments for the
    outer part of [Tl] as stored; its value, the valuation's, has its
    kind, is the empty set at a proof, and, applied to the values of an
    environment of the outer part, is of the [Π] over the inner part
    there. *)
Record set_filed_term_with (p : qname) (Tl : ctx) (x : string) (R0 : mdesc) (A0 : exp) (i : nat) : Prop :=
  { (** The type is of the sort of the member's kind *)
    set_filed_term_typed : set_rel_exp_eq T γ Tl (abs_kind_sort (mdesc_kind R0) (a_typ i)) A0 A0
    (** The type is over the telescope only *)
  ; set_filed_term_scoped : exp_scoped (List.length Tl) A0
    (** Read at arguments [Ns] for the outer part [T2]: the [Π] over the
        inner part [T1], instantiated, and the reduct, if any, a term over
        [T2] instantiated *)
  ; set_filed_term_reads : forall Ns R1 T1 T2, Tl = T1 ++ T2 -> List.length T2 = List.length Ns ->
      mdesc_term_part_ats R0 Ns = Some R1 ->
      mdesc_type R1 = Some (exp_sub (ctx_pi_at (mdesc_kind R0) T1 A0) (sb_of_list sb_id Ns)) /\
      (mdesc_reduct R1 = None \/ exists M1, set_filed_reduct_with p x R1 Ns T1 T2 (mdesc_kind R0) A0 M1)
    (** The valuation's table has the member a proof exactly when its
        stored kind is a proposition's *)
  ; set_filed_term_proofs : global_proofs γ p x = is_proof_kind (mdesc_kind R0)
    (** A proof's value is the empty set *)
  ; set_filed_term_proof : mdesc_kind R0 = ak_propositional -> set_eq (snd (global_term γ (qname_in p x))) empty_set
    (** Applied to the values of an environment of the outer part, it is
        of the [Π] over the inner part there *)
  ; set_filed_term_value : forall T1 T2 ρ a, Tl = T1 ++ T2 -> set_env_in T γ T2 ρ ->
      set_interp T γ T2 ρ (ctx_pi_at (mdesc_kind R0) T1 A0) a ->
      set_mem (apply_values (snd (global_term γ (qname_in p x))) (set_env_values T2 ρ)) (code_carrier a)
    (** The [Π]s over the telescope into the member's kind are formed *)
  ; set_filed_term_pi_kinds : forall Δ1 κ A Δ2, Tl = Δ1 ++ ce_ass κ A :: Δ2 -> pi_kinds κ (mdesc_kind R0) }.

(** [set_filed_mod Ξm p Tl Φ]: the filed module [p], over its telescope
    [Tl], of the stored body [Φ], is modelled, its members read with the
    stack [Ξm].  The stack is a parameter because a module's members are
    not all in its body: the type former of an inductive type whose frame
    is open under [p] is read off the stack ([stored_term_member]).  In
    [module P where inductive V : Type where | mk : V → V end], [P.V] in
    [mk]'s type is the former of the open frame [P.V], not an entry of
    [P]'s body; once the frame closes it is an entry of a bigger body.  A
    valuation modelling a context reads its own stack ([set_gctx_ok]); one
    modelling a context where it grows reads the smaller context's
    ([set_gctx_embedding]), whose open frames are the ones its
    derivations saw. *)
Record set_filed_mod (Ξm : gstack) (p : qname) (Tl : ctx) (Φ : gmod) : Prop :=
  { (** The telescope denotes.  That its path reads its global module is
        no field: it follows from the module being its own global module
        and the path's typing ([set_interp_filed_path]) *)
    set_filed_mod_tele_ctx : set_ctx T γ Tl
    (** Of assumptions *)
  ; set_filed_mod_tele_assumptions : all_assumptions Tl
    (** Closed *)
  ; set_filed_mod_tele_scoped : ctx_scoped 0 Tl
    (** Of evaluated sorts, at one level *)
  ; set_filed_mod_tele_evaluated : exists l, set_params_evaluated T γ nil Tl l
    (** Every term member stored at it, of an entry or of a type former
        whose frame is open on [Ξm], is modelled *)
  ; set_filed_mod_terms : forall x R0, stored_term_member Ξm Φ p x R0 -> exists A0 i, set_filed_term_with p Tl x R0 A0 i
    (** An alias stored in it is the module at its path, and a valid unit
        in every denoting context *)
  ; set_filed_mod_aliases : forall y Φ0 E Ua, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua ->
      gc_module gc_deps gc_stack (qname_in p y) = Some (mr_alias Ua) /\
      forall Γ, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_valid_unit T γ Γ (me_lit Ua) }.

(** ** Groups of Inductive Types *)

(** [set_arguments_shape gs sgs]: the semantic arguments [sgs] are of the
    kinds of the declared [gs], a recursive one at its shape's member, over
    as many domains. *)
Inductive set_arguments_shape : list carg -> list set_argument -> Prop :=
(** No argument *)
| set_arguments_shape_nil : set_arguments_shape nil nil
(** A non-recursive argument, of its kind *)
| set_arguments_shape_plain : forall κ A F gs sgs, set_arguments_shape gs sgs ->
    set_arguments_shape (ca_arg κ A :: gs) (set_argument_plain κ F :: sgs)
(** A recursive argument, into its shape's member over its domains *)
| set_arguments_shape_recursive : forall t F ds tparams gs sgs, List.length ds = ptyp_depth t -> set_arguments_shape gs sgs ->
    set_arguments_shape (ca_rec t :: gs) (set_argument_recursive F ds (ptyp_mem t) tparams :: sgs).

(** The context at the end of the shape [t] of a recursive argument of a
    constructor of [Mk] after the arguments [gs1]: its domains, the
    arguments before it and the parameters. *)
Definition recursive_end_ctx (p : qname) (D : ind_decl) (Mk : imember) (gs1 : list carg) (t : ptyp) : ctx :=
  shape_domains_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk.

(** [set_target_instance_with D target vals Mt ρt]: the values [vals] are
    those of the environment [ρt] of the parameters of the member [Mt] of
    [D] at [target]. *)
Record set_target_instance_with (D : ind_decl) (target : nat) (vals : list aczel_set) (Mt : imember) (ρt : set_env) : Prop :=
  { (** [Mt] is the member at [target] *)
    set_target_instance_member : ind_member D target = Some Mt
    (** [ρt] is an environment of its parameters *)
  ; set_target_instance_env : set_env_in T γ (im_params D Mt) ρt
    (** whose values are [vals] *)
  ; set_target_instance_values : list_set_eq vals (set_env_values (im_params D Mt) ρt) }.

(** [set_constructor_ok p D G Mk gs sgs]: the semantic arguments [sgs] of a
    constructor of the member [Mk] of the group [D] at [p] are those of
    its declared arguments [gs]. *)
Record set_constructor_ok (p : qname) (D : ind_decl) (G : set_group) (Mk : imember) (gs : list carg) (sgs : list set_argument) : Prop :=
  { (** Of the declared kinds and shapes *)
    set_constructor_ok_shape : set_arguments_shape gs sgs
    (** Their types read the arguments' types, over the parameters *)
  ; set_constructor_ok_types : set_tele_types (im_params D Mk) (cargs_ctx p D Mk gs) (List.map set_argument_type sgs)
    (** A recursive argument's type is its shape's code in the group *)
  ; set_constructor_ok_recursive : forall i t F ds target tparams ρ,
      List.nth_error gs i = Some (ca_rec t) -> List.nth_error sgs i = Some (set_argument_recursive F ds target tparams) ->
      set_env_in T γ (List.skipn (List.length gs - i) (cargs_ctx p D Mk gs) ++ im_params D Mk) ρ ->
      set_eq (F (set_env_values (List.skipn (List.length gs - i) (cargs_ctx p D Mk gs) ++ im_params D Mk) ρ))
             (shape_code G ds target tparams (set_env_values (List.skipn (List.length gs - i) (cargs_ctx p D Mk gs) ++ im_params D Mk) ρ) nil)
    (** No argument reads a recursive argument before it, at any values:
        for [node : T → T → (n : ℕ) → T], the type of [n] at [[t1; t2]]
        is the one at [[∅; ∅]], two erasures, the second one at values
        that are no environment's, as [∅] need not be of [T] *)
  ; set_constructor_ok_ignores : forall n t j g pre, List.nth_error gs n = Some (ca_rec t) -> n < j -> List.nth_error sgs j = Some g ->
      List.length pre = im_np D Mk + j -> argument_ignores (im_np D Mk + n) g pre
    (** A recursive argument ends in the member its shape names.  For
        [Vec (A : Type) : ℕ → Type] and [cons : (n : ℕ) → A → Vec A n →
        Vec A (S n)], the branch of [cons] binds its recursive result at
        [P n xs]: the recursive argument is in [Vec]'s carrier at [n]
        exactly, not only at parameters of the same carrier *)
  ; set_constructor_ok_target : forall gs1 t gs2 F ds target tparams, gs = gs1 ++ ca_rec t :: gs2 ->
      List.nth_error sgs (List.length gs1) = Some (set_argument_recursive F ds target tparams) -> target = ptyp_mem t
    (** Its target's non-uniform parameters are the values of the shape's,
        at the shape's end *)
  ; set_constructor_ok_target_params : forall gs1 t gs2 F ds target tparams, gs = gs1 ++ ca_rec t :: gs2 ->
      List.nth_error sgs (List.length gs1) = Some (set_argument_recursive F ds target tparams) ->
      forall ρ, set_env_in T γ (recursive_end_ctx p D Mk gs1 t) ρ ->
      set_interp_list T γ (recursive_end_ctx p D Mk gs1 t) ρ (ptyp_ps_at (cargs_pat gs1) t)
        (List.skipn (ind_nu D) (tparams (set_env_values (recursive_end_ctx p D Mk gs1 t) ρ)))
    (** With the uniform ones, they are an instance of the target's
        parameters *)
  ; set_constructor_ok_target_instance : forall gs1 t gs2 F ds target tparams, gs = gs1 ++ ca_rec t :: gs2 ->
      List.nth_error sgs (List.length gs1) = Some (set_argument_recursive F ds target tparams) ->
      forall ρ, set_env_in T γ (recursive_end_ctx p D Mk gs1 t) ρ ->
      exists Mt ρt, set_target_instance_with D target
        (List.firstn (ind_nu D) (set_env_values (recursive_end_ctx p D Mk gs1 t) ρ) ++
         List.skipn (ind_nu D) (tparams (set_env_values (recursive_end_ctx p D Mk gs1 t) ρ))) Mt ρt }.

(** [set_member_ok p D G Mk SMk]: the semantic member [SMk] of [G] is the
    member [Mk] of the group [D] at [p]. *)
Record set_member_ok (p : qname) (D : ind_decl) (G : set_group) (Mk : imember) (SMk : set_member) : Prop :=
  { (** The non-uniform parameters' types, over the uniform ones *)
    set_member_ok_nparams : set_tele_types (ind_uparams D) (im_nparams Mk) (set_member_nparam_types SMk)
    (** The constructors' names, in order *)
  ; set_member_ok_names : List.map set_constructor_name (set_member_constructors SMk) = List.map fst (im_cons Mk)
    (** Each constructor's arguments are its declared ones' *)
  ; set_member_ok_constructors : forall cs gs, In cs (set_member_constructors SMk) -> ind_con Mk (set_constructor_name cs) = Some gs ->
      set_constructor_ok p D G Mk gs (set_constructor_arguments cs)
    (** A record view has its record's field names *)
  ; set_member_ok_record_fields : forall fl, set_member_record_fields SMk = Some fl <-> exists qr Is, im_head Mk = mh_record qr Is fl }.

(** The values of the uniform parameters and of the rest of an
    environment of a member's parameters. *)
Definition uniform_values (D : ind_decl) (Mk : imember) (ρ : set_env) : list aczel_set :=
  set_env_values (ind_uparams D) (set_env_drop (im_nn Mk) ρ).

(** [set_group_carriers_with G D us s U l]: at the uniform parameters
    [us], the sort's value [s] is the universe [U] at the index [l], and
    every member's carrier at an instance of its parameters is the one
    [Carriers] builds in [U]: one least fixed point for all the members,
    which the eliminator's induction runs over. *)
Record set_group_carriers_with (G : set_group) (D : ind_decl) (us : list aczel_set) (s U l : aczel_set) : Prop :=
  { (** A universe of sets *)
    set_group_carriers_universe : grothendieck U
    (** The sort is its universe *)
  ; set_group_carriers_sort : set_eq s (universe_code l U)
    (** Each carrier is the least fixed point's *)
  ; set_group_carriers_fixed_point : forall k Mk ρ, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) ρ ->
      list_set_eq (uniform_values D Mk ρ) us ->
      set_eq (set_group_carrier G k (set_env_values (im_params D Mk) ρ)) (member_carrier G us U U k (set_env_values (im_nparams Mk) ρ)) }.

(** [set_group_carriers_at G D ρu s U l]: at the environment [ρu] of the
    uniform parameters, the sort reads [s], and the carriers are as
    [set_group_carriers_with] says at their values. *)
Record set_group_carriers_at (G : set_group) (D : ind_decl) (ρu : set_env) (s U l : aczel_set) : Prop :=
  { (** The sort reads [s] at [ρu] *)
    set_group_carriers_at_sort : set_interp T γ (ind_uparams D) ρu (ind_sort D) s
    (** The carriers at the values of [ρu], in [U] *)
  ; set_group_carriers_at_fixed : set_group_carriers_with G D (set_env_values (ind_uparams D) ρu) s U l }.

(** The element the constructor [c] of the member [Mk] builds from the
    values [vals] of the non-uniform parameters and the arguments: at a
    record view the tuple of the arguments by field name (a record view
    has no non-uniform parameter), otherwise its [con_val], as
    [constructed_element] reads it off the semantic member. *)
Definition member_constructor_element (Mk : imember) (c : string) (vals : list aczel_set) : aczel_set :=
  match im_head Mk with
  | mh_record _ _ fl => tuple_code (List.combine fl vals)
  | _ => con_val c vals
  end.

(** [set_group_ok p D G]: [G] is the group [D] at [p]. *)
Record set_group_ok (p : qname) (D : ind_decl) (G : set_group) : Prop :=
  { (** The uniform parameters' types *)
    set_group_ok_uniform : set_tele_types nil (ind_uparams D) (set_group_uniform_types G)
    (** As many members *)
  ; set_group_ok_member_count : List.length (set_group_members G) = List.length (ind_members D)
    (** Each member is the declared one *)
  ; set_group_ok_members : forall k Mk SMk, ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk ->
      set_member_ok p D G Mk SMk
    (** At every environment of the uniform parameters the sort reads,
        and the carriers are the least fixed points in its universe *)
  ; set_group_ok_carriers : forall ρu, set_env_in T γ (ind_uparams D) ρu -> exists s U l, set_group_carriers_at G D ρu s U l
    (** A type former's closed type denotes *)
  ; set_group_ok_former_types : forall k Mk, ind_member D k = Some Mk -> exists FA, set_denotes T γ nil (ind_ty D Mk) FA
    (** A constructor's closed type denotes *)
  ; set_group_ok_constructor_types : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      exists FA, set_denotes T γ nil (con_ty p D k Mk gs) FA
    (** A type former is of its closed type *)
  ; set_group_ok_formers_typed : forall k Mk FA, ind_member D k = Some Mk -> set_denotes T γ nil (ind_ty D Mk) FA ->
      set_mem (global_former γ p k) (code_carrier (FA empty_set_env))
    (** At parameters, it is the inductive type of the carrier *)
  ; set_group_ok_formers_value : forall k Mk ρ, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) ρ ->
      set_eq (apply_values (global_former γ p k) (set_env_values (im_params D Mk) ρ))
             (inductive_code (set_group_carrier G k (set_env_values (im_params D Mk) ρ)))
    (** A constructor is of its closed type *)
  ; set_group_ok_constructors_typed : forall k Mk c gs FA, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      set_denotes T γ nil (con_ty p D k Mk gs) FA -> set_mem (global_constructor γ p k c) (code_carrier (FA empty_set_env))
    (** At parameters and arguments, it is the element of its name at the
        non-uniform parameters and the arguments *)
  ; set_group_ok_constructors_value : forall k Mk c gs ρ, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      set_env_in T γ (cargs_ctx p D Mk gs ++ im_params D Mk) ρ ->
      set_eq (apply_values (global_constructor γ p k c) (set_env_values (cargs_ctx p D Mk gs ++ im_params D Mk) ρ))
             (member_constructor_element Mk c (List.skipn (ind_nu D) (set_env_values (cargs_ctx p D Mk gs ++ im_params D Mk) ρ)))
    (** A view's constructor at the uniform parameters is its container's
        at the view's arguments there *)
  ; set_group_ok_view_constructors : forall k Mk qc k' Is vm c gs ρ is, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm -> ind_con Mk c = Some gs -> set_env_in T γ (ind_uparams D) ρ ->
      set_interp_list T γ (ind_uparams D) ρ Is is ->
      set_eq (apply_values (global_constructor γ p k c) (set_env_values (ind_uparams D) ρ))
             (apply_values (global_constructor γ qc k' c) is)
    (** A view's type former at the uniform parameters is its container's
        at the view's arguments there *)
  ; set_group_ok_view_formers : forall k Mk qc k' Is vm ρ is, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm -> set_env_in T γ (ind_uparams D) ρ ->
      set_interp_list T γ (ind_uparams D) ρ Is is ->
      set_eq (apply_values (global_former γ p k) (set_env_values (ind_uparams D) ρ)) (apply_values (global_former γ qc k') is)
    (** The semantic signature respects equality *)
  ; set_group_ok_respects : signature_respects G
    (** So do the carriers, in their parameters: an element of a [Π] code
        over a shape's domains is read at equal points *)
  ; set_group_ok_carrier_resp : forall k ps ps', list_set_eq ps ps' -> set_eq (set_group_carrier G k ps) (set_group_carrier G k ps')
    (** A member's constructors have distinct names *)
  ; set_group_ok_names : forall k SMk, List.nth_error (set_group_members G) k = Some SMk ->
      NoDup (List.map set_constructor_name (set_member_constructors SMk))
    (** A record view has one constructor, of one argument per field, and
        distinct field names *)
  ; set_group_ok_record_views : forall k SMk fl, List.nth_error (set_group_members G) k = Some SMk ->
      set_member_record_fields SMk = Some fl ->
      NoDup fl /\ List.length (set_member_constructors SMk) = 1 /\
      (forall cs, In cs (set_member_constructors SMk) -> List.length (set_constructor_arguments cs) = List.length fl)
    (** A view's carrier is its container member's at the view's arguments *)
  ; set_group_ok_views : forall k Mk qc k' Is vm ρ is, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      set_env_in T γ (im_params D Mk) ρ -> set_interp_list T γ (ind_uparams D) (set_env_drop (im_nn Mk) ρ) Is is ->
      set_eq (set_group_carrier G k (set_env_values (im_params D Mk) ρ))
             (set_group_carrier (global_group γ qc) k' (is ++ set_env_values (im_nparams Mk) ρ))
    (** A record view's carrier is its record's at the view's arguments *)
  ; set_group_ok_record_view_carriers : forall k Mk qr Is fl ρ is, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      set_env_in T γ (im_params D Mk) ρ -> set_interp_list T γ (ind_uparams D) (set_env_drop (im_nn Mk) ρ) Is is ->
      set_eq (set_group_carrier G k (set_env_values (im_params D Mk) ρ)) (set_record_carrier (global_record γ qr) is)
    (** A view's instance has a reading, one function of the environment
        of the uniform parameters: the instance is typed in the
        declaration, so the model's construction reads it *)
  ; set_group_ok_view_instances : forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      exists Fis, forall ρ, set_env_in T γ (ind_uparams D) ρ -> set_interp_list T γ (ind_uparams D) ρ Is (Fis ρ) }.

(** ** Record Types *)

(** [set_fields_fit Fs pre vs]: the values [vs] are of the field types
    [Fs], each read off the parameters [pre] and the fields before it. *)
Inductive set_fields_fit : list (list aczel_set -> aczel_set) -> list aczel_set -> list aczel_set -> Prop :=
(** No field *)
| set_fields_fit_nil : forall pre, set_fields_fit nil pre nil
(** A field of its type, then the rest *)
| set_fields_fit_cons : forall F Fs pre v vs, set_mem v (code_carrier (F pre)) -> set_fields_fit Fs (pre ++ [v]) vs ->
    set_fields_fit (F :: Fs) pre (v :: vs).

(** [set_record_element_with SR pre t vs]: [t] is the tuple of the fields
    [vs] of the record [SR] at the parameters [pre]. *)
Record set_record_element_with (SR : set_record) (pre : list aczel_set) (t : aczel_set) (vs : list aczel_set) : Prop :=
  { (** One value per field *)
    set_record_element_length : List.length vs = List.length (set_record_field_names SR)
    (** [t] is their tuple *)
  ; set_record_element_tuple : set_eq t (tuple_code (List.combine (set_record_field_names SR) vs))
    (** Each is of its field's type *)
  ; set_record_element_fit : set_fields_fit (set_record_field_types SR) pre vs }.

(** [set_record_ok p R SR]: [SR] is the record type [R] at [p]. *)
Record set_record_ok (p : qname) (R : record_decl) (SR : set_record) : Prop :=
  { (** The parameters' types *)
    set_record_ok_params : set_tele_types nil (record_params R) (set_record_param_types SR)
    (** The fields' names *)
  ; set_record_ok_names : set_record_field_names SR = List.map fst (record_fields R)
    (** The fields' types, over the parameters *)
  ; set_record_ok_field_types : set_tele_types (record_params R) (record_fctx R (List.length (record_fields R)))
      (set_record_field_types SR)
    (** The elements are the tuples of fields of their types *)
  ; set_record_ok_carrier : forall ρ t, set_env_in T γ (record_params R) ρ ->
      set_mem t (set_record_carrier SR (set_env_values (record_params R) ρ)) <->
      exists vs, set_record_element_with SR (set_env_values (record_params R) ρ) t vs
    (** The type former is of its closed type *)
  ; set_record_ok_former_typed : forall FA, set_denotes T γ nil (ctx_pi (record_params R) (record_sort R)) FA ->
      set_mem (global_record_former γ p) (code_carrier (FA empty_set_env))
    (** At parameters, it is the record type of the carrier *)
  ; set_record_ok_former_value : forall ρ, set_env_in T γ (record_params R) ρ ->
      set_eq (apply_values (global_record_former γ p) (set_env_values (record_params R) ρ))
             (record_code (set_record_carrier SR (set_env_values (record_params R) ρ)))
    (** Its applications hold elements only at instances of the
        parameters: for a record [R (A : Type)] and [M : R ℕ] in
        [n : ℕ], the η rule types no parameter, so that [M]'s value
        lies in the record type's carrier at [⟦ℕ⟧] is read from this,
        not from [⟦ℕ⟧ ∈ ⟦Type⟧] *)
  ; set_record_ok_instances : forall ns z, List.length ns = List.length (record_params R) ->
      set_mem z (code_carrier (apply_values (global_record_former γ p) ns)) ->
      exists ρ, set_env_in T γ (record_params R) ρ /\ list_set_eq ns (set_env_values (record_params R) ρ) }.

(** ** Models *)

(** [set_gctx_ok]: [γ] models the global context. *)
Record set_gctx_ok : Prop :=
  { (** Every filed module or frame is modelled *)
    set_gctx_ok_filed : forall p Tl Φ, gc_loc gc_deps gc_stack p = Some (Tl, Φ) -> set_filed_mod gc_stack p Tl Φ
    (** A filed module or frame is its own global module *)
  ; set_gctx_ok_bodies : forall q TΦ, gc_loc gc_deps gc_stack q = Some TΦ -> global_module γ q = set_module_global q nil
    (** Every global module equals itself, so selection respects equality *)
  ; set_gctx_ok_modules : forall q, set_module_eq γ (global_module γ q) (global_module γ q)
    (** An alias is the module its closed unit denotes *)
  ; set_gctx_ok_aliases : forall q Ua FU, gc_module gc_deps gc_stack q = Some (mr_alias Ua) ->
      set_modexp_denotes T γ nil (me_lit Ua) FU -> set_module_eq γ (global_module γ q) (FU empty_set_env)
    (** Every group is modelled *)
  ; set_gctx_ok_groups : forall p D, ind_lookup gc_deps gc_stack p = Some D -> set_group_ok p D (global_group γ p)
    (** Every record type is modelled *)
  ; set_gctx_ok_records : forall p R, record_lookup gc_deps gc_stack p = Some R -> set_record_ok p R (global_record γ p) }.

End Model.

(** * Modelling a Context Where It Grows

    A valuation models a global context at a bigger one
    ([set_gctx_embedding]) when everything the smaller context resolves is
    modelled there.  One valuation serves the whole growth, as in the
    gluing model ([glu_gctx_embedding]): the context grows, the valuation
    does not.  [set_gctx_ok] is the instance where the two contexts are
    the same ([set_gctx_embedding_refl], [set_gctx_ok_of_embedding]). *)

(** [set_gctx_embedding Θ1 Ξ1 Θ2 Ξ2 T γ]: everything the context
    [Θ1 ⍮ Ξ1] resolves is modelled at [Θ2 ⍮ Ξ2] by [γ].  The fields are
    [set_gctx_ok]'s, with the lookups read at the smaller context and the
    set judgments taken at the bigger one, beside what the bigger context
    must satisfy for terms to be read there at all.  The shape is
    [glu_gctx_embedding]'s. *)
Record set_gctx_embedding (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack)
    (T : universe_tower) (γ : global_valuation) : Prop :=
  { (** The smaller context grows into the bigger one.  An embedding
        gives the bigger context's well-formedness, not the smaller
        one's: its two fields are [⊢ᵍ Θ2 ⍮ Ξ2] and [gc_sub] *)
    set_gctx_embedding_embedding : gctx_embedding Θ1 Ξ1 Θ2 Ξ2
    (** The smaller context is well formed, so what it files can be read
        there at all.  The rules read their global lookups at the
        smaller context and everything else at the bigger one, so this
        does not follow from a context premise as it does in the gluing
        model *)
  ; set_gctx_embedding_source_wf : ⊢ᵍ Θ1 ⍮ Ξ1
    (** A λ of the bigger context has one pair of kinds, a consequence of
        the NbE theorems that the interpretation needs wherever it reads a
        λ *)
  ; set_gctx_embedding_fn_kinds : @fn_kinds_unique_ext (gc_mk Θ2 Ξ2)
    (** Every module it files or has open is modelled there *)
  ; set_gctx_embedding_filed : forall p Tl Φ, gc_loc Θ1 Ξ1 p = Some (Tl, Φ) ->
      @set_filed_mod (gc_mk Θ2 Ξ2) T γ Ξ1 p Tl Φ
    (** A module or frame the bigger context files or has open is its own
        global module.  Read at the bigger context: a path filed there
        after the smaller one reads its global module as any other does,
        and this fixes only which module the valuation gives a path *)
  ; set_gctx_embedding_bodies : forall q TΦ, gc_loc Θ2 Ξ2 q = Some TΦ -> global_module γ q = set_module_global q nil
    (** Every global module equals itself, so selection respects
        equality *)
  ; set_gctx_embedding_modules : forall q, set_module_eq γ (global_module γ q) (global_module γ q)
    (** An alias is the module its closed unit denotes there *)
  ; set_gctx_embedding_aliases : forall q Ua FU, gc_module Θ1 Ξ1 q = Some (mr_alias Ua) ->
      @set_modexp_denotes (gc_mk Θ2 Ξ2) T γ nil (me_lit Ua) FU ->
      set_module_eq γ (global_module γ q) (FU empty_set_env)
    (** Every group it declares is modelled there *)
  ; set_gctx_embedding_groups : forall p D, ind_lookup Θ1 Ξ1 p = Some D ->
      @set_group_ok (gc_mk Θ2 Ξ2) T γ p D (global_group γ p)
    (** So is every record type *)
  ; set_gctx_embedding_records : forall p R, record_lookup Θ1 Ξ1 p = Some R ->
      @set_record_ok (gc_mk Θ2 Ξ2) T γ p R (global_record γ p) }.

(** A valuation that models a context models it where it is. *)
Lemma set_gctx_embedding_refl : forall Θ Ξ T γ, ⊢ᵍ Θ ⍮ Ξ -> @fn_kinds_unique_ext (gc_mk Θ Ξ) ->
    @set_gctx_ok (gc_mk Θ Ξ) T γ -> set_gctx_embedding Θ Ξ Θ Ξ T γ.
Proof.
  intros * Hg Hfn [Hf Hb Hm Ha Hgr Hr]; constructor;
    [ exact (gctx_embedding_refl _ _ Hg) | exact Hg | exact Hfn
    | exact Hf | exact Hb | exact Hm | exact Ha | exact Hgr | exact Hr ].
Qed.

(** So, read where it is, an embedding is what it is to model a context. *)
Lemma set_gctx_ok_of_embedding : forall Θ Ξ T γ, set_gctx_embedding Θ Ξ Θ Ξ T γ -> @set_gctx_ok (gc_mk Θ Ξ) T γ.
Proof.
  intros * [_ _ _ Hf Hb Hm Ha Hgr Hr]; constructor;
    [ exact Hf | exact Hb | exact Hm | exact Ha | exact Hgr | exact Hr ].
Qed.

(** * The Judgments of the Fundamental Theorem

    A judgment of a global context holds at every context that one is
    modelled at ([set_gctx_embedding]): the derivation is read where it
    is checked, and the set judgment lands wherever the derivation is
    used.  This is the gluing model's shape ([glu_ctx], [glu_exp]): the
    embedding is part of the judgment, so no value is ever carried from
    one context to another.  Each is its building block at one context,
    read at every context modelling its own. *)

(** [Γ] denotes with valid slots. *)
Definition set_ctx_slots (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation) (Γ : ctx) : Prop :=
  forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> @set_rel_ctx_slots (gc_mk Θ2 Ξ2) T γ Γ.

(** [M] and [M'] are equal terms of the type [A] in [Γ]. *)
Definition set_exp_eq (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation)
    (Γ : ctx) (A M M' : exp) : Prop :=
  forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> @set_rel_exp_eq (gc_mk Θ2 Ξ2) T γ Γ A M M'.

(** [A] is a subtype of [A'] in [Γ]. *)
Definition set_subtyp (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation)
    (Γ : ctx) (A A' : exp) : Prop :=
  forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> @set_rel_subtyp (gc_mk Θ2 Ξ2) T γ Γ A A'.

(** [U] is a universe in [Γ]. *)
Definition set_universe (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation)
    (Γ : ctx) (U : exp) : Prop :=
  forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> @set_rel_universe (gc_mk Θ2 Ξ2) T γ Γ U.

(** Suffixes of equal length of [Δ] and [Δ'] are equal extensions of
    [Γ], and both whole extensions have valid slots. *)
Definition set_ext_eq_suffixes (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation)
    (Γ Δ Δ' : ctx) : Prop :=
  forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> @set_rel_ext_eq_suffixes (gc_mk Θ2 Ξ2) T γ Γ Δ Δ'.

(** [U] and [U'] are equal units in [Γ]. *)
Definition set_unit_eq (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation)
    (Γ : ctx) (U U' : gunit) : Prop :=
  forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> @set_rel_unit_eq (gc_mk Θ2 Ξ2) T γ Γ U U'.

(** [H] and [H'] are equal module expressions in [Γ]. *)
Definition set_modexp_eq (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation)
    (Γ : ctx) (H H' : modexp) : Prop :=
  forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> @set_rel_modexp_eq (gc_mk Θ2 Ξ2) T γ Γ H H'.

(** A term equal to another is equal to itself. *)
Lemma set_exp_eq_left_refl : forall Θ Ξ T γ Γ A M M', set_exp_eq Θ Ξ T γ Γ A M M' -> set_exp_eq Θ Ξ T γ Γ A M M.
Proof.
  intros * H Θ2 Ξ2 Hμ. destruct (H _ _ Hμ) as (FA & FM & FM' & [HA HM _ _ Hm]).
  exists FA, FM, FM. constructor; [exact HA | exact HM | exact HM | intros; apply set_eq_refl | exact Hm].
Qed.

(** A substitution moves along an embedding unchanged: its record is of
    judgments. *)
Lemma gctx_embedding_preserves_wf_sub : forall Θ1 Ξ1 Θ2 Ξ2, gctx_embedding Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ Δ σ, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ˢ σ : Δ -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ˢ σ : Δ.
Proof.
  intros * He * [Hd Hc Ha Had Ham]. destruct (gctx_embedding_preserves_wf _ _ _ _ He) as (Mc & Mx & Mq & _ & _ & Mu & _).
  constructor; [exact (Mc _ Hd) | exact (Mc _ Hc) | intros; apply Mx; auto | intros; apply Mq; auto |].
  intros x U Hx. destruct (Ham x U Hx) as [[E Hu] | Hy]; [left; split; [exact E | exact (Mu _ _ _ Hu)] | right; exact Hy].
Qed.

(** A rule over these judgments, proved at one context [gc_mk Θ2 Ξ2] its
    premises' context grows into ([Hμ]): each judgment premise read there,
    each syntactic premise moved there along the embedding, and what the
    valuation gives there ([Hfn], [Hmods], [Hgw]). *)
Ltac set_open :=
  let Θ2 := fresh "Θ2" in let Ξ2 := fresh "Ξ2" in let Hμ := fresh "Hμ" in
  intros Θ2 Ξ2 Hμ;
  match type of Hμ with set_gctx_embedding ?Θs ?Ξs _ _ ?T ?γ =>
    repeat match goal with
      | H : set_ctx_slots Θs Ξs T γ _ |- _ => specialize (H _ _ Hμ)
      | H : set_exp_eq Θs Ξs T γ _ _ _ _ |- _ => specialize (H _ _ Hμ)
      | H : set_subtyp Θs Ξs T γ _ _ _ |- _ => specialize (H _ _ Hμ)
      | H : set_universe Θs Ξs T γ _ _ |- _ => specialize (H _ _ Hμ)
      | H : set_ext_eq_suffixes Θs Ξs T γ _ _ _ |- _ => specialize (H _ _ Hμ)
      | H : set_unit_eq Θs Ξs T γ _ _ _ |- _ => specialize (H _ _ Hμ)
      | H : set_modexp_eq Θs Ξs T γ _ _ _ |- _ => specialize (H _ _ Hμ)
      end;
    (* what moves is read at [gc_mk Θ2 Ξ2] itself *)
    change (set_gctx_embedding Θs Ξs (@gc_deps (gc_mk Θ2 Ξ2)) (@gc_stack (gc_mk Θ2 Ξ2)) T γ) in Hμ;
    let He := fresh "Hμe" in pose proof (set_gctx_embedding_embedding _ _ _ _ _ _ Hμ) as He;
    let Mc := fresh in let Mx := fresh in let Mq := fresh in let Ms := fresh in
    let Me := fresh in let Mu := fresh in let Mm := fresh in let Mn := fresh in
    destruct (gctx_embedding_preserves_wf _ _ _ _ He) as (Mc & Mx & Mq & Ms & Me & Mu & Mm & Mn);
    repeat match goal with
      | H : wf_ctx Θs Ξs _ |- _ => apply Mc in H
      | H : wf_exp Θs Ξs _ _ _ |- _ => apply Mx in H
      | H : wf_exp_eq Θs Ξs _ _ _ _ |- _ => apply Mq in H
      | H : wf_subtyp Θs Ξs _ _ _ |- _ => apply Ms in H
      | H : wf_ext_eq Θs Ξs _ _ _ |- _ => apply Me in H
      | H : wf_unit_eq Θs Ξs _ _ _ |- _ => apply Mu in H
      | H : wf_modexp_eq Θs Ξs _ _ _ |- _ => apply Mm in H
      | H : wf_no_level_members Θs Ξs _ _ |- _ => apply Mn in H
      | H : wf_sub Θs Ξs _ _ _ |- _ => apply (gctx_embedding_preserves_wf_sub _ _ _ _ He) in H
      | H : body_xp Θs Ξs _ _ _ |- _ =>
          apply (proj1 (proj2 (proj2 (proj2 (mdenote_grow_all _ _ _ _ (set_gctx_embedding_source_wf _ _ _ _ _ _ Hμ)
                   (gctx_embedding_wf _ _ _ _ He) (gctx_embedding_resolution _ _ _ _ He)))))) in H
      end;
    clear Mc Mx Mq Ms Me Mu Mm Mn;
    let Hgw := fresh "Hgw" in pose proof (gctx_embedding_wf _ _ _ _ He) as Hgw;
    let Hfnx := fresh "Hfnx" in pose proof (set_gctx_embedding_fn_kinds _ _ _ _ _ _ Hμ) as Hfnx;
    let Hfn := fresh "Hfn" in pose proof (fn_kinds_unique_of_ext Hfnx) as Hfn;
    let Hmods := fresh "Hmods" in pose proof (set_gctx_embedding_modules _ _ _ _ _ _ Hμ) as Hmods
  end;
  let GC := fresh "GC" in set (GC := gc_mk Θ2 Ξ2) in *.
