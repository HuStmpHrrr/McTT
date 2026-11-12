(** * The Set Interpretation of Terms

    A relation ([set_interp]) between a term of a context and its value in
    an environment, at a universe tower and a valuation of the global
    context.  It is syntax-directed; a λ is a proof, denoting the empty
    set, when it is typed at a [Π] into propositions: the syntax does not
    record the codomain's kind, and the typing does, the same at every type
    of the λ.  Every other proof denotes the empty set by its former
    ([a_tt], [a_conj], an elimination into propositions, …) or by its
    environment (a proof variable holds the empty set).  Modules, units and
    bodies are interpreted alongside ([set_interp_modexp] and the relations
    after it), and the eliminator reads its recursive results off the
    declaration, as evaluation does ([set_elim]).

    A binder's body is a function [F] of the bound value, related to the
    body's value at every value of the domain and arbitrary elsewhere.  A
    well-formed term has one value up to equality at related environments,
    which the fundamental theorem's set field states ([set_denotes]). *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Operations.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Syntactic Require Import Syntax Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
Import ListNotations.

(** The universe of sets the types of levels are drawn from: every small
    universe's. *)
Definition level_types_universe (T : universe_tower) : aczel_set :=
  union_set (family_set (nat * nat) (fun o => tower T (us o))).

Section Interpretation.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** ** Which Members of a Unit Are Proofs

    Read off the unit's syntax, the units of the slots it reads given
    ([κs]): the members' kinds are its entries' tags, an alias's its
    target's.  A position that holds no slot reads as a term entry's module
    part does ([no_slot_proofs]), as an environment does there. *)

(** The proofness at a position holding no slot. *)
Definition no_slot_proofs : member_proofness := module_member_proofs γ (set_module_global (q_abs nil nil) nil).

(** The slots' proofness past one more entry, of the proofness [P]. *)
Definition push_slot_proofs (κs : nat -> member_proofness) (P : member_proofness) : nat -> member_proofness :=
  fun s => match s with 0 => P | S s' => κs s' end.

(** The name a chain selects first: its head, or the member itself. *)
Definition chain_key (ys : list string) (x : string) : string :=
  match ys with nil => x | y :: _ => y end.

(** A body's entry is a proof's term. *)
Definition gentry_is_proof (E : gentry) : bool :=
  match E with ge_def _ _ κ _ _ => is_proof_kind κ | _ => false end.

Fixpoint modexp_member_proofs (κs : nat -> member_proofness) (H : modexp) {struct H} : member_proofness :=
  match H with
  (** A loaded unit: its global module's *)
  | me_unit fp => module_member_proofs γ (set_module_global (q_abs fp nil) nil)
  (** A slot: its unit's, given *)
  | me_var k => κs k
  (** A submodule: at the chain past it *)
  | me_mem H' y => fun ys x => modexp_member_proofs κs H' (y :: ys) x
  (** An application: the module's *)
  | me_app H' _ => modexp_member_proofs κs H'
  (** A literal: its unit's *)
  | me_lit U => unit_member_proofs κs U
  end
with unit_member_proofs (κs : nat -> member_proofness) (U : gunit) {struct U} : member_proofness :=
  match U with
  (** Under its telescope: an assumption or a definition is no slot, a
      slot or a definition with a module part one of its unit's *)
  | gu_mk Δ D =>
      moddef_member_proofs
        ((fix tele (Δ : list centry) : nat -> member_proofness :=
            match Δ with
            | nil => κs
            | e :: Δ' =>
                push_slot_proofs (tele Δ')
                  (match e with
                   | ce_mod U' => unit_member_proofs (tele Δ') U'
                   | ce_dm _ _ U' => unit_member_proofs (tele Δ') U'
                   | _ => no_slot_proofs
                   end)
            end) Δ) D
  end
with moddef_member_proofs (κs : nat -> member_proofness) (D : moddef) {struct D} : member_proofness :=
  match D with
  (** A body: the entry the chain names *)
  | md_body _ Φ => fun ys x => match body_member_lookup κs Φ ys x with Some b => b | None => false end
  (** An alias: its target's *)
  | md_alias E => modexp_member_proofs κs E
  end
with body_slot_proofs (κs : nat -> member_proofness) (Φ : gmod) {struct Φ} : nat -> member_proofness :=
  match Φ with
  (** No entry *)
  | gm_nil => κs
  (** An entry, after the ones before it *)
  | gm_ext Φ' _ E => push_slot_proofs (body_slot_proofs κs Φ') (gentry_slot_proofs (body_slot_proofs κs Φ') E)
  (** An open: its stored entries, after the ones before it *)
  | gm_open Φ' _ _ Φg => body_slot_proofs (body_slot_proofs κs Φ') Φg
  end
with body_member_lookup (κs : nat -> member_proofness) (Φ : gmod) (ys : list string) (x : string) {struct Φ}
    : option bool :=
  match Φ with
  (** No entry *)
  | gm_nil => None
  (** The last entry so named: its term's kind, or its module part's member *)
  | gm_ext Φ' z E =>
      if String.eqb (chain_key ys x) z
      then Some (match ys with
                 | nil => gentry_is_proof E
                 | _ :: ys' => gentry_slot_proofs (body_slot_proofs κs Φ') E ys' x
                 end)
      else body_member_lookup κs Φ' ys x
  (** An open: its stored entries first, as they come later *)
  | gm_open Φ' _ _ Φg =>
      match body_member_lookup (body_slot_proofs κs Φ') Φg ys x with
      | Some b => Some b
      | None => body_member_lookup κs Φ' ys x
      end
  end
with gentry_slot_proofs (κs : nat -> member_proofness) (E : gentry) {struct E} : member_proofness :=
  match E with
  (** A definition: its module part is no module *)
  | ge_def _ _ _ _ _ => no_slot_proofs
  (** A module: its unit's *)
  | ge_mod _ U => unit_member_proofs κs U
  (** A definition with a module part: its unit's *)
  | ge_def_mod _ _ _ U => unit_member_proofs κs U
  (** An inductive or a record type of a body: none is local, the empty table *)
  | ge_ind _ _ _ _ _ => module_member_proofs γ (set_module_members nil)
  | ge_record _ _ _ _ => module_member_proofs γ (set_module_members nil)
  end.

(** The slots' proofness an environment gives: of its entries' modules. *)
Definition env_slot_proofs (ρ : set_env) : nat -> member_proofness :=
  fun s => module_member_proofs γ (set_entry_module_part (ρ s)).

(** [set_interp Γ ρ M v]: the term [M] of the context [Γ] denotes [v] in
    the environment [ρ]. *)
Inductive set_interp : ctx -> set_env -> exp -> aczel_set -> Prop :=
(** The large universe [Typeω@i] *)
| set_interp_typ : forall Γ ρ i,
    set_interp Γ ρ (a_typ i) (universe_code (large_ordinal_set i) (tower T (ul i)))
(** The small universe at a level *)
| set_interp_univ : forall Γ ρ t l,
    set_interp Γ ρ t l ->
    set_interp Γ ρ (a_univ t) (universe_code l (small_universe_set T l))
(** The type of the levels below [ω·(n+1)] *)
| set_interp_level : forall Γ ρ n, set_interp Γ ρ (a_level n) (level_type_code n)
(** The sort of the types of levels *)
| set_interp_level_sort : forall Γ ρ, set_interp Γ ρ a_level_sort (level_sort_code (level_types_universe T))
(** A level literal: its ordinal *)
| set_interp_llit : forall Γ ρ o, set_interp Γ ρ (a_llit o) (pair_ordinal_set o)
(** The successor of a level *)
| set_interp_succl : forall Γ ρ M l, set_interp Γ ρ M l -> set_interp Γ ρ (a_succl M) (successor_set l)
(** The join of two levels: their union *)
| set_interp_maxl : forall Γ ρ M N l l', set_interp Γ ρ M l -> set_interp Γ ρ N l' ->
    set_interp Γ ρ (a_maxl M N) (union_set (unordered_pair_set l l'))
(** The universe of propositions *)
| set_interp_prop : forall Γ ρ, set_interp Γ ρ a_prop prop_universe_code
(** The true proposition *)
| set_interp_True : forall Γ ρ, set_interp Γ ρ a_True (prop_code True)
(** Its proof *)
| set_interp_tt : forall Γ ρ, set_interp Γ ρ a_tt empty_set
(** The false proposition *)
| set_interp_False : forall Γ ρ, set_interp Γ ρ a_False (prop_code False)
(** Ex falso: no element is ever needed, the empty set *)
| set_interp_absurd : forall Γ ρ C M, set_interp Γ ρ (a_absurd C M) empty_set
(** A conjunction: both components true, the second at the proof of the
    first, the empty set.  [Q] is read only at proofs of [P], as a [Π]'s
    codomain is: in [Σₚ ⊥ (efq #0 return Prop)] the second component reads
    a proof of [⊥], and has a value only at one.  When [P] is false the
    conjunction is false, whatever [F] is at the empty set. *)
| set_interp_and : forall Γ ρ P Q p F,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_propositional P :: Γ ->
    set_interp Γ ρ P p ->
    (forall x, set_mem x (code_carrier p) ->
       set_interp (ce_ass ak_propositional P :: Γ) (set_env_extend ρ (set_entry_term ak_propositional x)) Q (F x)) ->
    set_interp Γ ρ (a_and P Q) (prop_code (prop_true p /\ prop_true (F empty_set)))
(** A proof of a conjunction *)
| set_interp_conj : forall Γ ρ P Q M N, set_interp Γ ρ (a_conj P Q M N) empty_set
(** The proof of a conjunction's first component *)
| set_interp_left : forall Γ ρ M, set_interp Γ ρ (a_left M) empty_set
(** The proof of a conjunction's second component *)
| set_interp_right : forall Γ ρ M, set_interp Γ ρ (a_right M) empty_set
(** A tagged proof: the proof's value *)
| set_interp_proof : forall Γ ρ P M v, set_interp Γ ρ M v -> set_interp Γ ρ (a_proof P M) v
(** The type former of a member of a group *)
| set_interp_indty : forall Γ ρ p k, set_interp Γ ρ (a_ind p k) (global_former γ p k)
(** A constructor *)
| set_interp_con : forall Γ ρ p k c, set_interp Γ ρ (a_con p k c) (global_constructor γ p k c)
(** An elimination into propositions: a proof *)
| set_interp_elim_prop : forall Γ ρ p Us m Bks M,
    set_interp Γ ρ (a_elim ak_propositional p Us m Bks M) empty_set
(** An elimination into types, typed: the eliminator at the scrutinee's
    value.  The typing fixes the uniform parameters' and the blocks'
    shapes, which weakening and substitution move the branches by *)
| set_interp_elim : forall Γ ρ r p Us m Bks M C v r0,
    r <> ak_propositional ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_elim r p Us m Bks M : C ->
    set_interp Γ ρ M v ->
    set_elim Γ ρ r p Us Bks m v r0 ->
    set_interp Γ ρ (a_elim r p Us m Bks M) r0
(** A [Π] into propositions: the impredicative quantification *)
| set_interp_pi_prop : forall Γ ρ κd A B a F,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_interp Γ ρ A a ->
    (forall x, set_mem x (code_carrier a) ->
       set_interp (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)) B (F x)) ->
    set_interp Γ ρ (a_pi κd ak_propositional A B) (forall_code a F)
(** A [Π] into types or types of levels: the dependent functions *)
| set_interp_pi : forall Γ ρ κd κc A B a F,
    κc <> ak_propositional ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_interp Γ ρ A a ->
    (forall x, set_mem x (code_carrier a) ->
       set_interp (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)) B (F x)) ->
    set_interp Γ ρ (a_pi κd κc A B) (pi_code a F)
(** A λ typed at a [Π] into propositions: a proof *)
| set_interp_fn_proof : forall Γ ρ A M κd C B,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd ak_propositional C B ->
    set_interp Γ ρ (a_fn A M) empty_set
(** Any other λ: the graph of its body on the domain *)
| set_interp_fn : forall Γ ρ A M κd κc C B a F,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd κc C B -> κc <> ak_propositional ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_interp Γ ρ A a ->
    (forall x, set_mem x (code_carrier a) ->
       set_interp (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)) M (F x)) ->
    set_interp Γ ρ (a_fn A M) (graph_set (code_carrier a) F)
(** An application *)
| set_interp_app : forall Γ ρ M N f n, set_interp Γ ρ M f -> set_interp Γ ρ N n ->
    set_interp Γ ρ (a_app M N) (set_apply f n)
(** A variable: its entry's term *)
| set_interp_var : forall Γ ρ x, set_interp Γ ρ (a_var x) (set_entry_value (ρ x))
(** A local definition *)
| set_interp_let_def : forall Γ ρ A M B v w,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A M :: Γ ->
    set_interp Γ ρ M v ->
    set_interp (ce_def A M :: Γ) (set_env_extend ρ (set_entry_term ak_relevant v)) B w ->
    set_interp Γ ρ (a_let (b_def A M) B) w
(** A local module *)
| set_interp_let_mod : forall Γ ρ U B m w,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_mod U :: Γ ->
    set_interp_gunit Γ ρ U m ->
    set_interp (ce_mod U :: Γ) (set_env_extend ρ (set_entry_module m)) B w ->
    set_interp Γ ρ (a_let (b_mod U) B) w
(** A local definition with a module part *)
| set_interp_let_dm : forall Γ ρ A M U B v m w,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_dm A M U :: Γ ->
    set_interp Γ ρ M v -> set_interp_gunit Γ ρ U m ->
    set_interp (ce_dm A M U :: Γ) (set_env_extend ρ (set_entry_both v m)) B w ->
    set_interp Γ ρ (a_let (b_def_mod A M U) B) w
(** A member of a module *)
| set_interp_mem : forall Γ ρ H x m,
    set_interp_modexp Γ ρ H m -> set_interp Γ ρ (a_mem H x) (select_term γ m x)
(** The type former of a record type *)
| set_interp_record : forall Γ ρ p, set_interp Γ ρ (a_record p) (global_record_former γ p)
(** A tuple: the graph of its fields on their names *)
| set_interp_tuple : forall Γ ρ A fs vs,
    set_interp_fields Γ ρ fs vs -> set_interp Γ ρ (a_tuple A fs) (tuple_code vs)
(** A projection: the field of the tuple *)
| set_interp_proj : forall Γ ρ f M v, set_interp Γ ρ M v -> set_interp Γ ρ (a_proj f M) (tuple_field v f)
(** [set_interp_list Γ ρ Ms vs]: the terms [Ms] denote [vs] *)
with set_interp_list : ctx -> set_env -> list exp -> list aczel_set -> Prop :=
(** No term *)
| set_interp_list_nil : forall Γ ρ, set_interp_list Γ ρ nil nil
(** A term, then the rest *)
| set_interp_list_cons : forall Γ ρ M Ms v vs, set_interp Γ ρ M v -> set_interp_list Γ ρ Ms vs ->
    set_interp_list Γ ρ (M :: Ms) (v :: vs)
(** [set_interp_fields Γ ρ fs vs]: the named fields [fs] denote the named
    values [vs] *)
with set_interp_fields : ctx -> set_env -> list (string * exp) -> list (string * aczel_set) -> Prop :=
(** No field *)
| set_interp_fields_nil : forall Γ ρ, set_interp_fields Γ ρ nil nil
(** A field, then the rest *)
| set_interp_fields_cons : forall Γ ρ f M fs v vs, set_interp Γ ρ M v -> set_interp_fields Γ ρ fs vs ->
    set_interp_fields Γ ρ ((f, M) :: fs) ((f, v) :: vs)
(** [set_interp_modexp Γ ρ H m]: the module expression [H] denotes [m] *)
with set_interp_modexp : ctx -> set_env -> modexp -> set_module -> Prop :=
(** A unit: the global module at its path *)
| set_interp_me_unit : forall Γ ρ fp, set_interp_modexp Γ ρ (me_unit fp) (set_module_global (q_abs fp nil) nil)
(** A module slot: its entry's module *)
| set_interp_me_var : forall Γ ρ k, set_interp_modexp Γ ρ (me_var k) (set_entry_module_part (ρ k))
(** A submodule *)
| set_interp_me_mem : forall Γ ρ H y m, set_interp_modexp Γ ρ H m ->
    set_interp_modexp Γ ρ (me_mem H y) (select_module γ m y)
(** An application *)
| set_interp_me_app : forall Γ ρ H N m n, set_interp_modexp Γ ρ H m -> set_interp Γ ρ N n ->
    set_interp_modexp Γ ρ (me_app H N) (apply_module m n)
(** A literal unit *)
| set_interp_me_lit : forall Γ ρ U m, set_interp_gunit Γ ρ U m -> set_interp_modexp Γ ρ (me_lit U) m
(** [set_interp_gunit Γ ρ U m]: the unit [U] denotes [m] *)
with set_interp_gunit : ctx -> set_env -> gunit -> set_module -> Prop :=
(** Its parameters, outermost first, then its definition, with which of
    its members are proofs as its syntax says *)
| set_interp_gunit_mk : forall Γ ρ Δ D P m,
    (forall ys x, P ys x = unit_member_proofs (env_slot_proofs ρ) (gu_mk Δ D) ys x) ->
    set_interp_unit_params Γ ρ P (List.rev Δ) D m ->
    set_interp_gunit Γ ρ (gu_mk Δ D) m
(** [set_interp_unit_params Γ ρ P Δ D m]: over the parameters [Δ],
    outermost first, the definition [D], of the members' proofness [P],
    denotes [m] *)
with set_interp_unit_params : ctx -> set_env -> member_proofness -> list centry -> moddef -> set_module -> Prop :=
(** No parameter left: the definition *)
| set_interp_unit_params_nil : forall Γ ρ P D m, set_interp_moddef Γ ρ D m -> set_interp_unit_params Γ ρ P nil D m
(** A parameter: a function of its value *)
| set_interp_unit_params_ass : forall Γ ρ P κ A Δ D a f,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ A :: Γ ->
    set_interp Γ ρ A a ->
    (forall x, set_mem x (code_carrier a) ->
       set_interp_unit_params (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ x)) P Δ D (f x)) ->
    set_interp_unit_params Γ ρ P (ce_ass κ A :: Δ) D (set_module_params a P f)
(** A definition of the telescope *)
| set_interp_unit_params_def : forall Γ ρ P A M Δ D v m,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A M :: Γ ->
    set_interp Γ ρ M v ->
    set_interp_unit_params (ce_def A M :: Γ) (set_env_extend ρ (set_entry_term ak_relevant v)) P Δ D m ->
    set_interp_unit_params Γ ρ P (ce_def A M :: Δ) D m
(** A module slot of the telescope *)
| set_interp_unit_params_mod : forall Γ ρ P U Δ D mu m,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_mod U :: Γ ->
    set_interp_gunit Γ ρ U mu ->
    set_interp_unit_params (ce_mod U :: Γ) (set_env_extend ρ (set_entry_module mu)) P Δ D m ->
    set_interp_unit_params Γ ρ P (ce_mod U :: Δ) D m
(** A definition with a module part of the telescope *)
| set_interp_unit_params_dm : forall Γ ρ P A M U Δ D v mu m,
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_dm A M U :: Γ ->
    set_interp Γ ρ M v -> set_interp_gunit Γ ρ U mu ->
    set_interp_unit_params (ce_dm A M U :: Γ) (set_env_extend ρ (set_entry_both v mu)) P Δ D m ->
    set_interp_unit_params Γ ρ P (ce_dm A M U :: Δ) D m
(** [set_interp_moddef Γ ρ D m]: the definition [D] denotes [m] *)
with set_interp_moddef : ctx -> set_env -> moddef -> set_module -> Prop :=
(** A body: the table of the members of its expansion, its opens replaced
    by the entries they generate, as evaluation reads it *)
| set_interp_md_body : forall Γ ρ sm Φ ms ρ', set_interp_gmod Γ ρ (gm_expand Φ) ms ρ' ->
    set_interp_moddef Γ ρ (md_body sm Φ) (set_module_members ms)
(** An alias: its target *)
| set_interp_md_alias : forall Γ ρ E m, set_interp_modexp Γ ρ E m -> set_interp_moddef Γ ρ (md_alias E) m
(** [set_interp_gmod Γ ρ Φ ms ρ']: the body [Φ], with no open, has the
    members [ms], and the entries after it see [ρ'] *)
with set_interp_gmod : ctx -> set_env -> gmod -> list (string * set_entry) -> set_env -> Prop :=
(** The empty body *)
| set_interp_gm_nil : forall Γ ρ, set_interp_gmod Γ ρ gm_nil nil ρ
(** A named entry, read in the body before it *)
| set_interp_gm_ext : forall Γ ρ Φ x E ms ρ' e,
    ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ Γ ->
    set_interp_gmod Γ ρ Φ ms ρ' -> set_interp_gentry (body_ctx Φ ++ Γ) ρ' E e ->
    set_interp_gmod Γ ρ (gm_ext Φ x E) (ms ++ [(x, e)]) (set_env_extend ρ' e)
(** [set_interp_gentry Γ ρ E e]: the entry [E] denotes [e] *)
with set_interp_gentry : ctx -> set_env -> gentry -> set_entry -> Prop :=
(** A definition: its body's value, of its kind *)
| set_interp_ge_def : forall Γ ρ b pv r A M v, set_interp Γ ρ M v ->
    set_interp_gentry Γ ρ (ge_def b pv r A (Some M)) (set_entry_term r v)
(** An assumption of a body: the empty set (no local body has one) *)
| set_interp_ge_ax : forall Γ ρ b pv r A, set_interp_gentry Γ ρ (ge_def b pv r A None) (set_entry_term r empty_set)
(** A submodule *)
| set_interp_ge_mod : forall Γ ρ pv U m, set_interp_gunit Γ ρ U m -> set_interp_gentry Γ ρ (ge_mod pv U) (set_entry_module m)
(** A definition with a module part *)
| set_interp_ge_def_mod : forall Γ ρ pv A M U v m, set_interp Γ ρ M v -> set_interp_gunit Γ ρ U m ->
    set_interp_gentry Γ ρ (ge_def_mod pv A M U) (set_entry_both v m)
(** An inductive type of a body: none is local, the empty table *)
| set_interp_ge_ind : forall Γ ρ pv pq k D Φ, set_interp_gentry Γ ρ (ge_ind pv pq k D Φ) (set_entry_module (set_module_members nil))
(** A record type of a body: none is local, the empty table *)
| set_interp_ge_record : forall Γ ρ pv p R Φ, set_interp_gentry Γ ρ (ge_record pv p R Φ) (set_entry_module (set_module_members nil))
(** [set_elim Γ ρ r p Us Bks j v res]: the eliminator of the group at
    [p] at its member [j], into the sort [r], at the uniform parameters
    [Us] and the blocks [Bks], takes [v] to [res] ([eval_elim]) *)
with set_elim : ctx -> set_env -> abs_kind -> qname -> list exp -> list eblock -> nat -> aczel_set -> aczel_set -> Prop :=
(** At a constructor of the member's container ([im_ref]: a view's
    elements are its container's): the branch, read in its context, at the
    non-uniform parameters, the arguments and the recursive results *)
| set_elim_con : forall Γ ρ r p Us Bks j v res D Mj pc k Dq Mk c gs ns vs nm Z A Bs n B ihs,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D j = Some Mj -> im_ref p j Mj = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk -> ind_con Mj c = Some gs ->
    set_eq v (con_val c (ns ++ vs)) -> List.length ns = im_nn Mk -> List.length vs = List.length gs ->
    List.nth_error Bks j = Some (eb_mk nm Z A Bs) -> brs_lookup Bs c = Some (n, B) ->
    set_ihs Γ ρ r p Us Bks gs vs ihs ->
    List.length (ns ++ vs ++ ihs) = List.length (elim_bctx r p D Mj gs (blocks_motives Bks) Us) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ ->
    set_interp (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)
      (set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mj gs (blocks_motives Bks) Us)) (ns ++ vs ++ ihs)) B res ->
    set_elim Γ ρ r p Us Bks j v res
(** A result equal to one: the eliminator's value as a function of the
    environment is a set equal to the branch's value, described among the
    motive's elements ([set_describe]), not the branch's value itself,
    which only an [∃] gives at each environment; without the axiom of
    choice no function picks it *)
| set_elim_resp : forall Γ ρ r p Us Bks j v res res',
    set_elim Γ ρ r p Us Bks j v res -> set_eq res res' -> set_elim Γ ρ r p Us Bks j v res'
(** [set_ihs Γ ρ r p Us Bks gs vs ihs]: the arguments [vs] of the kinds
    [gs] have the recursive results [ihs], one per leaf path of each
    recursive argument, in order ([eval_ihs]) *)
with set_ihs : ctx -> set_env -> abs_kind -> qname -> list exp -> list eblock -> list carg -> list aczel_set -> list aczel_set -> Prop :=
(** No argument, no result *)
| set_ihs_nil : forall Γ ρ r p Us Bks, set_ihs Γ ρ r p Us Bks nil nil nil
(** A non-recursive argument has none *)
| set_ihs_arg : forall Γ ρ r p Us Bks κ T gs v vs ihs,
    set_ihs Γ ρ r p Us Bks gs vs ihs -> set_ihs Γ ρ r p Us Bks (ca_arg κ T :: gs) (v :: vs) ihs
(** A recursive argument has its recursive results *)
| set_ihs_rec : forall Γ ρ r p Us Bks t gs v vs ihs1 ihs2,
    set_ih Γ ρ r p Us Bks t v ihs1 -> set_ihs Γ ρ r p Us Bks gs vs ihs2 ->
    set_ihs Γ ρ r p Us Bks (ca_rec t :: gs) (v :: vs) (ihs1 ++ ihs2)
(** [set_ih Γ ρ r p Us Bks t v ihs]: the argument [v] of the shape [t] has
    the recursive results [ihs], one per leaf path ([eval_ih]) *)
with set_ih : ctx -> set_env -> abs_kind -> qname -> list exp -> list eblock -> ptyp -> aczel_set -> list aczel_set -> Prop :=
(** At the end of a shape, at a member with a block: the eliminator there *)
| set_ih_self : forall Γ ρ r p Us Bks D j Mj Ps v r0,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D j = Some Mj -> im_is_rview Mj = false ->
    set_elim Γ ρ r p Us Bks j v r0 -> set_ih Γ ρ r p Us Bks (pt_self j Ps) v [r0]
(** At the end of a shape, at a record view: the recursive results of its
    fields at the fields of [v] *)
| set_ih_rview : forall Γ ρ r p Us Bks D j Mj qr Is fl c gs Ps v rs,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    im_cons Mj = [(c, gs)] -> set_ihs Γ ρ r p Us Bks gs (List.map (tuple_field v) fl) rs ->
    set_ih Γ ρ r p Us Bks (pt_self j Ps) v rs
(** At a function shape: for each leaf path of the rest, the function on
    [v]'s domain of the result at [v]'s values *)
| set_ih_pi : forall Γ ρ r p Us Bks D B t v Rs,
    ind_lookup gc_deps gc_stack p = Some D ->
    (forall b, set_mem b (relation_domain v) -> set_ih Γ ρ r p Us Bks t (set_apply v b) (Rs b)) ->
    set_ih Γ ρ r p Us Bks (pt_pi B t) v
      (List.map (fun i => graph_set (relation_domain v) (fun b => List.nth i (Rs b) empty_set))
                (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t))))
(** Results equal to ones: [Rs] above is a function of the domain's
    points, and at each point only an [∃] gives the results.  For
    [inductive Tree : Type := node : (ℕ → Tree) → Tree] and the eliminator
    at [node f], the recursive result of [f] is the graph of [n ↦] the
    eliminator at [f n]; without the axiom of choice no function picks the
    results at every [n], but one gives sets equal to them, described
    among the elements of the results' types ([set_describe]) *)
| set_ih_resp : forall Γ ρ r p Us Bks t v rs rs',
    set_ih Γ ρ r p Us Bks t v rs -> list_set_eq rs rs' -> set_ih Γ ρ r p Us Bks t v rs'.

End Interpretation.

Scheme set_interp_mut_ind := Minimality for set_interp Sort Prop
with set_interp_list_mut_ind := Minimality for set_interp_list Sort Prop
with set_interp_fields_mut_ind := Minimality for set_interp_fields Sort Prop
with set_interp_modexp_mut_ind := Minimality for set_interp_modexp Sort Prop
with set_interp_gunit_mut_ind := Minimality for set_interp_gunit Sort Prop
with set_interp_unit_params_mut_ind := Minimality for set_interp_unit_params Sort Prop
with set_interp_moddef_mut_ind := Minimality for set_interp_moddef Sort Prop
with set_interp_gmod_mut_ind := Minimality for set_interp_gmod Sort Prop
with set_interp_gentry_mut_ind := Minimality for set_interp_gentry Sort Prop
with set_elim_mut_ind := Minimality for set_elim Sort Prop
with set_ihs_mut_ind := Minimality for set_ihs Sort Prop
with set_ih_mut_ind := Minimality for set_ih Sort Prop.
Combined Scheme set_interp_combined_ind from set_interp_mut_ind, set_interp_list_mut_ind, set_interp_fields_mut_ind,
  set_interp_modexp_mut_ind, set_interp_gunit_mut_ind, set_interp_unit_params_mut_ind, set_interp_moddef_mut_ind,
  set_interp_gmod_mut_ind, set_interp_gentry_mut_ind, set_elim_mut_ind, set_ihs_mut_ind, set_ih_mut_ind.
