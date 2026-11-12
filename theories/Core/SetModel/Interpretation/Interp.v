(** * The Set Interpretation of Terms

    A functional relation ([set_interp]) between a term of a context and
    its value in an environment, at a universe tower and a valuation of
    the global context.  It is syntax-directed; a λ is a proof, denoting
    the empty set, when the algorithmic inference of the λ gives it a [Π]
    into propositions ([alg_type_infer_fn]): the syntax does not record the
    codomain's kind, and the typing does.  Every other proof denotes the
    empty set by its former ([a_tt], [a_conj], an elimination into
    propositions, …) or by its environment (a proof variable holds the
    empty set).  Modules, units and bodies are interpreted alongside
    ([set_interp_modexp] and the relations after it).

    A binder's body is a function [F] of the bound value, related to the
    body's value at every value of the domain and arbitrary elsewhere;
    that [F] respects equality on the domain follows from functionality
    ([set_interp_functional]). *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Operations.
From Mctt.Algorithmic.Typing Require Import Definitions.
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
    first, the empty set *)
| set_interp_and : forall Γ ρ P Q p q,
    set_interp Γ ρ P p -> set_interp (ce_ass ak_propositional P :: Γ) (set_env_extend ρ (set_entry_term ak_propositional empty_set)) Q q ->
    set_interp Γ ρ (a_and P Q) (prop_code (prop_true p /\ prop_true q))
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
(** An elimination into types: the result the eliminator's graph relates
    the scrutinee to, at the uniform parameters and the scrutinee's
    non-uniform ones, each branch at its constructor read in its context *)
| set_interp_elim : forall Γ ρ r p D Us m Bks M us v ns r0,
    r <> ak_propositional ->
    ind_lookup gc_deps gc_stack p = Some D ->
    List.length Us = List.length (set_group_uniform_types (global_group γ p)) ->
    set_interp_list Γ ρ Us us ->
    set_interp Γ ρ M v ->
    set_elim_graph Γ ρ r p D Us Bks m (us ++ ns) v r0 ->
    set_interp Γ ρ (a_elim r p Us m Bks M) r0
(** A [Π] into propositions: the impredicative quantification *)
| set_interp_pi_prop : forall Γ ρ κd A B a F,
    set_interp Γ ρ A a ->
    (forall x, set_mem x (code_carrier a) ->
       set_interp (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)) B (F x)) ->
    set_interp Γ ρ (a_pi κd ak_propositional A B) (forall_code a F)
(** A [Π] into types or types of levels: the dependent functions *)
| set_interp_pi : forall Γ ρ κd κc A B a F,
    κc <> ak_propositional ->
    set_interp Γ ρ A a ->
    (forall x, set_mem x (code_carrier a) ->
       set_interp (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)) B (F x)) ->
    set_interp Γ ρ (a_pi κd κc A B) (pi_code a F)
(** A λ the algorithmic inference gives a [Π] into propositions: a
    proof *)
| set_interp_fn_proof : forall Γ ρ A M κd C B,
    Γ ⊢a a_fn A M ⟹ nf_pi κd ak_propositional C B ->
    set_interp Γ ρ (a_fn A M) empty_set
(** Any other λ: the graph of its body on the domain *)
| set_interp_fn : forall Γ ρ A M κd κc C B a F,
    Γ ⊢a a_fn A M ⟹ nf_pi κd κc C B -> κc <> ak_propositional ->
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
    set_interp Γ ρ M v ->
    set_interp (ce_def A M :: Γ) (set_env_extend ρ (set_entry_term ak_relevant v)) B w ->
    set_interp Γ ρ (a_let (b_def A M) B) w
(** A local module *)
| set_interp_let_mod : forall Γ ρ U B m w,
    set_interp_gunit Γ ρ U m ->
    set_interp (ce_mod U :: Γ) (set_env_extend ρ (set_entry_module m)) B w ->
    set_interp Γ ρ (a_let (b_mod U) B) w
(** A local definition with a module part *)
| set_interp_let_dm : forall Γ ρ A M U B v m w,
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
(** Its parameters, outermost first, then its definition *)
| set_interp_gunit_mk : forall Γ ρ Δ D m, set_interp_unit_params Γ ρ (List.rev Δ) D m ->
    set_interp_gunit Γ ρ (gu_mk Δ D) m
(** [set_interp_unit_params Γ ρ Δ D m]: over the parameters [Δ],
    outermost first, the definition [D] denotes [m] *)
with set_interp_unit_params : ctx -> set_env -> list centry -> moddef -> set_module -> Prop :=
(** No parameter left: the definition *)
| set_interp_unit_params_nil : forall Γ ρ D m, set_interp_moddef Γ ρ D m -> set_interp_unit_params Γ ρ nil D m
(** A parameter: a function of its value *)
| set_interp_unit_params_ass : forall Γ ρ κ A Δ D a f,
    set_interp Γ ρ A a ->
    (forall x, set_mem x (code_carrier a) ->
       set_interp_unit_params (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ x)) Δ D (f x)) ->
    set_interp_unit_params Γ ρ (ce_ass κ A :: Δ) D (set_module_params a f)
(** A definition of the telescope *)
| set_interp_unit_params_def : forall Γ ρ A M Δ D v m,
    set_interp Γ ρ M v ->
    set_interp_unit_params (ce_def A M :: Γ) (set_env_extend ρ (set_entry_term ak_relevant v)) Δ D m ->
    set_interp_unit_params Γ ρ (ce_def A M :: Δ) D m
(** A module slot of the telescope *)
| set_interp_unit_params_mod : forall Γ ρ U Δ D mu m,
    set_interp_gunit Γ ρ U mu ->
    set_interp_unit_params (ce_mod U :: Γ) (set_env_extend ρ (set_entry_module mu)) Δ D m ->
    set_interp_unit_params Γ ρ (ce_mod U :: Δ) D m
(** A definition with a module part of the telescope *)
| set_interp_unit_params_dm : forall Γ ρ A M U Δ D v mu m,
    set_interp Γ ρ M v -> set_interp_gunit Γ ρ U mu ->
    set_interp_unit_params (ce_dm A M U :: Γ) (set_env_extend ρ (set_entry_both v mu)) Δ D m ->
    set_interp_unit_params Γ ρ (ce_dm A M U :: Δ) D m
(** [set_interp_moddef Γ ρ D m]: the definition [D] denotes [m] *)
with set_interp_moddef : ctx -> set_env -> moddef -> set_module -> Prop :=
(** A body: the table of its members *)
| set_interp_md_body : forall Γ ρ sm Φ ms ρ', set_interp_gmod Γ ρ Φ ms ρ' ->
    set_interp_moddef Γ ρ (md_body sm Φ) (set_module_members ms)
(** An alias: its target *)
| set_interp_md_alias : forall Γ ρ E m, set_interp_modexp Γ ρ E m -> set_interp_moddef Γ ρ (md_alias E) m
(** [set_interp_gmod Γ ρ Φ ms ρ']: the body [Φ] has the members [ms], and
    the entries after it see [ρ'] *)
with set_interp_gmod : ctx -> set_env -> gmod -> list (string * set_entry) -> set_env -> Prop :=
(** The empty body *)
| set_interp_gm_nil : forall Γ ρ, set_interp_gmod Γ ρ gm_nil nil ρ
(** A named entry, read in the body before it *)
| set_interp_gm_ext : forall Γ ρ Φ x E ms ρ' e,
    set_interp_gmod Γ ρ Φ ms ρ' -> set_interp_gentry (body_ctx Φ ++ Γ) ρ' E e ->
    set_interp_gmod Γ ρ (gm_ext Φ x E) (ms ++ [(x, e)]) (set_env_extend ρ' e)
(** A local open: the entries it generates, read in the body before it *)
| set_interp_gm_open : forall Γ ρ Φ H its Φg ms ρ' ms' ρ'',
    set_interp_gmod Γ ρ Φ ms ρ' -> set_interp_gmod (body_ctx Φ ++ Γ) ρ' Φg ms' ρ'' ->
    set_interp_gmod Γ ρ (gm_open Φ H its Φg) (ms ++ ms') ρ''
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
(** [set_branch Γ ρ r p D Us Bks k c vals res]: the branch of the
    constructor [c] of the member [k], at the values [vals] of its binders,
    has the result [res] ([elim_graph]'s branches, here as part of the
    interpretation) *)
with set_branch : ctx -> set_env -> abs_kind -> qname -> ind_decl -> list exp -> list eblock ->
    nat -> string -> list aczel_set -> aczel_set -> Prop :=
(** The branch read in its context, at the binders' values *)
| set_branch_intro : forall Γ ρ r p D Us Bks k c vals res Mk gs nm Z A Bs n B,
    ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    List.nth_error Bks k = Some (eb_mk nm Z A Bs) -> brs_lookup Bs c = Some (n, B) ->
    set_interp (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ) (set_env_extend_values ρ vals) B res ->
    set_branch Γ ρ r p D Us Bks k c vals res
(** [set_elim_graph Γ ρ r p D Us Bks k params v res]: [elim_graph] of the
    group at [p] with the branches [set_branch] *)
with set_elim_graph : ctx -> set_env -> abs_kind -> qname -> ind_decl -> list exp -> list eblock ->
    nat -> list aczel_set -> aczel_set -> aczel_set -> Prop :=
(** At a constructor: its branch at the recursive results *)
| set_elim_graph_intro : forall Γ ρ r p D Us Bks k Mk cs params vals ihs v res,
    List.nth_error (set_group_members (global_group γ p)) k = Some Mk ->
    In cs (set_member_constructors Mk) ->
    set_eq v (con_val (set_constructor_name cs) (List.skipn (List.length (set_group_uniform_types (global_group γ p))) params ++ vals)) ->
    set_arguments_results Γ ρ r p D Us Bks params (set_constructor_arguments cs) vals ihs ->
    set_branch Γ ρ r p D Us Bks k (set_constructor_name cs)
      (List.skipn (List.length (set_group_uniform_types (global_group γ p))) params ++ vals ++ ihs) res ->
    set_elim_graph Γ ρ r p D Us Bks k params v res
(** [arguments_results] with the branches [set_branch] *)
with set_arguments_results : ctx -> set_env -> abs_kind -> qname -> ind_decl -> list exp -> list eblock ->
    list aczel_set -> list set_argument -> list aczel_set -> list aczel_set -> Prop :=
(** No argument *)
| set_arguments_results_nil : forall Γ ρ r p D Us Bks pre, set_arguments_results Γ ρ r p D Us Bks pre nil nil nil
(** A non-recursive argument *)
| set_arguments_results_plain : forall Γ ρ r p D Us Bks pre κ type gs a vals ihs,
    set_arguments_results Γ ρ r p D Us Bks (pre ++ [a]) gs vals ihs ->
    set_arguments_results Γ ρ r p D Us Bks pre (set_argument_plain κ type :: gs) (a :: vals) ihs
(** A recursive argument, one result per leaf path *)
| set_arguments_results_recursive : forall Γ ρ r p D Us Bks pre type ds target tparams ls gs a vals ihs1 ihs2,
    set_leaves_results Γ ρ r p D Us Bks pre a ls ihs1 ->
    set_arguments_results Γ ρ r p D Us Bks (pre ++ [empty_set]) gs vals ihs2 ->
    set_arguments_results Γ ρ r p D Us Bks pre (set_argument_recursive type ds target tparams ls :: gs) (a :: vals) (ihs1 ++ ihs2)
(** [leaves_results] with the branches [set_branch] *)
with set_leaves_results : ctx -> set_env -> abs_kind -> qname -> ind_decl -> list exp -> list eblock ->
    list aczel_set -> aczel_set -> list set_leaf -> list aczel_set -> Prop :=
(** No path *)
| set_leaves_results_nil : forall Γ ρ r p D Us Bks pre a, set_leaves_results Γ ρ r p D Us Bks pre a nil nil
(** A path, then the others *)
| set_leaves_results_cons : forall Γ ρ r p D Us Bks pre a l ls ih ihs,
    set_leaf_result Γ ρ r p D Us Bks pre (set_leaf_steps l) l nil a ih ->
    set_leaves_results Γ ρ r p D Us Bks pre a ls ihs ->
    set_leaves_results Γ ρ r p D Us Bks pre a (l :: ls) (ih :: ihs)
(** [leaf_result] with the branches [set_branch] *)
with set_leaf_result : ctx -> set_env -> abs_kind -> qname -> ind_decl -> list exp -> list eblock ->
    list aczel_set -> list set_leaf_step -> set_leaf -> list aczel_set -> aczel_set -> aczel_set -> Prop :=
(** At the end: the eliminator at the path's member *)
| set_leaf_result_end : forall Γ ρ r p D Us Bks pre l points a ih,
    set_elim_graph Γ ρ r p D Us Bks (set_leaf_target l) (set_leaf_target_params l (pre ++ points)) a ih ->
    set_leaf_result Γ ρ r p D Us Bks pre nil l points a ih
(** Through a domain: a function of the results at its points *)
| set_leaf_result_domain : forall Γ ρ r p D Us Bks pre d steps l points a ih,
    is_function_on (code_carrier (d (pre ++ points))) ih ->
    (forall b, set_mem b (code_carrier (d (pre ++ points))) ->
       set_leaf_result Γ ρ r p D Us Bks pre steps l (points ++ [b]) (set_apply a b) (set_apply ih b)) ->
    set_leaf_result Γ ρ r p D Us Bks pre (set_leaf_step_domain d :: steps) l points a ih
(** Through a field: the result of the field *)
| set_leaf_result_field : forall Γ ρ r p D Us Bks pre f steps l points a ih,
    set_leaf_result Γ ρ r p D Us Bks pre steps l points (tuple_field a f) ih ->
    set_leaf_result Γ ρ r p D Us Bks pre (set_leaf_step_field f :: steps) l points a ih.

End Interpretation.
