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

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export Bound.
From Mctt.Core.Syntactic Require Import Syntax Members Records.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
Import ListNotations.

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
  ; set_filed_reduct_valid : set_exp_eq T γ T2 (ctx_pi_at r T1 A0) M1 M1
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
    set_filed_term_typed : set_exp_eq T γ Tl (abs_kind_sort (mdesc_kind R0) (a_typ i)) A0 A0
    (** The type is over the telescope only *)
  ; set_filed_term_scoped : exp_scoped (List.length Tl) A0
    (** Read at arguments [Ns] for the outer part [T2]: the [Π] over the
        inner part [T1], instantiated, and the reduct, if any, a term over
        [T2] instantiated *)
  ; set_filed_term_reads : forall Ns R1 T1 T2, Tl = T1 ++ T2 -> List.length T2 = List.length Ns ->
      mdesc_term_part_ats R0 Ns = Some R1 ->
      mdesc_type R1 = Some (exp_sub (ctx_pi_at (mdesc_kind R0) T1 A0) (sb_of_list sb_id Ns)) /\
      (mdesc_reduct R1 = None \/ exists M1, set_filed_reduct_with p x R1 Ns T1 T2 (mdesc_kind R0) A0 M1)
    (** The value's kind is the stored one *)
  ; set_filed_term_kind : fst (global_term γ (qname_in p x)) = mdesc_kind R0
    (** A proof's value is the empty set *)
  ; set_filed_term_proof : mdesc_kind R0 = ak_propositional -> set_eq (snd (global_term γ (qname_in p x))) empty_set
    (** Applied to the values of an environment of the outer part, it is
        of the [Π] over the inner part there *)
  ; set_filed_term_value : forall T1 T2 ρ a, Tl = T1 ++ T2 -> set_env_in T γ T2 ρ ->
      set_interp T γ T2 ρ (ctx_pi_at (mdesc_kind R0) T1 A0) a ->
      set_mem (apply_values (snd (global_term γ (qname_in p x))) (set_env_values T2 ρ)) (code_carrier a)
    (** The [Π]s over the telescope into the member's kind are formed *)
  ; set_filed_term_pi_kinds : forall Δ1 κ A Δ2, Tl = Δ1 ++ ce_ass κ A :: Δ2 -> pi_kinds κ (mdesc_kind R0) }.

(** [set_filed_mod p Tl Φ]: the filed module [p], over its telescope [Tl],
    of the stored body [Φ], is modelled. *)
Record set_filed_mod (p : qname) (Tl : ctx) (Φ : gmod) : Prop :=
  { (** Its path reads the global module at no argument, anywhere *)
    set_filed_mod_path : forall Γ ρ, set_interp_modexp T γ Γ ρ (qname_mod p) (set_module_global p nil)
    (** The telescope denotes *)
  ; set_filed_mod_tele_ctx : set_ctx T γ Tl
    (** Of assumptions *)
  ; set_filed_mod_tele_assumptions : all_assumptions Tl
    (** Closed *)
  ; set_filed_mod_tele_scoped : ctx_scoped 0 Tl
    (** Of evaluated sorts, at one level *)
  ; set_filed_mod_tele_evaluated : exists l, set_params_evaluated T γ nil Tl l
    (** Every term member stored at it, of an entry or an open frame's
        type former, is modelled *)
  ; set_filed_mod_terms : forall x R0, stored_term_member gc_stack Φ p x R0 -> exists A0 i, set_filed_term_with p Tl x R0 A0 i
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
    (** The carriers are the least fixed points in the sort's universe *)
  ; set_group_ok_carriers : forall ρu s, set_env_in T γ (ind_uparams D) ρu -> set_interp T γ (ind_uparams D) ρu (ind_sort D) s ->
      exists U l, set_group_carriers_with G D (set_env_values (ind_uparams D) ρu) s U l
    (** A type former's closed type denotes *)
  ; set_group_ok_former_types : forall k Mk, ind_member D k = Some Mk -> exists FA, set_denotes T γ nil (ind_ty D Mk) FA
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
      set_eq (set_group_carrier G k (set_env_values (im_params D Mk) ρ)) (set_record_carrier (global_record γ qr) is) }.

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
    set_gctx_ok_filed : forall p Tl Φ, gc_loc gc_deps gc_stack p = Some (Tl, Φ) -> set_filed_mod p Tl Φ
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
