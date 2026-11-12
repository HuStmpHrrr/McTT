(** * Valuations That Model a Global Context

    A valuation models the global context ([set_gctx_ok]) when what it
    gives each global is what the global's stored description denotes:

    - a term member of a filed module or frame, closed over the module's
      telescope, has its stored kind, is of its closed type and is its
      closed δ-reduct ([set_filed_term_with]);
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
    reads them alike with the [n]-th erased: its type, or its domains at
    every point and its target's parameters. *)
Definition argument_ignores (n : nat) (g : set_argument) (pre : list aczel_set) : Prop :=
  match g with
  | set_argument_plain _ type => set_eq (type pre) (type (erase_at n pre))
  | set_argument_recursive _ ds _ tparams =>
      (forall points pts, points_fit ds pre points pts ->
         Forall2 (fun d k => set_eq (d (pre ++ List.firstn k pts)) (d (erase_at n pre ++ List.firstn k pts))) ds (List.seq 0 (List.length ds))) /\
      (forall pts, points_fit ds pre nil pts -> list_set_eq (tparams (pre ++ pts)) (tparams (erase_at n pre ++ pts)))
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

(** [set_filed_term_with R0 κ g]: the closed member read as [R0] has the
    kind [κ] and the value [g]: of its type, its δ-reduct's. *)
Record set_filed_term_with (R0 : mdesc) (κ : abs_kind) (g : aczel_set) : Prop :=
  { (** The kind is the stored one *)
    set_filed_term_kind : κ = mdesc_kind R0
    (** The value is of the closed type *)
  ; set_filed_term_typed : forall A FA, mdesc_type R0 = Some A -> set_denotes T γ nil A FA ->
      set_mem g (code_carrier (FA empty_set_env))
    (** The value is the closed δ-reduct's *)
  ; set_filed_term_reduct : forall M FM, mdesc_reduct R0 = Some M -> set_denotes T γ nil M FM ->
      set_eq g (FM empty_set_env) }.

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
    (** No argument reads a recursive argument before it *)
  ; set_constructor_ok_ignores : forall n t j g ρ, List.nth_error gs n = Some (ca_rec t) -> n < j -> List.nth_error sgs j = Some g ->
      set_env_in T γ (List.skipn (List.length gs - j) (cargs_ctx p D Mk gs) ++ im_params D Mk) ρ ->
      argument_ignores (im_np D Mk + n) g (set_env_values (List.skipn (List.length gs - j) (cargs_ctx p D Mk gs) ++ im_params D Mk) ρ) }.

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

(** [set_group_carrier_with G k us ns s U l]: at the uniform parameters
    [us], the sort's value [s] is the universe [U] at the index [l], and
    the member [k]'s carrier at the non-uniform [ns] is the one [Carriers]
    builds in [U]. *)
Record set_group_carrier_with (G : set_group) (k : nat) (us ns : list aczel_set) (s U l : aczel_set) : Prop :=
  { (** A universe of sets *)
    set_group_carrier_universe : grothendieck U
    (** The sort is its universe *)
  ; set_group_carrier_sort : set_eq s (universe_code l U)
    (** The carrier is the least fixed point's *)
  ; set_group_carrier_fixed_point : set_eq (set_group_carrier G k (us ++ ns)) (member_carrier G us U U k ns) }.

(** The values of the uniform parameters and of the rest of an
    environment of a member's parameters. *)
Definition uniform_values (D : ind_decl) (Mk : imember) (ρ : set_env) : list aczel_set :=
  set_env_values (ind_uparams D) (set_env_drop (im_nn Mk) ρ).

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
  ; set_group_ok_carriers : forall k Mk ρ s, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) ρ ->
      set_interp T γ (ind_uparams D) (set_env_drop (im_nn Mk) ρ) (ind_sort D) s ->
      exists U l, set_group_carrier_with G k (uniform_values D Mk ρ) (set_env_values (im_nparams Mk) ρ) s U l
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
             (con_val c (List.skipn (ind_nu D) (set_env_values (cargs_ctx p D Mk gs ++ im_params D Mk) ρ)))
    (** The semantic signature respects equality *)
  ; set_group_ok_respects : signature_respects G
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
             (record_code (set_record_carrier SR (set_env_values (record_params R) ρ))) }.

(** ** Models *)

(** [set_gctx_ok]: [γ] models the global context. *)
Record set_gctx_ok : Prop :=
  { (** Every term member stored at a filed module or frame is modelled *)
    set_gctx_ok_terms : forall p Tl Φ x R0, gc_loc gc_deps gc_stack p = Some (Tl, Φ) ->
      stored_term_member gc_stack Φ p x R0 ->
      set_filed_term_with R0 (fst (global_term γ (qname_in p x))) (snd (global_term γ (qname_in p x)))
    (** A filed module or frame is its own global module *)
  ; set_gctx_ok_bodies : forall q TΦ, gc_loc gc_deps gc_stack q = Some TΦ -> global_module γ q = set_module_global q nil
    (** Every global module equals itself, so selection respects equality *)
  ; set_gctx_ok_modules : forall q, set_module_eq (global_module γ q) (global_module γ q)
    (** An alias is the module its closed unit denotes *)
  ; set_gctx_ok_aliases : forall q Ua FU, gc_module gc_deps gc_stack q = Some (mr_alias Ua) ->
      set_modexp_denotes T γ nil (me_lit Ua) FU -> set_module_eq (global_module γ q) (FU empty_set_env)
    (** Every group is modelled *)
  ; set_gctx_ok_groups : forall p D, ind_lookup gc_deps gc_stack p = Some D -> set_group_ok p D (global_group γ p)
    (** Every record type is modelled *)
  ; set_gctx_ok_records : forall p R, record_lookup gc_deps gc_stack p = Some R -> set_record_ok p R (global_record γ p) }.

End Model.
