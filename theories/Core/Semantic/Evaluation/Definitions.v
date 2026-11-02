From Stdlib Require Import Lia List Morphisms String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'⟦' M '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦elim' m 'at' j 'of' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, j at level 0, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihs' vs 'of' gs 'under' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ih' v 'of' t 'under' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦shty' t 'of' p ups '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, t at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihty' v 'of' t 'at' p ups 'under' ρm As '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, ρm at level 0, As at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihtys' vs 'of' gs 'at' p ups 'under' ρm As '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, ρm at level 0, As at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦projs' fl 'of' v '⟧' Θ '⍮' Ξ '↘' ws" (at level 70, fl at level 69, v at level 69, Θ at level 69, Ξ at level 69, ws at level 69).
Reserved Notation "'⟦mref' j 'of' p ups '⟧' Θ '⍮' Ξ '↘' r" (at level 70, j at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' e '⟧ᵉ' Θ '⍮' Ξ '⍮' ρ '↘' d" (at level 70, e at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, d at level 69).
Reserved Notation "'⟦' σ ':' Δ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" (at level 70, σ at level 69, Δ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρσ at level 69).

Reserved Notation "'⟦' H '⟧ᵐ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, H at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦' Ms '⟧*' Θ '⍮' Ξ '⍮' ρ '↘' ms" (at level 70, Ms at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ms at level 69).
Reserved Notation "'⟦' Φ '⟧ᵇ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" (at level 70, Φ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρ' at level 69).
Reserved Notation "'$*|' m '&' ns '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, ns at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'$ᵐ|' h '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, h at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'$ᵐ*|' h '&' ns '|' Θ '⍮' Ξ '↘' r" (at level 70, h at level 69, ns at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' Δ '⊢' D '⟧ᶜ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, Δ at level 69, D at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "h '·ₜ' x Θ '⍮' Ξ '↘' r" (at level 70, x at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘ' y Θ '⍮' Ξ '↘' r" (at level 70, y at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₜ*' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘ*' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).

Generalizable All Variables.

(** The codomain of a [Π] whose codomain is a family value [f]: in the
    environment of [f], [#1 $ #0] is [f] at the argument.  The types of the
    arguments of a function shape and of their recursive results are such
    [Π]s ([d_shfam], [d_ihfam]): their codomains are computed by the
    families, so no term is built. *)
Definition fam_cod : exp := a_app (a_var 1) (a_var 0).

(** * Relevance-Directed Evaluation

    No proof is ever evaluated: a term of a propositional type is kept as
    it is written, with the environment it stands in, as the proof value
    [⋆ᵈ⟨M, ρ⟩].  The places where a proof may stand inside a relevant term
    read the sort of what stands there off values or declarations, never
    off types: the argument of an application ([arg_relevance]), a field of
    a record value (its declaration's [record_field_relevance]), a local
    definition and an entry of a module body (their types), and a
    substitution's entry (its target context's type, [eval_sub]).

    Every variable an environment binds carries its type ([entry_type]), which
    the readback of a kept proof reads the variable at; the type is a
    closure, evaluated only there. *)

(** The number of values a constructor of the member [Mk] of [D] takes
    before its arguments: all the member's parameters, the uniform ones
    only at a record view. *)
Definition con_param_count (D : ind_decl) (Mk : imember) : nat :=
  match im_head Mk with mh_record _ _ _ => ind_nu D | _ => im_np D Mk end.

(** The sort of the [n]-th argument of the constructor [c] of the member
    [Mk], as the declaration classifies it; a recursive argument is
    relevant. *)
Definition con_arg_relevance (Mk : imember) (c : string) (n : nat) : relevance :=
  match ind_con Mk c with
  | Some gs => match List.nth_error gs n with Some (ca_arg r _) => r | _ => relevant end
  | None => relevant
  end.

(** The global module at [p], given [args], lacks no parameter of its
    telescope.  A term member is selected from a saturated global module
    only; one lacking a parameter gives a member closure, as a local
    closure lacking one does. *)
Definition module_saturated (Θ : gdeps) (Ξ : gstack) (p : qname) (args : list domain) : Prop :=
  forall T Φ, gc_loc Θ Ξ p = Some (T, Φ) -> List.length T <= List.length args.

(** The sort of the next argument a function value takes: the sort of a
    function's own domain or of a neutral's [Π] domain, and the stored
    sort of a constructor's next argument.  Every other function value
    takes relevant arguments only (parameters are relevant). *)
Definition arg_relevance (Θ : gdeps) (Ξ : gstack) (f : domain) : relevance :=
  match f with
  | d_fn a _ _ => domain_relevance a
  | d_neut (d_pi _ a _ _) _ => domain_relevance a
  | d_con p k c vs =>
      match ind_lookup Θ Ξ p with
      | Some D =>
          match ind_member D k with
          | Some Mk =>
              if Nat.ltb (List.length vs) (con_param_count D Mk) then relevant
              else con_arg_relevance Mk c (List.length vs - con_param_count D Mk)
          | None => relevant
          end
      | None => relevant
      end
  | _ => relevant
  end.
(** The proof a member [x] of a saturated module is, kept as its
    selection from the module bound at [#0]: a proof member is never
    evaluated, so its value is this proof in an environment holding the
    module at [#0]. *)
Definition member_proof (x : string) : exp := a_mem (me_var 0) x.

(** The environment a proof member of a global module [p] at the
    arguments [args] is kept over ([eval_sel_global_proof]): the arguments,
    at [p]'s parameter telescope [T] (innermost first, as [gc_loc] gives
    it), then the module at [#0], stored at its alias applied to them, a
    unit written over the arguments.  So every entry is written over its
    own tail, and readback binds the arguments, then the module. *)
Definition global_proof_env (p : qname) (T : list centry) (args : list domain) : env :=
  env_tele nil (List.rev T) args ↦ᵐ dm_global p args ⦂ gu_mk nil (md_alias (me_apps (qname_mod p) (vars_from 0 (List.length args)))).

(** ** The Types of the Variables an Eliminator Binds

    A branch binds the non-uniform parameters of its member, the arguments
    of its constructor and their recursive results; a motive binds the
    member's non-uniform parameters and the scrutinee.  Their types are
    closures over the declaration's telescopes, at the uniform parameters
    [ups] ([decl_env]); none is evaluated.  At a declared member the types
    are those of the values.  REVISIT at a view: the values are the
    container's and the telescopes the view's. *)

(** The environment of a group's uniform parameters [ups]. *)
Definition decl_env (D : ind_decl) (ups : list domain) : env := env_tele nil (List.rev (ind_uparams D)) ups.

(** The arguments [vs] of a constructor of kinds [gs], with their types: a
    non-recursive one the type its declaration gives, in [ρ] extended by
    the non-recursive arguments before it; a recursive one the type of its
    shape there, at the uniform parameters [ups] of the group at [p]. *)
Fixpoint cargs_entries (p : qname) (ups : list domain) (ρ : env) (gs : list carg) (vs : list domain) : list (domain * entry_type) :=
  match vs with
  | nil => nil
  | v :: vs' =>
      match gs with
      | ca_arg _ A :: gs' => (v, entry_type_closure A ρ) :: cargs_entries p ups (ρ ↦ v ⦂ entry_type_closure A ρ) gs' vs'
      | ca_rec t :: gs' => (v, entry_type_shape p ups ρ t) :: cargs_entries p ups ρ gs' vs'
      | nil => (v, entry_type_none) :: cargs_entries p ups ρ nil vs'
      end
  end.

(** The types of the recursive results of the arguments [vs] of kinds
    [gs]: one per leaf path of each recursive argument, the motives [As]
    in [ρm], the shape's components in [ρ], which a non-recursive argument
    extends. *)
Fixpoint ihs_types (D : ind_decl) (p : qname) (ups : list domain) (ρm : env) (As : list exp)
    (ρ : env) (gs : list carg) (vs : list domain) : list entry_type :=
  match gs, vs with
  | ca_arg _ A :: gs', v :: vs' => ihs_types D p ups ρm As (ρ ↦ v ⦂ entry_type_closure A ρ) gs' vs'
  | ca_rec t :: gs', v :: vs' =>
      List.map (fun i => entry_type_induction_hypothesis ρm As p ups ρ t v i) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))
        ++ ihs_types D p ups ρm As ρ gs' vs'
  | _, _ => nil
  end.

(** [pair_values_with_types vs ts]: each value of [vs] paired with the type
    at its position in [ts]; a value past the end of [ts] is paired with no
    type ([entry_type_none]). *)
Fixpoint pair_values_with_types (vs : list domain) (ts : list entry_type) : list (domain * entry_type) :=
  match vs with
  | nil => nil
  | v :: vs' => (v, List.hd entry_type_none ts) :: pair_values_with_types vs' (List.tl ts)
  end.

(** The variables of a branch of the member [Mj] of the group [D] at
    [p], at the uniform parameters [ups], the motives [As] in [ρm]: the
    non-uniform parameters [ns], the arguments [vs] of kinds [gs] and the
    recursive results [ihs], with their types. *)
Definition branch_entries (D : ind_decl) (Mj : imember) (p : qname) (ups : list domain) (As : list exp) (ρm : env)
    (gs : list carg) (ns vs ihs : list domain) : list (domain * entry_type) :=
  let nts := tele_entries (decl_env D ups) (List.rev (im_nparams Mj)) ns in
  let ρa := env_extend_typed (decl_env D ups) nts in
  nts ++ cargs_entries p ups ρa gs vs ++ pair_values_with_types ihs (ihs_types D p ups ρm As ρa gs vs).

(** The variables of a motive of the member [Mk] of [D] at the uniform
    parameters [ups]: the non-uniform parameters [ns], and a scrutinee [m]
    of the type [a]. *)
Definition motive_entries (D : ind_decl) (Mk : imember) (ups ns : list domain) (a m : domain) : list (domain * entry_type) :=
  tele_entries (decl_env D ups) (List.rev (im_nparams Mk)) ns ++ (m, entry_type_value a) :: nil.

(** The environment of a motive over [ρ], at a scrutinee [m] of the type
    [a] at all the member's parameters [as']. *)
Definition motive_env (D : ind_decl) (Mk : imember) (ρ : env) (as' : list domain) (a m : domain) : env :=
  env_extend_typed ρ (motive_entries D Mk (List.firstn (ind_nu D) as') (List.skipn (ind_nu D) as') a m).

(** The group an eliminator eliminates by: the one written, or else that
    of the value, a constructor or a neutral of a member. *)
Definition elim_grp_of (oq : option qname) (m : domain) : option qname :=
  match oq, m with
  | Some p, _ => Some p
  | None, d_con p _ _ _ => Some p
  | None, d_neut (d_ind p _ _) _ => Some p
  | None, _ => None
  end.

(** * The Kinds of Members of Module Values

    Selection tells a member's kind (a term of a sort, a module, or both)
    without a type: the kind of a member is read off the module value and
    the syntax of the units it closes over.  A body is read through the
    entries it makes ([kinds_env]), as evaluation would but with no value
    for any definition, so that no term is evaluated: a kind does not
    depend on the values of terms, nor on a module's arguments, which are
    terms ([kinds_pads]).  The bodies read are expanded: the core open
    phase has replaced every local open by the entries it generates.  The
    relations read a closure or a submodule closure as selection on module
    values does ([eval_selm]). *)

(** The closure of a unit over [ρ], as kinds read it: a saturated alias is
    left as a closure, which kinds read through. *)
Definition dm_clo (U : gunit) (ρ : env) : dmod :=
  match U with gu_mk Δ D => dm_local Δ D ρ end.

(** [n] pads for parameters, terms whose values kinds never read, over
    [ρ]. *)
Definition kinds_pads (n : nat) (ρ : env) : env := List.repeat absent_entry n ++ ρ.

(** The entry a body's entry [y] adds over [ρ], as kinds read it, as
    [body_ctx] binds it: a module, its closure; an inductive or a record
    type, the closure of the alias of its module; a definition with a
    module part, the closure of its unit with no term value; a definition,
    a pad ([absent_entry]). *)
Definition kinds_body_entry (ρ : env) (y : string) (E : gentry) : dentry :=
  match E with
  | ge_mod _ U => de_mod (dm_clo U ρ) U
  | ge_ind _ pq _ _ _ =>
      let U := gu_mk nil (md_alias (qname_mod (qname_sibling pq y))) in de_mod (dm_clo U ρ) U
  | ge_record _ p _ _ => let U := gu_mk nil (md_alias (qname_mod p)) in de_mod (dm_clo U ρ) U
  | ge_def_mod _ _ _ U => de_dm d_prop entry_type_none (dm_clo U ρ) U
  | _ => absent_entry
  end.

(** The kind of a member with a term part and a module part, by its module
    part's kind at the empty chain: a module makes it [member_kind_dm].  For a typed
    program the module part is always a module, so this is always [member_kind_dm];
    the other cases exist only so that the kind theorems ([kind_eval]) hold
    without typing, of module parts that are no modules. *)
Definition dm_of (k : member_kind) : member_kind :=
  match k with
  | member_kind_mod => member_kind_dm
  | _ => k
  end.

Inductive dmod_member_kind (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> member_kind -> Prop :=
(** A chain of a global module, read off the global context one name at a
    time, as selection on module values reads it ([eval_selm]): the path
    reached names a definition, a term, or a body module or an open frame,
    a module; a member with a term part and a module part ([dm_path]) is
    one, named from its parent, and a chain through it is read in its
    module part; a chain through an alias is read in the alias past it.
    At the empty chain a module value, whatever member it is the module
    part of, is a module. *)
(** The path names a definition: a term of its sort *)
| dmod_member_kind_global_here_def : forall p args b pv ra A B,
    gc_resolve Θ Ξ p = Some (ge_def b pv ra A B) ->
    dmod_member_kind Θ Ξ (dm_global p args) nil (member_kind_term ra)
(** The path names a body module or an open frame: a module *)
| dmod_member_kind_global_here_mod : forall p args,
    (exists T oD, gc_module Θ Ξ p = Some (mr_body T oD)) \/ (exists TΦ, gc_frame Ξ p = Some TΦ) ->
    dmod_member_kind Θ Ξ (dm_global p args) nil member_kind_mod
(** The member [y] of the module at the path is a definition with a module
    part stored in place (its module part a body, located by [gc_loc]):
    a definition with a module part *)
| dmod_member_kind_global_here_dm : forall p args y TΦ,
    dm_path Θ Ξ (qname_app p (y :: nil)) ->
    gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ ->
    dmod_member_kind Θ Ξ (dm_global p args) (y :: nil) member_kind_dm
(** The member [y] is an alias, other than the module part of a definition
    at the end of the chain: the chain after [y] is read in the alias *)
| dmod_member_kind_global_alias_case : forall p args y ch U k,
    gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U) ->
    ch <> nil \/ ~ dm_path Θ Ξ (qname_app p (y :: nil)) ->
    gunit_member_kind Θ Ξ nil U ch k ->
    dmod_member_kind Θ Ξ (dm_global p args) (y :: ch) k
(** A definition with a module part stored as an alias: [dm_of] its alias's
    kind *)
| dmod_member_kind_global_alias_dm : forall p args y U k,
    gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U) ->
    dm_path Θ Ξ (qname_app p (y :: nil)) ->
    gunit_member_kind Θ Ξ nil U nil k ->
    dmod_member_kind Θ Ξ (dm_global p args) (y :: nil) (dm_of k)
(** The member [y] is located in place (a body, a frame or a definition),
    and the chain does not stop at the module part of a definition: the
    rest of the chain is read at the path of [y] *)
| dmod_member_kind_global_step : forall p args y ch k,
    (exists TΦ, gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ) \/
    (exists b pv ra A B, gc_resolve Θ Ξ (qname_app p (y :: nil)) = Some (ge_def b pv ra A B)) ->
    ch <> nil \/ ~ dm_path Θ Ξ (qname_app p (y :: nil)) ->
    dmod_member_kind Θ Ξ (dm_global (qname_app p (y :: nil)) args) ch k ->
    dmod_member_kind Θ Ξ (dm_global p args) (y :: ch) k
(** A closure, by its unit. *)
| dmod_member_kind_local : forall Δ D ρ ch k,
    gunit_member_kind Θ Ξ ρ (gu_mk Δ D) ch k ->
    dmod_member_kind Θ Ξ (dm_local Δ D ρ) ch k
(** A submodule closure, by the longer chain; at the empty chain it is a
    module, its member's module part when that member has a term part too. *)
(** The longer chain, unless it is the empty chain at a definition with a
    module part *)
| dmod_member_kind_member : forall h ch0 ch k,
    dmod_member_kind Θ Ξ h (ch0 ++ ch) k ->
    ch <> nil \/ k <> member_kind_dm ->
    dmod_member_kind Θ Ξ (dm_member h ch0) ch k
(** The empty chain at a definition with a module part: the closure is its
    module part, a module *)
| dmod_member_kind_member_dm : forall h ch0,
    dmod_member_kind Θ Ξ h ch0 member_kind_dm ->
    dmod_member_kind Θ Ξ (dm_member h ch0) nil member_kind_mod
with gunit_member_kind (Θ : gdeps) (Ξ : gstack) : env -> gunit -> list string -> member_kind -> Prop :=
(** A body itself, at the empty chain: a module *)
| gunit_member_kind_self : forall ρ Δ sm Φ, gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) nil member_kind_mod
(** A definition of the body: a term of its sort *)
| gunit_member_kind_def : forall ρ Δ sm Φ Φ' x b pv ra A B,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv ra A B)) ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: nil) (member_kind_term ra)
(** A submodule of the body: the rest of the chain read in its unit, in the
    environment of the entries before it *)
| gunit_member_kind_mod : forall ρ Δ sm Φ Φ' y pm Uy ρ1 ch k,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    kinds_env Θ Ξ (kinds_pads (List.length Δ) ρ) Φ' ρ1 ->
    gunit_member_kind Θ Ξ ρ1 Uy ch k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (y :: ch) k
(** A definition with a module part is one ([dm_of] its module part's
    kind), and a chain through it is read in its module part, as at the
    global level. *)
(** A definition with a module part of the body, at the end of the chain:
    [dm_of] the kind of its module part *)
| gunit_member_kind_dm_here : forall ρ Δ sm Φ Φ' y pv A M Uy ρ1 k,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
    kinds_env Θ Ξ (kinds_pads (List.length Δ) ρ) Φ' ρ1 ->
    gunit_member_kind Θ Ξ ρ1 Uy nil k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (y :: nil) (dm_of k)
(** A definition with a module part of the body, the chain going on: the
    rest of the chain read in its module part, in the environment of the
    entries before it *)
| gunit_member_kind_dm_step : forall ρ Δ sm Φ Φ' y pv A M Uy ρ1 ch k,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
    ch <> nil ->
    kinds_env Θ Ξ (kinds_pads (List.length Δ) ρ) Φ' ρ1 ->
    gunit_member_kind Θ Ξ ρ1 Uy ch k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (y :: ch) k
(** An alias unit: the chain is read in its target *)
| gunit_member_kind_alias : forall ρ Δ E ch k,
    modexp_member_kind Θ Ξ (kinds_pads (List.length Δ) ρ) E ch k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_alias E)) ch k
with modexp_member_kind (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list string -> member_kind -> Prop :=
(** A unit: the chain read in the global module of the unit *)
| modexp_member_kind_unit : forall ρ fp ch k,
    dmod_member_kind Θ Ξ (dm_global (q_abs fp nil) nil) ch k ->
    modexp_member_kind Θ Ξ ρ (me_unit fp) ch k
(** A module slot: the chain read in the module value of the slot *)
| modexp_member_kind_var : forall ρ x ch k,
    dmod_member_kind Θ Ξ (env_mod ρ x) ch k ->
    modexp_member_kind Θ Ξ ρ (me_var x) ch k
(** A literal unit: the chain read in the unit *)
| modexp_member_kind_lit : forall ρ U ch k,
    gunit_member_kind Θ Ξ ρ U ch k ->
    modexp_member_kind Θ Ξ ρ (me_lit U) ch k
(** A selection, by the longer chain; at the empty chain it is a module,
    its member's module part when that member has a term part too. *)
(** The longer chain, unless it is the empty chain at a definition with a
    module part *)
| modexp_member_kind_mem : forall ρ H y ch k,
    modexp_member_kind Θ Ξ ρ H (y :: ch) k ->
    ch <> nil \/ k <> member_kind_dm ->
    modexp_member_kind Θ Ξ ρ (me_mem H y) ch k
(** The empty chain at a definition with a module part: the selection is
    its module part, a module *)
| modexp_member_kind_mem_dm : forall ρ H y,
    modexp_member_kind Θ Ξ ρ H (y :: nil) member_kind_dm ->
    modexp_member_kind Θ Ξ ρ (me_mem H y) nil member_kind_mod
(** An application: the chain read in the module applied *)
| modexp_member_kind_app : forall ρ H N ch k,
    modexp_member_kind Θ Ξ ρ H ch k ->
    modexp_member_kind Θ Ξ ρ (me_app H N) ch k
(** The environment an expanded body makes, as kinds read it: an entry
    each body entry adds ([kinds_body_entry]). *)
with kinds_env (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
(** The empty body adds nothing *)
| kinds_env_nil : forall ρ, kinds_env Θ Ξ ρ gm_nil ρ
(** An entry adds its [kinds_body_entry] *)
| kinds_env_ext : forall ρ Φ ρ1 y E,
    kinds_env Θ Ξ ρ Φ ρ1 ->
    kinds_env Θ Ξ ρ (gm_ext Φ y E) (kinds_body_entry ρ1 y E :: ρ1).

Scheme dmod_member_kind_mut_ind := Induction for dmod_member_kind Sort Prop
with gunit_member_kind_mut_ind := Induction for gunit_member_kind Sort Prop
with modexp_member_kind_mut_ind := Induction for modexp_member_kind Sort Prop
with kinds_env_mut_ind := Induction for kinds_env Sort Prop.
Combined Scheme kind_mut_ind from dmod_member_kind_mut_ind, gunit_member_kind_mut_ind, modexp_member_kind_mut_ind, kinds_env_mut_ind.

#[export]
Hint Constructors dmod_member_kind gunit_member_kind modexp_member_kind kinds_env : mctt.

(** * Evaluation of Expressions

    The relations are mutually defined: evaluation of terms, the
    eliminator's cases and semantic application; evaluation of module
    expressions and the operations on module values (application, selection
    of a submodule or a member, along a chain); and the environment a body
    unit's members see.  All are relative to the global context [Θ ⍮ Ξ],
    which does not change during NbE.  A global is resolved by lookup in
    [Θ ⍮ Ξ]: a transparent definition unfolds to its body, and any other global
    is a neutral at its type.  No rule applies a syntactic operation such as
    substitution to a term, and none builds syntax: a global is looked up,
    never rebuilt.

    A module value is saturated when it has as many arguments as its unit has
    parameters.  Selection on a saturated module is [δ]: it gives the bound
    value, by evaluating the body up to the member, or by selecting from the
    alias's target.  Selection on an unsaturated one gives a member closure
    ([d_member], [dm_member]), which the remaining arguments complete.  A global
    module needs neither: its members are stored generalized over its
    parameters, so selection applies the generalized member to the arguments
    there are. *)
Inductive eval_exp (Θ : gdeps) (Ξ : gstack) : exp -> env -> domain -> Prop :=
(** A universe is its own value. *)
| eval_exp_typ :
  `( ⟦ Typeω@i ⟧ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌ω@i )
(** A small universe evaluates its level. *)
| eval_exp_univ :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ l ->
     ⟦ Type⟨M⟩ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌@l )
(** [Level] is a value. *)
| eval_exp_level :
  `( ⟦ Level@n ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Levelᵈ@n )
(** So is the sort of the types of levels. *)
| eval_exp_level_sort :
  `( ⟦ LevelSort ⟧ Θ ⍮ Ξ ⍮ ρ ↘ LevelSortᵈ )
(** A level literal is the flat level with that constant and no atom. *)
| eval_exp_llit :
  `( ⟦ 𝕃ᵒ o ⟧ Θ ⍮ Ξ ⍮ ρ ↘ domain_level_lit o )
(** The level operations only flatten: they add to the offsets, or join the
    constants and concatenate the atoms.  Canonicalisation is readback's. *)
| eval_exp_succl :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succl M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ domain_level_suc m )
(** The join of two levels: the flat join of their values. *)
| eval_exp_maxl :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     ⟦ maxl M N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ domain_level_max m n )
(** A variable is read off the environment. *)
| eval_exp_var :
  `( ⟦ #x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρ x )
(** [Prop] is a value. *)
| eval_exp_prop :
  `( ⟦ Propₘ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Propᵈ )
(** [⊤] is a value. *)
| eval_exp_True :
  `( ⟦ ⊤ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⊤ᵈ )
(** The introduction of [⊤] is a proof, kept as it is. *)
| eval_exp_tt :
  `( ⟦ a_tt ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_tt, ρ⟩ )
(** [⊥] is a value. *)
| eval_exp_False :
  `( ⟦ ⊥ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⊥ᵈ )
(** Ex falso never evaluates its proof: it is stuck at its type, on the
    proof kept as it is. *)
| eval_exp_absurd :
  `( ⟦ C ⟧ Θ ⍮ Ξ ⍮ ρ ↘ c ->
     ⟦ efq M return C ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ c (efqᵈ ⋆ᵈ⟨M, ρ⟩ return c) )
(** A [Σₚ] evaluates its first component and closes over its second. *)
| eval_exp_and :
  `( ⟦ P ⟧ Θ ⍮ Ξ ⍮ ρ ↘ p ->
     ⟦ Σₚ P Q ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Σₚᵈ p ρ Q )
(** The proof of a conjunction is kept as it is; its parts are not
    evaluated. *)
| eval_exp_conj :
  `( ⟦ a_conj T M N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_conj T M N, ρ⟩ )
(** So is the proof of its first component. *)
| eval_exp_left :
  `( ⟦ a_left M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_left M, ρ⟩ )
(** And that of its second. *)
| eval_exp_right :
  `( ⟦ a_right M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_right M, ρ⟩ )
(** The type former and a constructor of a member of a group of inductive
    types are values, with no argument yet. *)
| eval_exp_indty :
  `( ⟦ a_ind p k ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_ind p k nil )
(** A constructor, with no argument yet, when it is a value of its own
    before any argument ([im_starts]). *)
| eval_exp_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_starts D Mk = true ->
     ⟦ a_con p k c ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_con p k c nil )
(** A constructor of a view of a group with no uniform parameters is at
    once the container's, at the view's arguments. *)
| eval_exp_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_nu D = 0 ->
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ nil ↘ cups ->
     ⟦ a_con p j c ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_con qc k c cups )
(** The constructor of a record view of a group with no uniform
    parameters, of a record with fields: a value of its own, waiting for
    the fields. *)
| eval_exp_con_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ind_nu D = 0 ->
     0 < List.length fl ->
     ⟦ a_con p j c ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_con p j c nil )
(** The constructor of a record view of a group with no uniform
    parameters, of a record without fields: at once the empty tuple. *)
| eval_exp_con_rview_empty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is nil ->
     ind_nu D = 0 ->
     ⟦ a_con p j c ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_tuple nil )
(** The eliminator evaluates its scrutinee, then eliminates the value, by
    the blocks of its group: the one written, or the group of the value,
    at the group's uniform parameters it carries. *)
| eval_exp_elim :
  `( ⟦ Us ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ups ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     elim_grp_of oq m = Some p ->
     ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ a_elim relevant oq Us j Bks M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An eliminator into propositions is a proof, kept as it is. *)
| eval_exp_elim_proof :
  `( ⟦ a_elim propositional oq Us j Bks M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_elim propositional oq Us j Bks M, ρ⟩ )
(** A [Π] evaluates its domain and closes over its codomain, at its
    relevance tag. *)
| eval_exp_pi :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ a_pi r A B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_pi r a ρ B )
(** A function evaluates its domain and closes over its body: it keeps its
    domain, so that its application can tell a proof argument. *)
| eval_exp_fn :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ λ A M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ λᵈ a ρ M )
(** An application of a function taking a relevant argument applies the
    value of the function to that of the argument. *)
| eval_exp_app :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     arg_relevance Θ Ξ m = relevant ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $| m & n | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An application of a function taking a proof applies it to the proof
    kept as it is; the argument is not evaluated. *)
| eval_exp_app_proof :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     arg_relevance Θ Ξ m = propositional ->
     $| m & ⋆ᵈ⟨N, ρ⟩ | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local definition at a relevant type extends the environment by the
    value of its body, at its type; nothing is substituted. *)
| eval_exp_let :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     domain_relevance a = relevant ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ m ⦂ entry_type_value a ↘ r ->
     ⟦ ℓ A ≔ M in B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** One at a proposition binds its body, a proof, kept as it is. *)
| eval_exp_let_proof :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     domain_relevance a = propositional ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⋆ᵈ⟨M, ρ⟩ ⦂ entry_type_value a ↘ r ->
     ⟦ ℓ A ≔ M in B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local module extends it by the unit's closure, at the unit. *)
| eval_exp_let_mod :
  `( ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ᵐ h ⦂ gu_mk Δ D ↘ r ->
     ⟦ ℓₘ (gu_mk Δ D) in B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A member is read off the root of its module expression, then applied to
    the module's arguments: arguments commute with selection.  Without
    arguments this is selection from the module's value.  The parameters
    of a module are relevant, so its arguments are all evaluated, as
    [eval_me_app] evaluates them. *)
| eval_exp_mem :
  `( modexp_spine H = (R, args, pre) ->
     ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     h ·ₜ* (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
     ⟦ args ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns ->
     $*| f & ns | Θ ⍮ Ξ ↘ r ->
     ⟦ a_mem H x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A record's type former is a value, with no argument yet. *)
| eval_exp_record :
  `( ⟦ a_record p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_record p nil )
(** A record element is the tuple of its fields' values, by name, a
    propositional field kept as it is ([eval_field_vals]); the type it is annotated with
    is evaluated only to find the record, whose declaration stores the
    fields' sorts, and the value carries no parameters. *)
| eval_exp_tuple :
  `( ⟦ T ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_record p ns ->
     record_lookup Θ Ξ p = Some R ->
     eval_field_vals Θ Ξ (record_field_relevance R) (List.map snd fs) ρ vs ->
     ⟦ a_tuple T fs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_tuple (List.combine (List.map fst fs) vs) )
(** A field: the field of the value. *)
| eval_exp_proj :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     eval_proj Θ Ξ f m r ->
     ⟦ a_proj f M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' e '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_exp Θ Ξ e ρ r)
(** The field [f] of a value: of a tuple, the value of its first field so
    named; of a neutral of a record type, the neutral projection, at the
    field's type at the type's parameters and the neutral projections of
    the fields before it (read off the neutral's annotation, as a stuck
    eliminator's motive is). *)
with eval_proj (Θ : gdeps) (Ξ : gstack) : string -> domain -> domain -> Prop :=
(** A tuple: its field *)
| eval_proj_tuple :
  `( field_lookup vs f = Some r ->
     eval_proj Θ Ξ f (d_tuple vs) r )
(** A neutral: its projection, at the field's type *)
| eval_proj_neut :
  `( record_lookup Θ Ξ p = Some R ->
     field_index (record_fields R) f = Some k ->
     eval_neutral_fields Θ Ξ m (env_tele nil (List.rev (record_params R)) ns) (List.firstn (S k) (record_fields R)) rs ->
     List.nth_error rs k = Some r ->
     eval_proj Θ Ξ f (⇑ (d_record p ns) m) r )
(** [eval_neutral_fields m ρ fl rs]: the neutral projections [rs] of [m] at
    the fields [fl], each at its type in [ρ], the environment of the
    type's parameters and the projections of the fields before it. *)
with eval_neutral_fields (Θ : gdeps) (Ξ : gstack) : domain_ne -> env -> list (string * exp) -> list domain -> Prop :=
(** No field left *)
| eval_neutral_fields_nil :
  `( eval_neutral_fields Θ Ξ m ρ nil nil )
(** The next field's projection, at its type, then the rest after it *)
| eval_neutral_fields_cons :
  `( ⟦ T ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     eval_neutral_fields Θ Ξ m (ρ ↦ ⇑ a (d_proj g m) ⦂ entry_type_closure T ρ) fl rs ->
     eval_neutral_fields Θ Ξ m ρ ((g, T) :: fl) (⇑ a (d_proj g m) :: rs) )
(** The eliminator of the group at [p] at its member [j], on a value.  The
    member is the declared member [k] of the group at [q] ([im_ref]): the
    group itself at a declared member, the container's at a view.  On a
    constructor of it at all its parameters and arguments, the branch of
    the constructor in the member's block, with its non-uniform parameters,
    its arguments and the recursive results, each by the eliminator at the
    member of the group its argument is recursive in, as the group
    classifies the member's arguments.  On a neutral of the member, a
    neutral at the motive's instance; the neutral records the parameters of
    its type, which readback needs, and the group's uniform parameters
    [ups] the eliminator carries. *)
with eval_elim (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> domain -> Prop :=
(** On a saturated constructor: its branch, at the non-uniform parameters,
    the arguments and the recursive results.  The group's table of leaf
    paths is coherent ([leaves_coherent D]), a gate on the group, the twin
    of readback's [rview_leaf_arity]: the recursive results along the
    record views' fields are then as many as the branch binds
    ([cargs_nrec]). *)
| eval_elim_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     ind_con Mj c = Some gs ->
     List.length vs = (im_np Dq Mk + List.length gs)%nat ->
     List.nth_error Bks j = Some b ->
     brs_lookup (eb_brs b) c = Some (n, B) ->
     n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat ->
     leaves_coherent D ->
     ⟦ihs skipn (im_np Dq Mk) vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (branch_entries D Mj p ups (blocks_motives Bks) ρ gs
                                    (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs)) (skipn (im_np Dq Mk) vs) ihs) ↘ r ->
     ⟦elim d_con pc k c vs at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** On a neutral: a stuck eliminator, at the motive's instance.  The
    motive's variables are typed by the eliminator's own telescope: its
    non-uniform parameters, the neutral's, at the member [j] of [D] at the
    eliminator's uniform parameters [ups], and the scrutinee, the neutral
    itself, at the member's type at [ups] ([eval_mref]) and at those
    parameters; as the eliminator's typing rule checks the motive, as
    [eval_ihty_self] types it, and as readback reads it.  So its entries
    read back at that admissible base whatever the neutral's annotation
    is, which the model does not constrain: for [W (A : Type) : A → Type]
    eliminated at [ups = [ℕ]], a neutral annotated [W Bool x] binds [x] at
    [ℕ] and itself at [W ℕ x], where they read back, not at [Bool] and
    [W Bool x].  In a well-typed program the annotation and this instance
    agree, so only the model sees the difference. *)
| eval_elim_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_binder_count b = S (im_nn Mk) ->
     ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (pc, k, cups) ->
     ⟦ eb_motive b ⟧ Θ ⍮ Ξ ⍮ motive_env D Mj ρ (ups ++ List.skipn (ind_nu Dq) as')
                               (d_ind pc k (cups ++ List.skipn (ind_nu Dq) as')) (⇑ (d_ind pc k as') m) ↘ a ->
     ⟦elim ⇑ (d_ind pc k as') m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_elim ρ Bks p ups j as' m) )
where "'⟦elim' m 'at' j 'of' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_elim Θ Ξ ρ p ups Bks j m r)
(** The recursive results of the arguments [vs], one per leaf path of each
    recursive argument, in order. *)
with eval_ihs (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> list carg -> list domain -> list domain -> Prop :=
(** No argument, no result *)
| eval_ihs_nil :
  `( ⟦ihs nil of nil under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A non-recursive argument has none *)
| eval_ihs_arg :
  `( ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihs v :: vs of ca_arg r T :: gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs )
(** A recursive argument has its recursive results *)
| eval_ihs_rec :
  `( ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs1 ->
     ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihs v :: vs of ca_rec t :: gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs1 ++ ihs )
where "'⟦ihs' vs 'of' gs 'under' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_ihs Θ Ξ ρ p ups Bks gs vs r)
(** The recursive results of an argument [v] of shape [t], one per leaf
    path: the eliminator at [v], at the member the shape ends in; at a
    record view, those of the view's fields, at [v]'s projections; at a
    function shape, the family of each recursive result at [v]'s
    values. *)
with eval_ih (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> ptyp -> domain -> list domain -> Prop :=
(** At the end of a shape, at a member with a block: the eliminator at the
    member [j] *)
| eval_ih_self :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     ⟦elim v at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ih v of pt_self j Ps under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r :: nil )
(** At the end of a shape, at a record view: the recursive results of its
    fields at the projections of [v] *)
| eval_ih_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws ->
     ⟦ihs ws of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦ih v of pt_self j Ps under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** At a function shape: the family of each recursive result of the rest
    at [v]'s values, one per leaf path of the rest *)
| eval_ih_pi :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ih v of pt_pi B t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ
       ↘ List.map (fun i => d_ihfn ρ Bks p ups t i v) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t))) )
where "'⟦ih' v 'of' t 'under' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_ih Θ Ξ ρ p ups Bks t v r)
(** The projections of a value at the fields [fl], in order. *)
with eval_projs (Θ : gdeps) (Ξ : gstack) : list string -> domain -> list domain -> Prop :=
(** No field *)
| eval_projs_nil :
  `( ⟦projs nil of v ⟧ Θ ⍮ Ξ ↘ nil )
(** The first field's projection, then the rest *)
| eval_projs_cons :
  `( eval_proj Θ Ξ f v w ->
     ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws ->
     ⟦projs f :: fl of v ⟧ Θ ⍮ Ξ ↘ w :: ws )
where "'⟦projs' fl 'of' v '⟧' Θ '⍮' Ξ '↘' ws" := (eval_projs Θ Ξ fl v ws)
(** The member [j] of the group at [p] at the uniform parameters [ups]:
    the declared member [k] of the group at [q] at the uniform parameters
    [pre] ([im_ref], [im_pre]), the group itself and [ups] at a declared
    member, the container's and the view's arguments at [ups] at a view. *)
with eval_mref (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> nat -> (qname * nat * list domain) -> Prop :=
(** A declared member: itself, at [ups] *)
| eval_mref_decl :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_decl pm ->
     ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (p, j, ups) )
(** A view: the container's member, at the view's arguments at [ups] *)
| eval_mref_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ decl_env D ups ↘ cups ->
     ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (qc, k, cups) )
where "'⟦mref' j 'of' p ups '⟧' Θ '⍮' Ξ '↘' r" := (eval_mref Θ Ξ p ups j r)
(** The type of an argument of shape [t] in [ρ], at the uniform parameters
    [ups] of the group at [p]: at the end, the member the shape ends in at
    the shape's non-uniform parameters: the container's type at a view, as
    every value and every neutral of a view is of the container's member.
    Readback reads an argument of a shape at the group's own member instead
    ([read_shape]). *)
with eval_shape_type (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> domain -> Prop :=
(** At the end: the member's type former at the shape's parameters *)
| eval_shape_type_self :
  `( ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (pc, k, pre) ->
     ⟦shty pt_self j Ps of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_ind pc k (pre ++ bs) )
(** At the end, at a record view: the record type at the view's instance
    at [ups] *)
| eval_shape_type_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ decl_env D ups ↘ cups ->
     ⟦shty pt_self j Ps of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_record qr cups )
(** At a domain: a [Π] over it, of the shape family.  The environment of
    the codomain [fam_cod] binds the family alone; it never holds a proof,
    so its entry is at no type ([entry_type_none]). *)
| eval_shape_type_pi :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦shty pt_pi B t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ b (nil ↦ d_shfam p ups ρ B t ⦂ entry_type_none) fam_cod )
where "'⟦shty' t 'of' p ups '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_shape_type Θ Ξ p ups ρ t r)
(** The types of the recursive results of an argument [v] of shape [t],
    one per leaf path, its components in [ρ], of the group at [p] at the
    uniform parameters [ups]: the motive of the member the shape ends in,
    among [As] in [ρm], at the shape's non-uniform parameters and [v]; at a
    record view, those of its fields at [v]'s projections, their components
    over [ups]; at a function shape, a [Π] over the domain of each. *)
with eval_ihty (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> ptyp -> domain -> list domain -> Prop :=
(** At the end, at a member with a block: the member's motive at the
    shape's parameters and [v] *)
| eval_ihty_self :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦ List.nth j As exp_default ⟧ Θ ⍮ Ξ ⍮
       env_extend_typed ρm (tele_entries (decl_env D ups) (List.rev (im_nparams Mj)) bs ++ (v, entry_type_shape p ups ρ (pt_self j Ps)) :: nil) ↘ a ->
     ⟦ihty v of pt_self j Ps at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a :: nil )
(** At the end, at a record view: those of its fields at [v]'s
    projections *)
| eval_ihty_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws ->
     ⟦ihtys ws of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ decl_env D ups ↘ rs ->
     ⟦ihty v of pt_self j Ps at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** At a domain: a [Π] over it, of each recursive result's family *)
| eval_ihty_pi :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦ihty v of pt_pi B t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ
       ↘ List.map (fun i => Πᵈ b (nil ↦ d_ihfam ρm As p ups ρ B t i v ⦂ entry_type_none) fam_cod)
           (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t))) )
where "'⟦ihty' v 'of' t 'at' p ups 'under' ρm As '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_ihty Θ Ξ p ups ρm As ρ t v r)
(** The types of the recursive results of the fields [vs] of a record
    view, of kinds [gs], their components in [ρ], which a non-recursive
    field extends. *)
with eval_ihtys (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> list carg -> list domain -> list domain -> Prop :=
(** No field, no result *)
| eval_ihtys_nil :
  `( ⟦ihtys nil of nil at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A non-recursive field has none, and extends the components'
    environment *)
| eval_ihtys_arg :
  `( ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↦ v ⦂ entry_type_closure T ρ ↘ rs ->
     ⟦ihtys v :: vs of ca_arg r T :: gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** A recursive field has those of its shape *)
| eval_ihtys_rec :
  `( ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs1 ->
     ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦ihtys v :: vs of ca_rec t :: gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs1 ++ rs )
where "'⟦ihtys' vs 'of' gs 'at' p ups 'under' ρm As '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_ihtys Θ Ξ p ups ρm As ρ gs vs r)
with eval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
(** A function's body, at the argument. *)
| eval_app_fn :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_value a ↘ m ->
     $| λᵈ a ρ M & n | Θ ⍮ Ξ ↘ m )
(** A neutral applied, at the codomain's instance.  No rule applies a
    proof: an application whose function is a proof is at a [∀], hence
    itself a proof, which relevance-directed evaluation never evaluates. *)
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_value a ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
(** The type former takes a parameter it still lacks. *)
| eval_app_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length as' < im_np D Mk ->
     $| d_ind p k as' & n | Θ ⍮ Ξ ↘ d_ind p k (as' ++ n :: nil) )
(** So does a record's type former. *)
| eval_app_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns < List.length (record_params R) ->
     $| d_record p ns & n | Θ ⍮ Ξ ↘ d_record p (ns ++ n :: nil) )
(** So does a constructor, a parameter or an argument. *)
| eval_app_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length vs < (im_np D Mk + List.length gs)%nat ->
     $| d_con p k c vs & n | Θ ⍮ Ξ ↘ d_con p k c (vs ++ n :: nil) )
(** A constructor of a view takes the group's uniform parameters; at the
    last of them it is the container's, at the view's arguments there. *)
| eval_app_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) < ind_nu D ->
     $| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con p j c (vs ++ n :: nil) )
(** At the last uniform parameter, the container's constructor at the
    view's arguments *)
| eval_app_con_view_ups :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) = ind_nu D ->
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ decl_env D (vs ++ n :: nil) ↘ cups ->
     $| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con qc k c cups )
(** The constructor of a record view takes the group's uniform parameters
    and the fields; before the last of them it waits for more *)
| eval_app_con_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) < ind_nu D + List.length fl ->
     $| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con p j c (vs ++ n :: nil) )
(** At the last one, the tuple of the fields, by name: a record value
    carries no parameters *)
| eval_app_con_rview_full :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) = ind_nu D + List.length fl ->
     $| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_tuple (List.combine fl (List.skipn (ind_nu D) (vs ++ n :: nil))) )
(** The [i]-th recursive result of a function shape, at the argument's
    value: the [i]-th of the rest's at the function's value there. *)
| eval_app_ihfn :
  `( $| f & n | Θ ⍮ Ξ ↘ fn ->
     ⟦ih fn of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     List.nth_error rs i = Some r ->
     $| d_ihfn ρ Bks p ups t i f & n | Θ ⍮ Ξ ↘ r )
(** The families of the types of an argument of a function shape and of its
    recursive result. *)
| eval_app_shfam :
  `( ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_closure B ρ ↘ a ->
     $| d_shfam p ups ρ B t & n | Θ ⍮ Ξ ↘ a )
(** The [i]-th recursive result's family, at the argument's value *)
| eval_app_ihfam :
  `( $| f & n | Θ ⍮ Ξ ↘ fn ->
     ⟦ihty fn of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_closure B ρ ↘ as' ->
     List.nth_error as' i = Some a ->
     $| d_ihfam ρm As p ups ρ B t i f & n | Θ ⍮ Ξ ↘ a )
(** A member closure takes the next argument of its module, and selects again. *)
| eval_app_member :
  `( $ᵐ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₜ* ch Θ ⍮ Ξ ↘ r ->
     $| d_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" := (eval_app Θ Ξ m n r)
with eval_exps (Θ : gdeps) (Ξ : gstack) : list exp -> env -> list domain -> Prop :=
(** No terms. *)
| eval_exps_nil :
  `( ⟦ nil ⟧* Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A term, then the rest. *)
| eval_exps_cons :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms ->
     ⟦ M :: Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ m :: ms )
where "'⟦' Ms '⟧*' Θ '⍮' Ξ '⍮' ρ '↘' ms" := (eval_exps Θ Ξ Ms ρ ms)
(** [eval_app_args f Ms ρ r]: [f] applied to the terms [Ms] in [ρ],
    outermost first, is [r]; an argument the function at that point takes
    as a proof ([arg_relevance]) is kept as it is, unevaluated, as in
    [eval_exp_app_proof]. *)
with eval_app_args (Θ : gdeps) (Ξ : gstack) : domain -> list exp -> env -> domain -> Prop :=
(** No argument: the function itself. *)
| eval_app_args_nil :
  `( eval_app_args Θ Ξ f nil ρ f )
(** A relevant argument: its value applied, then the rest. *)
| eval_app_args_relevant :
  `( arg_relevance Θ Ξ f = relevant ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $| f & n | Θ ⍮ Ξ ↘ g ->
     eval_app_args Θ Ξ g Ns ρ r ->
     eval_app_args Θ Ξ f (N :: Ns) ρ r )
(** A proof argument: the proof applied, kept as it is, then the rest. *)
| eval_app_args_proof :
  `( arg_relevance Θ Ξ f = propositional ->
     $| f & ⋆ᵈ⟨N, ρ⟩ | Θ ⍮ Ξ ↘ g ->
     eval_app_args Θ Ξ g Ns ρ r ->
     eval_app_args Θ Ξ f (N :: Ns) ρ r )
(** [eval_field_vals rs Ms ρ vs]: the values [vs] of the fields [Ms] of a record
    value, the field at the sort [propositional] in [rs] a proof kept as
    it is, not evaluated (a sort past [rs] is relevant). *)
with eval_field_vals (Θ : gdeps) (Ξ : gstack) : list relevance -> list exp -> env -> list domain -> Prop :=
(** No field. *)
| eval_field_vals_nil :
  `( eval_field_vals Θ Ξ rs nil ρ nil )
(** A relevant field: its value, then the rest. *)
| eval_field_vals_relevant :
  `( List.hd relevant rs = relevant ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     eval_field_vals Θ Ξ (List.tl rs) Ms ρ ms ->
     eval_field_vals Θ Ξ rs (M :: Ms) ρ (m :: ms) )
(** A propositional field: the proof kept as it is, then the rest. *)
| eval_field_vals_proof :
  `( List.hd relevant rs = propositional ->
     eval_field_vals Θ Ξ (List.tl rs) Ms ρ ms ->
     eval_field_vals Θ Ξ rs (M :: Ms) ρ (⋆ᵈ⟨M, ρ⟩ :: ms) )
with eval_apps (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> domain -> Prop :=
(** No arguments. *)
| eval_apps_nil :
  `( $*| m & nil | Θ ⍮ Ξ ↘ m )
(** The first argument, then the rest. *)
| eval_apps_cons :
  `( $| m & n | Θ ⍮ Ξ ↘ m1 ->
     $*| m1 & args | Θ ⍮ Ξ ↘ r ->
     $*| m & n :: args | Θ ⍮ Ξ ↘ r )
where "'$*|' m '&' ns '|' Θ '⍮' Ξ '↘' r" := (eval_apps Θ Ξ m ns r)
with eval_modexp (Θ : gdeps) (Ξ : gstack) : modexp -> env -> dmod -> Prop :=
(** A module slot is read off the environment. *)
| eval_me_var :
  `( ⟦ me_var x ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ env_mod ρ x )
(** A unit is a global body module, with no argument yet.  Its submodules
    are selected from it ([eval_selm_global]). *)
| eval_me_unit :
  `( ⟦ me_unit fp ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global (q_abs fp nil) nil )
(** A literal unit is its closure. *)
| eval_me_lit :
  `( ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ me_lit (gu_mk Δ D) ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h )
(** A submodule is selected from the module's value. *)
| eval_me_mem :
  `( ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     h ·ₘ y Θ ⍮ Ξ ↘ r ->
     ⟦ me_mem H y ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An application adds the argument's value to the module's. *)
| eval_me_app :
  `( ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $ᵐ| h & n | Θ ⍮ Ξ ↘ r ->
     ⟦ me_app H N ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' H '⟧ᵐ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_modexp Θ Ξ H ρ r)
(** The closure of a unit's definition [D] lacking the parameters [Δ], over
    [ρ]: a body, or an alias still lacking a parameter, is its closure; an
    alias lacking none is its target's value.  So no value is a saturated
    alias. *)
with eval_close (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> dmod -> Prop :=
(** A body: its closure *)
| eval_close_body :
  `( ⟦ Δ ⊢ md_body sm Φ ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_body sm Φ) ρ )
(** An alias still lacking a parameter: its closure *)
| eval_close_alias :
  `( 0 < List.length Δ ->
     ⟦ Δ ⊢ md_alias E ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_alias E) ρ )
(** An alias lacking none: its target's value *)
| eval_close_alias0 :
  `( ⟦ E ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ nil ⊢ md_alias E ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h )
where "'⟦' Δ '⊢' D '⟧ᶜ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_close Θ Ξ Δ D ρ r)
(** Applying a module value to one more argument, which it must still lack. *)
with eval_appm (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> dmod -> Prop :=
(** A global module records the argument. *)
| eval_appm_global :
  `( $ᵐ| dm_global p args & n | Θ ⍮ Ξ ↘ dm_global p (args ++ n :: nil) )
(** A closure takes it as its outermost missing parameter, in its
    environment. *)
| eval_appm_local :
  `( ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_closure A ρ ↘ r ->
     $ᵐ| dm_local (Δ ++ ce_ass A :: nil) D ρ & n | Θ ⍮ Ξ ↘ r )
(** A submodule of an unsaturated module passes it to the module, then selects again. *)
| eval_appm_member :
  `( $ᵐ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₘ* ch Θ ⍮ Ξ ↘ r ->
     $ᵐ| dm_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$ᵐ|' h '&' n '|' Θ '⍮' Ξ '↘' r" := (eval_appm Θ Ξ h n r)
(** Applying a module value to arguments, outermost first. *)
with eval_appms (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> dmod -> Prop :=
(** No argument *)
| eval_appms_nil :
  `( $ᵐ*| h & nil | Θ ⍮ Ξ ↘ h )
(** The first argument, then the rest *)
| eval_appms_cons :
  `( $ᵐ| h & n | Θ ⍮ Ξ ↘ h1 ->
     $ᵐ*| h1 & ns | Θ ⍮ Ξ ↘ r ->
     $ᵐ*| h & n :: ns | Θ ⍮ Ξ ↘ r )
where "'$ᵐ*|' h '&' ns '|' Θ '⍮' Ξ '↘' r" := (eval_appms Θ Ξ h ns r)
(** Selecting a term member.  A member of a global module is stored closed,
    over the module's parameters: δ evaluates a transparent one's body in the
    empty environment, and an opaque one or an axiom is a neutral at its
    (closed) type.  Either is then applied to the module's arguments, once
    the module lacks none ([module_saturated]). *)
with eval_sel (Θ : gdeps) (Ξ : gstack) : dmod -> string -> domain -> Prop :=
(** A term part of a saturated global module, a transparent definition's
    body or a definition with a module part's term ([gc_term]): it, applied
    to the module's arguments. *)
| eval_sel_global :
  `( module_saturated Θ Ξ p args ->
     gc_term Θ Ξ (qname_app p (x :: nil)) = Some M ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ f ->
     $*| f & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
(** A relevant opaque definition or axiom of a saturated global module: a
    neutral, applied to the module's arguments. *)
| eval_sel_global_neut :
  `( module_saturated Θ Ξ p args ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv relevant A B) ->
     b = false \/ B = None ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a ->
     $*| ⇑ a (d_glob (qname_app p (x :: nil))) & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
(** A definition of a global module given exactly its parameters, tagged a
    proposition, transparent or not: a proof, kept as the selection of the
    member from the module, over the module's arguments
    ([global_proof_env]).  Neither its body nor its type is evaluated.
    Unlike a relevant member, it is not selected from a module given more
    arguments than it has parameters: a kept proof takes no argument, so
    there the member of the over-applied module would have a value its
    spine does not.  For example, for [module M (a : ℕ)] with a theorem
    [h], the ill-typed [(M 3) 4] evaluates to [dm_global M [3; 4]], but
    [a_mem ((M 3) 4) h] has no value: its spine reaches the proof at [3]
    and cannot apply it to [4].  So [h] is not selected from it either. *)
| eval_sel_global_proof :
  `( gc_loc Θ Ξ p = Some (T, Φ) ->
     List.length args = List.length T ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv propositional A B) ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ ⋆ᵈ⟨member_proof x, global_proof_env p T args⟩ )
(** The module of a member of a group of inductive types, as a term, in a
    saturated global module: the member's type former, applied to the
    module's arguments. *)
| eval_sel_global_ind :
  `( module_saturated Θ Ξ p args ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app p (x :: nil)) = Some (pq, k, D) ->
     $*| d_ind pq k nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
(** A member of a global module lacking a parameter is a member closure. *)
| eval_sel_global_unsat :
  `( gc_loc Θ Ξ p = Some (T, Φ) ->
     List.length args < List.length T ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ d_member (dm_global p args) (x :: nil) )
(** A member of a closure lacking a parameter is a member closure. *)
| eval_sel_unsat :
  `( 0 < List.length Δ ->
     dm_local Δ D ρ ·ₜ x Θ ⍮ Ξ ↘ d_member (dm_local Δ D ρ) (x :: nil) )
(** A term part of a saturated body ([entry_tm]: a definition's body or a
    definition with a module part's term): it, in the environment of the
    body before it, when the entry is relevant. *)
| eval_sel_body :
  `( gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     entry_relevance E = relevant ->
     ⟦ Φ' ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₜ x Θ ⍮ Ξ ↘ r )
(** A definition of a saturated body tagged a proposition: a proof, kept
    as the selection of the member from the body, its body not evaluated;
    the environment of the proof is the body's environment extended by the
    body's closure, so that readback binds the body as its unit over the
    entries it closes over. *)
| eval_sel_body_proof :
  `( gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     entry_relevance E = propositional ->
     dm_local nil (md_body sm Φ) ρ ·ₜ x Θ ⍮ Ξ ↘ ⋆ᵈ⟨member_proof x, ρ ↦ᵐ dm_local nil (md_body sm Φ) ρ ⦂ gu_mk nil (md_body sm Φ)⟩ )
(** A member of a submodule closure extends the chain. *)
| eval_sel_member :
  `( dm_member h ch ·ₜ x Θ ⍮ Ξ ↘ d_member h (ch ++ x :: nil) )
(** A record type of a saturated global module, stored or with its
    module's frame open, as a term: its type former, applied to the
    module's arguments. *)
| eval_sel_global_record :
  `( module_saturated Θ Ξ p args ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     record_lookup Θ Ξ (qname_app p (x :: nil)) = Some R ->
     $*| d_record (qname_app p (x :: nil)) nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
where "h '·ₜ' x Θ '⍮' Ξ '↘' r" := (eval_sel Θ Ξ h x r)
(** Selecting a submodule. *)
with eval_selm (Θ : gdeps) (Ξ : gstack) : dmod -> string -> dmod -> Prop :=
(** A body submodule, an open frame or the module of an inductive type in a
    global module is a global module, with the same arguments. *)
| eval_selm_global :
  `( gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ ->
     dm_global p args ·ₘ y Θ ⍮ Ξ ↘ dm_global (qname_app p (y :: nil)) args )
(** An alias submodule of a global module is the closure of the alias,
    stored closed over the module's parameters, given the module's
    arguments. *)
| eval_selm_global_alias :
  `( gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ nil ↘ h ->
     $ᵐ*| h & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₘ y Θ ⍮ Ξ ↘ r )
(** A submodule of a closure lacking a parameter is a submodule closure. *)
| eval_selm_unsat :
  `( 0 < List.length Δ ->
     dm_local Δ D ρ ·ₘ y Θ ⍮ Ξ ↘ dm_member (dm_local Δ D ρ) (y :: nil) )
(** A module part of a saturated body ([entry_unit]: a submodule, or a
    definition with a module part's): its unit's closure, in the
    environment of the body before it. *)
| eval_selm_body :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y E) ->
     entry_unit E = Some (gu_mk Δy Dy) ->
     ⟦ Φ' ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ Δy ⊢ Dy ⟧ᶜ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₘ y Θ ⍮ Ξ ↘ r )
(** A submodule of a submodule closure extends the chain. *)
| eval_selm_member :
  `( dm_member h ch ·ₘ y Θ ⍮ Ξ ↘ dm_member h (ch ++ y :: nil) )
where "h '·ₘ' y Θ '⍮' Ξ '↘' r" := (eval_selm Θ Ξ h y r)
(** Selecting along a chain: submodules, then a term member. *)
with eval_selc (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> domain -> Prop :=
(** The last selection is a term member. *)
| eval_selc_one :
  `( h ·ₜ x Θ ⍮ Ξ ↘ r ->
     h ·ₜ* (x :: nil) Θ ⍮ Ξ ↘ r )
(** The ones before it are submodules. *)
| eval_selc_cons :
  `( h ·ₘ y Θ ⍮ Ξ ↘ h1 ->
     h1 ·ₜ* ch Θ ⍮ Ξ ↘ r ->
     h ·ₜ* (y :: ch) Θ ⍮ Ξ ↘ r )
where "h '·ₜ*' ch Θ '⍮' Ξ '↘' r" := (eval_selc Θ Ξ h ch r)
with eval_selmc (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> dmod -> Prop :=
(** The empty chain is the module itself. *)
| eval_selmc_nil :
  `( h ·ₘ* nil Θ ⍮ Ξ ↘ h )
(** A submodule, then the rest of the chain. *)
| eval_selmc_cons :
  `( h ·ₘ y Θ ⍮ Ξ ↘ h1 ->
     h1 ·ₘ* ch Θ ⍮ Ξ ↘ r ->
     h ·ₘ* (y :: ch) Θ ⍮ Ξ ↘ r )
where "h '·ₘ*' ch Θ '⍮' Ξ '↘' r" := (eval_selmc Θ Ξ h ch r)
(** The environment the members of a body see after its entries [Φ]: each
    definition adds its value and each module its closure. *)
with eval_body_env (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
(** The empty body adds nothing. *)
| eval_body_env_nil :
  `( ⟦ gm_nil ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ )
(** A definition tagged relevant adds its value.  A body is read by the
    sorts its definitions are tagged with, as selection reads it
    ([eval_sel_body]): typing makes a definition's tag the sort of its
    type, a definition an open generates included: the core open phase
    gives it the type of the member it names ([items_gen]). *)
| eval_body_env_def :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ gm_ext Φ y (ge_def b pv relevant A (Some M)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ m ⦂ entry_type_closure A ρ1 )
(** A definition tagged a proposition, a proof, adds it kept as it is,
    unevaluated. *)
| eval_body_env_def_proof :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ gm_ext Φ y (ge_def b pv propositional A (Some M)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ ⋆ᵈ⟨M, ρ1⟩ ⦂ entry_type_closure A ρ1 )
(** A submodule adds its unit's closure, at the unit. *)
| eval_body_env_mod :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ Δy ⊢ Dy ⟧ᶜ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_mod pm (gu_mk Δy Dy)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵐ h ⦂ gu_mk Δy Dy )
(** A definition with a module part adds its term's value and its unit's
    closure, at the unit. *)
| eval_body_env_dm :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ Δy ⊢ Dy ⟧ᶜ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵈ m ⦂ entry_type_closure A ρ1 ‖ h ⦂ gu_mk Δy Dy )
where "'⟦' Φ '⟧ᵇ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" := (eval_body_env Θ Ξ ρ Φ ρ').

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_exps_mut_ind := Induction for eval_exps Sort Prop
with eval_apps_mut_ind := Induction for eval_apps Sort Prop
with eval_modexp_mut_ind := Induction for eval_modexp Sort Prop
with eval_close_mut_ind := Induction for eval_close Sort Prop
with eval_appm_mut_ind := Induction for eval_appm Sort Prop
with eval_appms_mut_ind := Induction for eval_appms Sort Prop
with eval_sel_mut_ind := Induction for eval_sel Sort Prop
with eval_selm_mut_ind := Induction for eval_selm Sort Prop
with eval_selc_mut_ind := Induction for eval_selc Sort Prop
with eval_selmc_mut_ind := Induction for eval_selmc Sort Prop
with eval_body_env_mut_ind := Induction for eval_body_env Sort Prop
with eval_elim_mut_ind := Induction for eval_elim Sort Prop
with eval_ihs_mut_ind := Induction for eval_ihs Sort Prop
with eval_ih_mut_ind := Induction for eval_ih Sort Prop
with eval_mref_mut_ind := Induction for eval_mref Sort Prop
with eval_shape_type_mut_ind := Induction for eval_shape_type Sort Prop
with eval_ihty_mut_ind := Induction for eval_ihty Sort Prop
with eval_proj_mut_ind := Induction for eval_proj Sort Prop
with eval_neutral_fields_mut_ind := Induction for eval_neutral_fields Sort Prop
with eval_projs_mut_ind := Induction for eval_projs Sort Prop
with eval_ihtys_mut_ind := Induction for eval_ihtys Sort Prop
with eval_field_vals_mut_ind := Induction for eval_field_vals Sort Prop
with eval_app_args_mut_ind := Induction for eval_app_args Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_app_mut_ind,
  eval_exps_mut_ind,
  eval_apps_mut_ind,
  eval_modexp_mut_ind,
  eval_close_mut_ind,
  eval_appm_mut_ind,
  eval_appms_mut_ind,
  eval_sel_mut_ind,
  eval_selm_mut_ind,
  eval_selc_mut_ind,
  eval_selmc_mut_ind,
  eval_body_env_mut_ind,
  eval_elim_mut_ind,
  eval_ihs_mut_ind,
  eval_ih_mut_ind,
  eval_mref_mut_ind,
  eval_shape_type_mut_ind,
  eval_ihty_mut_ind,
  eval_proj_mut_ind,
  eval_neutral_fields_mut_ind,
  eval_projs_mut_ind,
  eval_ihtys_mut_ind,
  eval_field_vals_mut_ind,
  eval_app_args_mut_ind.

#[export]
Hint Constructors eval_exp eval_proj eval_neutral_fields eval_projs eval_elim eval_ihs eval_ih eval_mref eval_shape_type eval_ihty eval_ihtys eval_app eval_exps eval_apps eval_modexp eval_close eval_appm eval_appms eval_sel eval_selm
  eval_selc eval_selmc eval_body_env eval_field_vals eval_app_args : mctt.

(** [eval_exp_var] with the value as a premise.  The value [ρ x] is a flexible
    application, so unifying against it directly can pick the wrong [ρ] and
    [x]. *)
Proposition eval_exp_var_eq : forall {Θ Ξ} x (ρ : env) m,
    ρ x = m ->
    ⟦ #x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m.
Proof. intros * <-; apply eval_exp_var. Qed.

(** * Evaluation of Substitutions

    Evaluation of a substitution is pointwise: at every variable [x], [ρσ x]
    is the entry [σ x] denotes in [ρ]: the entry of a variable, the value of a
    term, the value of a module expression, or the values of both.  Past its end [ρσ] reads
    [absent_entry], so a result exists only when, from some index on, every
    [σ x] denotes it, for example as a variable past the end of [ρ].

    Only the metatheory evaluates substitutions; NbE never does.  An
    entry that is a term is stored at [substituted_type]: the type of a
    term is not known to evaluation, and the entry's type must not depend
    on the result environment, so that evaluation of a substitution stays
    functional.  REVISIT (P4): a substitution's term entries are to carry
    their type on the source side; until then they are at no type. *)
Definition substituted_type : entry_type := entry_type_none.

(** The unit a module entry of a substitution's result is stored at, for
    the same reason: the placeholder, an alias of the module at the dummy
    path [q_abs nil nil], which names no module, as in [dm_default].  The unit
    declared by the target context would change under precomposition by a
    weakening ([eval_sub_wk_pre]), which reindexes the entries but not the
    units stored in them.  REVISIT: the readback of a kept proof in such an
    environment binds those entries at the placeholder unit. *)
Definition substituted_unit : gunit := gu_mk nil (md_alias (qname_mod (q_abs nil nil))).

(** The entry a variable of a substitution denotes: the entry of the
    environment, with the unit of a module part replaced by
    [substituted_unit], as for any module entry a substitution stores.
    The stored unit is written over the tail the entry had in the
    environment, which the result of the substitution does not have.  For
    example [q σ] from [Γ' ▹ₘ U[σ]] into [Γ ▹ₘ U] keeps the head of its
    argument, which stores [U[σ]], scoped by [Γ'] but not by [Γ].  Values,
    modules and term entries are unchanged ([env_var_restamp],
    [env_mod_restamp]). *)
Definition restamp_entry (e : dentry) : dentry :=
  match e with
  | de_mod h _ => de_mod h substituted_unit
  | de_dm n t h _ => de_dm n t h substituted_unit
  | e => e
  end.

(** An environment with every entry restamped. *)
Definition restamp_env (ρ : env) : env := List.map restamp_entry ρ.

Lemma restamp_entry_idem : forall e, restamp_entry (restamp_entry e) = restamp_entry e.
Proof. intros []; reflexivity. Qed.

Lemma env_entry_restamp : forall ρ x, env_entry (restamp_env ρ) x = restamp_entry (env_entry ρ x).
Proof.
  intros ρ x; revert ρ; induction x as [| x IH]; intros [| e ρ]; cbn; try reflexivity;
    [ exact (IH nil) | exact (IH ρ) ].
Qed.

Lemma env_var_restamp : forall ρ x, env_var (restamp_env ρ) x = env_var ρ x.
Proof. intros; unfold env_var; rewrite env_entry_restamp; destruct (env_entry ρ x); reflexivity. Qed.

Lemma env_mod_restamp : forall ρ x, env_mod (restamp_env ρ) x = env_mod ρ x.
Proof. intros; unfold env_mod; rewrite env_entry_restamp; destruct (env_entry ρ x); reflexivity. Qed.

Lemma env_type_restamp : forall ρ x, env_type (restamp_env ρ) x = env_type ρ x.
Proof. intros; unfold env_type; rewrite env_entry_restamp; destruct (env_entry ρ x); reflexivity. Qed.

Lemma restamp_env_drop : forall ρ, restamp_env ρ↯ = (restamp_env ρ)↯.
Proof. intros []; reflexivity. Qed.

Definition eval_sentry (Θ : gdeps) (Ξ : gstack) (e : sentry) (ρ : env) (d : dentry) : Prop :=
  match e with
  | se_var y => d = restamp_entry (env_entry ρ y)
  | se_exp M => exists m, d = de_term m substituted_type /\ ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m
  | se_mod H => exists h, d = de_mod h substituted_unit /\ ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h
  | se_dm N H => exists n h, d = de_dm n substituted_type h substituted_unit /\ ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n /\ ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h
  end.

Notation "'⟦' e '⟧ᵉ' Θ '⍮' Ξ '⍮' ρ '↘' d" := (eval_sentry Θ Ξ e ρ d) : mctt_scope.

(** The entry a substitution entry [e] denotes in [ρ] at a proposition:
    the proof kept as it is, or the entry of a variable. *)
Definition eval_sentry_proof (e : sentry) (ρ : env) (d : dentry) : Prop :=
  match e with
  | se_var y => d = restamp_entry (env_entry ρ y)
  | se_exp M => d = de_term ⋆ᵈ⟨M, ρ⟩ substituted_type
  | _ => False
  end.

(** The type of the entry [x] of a context, a term's: of an assumption, a
    definition or a definition with a module part; a module slot has
    none. *)
Definition ctx_entry_type (Δ : ctx) (x : nat) : option typ :=
  match List.nth_error Δ x with
  | Some (ce_ass A) | Some (ce_def A _) | Some (ce_dm A _ _) => Some A
  | _ => None
  end.
(** The entry [x] of [Δ] is a proposition in the environment [ρσ] of [Δ]:
    its type, over the entries after it, evaluates in the tail of [ρσ]
    after [x] to a propositional value.  The tail is taken up to agreement
    on the entries of [Δ] after [x] ([env_agree_upto]), the ones the type
    is over: the notion depends neither on how an environment is
    represented (a closure captures the environment it is built in, so
    evaluation itself does not respect [env_eq]) nor on the entries past
    [Δ], of which a substitution into [Δ] says nothing ([eval_sub]). *)
#[warnings="-cannot-define-projection"]
Record entry_propositional (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (ρσ : env) (x : nat) : Prop := mk_entry_propositional
  { (** The entry's type *)
    entry_propositional_type : typ
    (** It is the type of the entry [x] *)
  ; entry_propositional_lookup : ctx_entry_type Δ x = Some entry_propositional_type
    (** An environment agreeing with the tail of [ρσ] after [x] on the
        entries of [Δ] after [x] *)
  ; entry_propositional_env : env
  ; entry_propositional_env_eq : env_agree_upto (List.length (List.skipn (S x) Δ)) entry_propositional_env (List.skipn (S x) ρσ)
    (** The type's value in it *)
  ; entry_propositional_value : domain
  ; entry_propositional_eval : ⟦ entry_propositional_type ⟧ Θ ⍮ Ξ ⍮ entry_propositional_env ↘ entry_propositional_value
    (** The value is a proposition *)
  ; entry_propositional_prop : domain_relevance entry_propositional_value = propositional }.

(** Evaluation of a substitution is directed by its target context [Δ]:
    at an entry of [Δ] that is a proposition, the substitution's entry, a
    proof, is kept as it is, not evaluated; at every other entry of [Δ],
    [ρσ] holds what [σ x] denotes in [ρ].  Past the entries of [Δ] nothing
    is said: a substitution into [Δ] says nothing of the indices past it.
    The two cases are stated as implications, so that building an
    evaluation needs no case analysis on whether an entry is a
    proposition. *)
Definition eval_sub (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (σ : sub) (ρ ρσ : env) : Prop :=
  forall x, x < List.length Δ ->
    (entry_propositional Θ Ξ Δ ρσ x -> eval_sentry_proof (σ x) ρ (env_entry ρσ x))
    /\ (~ entry_propositional Θ Ξ Δ ρσ x -> ⟦ σ x ⟧ᵉ Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρσ x).
Arguments eval_sub : simpl never.

Notation "'⟦' σ ':' Δ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" := (eval_sub Θ Ξ Δ σ ρ ρσ) : mctt_scope.

(** The tail of an environment past [n] entries reads its entries from
    [n] on. *)
Lemma env_entry_skipn : forall n ρ y, env_entry (List.skipn n ρ) y = env_entry ρ (n + y).
Proof.
  intros; rewrite !env_entry_nth.
  revert ρ; induction n as [| n IH]; intros [| d ρ]; cbn [List.skipn Nat.add]; try reflexivity.
  - rewrite !List.nth_overflow; cbn; [ reflexivity | lia | lia ].
  - apply IH.
Qed.

(** Pointwise-equal environments have pointwise-equal tails. *)
Lemma env_eq_skipn : forall n ρ ρ', env_eq ρ ρ' -> env_eq (List.skipn n ρ) (List.skipn n ρ').
Proof. intros * H y; rewrite !env_entry_skipn; apply H. Qed.

(** Being a proposition is read up to agreement on the entries of the
    context. *)
Lemma entry_propositional_resp_agree : forall {Θ Ξ} Δ ρσ ρσ' x,
    env_agree_upto (List.length Δ) ρσ ρσ' -> entry_propositional Θ Ξ Δ ρσ x -> entry_propositional Θ Ξ Δ ρσ' x.
Proof.
  intros * Hρ [T HT E HE v Ev Hv]; econstructor; [ exact HT | | exact Ev | exact Hv ].
  intros y Hy; rewrite (HE y Hy), !env_entry_skipn; apply Hρ; rewrite List.length_skipn in Hy; lia.
Qed.

(** In particular up to pointwise equality. *)
Corollary entry_propositional_resp_env_eq : forall {Θ Ξ} Δ ρσ ρσ' x,
    env_eq ρσ ρσ' -> entry_propositional Θ Ξ Δ ρσ x -> entry_propositional Θ Ξ Δ ρσ' x.
Proof. intros * Hρ; apply entry_propositional_resp_agree, env_eq_agree_upto, Hρ. Qed.

(** The entries after the first of [e :: Δ] are those of [Δ], in the tail
    of the environment. *)
Lemma entry_propositional_succ : forall {Θ Ξ} e Δ ρσ x,
    entry_propositional Θ Ξ (e :: Δ) ρσ (S x) <-> entry_propositional Θ Ξ Δ ρσ↯ x.
Proof.
  intros; split; intros [T HT E HE v Ev Hv]; econstructor; try eassumption;
    intros y Hy; rewrite (HE y Hy), !env_entry_skipn; cbn [drop_env];
    rewrite ?env_entry_drop; reflexivity.
Qed.

(** The same, for an environment extended by one entry. *)
Lemma entry_propositional_extend : forall {Θ Ξ} e Δ d ρσ x,
    entry_propositional Θ Ξ (e :: Δ) (d :: ρσ) (S x) <-> entry_propositional Θ Ξ Δ ρσ x.
Proof. intros; split; intros []; econstructor; eassumption. Qed.

Lemma entry_propositional_extend_inv : forall {Θ Ξ} e Δ d ρσ x,
    entry_propositional Θ Ξ (e :: Δ) (d :: ρσ) (S x) -> entry_propositional Θ Ξ Δ ρσ x.
Proof. intros *; apply entry_propositional_extend. Qed.

Lemma entry_propositional_extend_intro : forall {Θ Ξ} e Δ d ρσ x,
    entry_propositional Θ Ξ Δ ρσ x -> entry_propositional Θ Ξ (e :: Δ) (d :: ρσ) (S x).
Proof. intros *; apply entry_propositional_extend. Qed.

(** A module slot is never a proposition. *)
Lemma entry_propositional_mod : forall {Θ Ξ} Δ ρσ x,
    ctx_entry_type Δ x = None -> ~ entry_propositional Θ Ξ Δ ρσ x.
Proof. intros * Hx []; congruence. Qed.

(** A propositional entry is an entry. *)
Lemma entry_propositional_lt : forall {Θ Ξ} Δ ρσ x, entry_propositional Θ Ξ Δ ρσ x -> x < List.length Δ.
Proof.
  intros * [T HT _ _ _ _ _]; unfold ctx_entry_type in HT.
  destruct (List.nth_error Δ x) eqn:E; [ apply List.nth_error_Some; congruence | discriminate ].
Qed.

(** The two cases of an evaluation of a substitution at an index. *)
Lemma eval_sub_at_prop : forall {Θ Ξ} Δ σ ρ ρσ x,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ -> entry_propositional Θ Ξ Δ ρσ x -> eval_sentry_proof (σ x) ρ (env_entry ρσ x).
Proof. intros * H Hp; exact (proj1 (H x (entry_propositional_lt _ _ _ Hp)) Hp). Qed.

Proposition eval_sub_index : forall {Θ Ξ} Δ σ (ρ ρσ : env),
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    forall x, x < List.length Δ -> ~ entry_propositional Θ Ξ Δ ρσ x -> ⟦ σ x ⟧ᵉ Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρσ x.
Proof. intros * H x Hx; apply (H x Hx). Qed.

(** The identity evaluates to the environment itself, restamped: its
    module entries store [substituted_unit] ([restamp_entry]). *)
Lemma eval_sub_id : forall {Θ Ξ} Δ ρ, ⟦ Id : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_env ρ.
Proof. intros * x _; split; intros _; cbn; rewrite env_entry_restamp; reflexivity. Qed.

(** The shift evaluates to the tail, restamped. *)
Lemma eval_sub_shift : forall {Θ Ξ} Δ ρ, ⟦ Wk : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_env ρ↯.
Proof. intros * x _; split; intros _; cbn; rewrite env_entry_restamp; reflexivity. Qed.

(** The head entry of [e :: Δ] is a proposition over the tail [ρσ] of
    [Δ]: its type evaluates there, up to agreement on the entries of [Δ], to
    a proposition.  It does not depend on the head of the environment. *)
Definition head_propositional (Θ : gdeps) (Ξ : gstack) (e : centry) (Δ : ctx) (ρσ : env) : Prop :=
  entry_propositional Θ Ξ (e :: Δ) (absent_entry :: ρσ) 0.

Lemma entry_propositional_head : forall {Θ Ξ} e Δ d ρσ,
    entry_propositional Θ Ξ (e :: Δ) (d :: ρσ) 0 <-> head_propositional Θ Ξ e Δ ρσ.
Proof. intros; split; intros []; econstructor; eassumption. Qed.

(** An extension by a term at an entry that is not a proposition: the
    term's value. *)
Lemma eval_sub_extend : forall {Θ Ξ} e Δ σ ρ ρσ M m,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ~ head_propositional Θ Ξ e Δ ρσ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ σ,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m ⦂ substituted_type.
Proof.
  intros * H Hn HM [| x] Hx.
  - split; [ intros Hp; apply entry_propositional_head in Hp; contradiction
           | intros _; exists m; split; [ reflexivity | assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hp; apply (H x ltac:(lia)); intros Hp'; exact (Hp (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An extension at an entry that is a proposition: the term kept as it
    is, unevaluated. *)
Lemma eval_sub_extend_proof : forall {Θ Ξ} e Δ σ ρ ρσ M,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    head_propositional Θ Ξ e Δ ρσ ->
    ⟦ σ,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ ⋆ᵈ⟨M, ρ⟩ ⦂ substituted_type.
Proof.
  intros * H Hp [| x] Hx.
  - split; [ reflexivity | intros Hn; exfalso; exact (Hn (proj2 (entry_propositional_head _ _ _ _) Hp)) ].
  - cbn [List.length] in Hx.
    split; [ intros Hp'; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp')
           | intros Hn; apply (H x ltac:(lia)); intros Hp'; exact (Hn (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An extension by a module expression at a module slot. *)
Lemma eval_sub_extend_mod : forall {Θ Ξ} U Δ σ ρ ρσ H h,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ σ ,,ₘ H : ce_mod U :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ᵐ h ⦂ substituted_unit.
Proof.
  intros * Hσ HH [| x] Hx.
  - split; [ intros []; discriminate | intros _; exists h; split; [ reflexivity | assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (Hσ x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hn; apply (Hσ x ltac:(lia)); intros Hp'; exact (Hn (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An extension by a term and a module expression, at an entry that is
    not a proposition. *)
Lemma eval_sub_extend_dm : forall {Θ Ξ} e Δ σ ρ ρσ N H n h,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ~ head_propositional Θ Ξ e Δ ρσ ->
    ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ σ ,,ᵈ N ‖ H : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ᵈ n ⦂ substituted_type ‖ h ⦂ substituted_unit.
Proof.
  intros * Hσ Hn HN HH [| x] Hx.
  - split; [ intros Hp; apply entry_propositional_head in Hp; contradiction
           | intros _; exists n, h; split; [ reflexivity | split; assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (Hσ x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hm; apply (Hσ x ltac:(lia)); intros Hp'; exact (Hm (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

Corollary eval_sub_single_dm : forall {Θ Ξ} e Δ ρ N H n h,
    ~ head_propositional Θ Ξ e Δ (restamp_env ρ) ->
    ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ Id ,,ᵈ N ‖ H : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_env ρ ↦ᵈ n ⦂ substituted_type ‖ h ⦂ substituted_unit.
Proof.
  intros; apply eval_sub_extend_dm; [ apply eval_sub_id | assumption .. ].
Qed.

Corollary eval_sub_single : forall {Θ Ξ} e Δ ρ M m,
    ~ head_propositional Θ Ξ e Δ (restamp_env ρ) ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ Id,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_env ρ ↦ m ⦂ substituted_type.
Proof.
  intros; apply eval_sub_extend; [ apply eval_sub_id | assumption .. ].
Qed.

Corollary eval_sub_single_proof : forall {Θ Ξ} e Δ ρ M,
    head_propositional Θ Ξ e Δ (restamp_env ρ) ->
    ⟦ Id,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_env ρ ↦ ⋆ᵈ⟨M, ρ⟩ ⦂ substituted_type.
Proof.
  intros; apply eval_sub_extend_proof; [ apply eval_sub_id | assumption ].
Qed.

Corollary eval_sub_single_mod : forall {Θ Ξ} U Δ ρ H h,
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ Id ,,ₘ H : ce_mod U :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_env ρ ↦ᵐ h ⦂ substituted_unit.
Proof.
  intros; apply eval_sub_extend_mod; [ apply eval_sub_id | assumption ].
Qed.

(** The variables of a term and of a module expression read the entry their
    substitution denotes, at the right sort; at the wrong one both sides read
    the default.  A propositional entry holds a proof, which no relevant term
    reads. *)
Lemma eval_sub_var : forall {Θ Ξ} Δ σ ρ ρσ x,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    x < List.length Δ ->
    ~ entry_propositional Θ Ξ Δ ρσ x ->
    ⟦ #x[σ] ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρσ x.
Proof.
  intros * Hσ Hx Hnp; specialize (proj2 (Hσ x Hx) Hnp) as Hσx; clear Hσ Hnp; rename Hσx into Hσ; cbn; unfold env_var.
  destruct (σ x) as [y | M | H | N H]; cbn in Hσ |- *.
  - fold (env_var ρσ x).
    replace (env_var ρσ x) with (env_var ρ y) by (unfold env_var; rewrite Hσ; destruct (env_entry ρ y); reflexivity).
    apply eval_exp_var.
  - destruct Hσ as (m & -> & Hm); exact Hm.
  - destruct Hσ as (h & -> & _); constructor.
  - destruct Hσ as (n & h & -> & Hn & _); exact Hn.
Qed.

Lemma eval_sub_mvar : forall {Θ Ξ} Δ σ ρ ρσ x,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    x < List.length Δ ->
    ~ entry_propositional Θ Ξ Δ ρσ x ->
    ⟦ (me_var x)[σ]ᵐ ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ env_mod ρσ x.
Proof.
  intros * Hσ Hx Hnp; specialize (proj2 (Hσ x Hx) Hnp) as Hσx; clear Hσ Hnp; rename Hσx into Hσ; cbn; unfold env_mod.
  destruct (σ x) as [y | M | H | N H]; cbn in Hσ |- *.
  - fold (env_mod ρσ x).
    replace (env_mod ρσ x) with (env_mod ρ y) by (unfold env_mod; rewrite Hσ; destruct (env_entry ρ y); reflexivity).
    apply eval_me_var.
  - destruct Hσ as (m & -> & _); apply eval_me_unit.
  - destruct Hσ as (h & -> & Hh); exact Hh.
  - destruct Hσ as (n & h & -> & _ & Hh); exact Hh.
Qed.

(** The substitution and the result environment may be replaced by
    pointwise-equal ones.  The input environment may not, since a closure
    captures it. *)
#[export]
Instance eval_sub_Proper : forall {Θ Ξ} Δ, Proper (sb_eq ==> eq ==> env_eq ==> iff) (eval_sub Θ Ξ Δ).
Proof.
  intros Θ Ξ Δ σ σ' Hσ ρ ρ0 <- ρσ ρσ' Hρσ.
  assert (Hρσ' : env_eq ρσ' ρσ) by (intros y; symmetry; apply Hρσ).
  split; intros H x Hx; (split; [ intros Hp | intros Hn ]).
  - rewrite <- (Hσ x), <- (Hρσ x); apply (proj1 (H x Hx)); eapply entry_propositional_resp_env_eq; eassumption.
  - rewrite <- (Hσ x), <- (Hρσ x); apply (proj2 (H x Hx)); intros Hp; apply Hn; eapply entry_propositional_resp_env_eq; eassumption.
  - rewrite (Hσ x), (Hρσ x); apply (proj1 (H x Hx)); eapply entry_propositional_resp_env_eq; eassumption.
  - rewrite (Hσ x), (Hρσ x); apply (proj2 (H x Hx)); intros Hp; apply Hn; eapply entry_propositional_resp_env_eq; eassumption.
Qed.

(** ** The Substitutions that Compute

    Evaluation of the substitutions that occur in practice:

    - the image under [ι] of an order-preserving weakening, for which
      [⟪φ⟫ ρ] is [ρ ∘ φ] at every index;
    - weakened extensions and lifts;
    - precomposition by a weakening. *)
(** A substitution of variables evaluates to the environment its
    variables read, restamped. *)
Lemma eval_sub_of_vars : forall {Θ Ξ} Δ σ ρ ρσ,
    (forall x, exists y, σ x = se_var y /\ env_entry ρσ x = restamp_entry (env_entry ρ y)) ->
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ.
Proof.
  intros * Hv x _; destruct (Hv x) as (y & Hσ & Hy); rewrite Hσ; cbn; split; intros _; exact Hy.
Qed.

Lemma eval_sub_of_wk : forall {Θ Ξ} Δ φ ρ `{Hφ : WkMono φ},
    ⟦ ι φ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_env (⟪φ⟫ ρ).
Proof.
  intros Θ Ξ Δ φ ρ Hφ; apply eval_sub_of_vars.
  intros x; exists (φ x); split; [ reflexivity | rewrite env_entry_restamp, (eval_wk_entry _ _ Hφ x); reflexivity ].
Qed.

(** A weakened extension. *)
Lemma eval_sub_wk_extend : forall {Θ Ξ} e Δ σ M φ ρ ρσ m,
    ⟦ sb_wk σ φ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ~ head_propositional Θ Ξ e Δ ρσ ->
    ⟦ M[φ]ʷ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ sb_wk (σ,,M) φ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m ⦂ substituted_type.
Proof.
  intros * H Hn HM [| x] Hx.
  - split; [ intros Hp; apply entry_propositional_head in Hp; contradiction
           | intros _; exists m; split; [ reflexivity | assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hm; apply (H x ltac:(lia)); intros Hp'; exact (Hm (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** A lifted substitution, plain and weakened.  [q σ] extends [σ[↑]] by the
    variable [0], so its head is the entry already in [ρ], restamped. *)
Lemma eval_sub_q : forall {Θ Ξ} e Δ σ ρ ρσ,
    ⟦ sb_wk σ ↑ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ q σ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_entry (env_entry ρ 0) :: ρσ.
Proof.
  intros * H [| x] Hx.
  - split; intros _; reflexivity.
  - cbn [List.length] in Hx; split.
    + intros Hp'; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp').
    + intros Hn; exact (proj2 (H x ltac:(lia)) (fun Hp' => Hn (entry_propositional_extend_intro _ _ _ _ _ Hp'))).
Qed.

Lemma eval_sub_wk_q : forall {Θ Ξ} e Δ σ φ ρ ρσ,
    ⟦ sb_wk (sb_wk σ ↑) φ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ sb_wk (q σ) φ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ restamp_entry (env_entry ρ (φ 0)) :: ρσ.
Proof.
  intros * H [| x] Hx.
  - split; intros _; cbn [sb_wk]; rewrite sb_q_zero; reflexivity.
  - cbn [List.length] in Hx; split.
    + intros Hp'; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp').
    + intros Hn; exact (proj2 (H x ltac:(lia)) (fun Hp' => Hn (entry_propositional_extend_intro _ _ _ _ _ Hp'))).
Qed.

(** Precomposition by a weakening reindexes the environment [σ] evaluates
    to, when the weakening takes the propositional entries of its target
    exactly to those of [σ]'s. *)
Lemma eval_sub_wk_pre : forall {Θ Ξ} Δ Δ' φ σ ρ ρσ `{Hφ : WkMono φ},
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    (forall x, x < List.length Δ' -> φ x < List.length Δ) ->
    (forall x, entry_propositional Θ Ξ Δ' (⟪φ⟫ ρσ) x <-> entry_propositional Θ Ξ Δ ρσ (φ x)) ->
    ⟦ (ι φ) ⨟ σ : Δ' ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ⟪φ⟫ ρσ.
Proof.
  intros Θ Ξ Δ Δ' φ σ ρ ρσ Hφ H Hl Hiff x Hx; rewrite (eval_wk_entry _ _ Hφ x); split.
  - intros Hp; apply (H (φ x) (Hl _ Hx)), Hiff, Hp.
  - intros Hn; apply (H (φ x) (Hl _ Hx)); intros Hp; apply Hn, Hiff, Hp.
Qed.

(** The tail of an evaluated substitution is that of its result. *)
Corollary eval_sub_shift_pre : forall {Θ Ξ} e Δ σ ρ ρσ,
    ⟦ σ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ Wk ⨟ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ↯.
Proof.
  intros * H x Hx; rewrite env_entry_drop; split.
  - intros Hp; apply (H (S x) ltac:(cbn; lia)); exact (proj2 (entry_propositional_succ _ _ _ _) Hp).
  - intros Hn; apply (H (S x) ltac:(cbn; lia)); intros Hp; exact (Hn (proj1 (entry_propositional_succ _ _ _ _) Hp)).
Qed.

#[export]
Hint Resolve eval_sub_id eval_sub_shift eval_sub_extend eval_sub_extend_proof eval_sub_extend_mod eval_sub_single
             eval_sub_single_proof eval_sub_single_mod eval_sub_wk_extend eval_sub_q eval_sub_wk_q eval_sub_shift_pre : mctt.

(** From here on an evaluation of a substitution is used through the
    lemmas above only.  Its definition is a pointwise conjunction, which
    [split] and [constructor] would otherwise take apart in every goal of
    the form [⟦ σ : Δ ⟧s ρ ↘ ρσ /\ …]: [repeat split] introduces the index
    and splits the two cases of an entry, leaving goals no assumption
    closes.  A later file that needs the definition makes it
    [Transparent eval_sub] locally. *)
#[global] Opaque eval_sub.
