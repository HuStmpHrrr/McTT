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

    No proof is ever evaluated: a term of a propositional type is never
    reached by evaluation, which puts the proof [⋆ᵈ] in its place.  The
    places where a proof may stand inside a relevant term read the sort of
    what stands there off values or declarations, never off types: the
    argument of an application ([arg_relevance]), a field of a record
    value (its declaration's [record_field_relevance]), a local definition
    and an entry of a module body (their types), and a substitution's entry
    (its target context's type, [eval_sub]). *)

(** The value [v] at the type [a]: [⋆ᵈ] when [a] is a proposition. *)
Definition relevant_value (a v : domain) : domain :=
  match domain_relevance a with propositional => ⋆ᵈ | relevant => v end.

(** At a relevant type, the value itself. *)
Lemma relevant_value_relevant : forall a v, domain_relevance a = relevant -> relevant_value a v = v.
Proof. intros * H; unfold relevant_value; rewrite H; reflexivity. Qed.

(** At a proposition, the proof. *)
Lemma relevant_value_propositional : forall a v, domain_relevance a = propositional -> relevant_value a v = ⋆ᵈ.
Proof. intros * H; unfold relevant_value; rewrite H; reflexivity. Qed.

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

    A local open declares, for each item, a definition or an alias, by the
    kind of the member it names ([items_gen]).  Evaluation must tell them
    apart without a type: the kind of a member is read off the module value
    and the syntax of the units it closes over.  A body is read through the
    entries it makes ([kinds_env]), as evaluation would but with a placeholder
    for every definition, so that no term is evaluated: a kind does not
    depend on the values of terms, nor on a module's arguments, which are
    terms ([kinds_placeholders]).  The relations mirror [member_type] with the types left
    out, and read a closure or a submodule closure as selection on module
    values does ([eval_selm]). *)

(** The closure of a unit over [ρ], as kinds read it: a saturated alias is
    left as a closure, which kinds read through. *)
Definition dm_clo (U : gunit) (ρ : env) : dmod :=
  match U with gu_mk Δ D => dm_local Δ D ρ end.

(** [n] placeholders for parameters, terms, over [ρ]. *)
Definition kinds_placeholders (n : nat) (ρ : env) : env := List.repeat (de_term d_placeholder) n ++ ρ.

(** The entry a body's entry adds over [ρ], as kinds read it: a module, its
    closure; a definition with a module part, a placeholder and the
    closure of its unit; any other, a placeholder, as in [body_ctx]. *)
Definition kinds_body_entry (ρ : env) (E : gentry) : dentry :=
  match E with
  | ge_mod _ U => de_mod (dm_clo U ρ)
  | ge_def_mod _ _ _ U => de_dm d_placeholder (dm_clo U ρ)
  | _ => de_term d_placeholder
  end.

(** The entries generated items add over [ρ], as kinds read them, the
    [k]-th under the [k] before it: an alias, the closure of its unit; a
    definition with a module part, a placeholder and the closure of its
    module part's unit; a definition, a placeholder. *)
Definition kinds_generated_entry (ρ : env) (k : nat) (g : generated_item) : dentry :=
  match g with
  | generated_item_alias _ _ E => de_mod (dm_local nil (md_alias (modexp_wk E (wk_shiftn k))) ρ)
  | generated_item_def_mod _ _ _ _ E => de_dm d_placeholder (dm_local nil (md_alias (modexp_wk E (wk_shiftn k))) ρ)
  | _ => de_term d_placeholder
  end.

Fixpoint kinds_items_gen_env (ρ : env) (k : nat) (gs : list generated_item) : env :=
  match gs with
  | nil => ρ
  | g :: gs' => kinds_items_gen_env (kinds_generated_entry ρ k g :: ρ) (S k) gs'
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
    kinds_env Θ Ξ (kinds_placeholders (List.length Δ) ρ) Φ' ρ1 ->
    gunit_member_kind Θ Ξ ρ1 Uy ch k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (y :: ch) k
(** A definition with a module part is one ([dm_of] its module part's
    kind), and a chain through it is read in its module part, as at the
    global level. *)
(** A definition with a module part of the body, at the end of the chain:
    [dm_of] the kind of its module part *)
| gunit_member_kind_dm_here : forall ρ Δ sm Φ Φ' y pv A M Uy ρ1 k,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
    kinds_env Θ Ξ (kinds_placeholders (List.length Δ) ρ) Φ' ρ1 ->
    gunit_member_kind Θ Ξ ρ1 Uy nil k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (y :: nil) (dm_of k)
(** A definition with a module part of the body, the chain going on: the
    rest of the chain read in its module part, in the environment of the
    entries before it *)
| gunit_member_kind_dm_step : forall ρ Δ sm Φ Φ' y pv A M Uy ρ1 ch k,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
    ch <> nil ->
    kinds_env Θ Ξ (kinds_placeholders (List.length Δ) ρ) Φ' ρ1 ->
    gunit_member_kind Θ Ξ ρ1 Uy ch k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (y :: ch) k
(** A name a local open declares, by the kind of the member it names in the
    open's target, as the open generates it ([kinds_items_gen]): a definition of a term
    member, an alias of a module member or of the target itself, and a
    definition with a module part of a member with both parts. *)
(** The item names a term member of the target: a term of its sort *)
| gunit_member_kind_item_def : forall ρ Δ sm Φ Φ0 H its1 n d pv ρ0 x r,
    gm_item_upto Φ x = Some (Φ0, H, its1, (Some n, d, pv)) ->
    kinds_env Θ Ξ (kinds_placeholders (List.length Δ) ρ) Φ0 ρ0 ->
    modexp_member_kind Θ Ξ ρ0 H (n :: nil) (member_kind_term r) ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: nil) (member_kind_term r)
(** The item names a module member of the target: the chain is read in
    that member *)
| gunit_member_kind_item_mod : forall ρ Δ sm Φ Φ0 H its1 n d pv ρ0 x ch k,
    gm_item_upto Φ x = Some (Φ0, H, its1, (Some n, d, pv)) ->
    kinds_env Θ Ξ (kinds_placeholders (List.length Δ) ρ) Φ0 ρ0 ->
    modexp_member_kind Θ Ξ ρ0 H (n :: nil) member_kind_mod ->
    modexp_member_kind Θ Ξ ρ0 H (n :: ch) k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: ch) k
(** The item names a member of the target with a term part and a module
    part: the chain is read in that member, so at the empty chain it is a
    definition with a module part *)
| gunit_member_kind_item_dm : forall ρ Δ sm Φ Φ0 H its1 n d pv ρ0 x ch k,
    gm_item_upto Φ x = Some (Φ0, H, its1, (Some n, d, pv)) ->
    kinds_env Θ Ξ (kinds_placeholders (List.length Δ) ρ) Φ0 ρ0 ->
    modexp_member_kind Θ Ξ ρ0 H (n :: nil) member_kind_dm ->
    modexp_member_kind Θ Ξ ρ0 H (n :: ch) k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: ch) k
(** The item names the target itself: the chain is read in the target *)
| gunit_member_kind_item_self : forall ρ Δ sm Φ Φ0 H its1 d pv ρ0 x ch k,
    gm_item_upto Φ x = Some (Φ0, H, its1, (None, d, pv)) ->
    kinds_env Θ Ξ (kinds_placeholders (List.length Δ) ρ) Φ0 ρ0 ->
    modexp_member_kind Θ Ξ ρ0 H ch k ->
    gunit_member_kind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: ch) k
(** An alias unit: the chain is read in its target *)
| gunit_member_kind_alias : forall ρ Δ E ch k,
    modexp_member_kind Θ Ξ (kinds_placeholders (List.length Δ) ρ) E ch k ->
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
(** The environment a body makes, as kinds read it: an entry each body
    entry adds ([kinds_body_entry]), and the entries an open generates. *)
with kinds_env (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
(** The empty body adds nothing *)
| kinds_env_nil : forall ρ, kinds_env Θ Ξ ρ gm_nil ρ
(** An entry adds its [kinds_body_entry] *)
| kinds_env_ext : forall ρ Φ ρ1 y E,
    kinds_env Θ Ξ ρ Φ ρ1 ->
    kinds_env Θ Ξ ρ (gm_ext Φ y E) (kinds_body_entry ρ1 E :: ρ1)
(** An open adds the entries its items generate *)
| kinds_env_open : forall ρ Φ ρ1 H its gs,
    kinds_env Θ Ξ ρ Φ ρ1 ->
    kinds_items_gen Θ Ξ ρ1 H its gs ->
    kinds_env Θ Ξ ρ (gm_open Φ H its) (kinds_items_gen_env ρ1 0 gs)
(** A body read through the entries its local opens generate, as kinds read
    them: [body_xp] with the types left out.  Each open's items are read in
    the environment of the expanded body before it. *)
with kinds_body_xp (Θ : gdeps) (Ξ : gstack) : env -> gmod -> gmod -> Prop :=
(** The empty body is its own expansion *)
| kinds_body_xp_nil : forall ρ, kinds_body_xp Θ Ξ ρ gm_nil gm_nil
(** An entry stays as it is *)
| kinds_body_xp_ext : forall ρ Φ Φx x E,
    kinds_body_xp Θ Ξ ρ Φ Φx ->
    kinds_body_xp Θ Ξ ρ (gm_ext Φ x E) (gm_ext Φx x E)
(** An open is replaced by the entries its items generate *)
| kinds_body_xp_open : forall ρ Φ Φx ρ1 H its gs,
    kinds_body_xp Θ Ξ ρ Φ Φx ->
    kinds_env Θ Ξ ρ Φx ρ1 ->
    kinds_items_gen Θ Ξ ρ1 H its gs ->
    kinds_body_xp Θ Ξ ρ (gm_open Φ H its) (gens_append Φx 0 gs)
(** What the items of an open of [H] generate, by the kinds of the members
    they name, in [ρ]; a generated definition carries no type: its type
    is the placeholder, and its tag the sort of the member it names. *)
with kinds_items_gen (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list import_item -> list generated_item -> Prop :=
(** No items generate nothing *)
| kinds_items_gen_nil : forall ρ H, kinds_items_gen Θ Ξ ρ H nil nil
(** An item naming the target itself: an alias of the target *)
| kinds_items_gen_self : forall ρ H d pv its gs,
    kinds_items_gen Θ Ξ ρ H its gs ->
    kinds_items_gen Θ Ξ ρ H ((None, d, pv) :: its) (generated_item_alias d pv H :: gs)
(** An item naming a term member: a definition of the member, of its
    sort.  Kinds do not read types, so its type is a placeholder; a body
    is read by the sorts its definitions are tagged with
    ([eval_body_env]). *)
| kinds_items_gen_def : forall ρ H n d pv r its gs,
    modexp_member_kind Θ Ξ ρ H (n :: nil) (member_kind_term r) ->
    kinds_items_gen Θ Ξ ρ H its gs ->
    kinds_items_gen Θ Ξ ρ H ((Some n, d, pv) :: its) (generated_item_def d pv r a_placeholder_type (a_mem H n) :: gs)
(** An item naming a module member: an alias of the member *)
| kinds_items_gen_mod : forall ρ H n d pv its gs,
    modexp_member_kind Θ Ξ ρ H (n :: nil) member_kind_mod ->
    kinds_items_gen Θ Ξ ρ H its gs ->
    kinds_items_gen Θ Ξ ρ H ((Some n, d, pv) :: its) (generated_item_alias d pv (me_mem H n) :: gs)
(** An item naming a member with a term part and a module part: a
    definition with a module part, the member as its term part and as the
    target of its module part *)
| kinds_items_gen_dm : forall ρ H n d pv its gs,
    modexp_member_kind Θ Ξ ρ H (n :: nil) member_kind_dm ->
    kinds_items_gen Θ Ξ ρ H its gs ->
    kinds_items_gen Θ Ξ ρ H ((Some n, d, pv) :: its) (generated_item_def_mod d pv a_placeholder_type (a_mem H n) (me_mem H n) :: gs).

Scheme dmod_member_kind_mut_ind := Induction for dmod_member_kind Sort Prop
with gunit_member_kind_mut_ind := Induction for gunit_member_kind Sort Prop
with modexp_member_kind_mut_ind := Induction for modexp_member_kind Sort Prop
with kinds_env_mut_ind := Induction for kinds_env Sort Prop
with kinds_body_xp_mut_ind := Induction for kinds_body_xp Sort Prop
with kinds_items_gen_mut_ind := Induction for kinds_items_gen Sort Prop.
Combined Scheme kind_mut_ind from dmod_member_kind_mut_ind, gunit_member_kind_mut_ind, modexp_member_kind_mut_ind, kinds_env_mut_ind, kinds_body_xp_mut_ind, kinds_items_gen_mut_ind.

#[export]
Hint Constructors dmod_member_kind gunit_member_kind modexp_member_kind kinds_env kinds_body_xp kinds_items_gen : mctt.

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
(** So is [⋆]. *)
| eval_exp_true :
  `( ⟦ ⋆ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
(** The introduction of [⊤] is the proof [⋆ᵈ]. *)
| eval_exp_tt :
  `( ⟦ a_tt ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
(** [⊥] is a value. *)
| eval_exp_False :
  `( ⟦ ⊥ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⊥ᵈ )
(** Ex falso never evaluates its proof: it is stuck at its type, the
    proof [⋆ᵈ] at a proposition ([relevant_value]). *)
| eval_exp_absurd :
  `( ⟦ C ⟧ Θ ⍮ Ξ ⍮ ρ ↘ c ->
     ⟦ efq M return C ⟧ Θ ⍮ Ξ ⍮ ρ ↘ relevant_value c (⇑ c (efqᵈ c)) )
(** A [Σₚ] evaluates its first component and closes over its second. *)
| eval_exp_and :
  `( ⟦ P ⟧ Θ ⍮ Ξ ⍮ ρ ↘ p ->
     ⟦ Σₚ P Q ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Σₚᵈ p ρ Q )
(** The proof of a conjunction is [⋆ᵈ]; its parts are not evaluated. *)
| eval_exp_conj :
  `( ⟦ a_conj T M N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
(** So is the proof of its first component. *)
| eval_exp_left :
  `( ⟦ a_left M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
(** And that of its second. *)
| eval_exp_right :
  `( ⟦ a_right M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
(** The placeholder type is a value. *)
| eval_exp_placeholder_type :
  `( ⟦ a_placeholder_type ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_placeholder_type )
(** So is its element. *)
| eval_exp_placeholder :
  `( ⟦ a_placeholder ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_placeholder )
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
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ env_args nil nil ↘ cups ->
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
(** An eliminator into propositions is a proof: [⋆ᵈ], unevaluated. *)
| eval_exp_elim_proof :
  `( ⟦ a_elim propositional oq Us j Bks M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
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
(** An application of a function taking a proof applies it to [⋆ᵈ]; the
    argument is not evaluated. *)
| eval_exp_app_proof :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     arg_relevance Θ Ξ m = propositional ->
     $| m & ⋆ᵈ | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An unannotated local definition, of a type of a universe, extends the
    environment by the value of its body; nothing is substituted. *)
| eval_exp_let :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ m ↘ r ->
     ⟦ a_let (b_def None M) B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An annotated one at a relevant type, likewise. *)
| eval_exp_let_ann :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     domain_relevance a = relevant ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ m ↘ r ->
     ⟦ a_let (b_def (Some A) M) B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An annotated one at a proposition binds [⋆ᵈ]; its body is a proof,
    not evaluated. *)
| eval_exp_let_proof :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     domain_relevance a = propositional ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⋆ᵈ ↘ r ->
     ⟦ a_let (b_def (Some A) M) B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local module extends it by the unit's closure. *)
| eval_exp_let_mod :
  `( ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ᵐ h ↘ r ->
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
    propositional field [⋆ᵈ] ([eval_field_vals]); the type it is annotated with
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
     eval_neutral_fields Θ Ξ ns m (List.firstn (S k) (record_fields R)) nil rs ->
     List.nth_error rs k = Some r ->
     eval_proj Θ Ξ f (⇑ (d_record p ns) m) r )
(** [eval_neutral_fields ns m fl pre rs]: the neutral projections [rs] of [m] at
    the fields [fl], after the projections [pre] of the fields before them,
    each at its type at the parameters [ns] and the projections before
    it. *)
with eval_neutral_fields (Θ : gdeps) (Ξ : gstack) : list domain -> domain_ne -> list (string * exp) -> list domain -> list domain -> Prop :=
(** No field left *)
| eval_neutral_fields_nil :
  `( eval_neutral_fields Θ Ξ ns m nil pre nil )
(** The next field's projection, at its type, then the rest after it *)
| eval_neutral_fields_cons :
  `( ⟦ T ⟧ Θ ⍮ Ξ ⍮ env_args nil (ns ++ pre) ↘ a ->
     eval_neutral_fields Θ Ξ ns m fl (pre ++ relevant_value a (⇑ a (d_proj g m)) :: nil) rs ->
     eval_neutral_fields Θ Ξ ns m ((g, T) :: fl) pre (relevant_value a (⇑ a (d_proj g m)) :: rs) )
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
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs) ++ skipn (im_np Dq Mk) vs ++ ihs) ↘ r ->
     ⟦elim d_con pc k c vs at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** On a neutral: a stuck eliminator, at the motive's instance; the
    proof [⋆ᵈ] at a propositional instance, as every neutral evaluation
    builds ([relevant_value]) *)
| eval_elim_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_binder_count b = S (im_nn Mk) ->
     ⟦ eb_motive b ⟧ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu Dq) as' ++ ⇑ (d_ind pc k as') m :: nil) ↘ a ->
     ⟦elim ⇑ (d_ind pc k as') m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ relevant_value a (⇑ a (d_elim ρ Bks p ups j as' m)) )
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
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ env_args nil ups ↘ cups ->
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
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ env_args nil ups ↘ cups ->
     ⟦shty pt_self j Ps of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_record qr cups )
(** At a domain: a [Π] over it, of the shape family *)
| eval_shape_type_pi :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦shty pt_pi B t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ b (nil ↦ d_shfam p ups ρ t) fam_cod )
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
     ⟦ List.nth j As a_placeholder_type ⟧ Θ ⍮ Ξ ⍮ env_args ρm (bs ++ v :: nil) ↘ a ->
     ⟦ihty v of pt_self j Ps at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a :: nil )
(** At the end, at a record view: those of its fields at [v]'s
    projections *)
| eval_ihty_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws ->
     ⟦ihtys ws of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ env_args nil ups ↘ rs ->
     ⟦ihty v of pt_self j Ps at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** At a domain: a [Π] over it, of each recursive result's family *)
| eval_ihty_pi :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦ihty v of pt_pi B t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ
       ↘ List.map (fun i => Πᵈ b (nil ↦ d_ihfam ρm As p ups ρ t i v) fam_cod)
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
  `( ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↦ v ↘ rs ->
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
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ m ->
     $| λᵈ a ρ M & n | Θ ⍮ Ξ ↘ m )
(** The proof [⋆ᵈ] applied is a proof: [⋆ᵈ].  A proof member of a
    saturated module is [⋆ᵈ] ([eval_sel_global_proof]).  [arg_relevance ⋆ᵈ]
    is [relevant], but no term application reaches this rule with an
    argument to evaluate: an application whose function is a proof is at
    a [∀], hence itself a proof, which relevance-directed evaluation never
    evaluates. *)
| eval_app_proof :
  `( $| ⋆ᵈ & n | Θ ⍮ Ξ ↘ ⋆ᵈ )
(** A neutral applied, at the codomain's instance; the proof [⋆ᵈ] at a
    propositional instance, as every neutral evaluation builds
    ([relevant_value]). *)
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ relevant_value b (⇑ b (m $ᵈ ⇓ a n)) )
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
     ⟦ Is ⟧* Θ ⍮ Ξ ⍮ env_args nil (vs ++ n :: nil) ↘ cups ->
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
  `( ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ a ->
     $| d_shfam p ups ρ t & n | Θ ⍮ Ξ ↘ a )
(** The [i]-th recursive result's family, at the argument's value *)
| eval_app_ihfam :
  `( $| f & n | Θ ⍮ Ξ ↘ fn ->
     ⟦ihty fn of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ as' ->
     List.nth_error as' i = Some a ->
     $| d_ihfam ρm As p ups ρ t i f & n | Θ ⍮ Ξ ↘ a )
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
    as a proof ([arg_relevance]) is [⋆ᵈ], unevaluated, as in
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
(** A proof argument: [⋆ᵈ] applied, then the rest. *)
| eval_app_args_proof :
  `( arg_relevance Θ Ξ f = propositional ->
     $| f & ⋆ᵈ | Θ ⍮ Ξ ↘ g ->
     eval_app_args Θ Ξ g Ns ρ r ->
     eval_app_args Θ Ξ f (N :: Ns) ρ r )
(** [eval_field_vals rs Ms ρ vs]: the values [vs] of the fields [Ms] of a record
    value, the field at the sort [propositional] in [rs] the proof [⋆ᵈ],
    not evaluated (a sort past [rs] is relevant). *)
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
(** A propositional field: [⋆ᵈ], then the rest. *)
| eval_field_vals_proof :
  `( List.hd relevant rs = propositional ->
     eval_field_vals Θ Ξ (List.tl rs) Ms ρ ms ->
     eval_field_vals Θ Ξ rs (M :: Ms) ρ (⋆ᵈ :: ms) )
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
  `( ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ r ->
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
(** A definition of a saturated global module tagged a proposition,
    transparent or not: the proof [⋆ᵈ].  Neither its body nor its type is
    evaluated. *)
| eval_sel_global_proof :
  `( module_saturated Θ Ξ p args ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv propositional A B) ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ ⋆ᵈ )
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
    definition with a module part's term), found in the body read through
    the entries its local opens generate: it, in the environment of the
    body before it, when the entry is relevant. *)
| eval_sel_body :
  `( kinds_body_xp Θ Ξ ρ Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     entry_relevance E = relevant ->
     ⟦ Φ' ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₜ x Θ ⍮ Ξ ↘ r )
(** A definition of a saturated body tagged a proposition: the proof
    [⋆ᵈ], its body not evaluated. *)
| eval_sel_body_proof :
  `( kinds_body_xp Θ Ξ ρ Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     entry_relevance E = propositional ->
     dm_local nil (md_body sm Φ) ρ ·ₜ x Θ ⍮ Ξ ↘ ⋆ᵈ )
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
    definition with a module part's), found in the body read through the
    entries its local opens generate: its unit's closure, in the
    environment of the body before it. *)
| eval_selm_body :
  `( kinds_body_xp Θ Ξ ρ Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y E) ->
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
    type, and a definition an open generates is tagged with the sort of
    the member it names, where its type is not known ([kinds_items_gen]). *)
| eval_body_env_def :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ gm_ext Φ y (ge_def b pv relevant A (Some M)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ m )
(** A definition tagged a proposition, a proof, adds [⋆ᵈ], unevaluated. *)
| eval_body_env_def_proof :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ gm_ext Φ y (ge_def b pv propositional A (Some M)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ ⋆ᵈ )
(** A submodule adds its unit's closure. *)
| eval_body_env_mod :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ Δy ⊢ Dy ⟧ᶜ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_mod pm (gu_mk Δy Dy)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵐ h )
(** A definition with a module part adds its term's value and its unit's
    closure. *)
| eval_body_env_dm :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ Δy ⊢ Dy ⟧ᶜ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵈ m ‖ h )
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
    term, the value of a module expression, or the values of both.  Past its end [ρσ] reads the
    term [⋆ᵈ], so a result exists only when, from some index on, every
    [σ x] denotes it, for example as a variable past the end of [ρ]. *)
Definition eval_sentry (Θ : gdeps) (Ξ : gstack) (e : sentry) (ρ : env) (d : dentry) : Prop :=
  match e with
  | se_var y => d = env_entry ρ y
  | se_exp M => exists m, d = de_term m /\ ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m
  | se_mod H => exists h, d = de_mod h /\ ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h
  | se_dm N H => exists n h, d = de_dm n h /\ ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n /\ ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h
  end.

Notation "'⟦' e '⟧ᵉ' Θ '⍮' Ξ '⍮' ρ '↘' d" := (eval_sentry Θ Ξ e ρ d) : mctt_scope.

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
    at an entry of [Δ] that is a proposition, the value is the proof [⋆ᵈ],
    and the substitution's entry, a proof, is not evaluated; at every
    other entry of [Δ], [ρσ] holds what [σ x] denotes in [ρ].  Past the
    entries of [Δ] nothing is said: a substitution into [Δ] says nothing
    of the indices past it.  The two cases are stated as implications, so
    that building an evaluation needs no case analysis on whether an entry
    is a proposition. *)
Definition eval_sub (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (σ : sub) (ρ ρσ : env) : Prop :=
  forall x, x < List.length Δ ->
    (entry_propositional Θ Ξ Δ ρσ x -> env_entry ρσ x = de_term ⋆ᵈ)
    /\ (~ entry_propositional Θ Ξ Δ ρσ x -> ⟦ σ x ⟧ᵉ Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρσ x).
Arguments eval_sub : simpl never.

Notation "'⟦' σ ':' Δ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" := (eval_sub Θ Ξ Δ σ ρ ρσ) : mctt_scope.

(** An environment [ρ] of [Δ] holds [⋆ᵈ] at each of [Δ]'s propositional
    entries: relevance-directed evaluation only ever builds such
    environments.  It is the condition under which the identity evaluates
    to [ρ]. *)
Definition env_proofs (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (ρ : env) : Prop :=
  forall x, entry_propositional Θ Ξ Δ ρ x -> env_entry ρ x = de_term ⋆ᵈ.

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
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ -> entry_propositional Θ Ξ Δ ρσ x -> env_entry ρσ x = de_term ⋆ᵈ.
Proof. intros * H Hp; exact (proj1 (H x (entry_propositional_lt _ _ _ Hp)) Hp). Qed.

Proposition eval_sub_index : forall {Θ Ξ} Δ σ (ρ ρσ : env),
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    forall x, x < List.length Δ -> ~ entry_propositional Θ Ξ Δ ρσ x -> ⟦ σ x ⟧ᵉ Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρσ x.
Proof. intros * H x Hx; apply (H x Hx). Qed.

(** The identity evaluates to an environment holding its proofs. *)
Lemma eval_sub_id : forall {Θ Ξ} Δ ρ, env_proofs Θ Ξ Δ ρ -> ⟦ Id : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ.
Proof. intros * H x _; split; [ apply H | intros _; reflexivity ]. Qed.

(** The tail of an environment holding its proofs holds its tail's. *)
Lemma env_proofs_drop : forall {Θ Ξ} e Δ ρ, env_proofs Θ Ξ (e :: Δ) ρ -> env_proofs Θ Ξ Δ ρ↯.
Proof. intros * H x Hx; rewrite env_entry_drop; apply H; exact (proj2 (entry_propositional_succ _ _ _ _) Hx). Qed.

(** The shift evaluates to the tail of an environment holding its
    proofs. *)
Lemma eval_sub_shift : forall {Θ Ξ} e Δ ρ, env_proofs Θ Ξ (e :: Δ) ρ -> ⟦ Wk : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ↯.
Proof.
  intros * H x _; split; [ apply (env_proofs_drop _ _ _ H) | intros _; reflexivity ].
Qed.

(** The head entry of [e :: Δ] is a proposition over the tail [ρσ] of
    [Δ]: its type evaluates there, up to agreement on the entries of [Δ], to
    a proposition.  It does not depend on the head of the environment. *)
Definition head_propositional (Θ : gdeps) (Ξ : gstack) (e : centry) (Δ : ctx) (ρσ : env) : Prop :=
  entry_propositional Θ Ξ (e :: Δ) (de_term d_placeholder :: ρσ) 0.

Lemma entry_propositional_head : forall {Θ Ξ} e Δ d ρσ,
    entry_propositional Θ Ξ (e :: Δ) (d :: ρσ) 0 <-> head_propositional Θ Ξ e Δ ρσ.
Proof. intros; split; intros []; econstructor; eassumption. Qed.

(** An extension by a term at an entry that is not a proposition: the
    term's value. *)
Lemma eval_sub_extend : forall {Θ Ξ} e Δ σ ρ ρσ M m,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ~ head_propositional Θ Ξ e Δ ρσ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ σ,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H Hn HM [| x] Hx.
  - split; [ intros Hp; apply entry_propositional_head in Hp; contradiction
           | intros _; exists m; split; [ reflexivity | assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hp; apply (H x ltac:(lia)); intros Hp'; exact (Hp (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An extension at an entry that is a proposition: the proof [⋆ᵈ], the
    entry unevaluated. *)
Lemma eval_sub_extend_proof : forall {Θ Ξ} e Δ σ ρ ρσ M,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    head_propositional Θ Ξ e Δ ρσ ->
    ⟦ σ,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ ⋆ᵈ.
Proof.
  intros * H Hp [| x] Hx.
  - split; [ reflexivity | intros Hn; exfalso; exact (Hn (proj2 (entry_propositional_head _ _ _ _) Hp)) ].
  - cbn [List.length] in Hx.
    split; [ intros Hp'; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp')
           | intros Hn; apply (H x ltac:(lia)); intros Hp'; exact (Hn (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An extension by a term whose value is the proof [⋆ᵈ] whenever the
    entry is a proposition: either way the term's value. *)
Lemma eval_sub_extend_any : forall {Θ Ξ} e Δ σ ρ ρσ M m,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    (head_propositional Θ Ξ e Δ ρσ -> m = ⋆ᵈ) ->
    ⟦ σ,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H HM Hp [| x] Hx.
  - split; [ intros Hx0; cbn; rewrite (Hp (proj1 (entry_propositional_head _ _ _ _) Hx0)); reflexivity
           | intros _; exists m; split; [ reflexivity | assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp'; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp')
           | intros Hn; apply (H x ltac:(lia)); intros Hp'; exact (Hn (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An extension by a module expression at a module slot. *)
Lemma eval_sub_extend_mod : forall {Θ Ξ} U Δ σ ρ ρσ H h,
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ σ ,,ₘ H : ce_mod U :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ᵐ h.
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
    ⟦ σ ,,ᵈ N ‖ H : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ᵈ n ‖ h.
Proof.
  intros * Hσ Hn HN HH [| x] Hx.
  - split; [ intros Hp; apply entry_propositional_head in Hp; contradiction
           | intros _; exists n, h; split; [ reflexivity | split; assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (Hσ x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hm; apply (Hσ x ltac:(lia)); intros Hp'; exact (Hm (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

Corollary eval_sub_single_dm : forall {Θ Ξ} e Δ ρ N H n h,
    env_proofs Θ Ξ Δ ρ ->
    ~ head_propositional Θ Ξ e Δ ρ ->
    ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ Id ,,ᵈ N ‖ H : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ᵈ n ‖ h.
Proof.
  intros; apply eval_sub_extend_dm; [ apply eval_sub_id; assumption | assumption .. ].
Qed.

Corollary eval_sub_single : forall {Θ Ξ} e Δ ρ M m,
    env_proofs Θ Ξ Δ ρ ->
    ~ head_propositional Θ Ξ e Δ ρ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ Id,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ m.
Proof.
  intros; apply eval_sub_extend; [ apply eval_sub_id; assumption | assumption .. ].
Qed.

Corollary eval_sub_single_proof : forall {Θ Ξ} e Δ ρ M,
    env_proofs Θ Ξ Δ ρ ->
    head_propositional Θ Ξ e Δ ρ ->
    ⟦ Id,,M : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ ⋆ᵈ.
Proof.
  intros; apply eval_sub_extend_proof; [ apply eval_sub_id; assumption | assumption ].
Qed.

Corollary eval_sub_single_mod : forall {Θ Ξ} U Δ ρ H h,
    env_proofs Θ Ξ Δ ρ ->
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ Id ,,ₘ H : ce_mod U :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ᵐ h.
Proof.
  intros; apply eval_sub_extend_mod; [ apply eval_sub_id; assumption | assumption ].
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
  - rewrite Hσ; apply eval_exp_var.
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
  - rewrite Hσ; apply eval_me_var.
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
  - rewrite <- (Hρσ x); apply (proj1 (H x Hx)); eapply entry_propositional_resp_env_eq; eassumption.
  - rewrite <- (Hσ x), <- (Hρσ x); apply (proj2 (H x Hx)); intros Hp; apply Hn; eapply entry_propositional_resp_env_eq; eassumption.
  - rewrite (Hρσ x); apply (proj1 (H x Hx)); eapply entry_propositional_resp_env_eq; eassumption.
  - rewrite (Hσ x), (Hρσ x); apply (proj2 (H x Hx)); intros Hp; apply Hn; eapply entry_propositional_resp_env_eq; eassumption.
Qed.

(** ** The Substitutions that Compute

    Evaluation of the substitutions that occur in practice:

    - the image under [ι] of an order-preserving weakening, for which
      [⟪φ⟫ ρ] is [ρ ∘ φ] at every index;
    - weakened extensions and lifts;
    - precomposition by a weakening. *)
(** A substitution of variables evaluates to the environment its
    variables read, when the entries that are propositions read proofs. *)
Lemma eval_sub_of_vars : forall {Θ Ξ} Δ σ ρ ρσ,
    (forall x, exists y, σ x = se_var y /\ env_entry ρσ x = env_entry ρ y) ->
    env_proofs Θ Ξ Δ ρσ ->
    ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ.
Proof.
  intros * Hv Hp x _; split; [ apply Hp | intros _ ].
  destruct (Hv x) as (y & -> & ->); reflexivity.
Qed.

Lemma eval_sub_of_wk : forall {Θ Ξ} Δ φ ρ `{Hφ : WkMono φ},
    env_proofs Θ Ξ Δ (⟪φ⟫ ρ) ->
    ⟦ ι φ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ⟪φ⟫ ρ.
Proof.
  intros Θ Ξ Δ φ ρ Hφ Hp; apply eval_sub_of_vars; [| exact Hp ].
  intros x; exists (φ x); split; [ reflexivity | apply (eval_wk_entry _ _ Hφ x) ].
Qed.

(** A weakened extension. *)
Lemma eval_sub_wk_extend : forall {Θ Ξ} e Δ σ M φ ρ ρσ m,
    ⟦ sb_wk σ φ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ~ head_propositional Θ Ξ e Δ ρσ ->
    ⟦ M[φ]ʷ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ sb_wk (σ,,M) φ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H Hn HM [| x] Hx.
  - split; [ intros Hp; apply entry_propositional_head in Hp; contradiction
           | intros _; exists m; split; [ reflexivity | assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hm; apply (H x ltac:(lia)); intros Hp'; exact (Hm (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** A lifted substitution, plain and weakened.  [q σ] extends [σ[↑]] by the
    variable [0], so its head is the entry already in [ρ]. *)
Lemma eval_sub_q : forall {Θ Ξ} e Δ σ ρ ρσ,
    ⟦ sb_wk σ ↑ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    (head_propositional Θ Ξ e Δ ρσ -> env_entry ρ 0 = de_term ⋆ᵈ) ->
    ⟦ q σ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρ 0 :: ρσ.
Proof.
  intros * H Hp [| x] Hx.
  - split; [ intros Hp'; exact (Hp (proj1 (entry_propositional_head _ _ _ _) Hp')) | intros _; reflexivity ].
  - cbn [List.length] in Hx; split.
    + intros Hp'; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp').
    + intros Hn; exact (proj2 (H x ltac:(lia)) (fun Hp' => Hn (entry_propositional_extend_intro _ _ _ _ _ Hp'))).
Qed.

Lemma eval_sub_wk_q : forall {Θ Ξ} e Δ σ φ ρ ρσ,
    ⟦ sb_wk (sb_wk σ ↑) φ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    (head_propositional Θ Ξ e Δ ρσ -> env_entry ρ (φ 0) = de_term ⋆ᵈ) ->
    ⟦ sb_wk (q σ) φ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρ (φ 0) :: ρσ.
Proof.
  intros * H Hp [| x] Hx.
  - split; [ intros Hp'; exact (Hp (proj1 (entry_propositional_head _ _ _ _) Hp'))
           | intros _; cbn [sb_wk]; rewrite sb_q_zero; reflexivity ].
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
