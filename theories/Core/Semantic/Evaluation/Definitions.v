From Stdlib Require Import Lia List Morphisms String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Inductives.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'⟦' M '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦elim' m 'under' nm A Bs '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, nm at level 0, A at level 0, Bs at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihs' vs 'of' gs 'under' nm A Bs '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, nm at level 0, A at level 0, Bs at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" (at level 70, σ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρσ at level 69).

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

(** * The Kinds of Members of Module Values

    A local open declares, for each item, a definition or an alias, by the
    kind of the member it names ([items_gen]).  Evaluation must tell them
    apart without a type: the kind of a member is read off the module value
    and the syntax of the units it closes over.  A body is read through the
    entries it makes ([kenv]), as evaluation would but with a placeholder
    for every definition, so that no term is evaluated: a kind does not
    depend on the values of terms, nor on a module's arguments, which are
    terms ([kpad]).  The relations mirror [member_type] with the types left
    out, and read a closure or a submodule closure as selection on module
    values does ([eval_selm]). *)

(** The closure of a unit over [ρ], as kinds read it: a saturated alias is
    left as a closure, which kinds read through. *)
Definition dm_clo (U : gunit) (ρ : env) : dmod :=
  match U with gu_mk Δ D => dm_local Δ D ρ end.

(** [n] placeholders for parameters, terms, over [ρ]. *)
Definition kpad (n : nat) (ρ : env) : env := List.repeat (de_term d_true) n ++ ρ.

(** The entry a body's entry adds over [ρ], as kinds read it: a module, its
    closure; any other, a placeholder, as in [body_ctx]. *)
Definition kbentry (ρ : env) (E : gentry) : dentry :=
  match E with
  | ge_mod _ U => de_mod (dm_clo U ρ)
  | _ => de_term d_true
  end.

(** The entries generated items add over [ρ], as kinds read them, the
    [k]-th under the [k] before it: an alias, the closure of its unit; a
    definition, a placeholder. *)
Definition kentry (ρ : env) (k : nat) (g : igen) : dentry :=
  match g with
  | ig_alias _ _ E => de_mod (dm_local nil (md_alias (modexp_wk E (wk_shiftn k))) ρ)
  | _ => de_term d_true
  end.

Fixpoint kgens_env (ρ : env) (k : nat) (gs : list igen) : env :=
  match gs with
  | nil => ρ
  | g :: gs' => kgens_env (kentry ρ k g :: ρ) (S k) gs'
  end.

Inductive dkind (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> mkind -> Prop :=
(** A chain of a global module, read off the global context one name at a
    time, as selection on module values reads it ([eval_selm]): the path
    reached names a definition, a term, or a body module or an open frame,
    a module; a chain through an alias is read in the alias past it. *)
| dk_global_here_def : forall p args b pv A B,
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    dkind Θ Ξ (dm_global p args) nil mk_term
| dk_global_here_mod : forall p args,
    (exists T oD, gc_module Θ Ξ p = Some (mr_body T oD)) \/ (exists TΦ, gc_frame Ξ p = Some TΦ) ->
    dkind Θ Ξ (dm_global p args) nil mk_mod
| dk_global_alias : forall p args y ch U k,
    gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias U) ->
    ukind Θ Ξ nil U ch k ->
    dkind Θ Ξ (dm_global p args) (y :: ch) k
| dk_global_step : forall p args y ch k,
    (exists TΦ, gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ) \/
    (exists b pv A B, gc_resolve Θ Ξ (qname_app p (y :: nil)) = Some (ge_def b pv A B)) ->
    dkind Θ Ξ (dm_global (qname_app p (y :: nil)) args) ch k ->
    dkind Θ Ξ (dm_global p args) (y :: ch) k
(** A closure, by its unit. *)
| dk_local : forall Δ D ρ ch k,
    ukind Θ Ξ ρ (gu_mk Δ D) ch k ->
    dkind Θ Ξ (dm_local Δ D ρ) ch k
(** A submodule closure, by the longer chain. *)
| dk_member : forall h ch0 ch k,
    dkind Θ Ξ h (ch0 ++ ch) k ->
    dkind Θ Ξ (dm_member h ch0) ch k
with ukind (Θ : gdeps) (Ξ : gstack) : env -> gunit -> list string -> mkind -> Prop :=
| uk_self : forall ρ Δ sm Φ, ukind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) nil mk_mod
| uk_def : forall ρ Δ sm Φ Φ' x b pv A B,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    ukind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: nil) mk_term
| uk_mod : forall ρ Δ sm Φ Φ' y pm Uy ρ1 ch k,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    kenv Θ Ξ (kpad (List.length Δ) ρ) Φ' ρ1 ->
    ukind Θ Ξ ρ1 Uy ch k ->
    ukind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (y :: ch) k
(** A name a local open declares, by the kind of the member it names in the
    open's target, as the open generates it ([kgens]): a definition of a term
    member, an alias of a module member or of the target itself. *)
| uk_item_def : forall ρ Δ sm Φ Φ0 H its1 n d pv ρ0 x,
    gm_item_upto Φ x = Some (Φ0, H, its1, (Some n, d, pv)) ->
    kenv Θ Ξ (kpad (List.length Δ) ρ) Φ0 ρ0 ->
    skind Θ Ξ ρ0 H (n :: nil) mk_term ->
    ukind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: nil) mk_term
| uk_item_mod : forall ρ Δ sm Φ Φ0 H its1 n d pv ρ0 x ch k,
    gm_item_upto Φ x = Some (Φ0, H, its1, (Some n, d, pv)) ->
    kenv Θ Ξ (kpad (List.length Δ) ρ) Φ0 ρ0 ->
    skind Θ Ξ ρ0 H (n :: nil) mk_mod ->
    skind Θ Ξ ρ0 H (n :: ch) k ->
    ukind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: ch) k
| uk_item_self : forall ρ Δ sm Φ Φ0 H its1 d pv ρ0 x ch k,
    gm_item_upto Φ x = Some (Φ0, H, its1, (None, d, pv)) ->
    kenv Θ Ξ (kpad (List.length Δ) ρ) Φ0 ρ0 ->
    skind Θ Ξ ρ0 H ch k ->
    ukind Θ Ξ ρ (gu_mk Δ (md_body sm Φ)) (x :: ch) k
| uk_alias : forall ρ Δ E ch k,
    skind Θ Ξ (kpad (List.length Δ) ρ) E ch k ->
    ukind Θ Ξ ρ (gu_mk Δ (md_alias E)) ch k
with skind (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list string -> mkind -> Prop :=
| sk_unit : forall ρ fp ch k,
    dkind Θ Ξ (dm_global (q_abs fp nil) nil) ch k ->
    skind Θ Ξ ρ (me_unit fp) ch k
| sk_var : forall ρ x ch k,
    dkind Θ Ξ (env_mod ρ x) ch k ->
    skind Θ Ξ ρ (me_var x) ch k
| sk_lit : forall ρ U ch k,
    ukind Θ Ξ ρ U ch k ->
    skind Θ Ξ ρ (me_lit U) ch k
| sk_mem : forall ρ H y ch k,
    skind Θ Ξ ρ H (y :: ch) k ->
    skind Θ Ξ ρ (me_mem H y) ch k
| sk_app : forall ρ H N ch k,
    skind Θ Ξ ρ H ch k ->
    skind Θ Ξ ρ (me_app H N) ch k
(** The environment a body makes, as kinds read it: an entry each body
    entry adds ([kbentry]), and the entries an open generates. *)
with kenv (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
| ke_nil : forall ρ, kenv Θ Ξ ρ gm_nil ρ
| ke_ext : forall ρ Φ ρ1 y E,
    kenv Θ Ξ ρ Φ ρ1 ->
    kenv Θ Ξ ρ (gm_ext Φ y E) (kbentry ρ1 E :: ρ1)
| ke_open : forall ρ Φ ρ1 H its gs,
    kenv Θ Ξ ρ Φ ρ1 ->
    kgens Θ Ξ ρ1 H its gs ->
    kenv Θ Ξ ρ (gm_open Φ H its) (kgens_env ρ1 0 gs)
(** A body read through the entries its local opens generate, as kinds read
    them: [body_xp] with the types left out.  Each open's items are read in
    the environment of the expanded body before it. *)
with kbody (Θ : gdeps) (Ξ : gstack) : env -> gmod -> gmod -> Prop :=
| kb_nil : forall ρ, kbody Θ Ξ ρ gm_nil gm_nil
| kb_ext : forall ρ Φ Φx x E,
    kbody Θ Ξ ρ Φ Φx ->
    kbody Θ Ξ ρ (gm_ext Φ x E) (gm_ext Φx x E)
| kb_open : forall ρ Φ Φx ρ1 H its gs,
    kbody Θ Ξ ρ Φ Φx ->
    kenv Θ Ξ ρ Φx ρ1 ->
    kgens Θ Ξ ρ1 H its gs ->
    kbody Θ Ξ ρ (gm_open Φ H its) (gens_append Φx 0 gs)
(** What the items of an open of [H] generate, by the kinds of the members
    they name, in [ρ]; a generated definition carries no type. *)
with kgens (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list iitem -> list igen -> Prop :=
| kg_nil : forall ρ H, kgens Θ Ξ ρ H nil nil
| kg_self : forall ρ H d pv its gs,
    kgens Θ Ξ ρ H its gs ->
    kgens Θ Ξ ρ H ((None, d, pv) :: its) (ig_alias d pv H :: gs)
| kg_def : forall ρ H n d pv its gs,
    skind Θ Ξ ρ H (n :: nil) mk_term ->
    kgens Θ Ξ ρ H its gs ->
    kgens Θ Ξ ρ H ((Some n, d, pv) :: its) (ig_def d pv a_True (a_mem H n) :: gs)
| kg_mod : forall ρ H n d pv its gs,
    skind Θ Ξ ρ H (n :: nil) mk_mod ->
    kgens Θ Ξ ρ H its gs ->
    kgens Θ Ξ ρ H ((Some n, d, pv) :: its) (ig_alias d pv (me_mem H n) :: gs).

Scheme dkind_mut_ind := Induction for dkind Sort Prop
with ukind_mut_ind := Induction for ukind Sort Prop
with skind_mut_ind := Induction for skind Sort Prop
with kenv_mut_ind := Induction for kenv Sort Prop
with kbody_mut_ind := Induction for kbody Sort Prop
with kgens_mut_ind := Induction for kgens Sort Prop.
Combined Scheme kind_mut_ind from dkind_mut_ind, ukind_mut_ind, skind_mut_ind, kenv_mut_ind, kbody_mut_ind, kgens_mut_ind.

#[export]
Hint Constructors dkind ukind skind kenv kbody kgens : mctt.

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
  `( ⟦ 𝕃ᵒ o ⟧ Θ ⍮ Ξ ⍮ ρ ↘ dlvl_lit o )
(** The level operations only flatten: they add to the offsets, or join the
    constants and concatenate the atoms.  Canonicalisation is readback's. *)
| eval_exp_succl :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succl M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ dlvl_suc m )
| eval_exp_maxl :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     ⟦ maxl M N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ dlvl_max m n )
(** A variable is read off the environment. *)
| eval_exp_var :
  `( ⟦ #x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρ x )
(** [⊤] is a value. *)
| eval_exp_True :
  `( ⟦ ⊤ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⊤ᵈ )
(** So is [⋆]. *)
| eval_exp_true :
  `( ⟦ ⋆ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
(** [⊥] is a value. *)
| eval_exp_False :
  `( ⟦ ⊥ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⊥ᵈ )
(** [⊥] has no canonical values, so the eliminator only meets a neutral. *)
| eval_exp_exfalso :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ b m ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦ efq M return A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (efqᵈ m under ρ return A) )
(** The type former and a constructor of an inductive type are values,
    with no argument yet. *)
| eval_exp_indty :
  `( ⟦ a_ind p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_ind p nil )
| eval_exp_con :
  `( ⟦ a_con p c ⟧ Θ ⍮ Ξ ⍮ ρ ↘ d_con p c nil )
(** The eliminator evaluates its scrutinee, then eliminates the value. *)
| eval_exp_elim :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ a_elim nm A Bs M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A [Π] evaluates its domain and closes over its codomain. *)
| eval_exp_pi :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ Π A B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ a ρ B )
(** A function closes over its body. *)
| eval_exp_fn :
  `( ⟦ λ A M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ λᵈ ρ M )
(** An application applies the value of the function to that of the argument. *)
| eval_exp_app :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $| m & n | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local definition extends the environment by the value of its body;
    nothing is substituted. *)
| eval_exp_let :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ m ↘ r ->
     ⟦ a_let (b_def oA M) B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local module extends it by the unit's closure. *)
| eval_exp_let_mod :
  `( ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ᵐ h ↘ r ->
     ⟦ ℓₘ (gu_mk Δ D) in B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A member is read off the root of its module expression, then applied to
    the module's arguments: arguments commute with selection.  Without
    arguments this is selection from the module's value. *)
| eval_exp_mem :
  `( modexp_spine H = (R, args, pre) ->
     ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     h ·ₜ* (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
     ⟦ args ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ns ->
     $*| f & ns | Θ ⍮ Ξ ↘ r ->
     ⟦ a_mem H x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' e '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_exp Θ Ξ e ρ r)
(** The eliminator of an inductive type, on a value.  On a constructor at
    all its parameters and arguments, the branch of the constructor, with its
    non-uniform parameters, its arguments and the recursive results.  On a
    neutral of the type, a neutral at the motive's instance; the neutral
    records the inductive type and its parameters, which readback needs. *)
with eval_elim (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> domain -> domain -> Prop :=
| eval_elim_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     brs_lookup Bs c = Some (n, B) ->
     n = (ind_nn D + List.length gs + cargs_nrec gs)%nat ->
     ⟦ihs skipn (ind_np D) vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs) ↘ r ->
     ⟦elim d_con p c vs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
| eval_elim_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' = ind_np D ->
     nm = S (ind_nn D) ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (skipn (ind_nu D) as' ++ ⇑ (d_ind p as') m :: nil) ↘ a ->
     ⟦elim ⇑ (d_ind p as') m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_elim ρ nm A Bs p as' m) )
where "'⟦elim' m 'under' nm A Bs '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_elim Θ Ξ ρ nm A Bs m r)
(** The recursive results of the arguments [vs], one per recursive argument. *)
with eval_ihs (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> list carg -> list domain -> list domain -> Prop :=
| eval_ihs_nil :
  `( ⟦ihs nil of nil under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ nil )
| eval_ihs_arg :
  `( ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihs v :: vs of ca_arg T :: gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs )
| eval_ihs_rec :
  `( eval_ih Θ Ξ ρ nm A Bs t v ih ->
     ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihs v :: vs of ca_rec t :: gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ih :: ihs )
where "'⟦ihs' vs 'of' gs 'under' nm A Bs '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_ihs Θ Ξ ρ nm A Bs gs vs r)
(** The recursive result of an argument [v] of shape [t]: the eliminator
    at [v], or, at a function shape, the family of the eliminator at [v]'s
    values. *)
with eval_ih (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> ptyp -> domain -> domain -> Prop :=
| eval_ih_self :
  `( ⟦elim v under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     eval_ih Θ Ξ ρ nm A Bs (pt_self k Ps) v r )
| eval_ih_pi :
  `( eval_ih Θ Ξ ρ nm A Bs (pt_pi B t) v (d_ihfn ρ nm A Bs t v) )
(** The type of an argument of shape [t] in [ρ], at the uniform parameters
    [ups] of [p]. *)
with eval_shty (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> domain -> Prop :=
| eval_shty_self :
  `( ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     eval_shty Θ Ξ p ups ρ (pt_self k Ps) (d_ind p (ups ++ bs)) )
| eval_shty_pi :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     eval_shty Θ Ξ p ups ρ (pt_pi B t) (Πᵈ b (nil ↦ d_shfam p ups ρ t) fam_cod) )
(** The type of the recursive result of an argument [v] of shape [t], its
    components in [ρ]: the motive [A] in [ρm] at the shape's non-uniform
    parameters and [v]. *)
with eval_ihty (Θ : gdeps) (Ξ : gstack) : env -> exp -> env -> ptyp -> domain -> domain -> Prop :=
| eval_ihty_self :
  `( ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρm (bs ++ v :: nil) ↘ a ->
     eval_ihty Θ Ξ ρm A ρ (pt_self k Ps) v a )
| eval_ihty_pi :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     eval_ihty Θ Ξ ρm A ρ (pt_pi B t) v (Πᵈ b (nil ↦ d_ihfam ρm A ρ t v) fam_cod) )
with eval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
(** A function's body, at the argument. *)
| eval_app_fn :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ m ->
     $| λᵈ ρ M & n | Θ ⍮ Ξ ↘ m )
(** A neutral applied, at the codomain's instance. *)
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
(** The type former takes a parameter it still lacks. *)
| eval_app_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length as' < ind_np D ->
     $| d_ind p as' & n | Θ ⍮ Ξ ↘ d_ind p (as' ++ n :: nil) )
(** So does a constructor, a parameter or an argument. *)
| eval_app_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length vs < (ind_np D + List.length gs)%nat ->
     $| d_con p c vs & n | Θ ⍮ Ξ ↘ d_con p c (vs ++ n :: nil) )
(** The recursive result of a function shape, at the argument's value. *)
| eval_app_ihfn :
  `( $| f & n | Θ ⍮ Ξ ↘ fn ->
     eval_ih Θ Ξ ρ nm A Bs t fn r ->
     $| d_ihfn ρ nm A Bs t f & n | Θ ⍮ Ξ ↘ r )
(** The families of the types of an argument of a function shape and of its
    recursive result. *)
| eval_app_shfam :
  `( eval_shty Θ Ξ p ups (ρ ↦ n) t a ->
     $| d_shfam p ups ρ t & n | Θ ⍮ Ξ ↘ a )
| eval_app_ihfam :
  `( $| f & n | Θ ⍮ Ξ ↘ fn ->
     eval_ihty Θ Ξ ρm A (ρ ↦ n) t fn a ->
     $| d_ihfam ρm A ρ t f & n | Θ ⍮ Ξ ↘ a )
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
| eval_close_body :
  `( ⟦ Δ ⊢ md_body sm Φ ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_body sm Φ) ρ )
| eval_close_alias :
  `( 0 < List.length Δ ->
     ⟦ Δ ⊢ md_alias E ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_alias E) ρ )
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
| eval_appms_nil :
  `( $ᵐ*| h & nil | Θ ⍮ Ξ ↘ h )
| eval_appms_cons :
  `( $ᵐ| h & n | Θ ⍮ Ξ ↘ h1 ->
     $ᵐ*| h1 & ns | Θ ⍮ Ξ ↘ r ->
     $ᵐ*| h & n :: ns | Θ ⍮ Ξ ↘ r )
where "'$ᵐ*|' h '&' ns '|' Θ '⍮' Ξ '↘' r" := (eval_appms Θ Ξ h ns r)
(** Selecting a term member.  A member of a global module is stored closed,
    over the module's parameters: δ evaluates a transparent one's body in the
    empty environment, and an opaque one or an axiom is a neutral at its
    (closed) type.  Either is then applied to the module's arguments. *)
with eval_sel (Θ : gdeps) (Ξ : gstack) : dmod -> string -> domain -> Prop :=
(** A transparent definition of a global module: its body, applied to the module's arguments. *)
| eval_sel_global :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def true pv A (Some M)) ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ f ->
     $*| f & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
(** An opaque definition or an axiom of a global module: a neutral, applied to the module's arguments. *)
| eval_sel_global_neut :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a ->
     $*| ⇑ a (d_glob (qname_app p (x :: nil))) & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
(** The module of an inductive type, as a term: the type former, applied to
    the module's arguments. *)
| eval_sel_global_ind :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     ind_lookup Θ Ξ (qname_app p (x :: nil)) = Some D ->
     $*| d_ind (qname_app p (x :: nil)) nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
(** An inductive alias, as a term: the type former at its arguments, over
    its telescope. *)
| eval_sel_global_ind_alias :
  `( gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     ind_alias_lookup Θ Ξ (qname_app p (x :: nil)) = Some (Δ, pt, Ns) ->
     ⟦ ctx_fn Δ (apps (a_ind pt) Ns) ⟧ Θ ⍮ Ξ ⍮ nil ↘ f ->
     $*| f & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜ x Θ ⍮ Ξ ↘ r )
(** A member of a closure lacking a parameter is a member closure. *)
| eval_sel_unsat :
  `( 0 < List.length Δ ->
     dm_local Δ D ρ ·ₜ x Θ ⍮ Ξ ↘ d_member (dm_local Δ D ρ) (x :: nil) )
(** A definition of a saturated body, found in the body read through the
    entries its local opens generate: its body, in the environment of the
    body before it. *)
| eval_sel_body :
  `( kbody Θ Ξ ρ Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     ⟦ Φ' ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₜ x Θ ⍮ Ξ ↘ r )
(** A member of a submodule closure extends the chain. *)
| eval_sel_member :
  `( dm_member h ch ·ₜ x Θ ⍮ Ξ ↘ d_member h (ch ++ x :: nil) )
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
(** A submodule of a saturated body, found in the body read through the
    entries its local opens generate: its unit's closure, in the environment
    of the body before it. *)
| eval_selm_body :
  `( kbody Θ Ξ ρ Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pm (gu_mk Δy Dy))) ->
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
with eval_benv (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
(** The empty body adds nothing. *)
| eval_benv_nil :
  `( ⟦ gm_nil ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ )
(** A definition adds its value. *)
| eval_benv_def :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ gm_ext Φ y (ge_def b pv A (Some M)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ m )
(** A submodule adds its unit's closure. *)
| eval_benv_mod :
  `( ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ Δy ⊢ Dy ⟧ᶜ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_mod pm (gu_mk Δy Dy)) ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵐ h )
where "'⟦' Φ '⟧ᵇ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" := (eval_benv Θ Ξ ρ Φ ρ').

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
with eval_benv_mut_ind := Induction for eval_benv Sort Prop
with eval_elim_mut_ind := Induction for eval_elim Sort Prop
with eval_ihs_mut_ind := Induction for eval_ihs Sort Prop
with eval_ih_mut_ind := Induction for eval_ih Sort Prop
with eval_shty_mut_ind := Induction for eval_shty Sort Prop
with eval_ihty_mut_ind := Induction for eval_ihty Sort Prop.
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
  eval_benv_mut_ind,
  eval_elim_mut_ind,
  eval_ihs_mut_ind,
  eval_ih_mut_ind,
  eval_shty_mut_ind,
  eval_ihty_mut_ind.

#[export]
Hint Constructors eval_exp eval_elim eval_ihs eval_ih eval_shty eval_ihty eval_app eval_exps eval_apps eval_modexp eval_close eval_appm eval_appms eval_sel eval_selm
  eval_selc eval_selmc eval_benv : mctt.

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
    term, or the value of a module expression.  Past its end [ρσ] reads the
    term [⋆ᵈ], so a result exists only when, from some index on, every
    [σ x] denotes it, for example as a variable past the end of [ρ]. *)
Definition eval_sentry (Θ : gdeps) (Ξ : gstack) (e : sentry) (ρ : env) (d : dentry) : Prop :=
  match e with
  | se_var y => d = env_entry ρ y
  | se_exp M => exists m, d = de_term m /\ ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m
  | se_mod H => exists h, d = de_mod h /\ ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h
  end.

Definition eval_sub (Θ : gdeps) (Ξ : gstack) (σ : sub) (ρ ρσ : env) : Prop :=
  forall x, eval_sentry Θ Ξ (σ x) ρ (env_entry ρσ x).
Arguments eval_sub : simpl never.

Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" := (eval_sub Θ Ξ σ ρ ρσ) : mctt_scope.

Lemma eval_sub_id : forall {Θ Ξ} ρ, ⟦ Id ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ.
Proof. intros * x; reflexivity. Qed.

Lemma eval_sub_shift : forall {Θ Ξ} ρ, ⟦ Wk ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ↯.
Proof. intros * x; reflexivity. Qed.

Lemma eval_sub_extend : forall {Θ Ξ} σ ρ ρσ M m,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ σ,,M ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H HM [| x]; [ exists m; split; [ reflexivity | assumption ] | apply H ].
Qed.

Lemma eval_sub_extend_mod : forall {Θ Ξ} σ ρ ρσ H h,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ σ ,,ₘ H ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ᵐ h.
Proof.
  intros * Hσ HH [| x]; [ exists h; split; [ reflexivity | assumption ] | apply Hσ ].
Qed.

Corollary eval_sub_single : forall {Θ Ξ} ρ M m,
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ Id,,M ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ m.
Proof.
  intros; apply eval_sub_extend; [ apply eval_sub_id | assumption ].
Qed.

Corollary eval_sub_single_mod : forall {Θ Ξ} ρ H h,
    ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
    ⟦ Id ,,ₘ H ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρ ↦ᵐ h.
Proof.
  intros; apply eval_sub_extend_mod; [ apply eval_sub_id | assumption ].
Qed.

Proposition eval_sub_index : forall {Θ Ξ} σ (ρ ρσ : env),
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    forall x, eval_sentry Θ Ξ (σ x) ρ (env_entry ρσ x).
Proof. intros * H. exact H. Qed.

(** The variables of a term and of a module expression read the entry their
    substitution denotes, at the right sort; at the wrong one both sides read
    the default. *)
Lemma eval_sub_var : forall {Θ Ξ} σ ρ ρσ x,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ #x[σ] ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρσ x.
Proof.
  intros * Hσ; specialize (Hσ x); cbn; unfold env_var.
  destruct (σ x) as [y | M | H]; cbn in Hσ |- *.
  - rewrite Hσ; apply eval_exp_var.
  - destruct Hσ as (m & -> & Hm); exact Hm.
  - destruct Hσ as (h & -> & _); constructor.
Qed.

Lemma eval_sub_mvar : forall {Θ Ξ} σ ρ ρσ x,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ (me_var x)[σ]ᵐ ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ env_mod ρσ x.
Proof.
  intros * Hσ; specialize (Hσ x); cbn; unfold env_mod.
  destruct (σ x) as [y | M | H]; cbn in Hσ |- *.
  - rewrite Hσ; apply eval_me_var.
  - destruct Hσ as (m & -> & _); apply eval_me_unit.
  - destruct Hσ as (h & -> & Hh); exact Hh.
Qed.

(** The substitution and the result environment may be replaced by
    pointwise-equal ones.  The input environment may not, since a closure
    captures it. *)
#[export]
Instance eval_sub_Proper : forall {Θ Ξ}, Proper (sb_eq ==> eq ==> env_eq ==> iff) (eval_sub Θ Ξ).
Proof.
  intros Θ Ξ σ σ' Hσ ρ ρ0 <- ρσ ρσ' Hρσ.
  split; intros H x; [ rewrite <- (Hσ x), <- (Hρσ x) | rewrite (Hσ x), (Hρσ x) ]; apply H.
Qed.

(** ** The Substitutions that Compute

    Evaluation of the substitutions that occur in practice:

    - the image under [ι] of an order-preserving weakening, for which
      [⟪φ⟫ ρ] is [ρ ∘ φ] at every index;
    - weakened extensions and lifts;
    - precomposition by a weakening. *)
Lemma eval_sub_of_wk : forall {Θ Ξ} φ ρ `{Hφ : WkMono φ},
    ⟦ ι φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ⟪φ⟫ ρ.
Proof.
  intros Θ Ξ φ ρ Hφ x; cbn; rewrite (eval_wk_entry _ _ Hφ x); reflexivity.
Qed.

(** A weakened extension. *)
Lemma eval_sub_wk_extend : forall {Θ Ξ} σ M φ ρ ρσ m,
    ⟦ sb_wk σ φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ M[φ]ʷ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    ⟦ sb_wk (σ,,M) φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ↦ m.
Proof. intros * ? ? [| x]; [ exists m; split; [ reflexivity | assumption ] | apply H ]. Qed.

(** A lifted substitution, plain and weakened.  [q σ] extends [σ[↑]] by the
    variable [0], so its head is the entry already in [ρ]. *)
Lemma eval_sub_q : forall {Θ Ξ} σ ρ ρσ,
    ⟦ sb_wk σ ↑ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ q σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρ 0 :: ρσ.
Proof.
  intros * H [| x]; [ reflexivity |].
  rewrite sb_q_succ; exact (H x).
Qed.

Lemma eval_sub_wk_q : forall {Θ Ξ} σ φ ρ ρσ,
    ⟦ sb_wk (sb_wk σ ↑) φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ sb_wk (q σ) φ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ env_entry ρ (φ 0) :: ρσ.
Proof.
  intros * H [| x]; cbn [sb_wk]; [ rewrite sb_q_zero; reflexivity |].
  rewrite sb_q_succ; exact (H x).
Qed.

(** Precomposition by a weakening reindexes the environment [σ] evaluates to. *)
Lemma eval_sub_wk_pre : forall {Θ Ξ} φ σ ρ ρσ `{Hφ : WkMono φ},
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ (ι φ) ⨟ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ⟪φ⟫ ρσ.
Proof.
  intros Θ Ξ φ σ ρ ρσ Hφ H x; rewrite (eval_wk_entry _ _ Hφ x); exact (H (φ x)).
Qed.

Corollary eval_sub_shift_pre : forall {Θ Ξ} σ ρ ρσ,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    ⟦ Wk ⨟ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ↯.
Proof. intros * H x; rewrite env_entry_drop; exact (H (S x)). Qed.

#[export]
Hint Resolve eval_sub_id eval_sub_shift eval_sub_extend eval_sub_extend_mod eval_sub_single
             eval_sub_single_mod eval_sub_wk_extend eval_sub_q eval_sub_wk_q eval_sub_shift_pre : mctt.
#[export]
Hint Resolve eval_sub_index : mctt.
