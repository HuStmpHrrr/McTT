From Stdlib Require Import Lia List Morphisms String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution GlobalCtx Members.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'⟦' M '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' ρ '↘' ρσ" (at level 70, σ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρσ at level 69).

Reserved Notation "'⟦' H '⟧ᵐ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, H at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).

Generalizable All Variables.

(** * Evaluation of Expressions

    The relations are mutually defined: evaluation of terms, its
    [ℕ]-eliminator case and semantic application; evaluation of module
    expressions and the operations on module values (application, selection
    of a submodule or a member, along a chain); and the environment a body
    unit's members see.  All are relative to the global context [Θ ⍮ Ξ],
    which does not change during NbE.  A global is resolved by lookup in
    [Θ ⍮ Ξ]: a transparent definition unfolds to its body, and any other global
    is a neutral at its type.  No rule applies a syntactic operation such as
    substitution to a term, and none builds syntax.

    A module value is saturated when it has as many arguments as its unit has
    parameters.  Selection on a saturated module is [δ]: it gives the bound
    value, by evaluating the body up to the member, or by selecting from the
    alias's target.  Selection on an unsaturated one gives a member closure
    ([d_member], [dm_member]), which the remaining arguments complete.  A global
    module needs neither: its members are stored generalized over its
    parameters, so selection applies the generalized member to the arguments
    there are. *)
Inductive eval_exp (Θ : gdeps) (Ξ : gstack) : exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( ⟦ Type@i ⟧ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌@i )
| eval_exp_var :
  `( ⟦ #x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ρ x )
| eval_exp_nat :
  `( ⟦ ℕ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ℕᵈ )
| eval_exp_zero :
  `( ⟦ zero ⟧ Θ ⍮ Ξ ⍮ ρ ↘ zeroᵈ )
| eval_exp_succ :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ succᵈ m )
| eval_exp_natrec :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
| eval_exp_True :
  `( ⟦ ⊤ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⊤ᵈ )
| eval_exp_true :
  `( ⟦ ⋆ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ )
| eval_exp_False :
  `( ⟦ ⊥ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⊥ᵈ )
(** [⊥] has no canonical values, so the eliminator only meets a neutral. *)
| eval_exp_exfalso :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ b m ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦ efq M return A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (efqᵈ m under ρ return A) )
| eval_exp_pi :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ Π A B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ a ρ B )
| eval_exp_fn :
  `( ⟦ λ A M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ λᵈ ρ M )
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
     ⟦ ℓ A ≔ M in B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local module extends it by the unit's closure. *)
| eval_exp_let_mod :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ᵐ dm_local ρ U nil ↘ r ->
     ⟦ ℓₘ U in B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
| eval_exp_mem :
  `( ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     eval_sel Θ Ξ h x r ->
     ⟦ a_mem H x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** δ: a transparent definition evaluates to its body.  The body is stored
    closed, so it is evaluated in the empty environment. *)
| eval_exp_glob_delta :
  `( gc_resolve Θ Ξ p = Some (ge_def true pv A (Some M)) ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ m ->
     ⟦ a_glob p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m )
(** An opaque definition or an axiom stays a neutral at its (closed) type. *)
| eval_exp_glob_neut :
  `( gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a ->
     ⟦ a_glob p ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_glob p) )
where "'⟦' e '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_exp Θ Ξ e ρ r)
with eval_natrec (Θ : gdeps) (Ξ : gstack) : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦rec zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz )
| eval_natrec_succ :
  `( ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ MS ⟧ Θ ⍮ Ξ ⍮ ρ ↦ b ↦ r ↘ ms ->
     ⟦rec succᵈ b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ms )
| eval_natrec_neut :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ ρ ↘ mz ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦rec ⇑ b m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a recᵈ m under ρ return A | zero -> mz | succ -> MS end )
where "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_natrec Θ Ξ A MZ MS m ρ r)
with eval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ m ->
     $| λᵈ ρ M & n | Θ ⍮ Ξ ↘ m )
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
(** A member closure takes the next argument of its module, and selects again. *)
| eval_app_member :
  `( eval_appm Θ Ξ h n h' ->
     eval_selc Θ Ξ h' ch r ->
     $| d_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" := (eval_app Θ Ξ m n r)
with eval_apps (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> domain -> Prop :=
| eval_apps_nil :
  `( eval_apps Θ Ξ m nil m )
| eval_apps_cons :
  `( $| m & n | Θ ⍮ Ξ ↘ m1 ->
     eval_apps Θ Ξ m1 args r ->
     eval_apps Θ Ξ m (n :: args) r )
with eval_modexp (Θ : gdeps) (Ξ : gstack) : modexp -> env -> dmod -> Prop :=
| eval_me_var :
  `( ⟦ me_var x ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ env_mod ρ x )
(** A path names a global body module, unless it reaches an alias, which is
    the value of its target. *)
| eval_me_path :
  `( (forall U r, gc_module Θ Ξ p <> Some (mr_alias U r)) ->
     ⟦ me_path p ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global p nil )
| eval_me_path_alias :
  `( gc_module Θ Ξ p = Some (mr_alias U ch) ->
     eval_selmc Θ Ξ (dm_local nil U nil) ch h ->
     ⟦ me_path p ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h )
| eval_me_lit :
  `( ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_local ρ U nil )
| eval_me_mem :
  `( ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     eval_selm Θ Ξ h y r ->
     ⟦ me_mem H y ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ r )
| eval_me_app :
  `( ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     eval_appm Θ Ξ h n r ->
     ⟦ me_app H N ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' H '⟧ᵐ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (eval_modexp Θ Ξ H ρ r)
(** Applying a module value to one more argument.  A saturated alias is its
    target. *)
with eval_appm (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> dmod -> Prop :=
| eval_appm_global :
  `( eval_appm Θ Ξ (dm_global p args) n (dm_global p (args ++ n :: nil)) )
| eval_appm_body :
  `( eval_appm Θ Ξ (dm_local ρ (gu_body Δ Φ) args) n (dm_local ρ (gu_body Δ Φ) (args ++ n :: nil)) )
| eval_appm_alias_unsat :
  `( List.length args < List.length Δ ->
     eval_appm Θ Ξ (dm_local ρ (gu_mk Δ (md_alias E)) args) n
       (dm_local ρ (gu_mk Δ (md_alias E)) (args ++ n :: nil)) )
| eval_appm_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐ Θ ⍮ Ξ ⍮ env_args ρ args ↘ h ->
     eval_appm Θ Ξ h n r ->
     eval_appm Θ Ξ (dm_local ρ (gu_mk Δ (md_alias E)) args) n r )
| eval_appm_member :
  `( eval_appm Θ Ξ h n h' ->
     eval_selmc Θ Ξ h' ch r ->
     eval_appm Θ Ξ (dm_member h ch) n r )
(** Selecting a term member. *)
with eval_sel (Θ : gdeps) (Ξ : gstack) : dmod -> string -> domain -> Prop :=
| eval_sel_global :
  `( ⟦ a_glob (path_app p (x :: nil)) ⟧ Θ ⍮ Ξ ⍮ nil ↘ f ->
     eval_apps Θ Ξ f args r ->
     eval_sel Θ Ξ (dm_global p args) x r )
| eval_sel_unsat :
  `( List.length args < List.length (gu_params U) ->
     eval_sel Θ Ξ (dm_local ρ U args) x (d_member (dm_local ρ U args) (x :: nil)) )
| eval_sel_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     eval_benv Θ Ξ (env_args ρ args) Φ' ρ' ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     eval_sel Θ Ξ (dm_local ρ (gu_body Δ Φ) args) x r )
| eval_sel_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐ Θ ⍮ Ξ ⍮ env_args ρ args ↘ h ->
     eval_sel Θ Ξ h x r ->
     eval_sel Θ Ξ (dm_local ρ (gu_mk Δ (md_alias E)) args) x r )
| eval_sel_member :
  `( eval_sel Θ Ξ (dm_member h ch) x (d_member h (ch ++ x :: nil)) )
(** Selecting a submodule. *)
with eval_selm (Θ : gdeps) (Ξ : gstack) : dmod -> string -> dmod -> Prop :=
| eval_selm_global :
  `( (forall U r, gc_module Θ Ξ (path_app p (y :: nil)) <> Some (mr_alias U r)) ->
     eval_selm Θ Ξ (dm_global p args) y (dm_global (path_app p (y :: nil)) args) )
| eval_selm_global_alias :
  `( gc_module Θ Ξ (path_app p (y :: nil)) = Some (mr_alias U ch) ->
     eval_selmc Θ Ξ (dm_local nil U args) ch r ->
     eval_selm Θ Ξ (dm_global p args) y r )
| eval_selm_unsat :
  `( List.length args < List.length (gu_params U) ->
     eval_selm Θ Ξ (dm_local ρ U args) y (dm_member (dm_local ρ U args) (y :: nil)) )
| eval_selm_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
     eval_benv Θ Ξ (env_args ρ args) Φ' ρ' ->
     eval_selm Θ Ξ (dm_local ρ (gu_body Δ Φ) args) y (dm_local ρ' Uy nil) )
| eval_selm_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐ Θ ⍮ Ξ ⍮ env_args ρ args ↘ h ->
     eval_selm Θ Ξ h y r ->
     eval_selm Θ Ξ (dm_local ρ (gu_mk Δ (md_alias E)) args) y r )
| eval_selm_member :
  `( eval_selm Θ Ξ (dm_member h ch) y (dm_member h (ch ++ y :: nil)) )
(** Selecting along a chain: submodules, then a term member. *)
with eval_selc (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> domain -> Prop :=
| eval_selc_one :
  `( eval_sel Θ Ξ h x r ->
     eval_selc Θ Ξ h (x :: nil) r )
| eval_selc_cons :
  `( eval_selm Θ Ξ h y h1 ->
     eval_selc Θ Ξ h1 ch r ->
     eval_selc Θ Ξ h (y :: ch) r )
with eval_selmc (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> dmod -> Prop :=
| eval_selmc_nil :
  `( eval_selmc Θ Ξ h nil h )
| eval_selmc_cons :
  `( eval_selm Θ Ξ h y h1 ->
     eval_selmc Θ Ξ h1 ch r ->
     eval_selmc Θ Ξ h (y :: ch) r )
(** The environment the members of a body see after its entries [Φ]: each
    definition adds its value and each module its closure. *)
with eval_benv (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
| eval_benv_nil :
  `( eval_benv Θ Ξ ρ gm_nil ρ )
| eval_benv_def :
  `( eval_benv Θ Ξ ρ Φ ρ1 ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     eval_benv Θ Ξ ρ (gm_ext Φ y (ge_def b pv A (Some M))) (ρ1 ↦ m) )
| eval_benv_mod :
  `( eval_benv Θ Ξ ρ Φ ρ1 ->
     eval_benv Θ Ξ ρ (gm_ext Φ y (ge_mod Uy)) (ρ1 ↦ᵐ dm_local ρ1 Uy nil) )
| eval_benv_check :
  `( eval_benv Θ Ξ ρ Φ ρ1 ->
     eval_benv Θ Ξ ρ (gm_check Φ c) ρ1 )
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_apps_mut_ind := Induction for eval_apps Sort Prop
with eval_modexp_mut_ind := Induction for eval_modexp Sort Prop
with eval_appm_mut_ind := Induction for eval_appm Sort Prop
with eval_sel_mut_ind := Induction for eval_sel Sort Prop
with eval_selm_mut_ind := Induction for eval_selm Sort Prop
with eval_selc_mut_ind := Induction for eval_selc Sort Prop
with eval_selmc_mut_ind := Induction for eval_selmc Sort Prop
with eval_benv_mut_ind := Induction for eval_benv Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_natrec_mut_ind,
  eval_app_mut_ind,
  eval_apps_mut_ind,
  eval_modexp_mut_ind,
  eval_appm_mut_ind,
  eval_sel_mut_ind,
  eval_selm_mut_ind,
  eval_selc_mut_ind,
  eval_selmc_mut_ind,
  eval_benv_mut_ind.

#[export]
Hint Constructors eval_exp eval_natrec eval_app eval_apps eval_modexp eval_appm eval_sel eval_selm
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
    term [zeroᵈ], so a result exists only when, from some index on, every
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

Proposition eval_sub_intro : forall {Θ Ξ} σ (ρ ρσ : env),
    (forall x, eval_sentry Θ Ξ (σ x) ρ (env_entry ρσ x)) ->
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ.
Proof. intros * H. exact H. Qed.

Proposition eval_sub_index : forall {Θ Ξ} σ (ρ ρσ : env),
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
    forall x, eval_sentry Θ Ξ (σ x) ρ (env_entry ρσ x).
Proof. intros * H. exact H. Qed.

(** The path [p_abs nil nil], the default of [sentry_modexp], is never an
    alias, so it evaluates to the default module value. *)
Lemma gs_find_tele_default : forall Ξ U ip T, gs_find_tele Ξ (p_abs nil nil) = Some (U, ip, T) -> ip = nil.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn [gs_find_tele] in H; [ discriminate |].
  unfold path_strip in H; destruct (path_beq _ _); [| eapply IH; exact H ].
  destruct (p_mems mp) as [| z l]; cbn in H; [ injection H as _ <- _; reflexivity |].
  eapply IH; exact H.
Qed.

Lemma gc_module_default : forall Θ Ξ U r, gc_module Θ Ξ (p_abs nil nil) <> Some (mr_alias U r).
Proof.
  intros * H; unfold gc_module in H.
  destruct (gs_find_tele Ξ (p_abs nil nil)) as [[[V ip] T] |] eqn:E.
  - rewrite (gs_find_tele_default _ _ _ _ E) in H; discriminate.
  - destruct (gds_lookup Θ (p_unit (p_abs nil nil))); cbn in H; discriminate.
Qed.

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
  - destruct Hσ as (m & -> & _); apply eval_me_path, gc_module_default.
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
