From Stdlib Require Import Lia List Morphisms String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution GlobalCtx Members.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'⟦' M '⟧' Θ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' ρ '↘' r" (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, Θ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|' Θ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, r at level 69).
Reserved Notation "'⟦' σ '⟧s' Θ '⍮' ρ '↘' ρσ" (at level 70, σ at level 69, Θ at level 69, ρ at level 69, ρσ at level 69).

Reserved Notation "'⟦' H '⟧ᵐ' Θ '⍮' ρ '↘' r" (at level 70, H at level 69, Θ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦' Ms '⟧*' Θ '⍮' ρ '↘' ms" (at level 70, Ms at level 69, Θ at level 69, ρ at level 69, ms at level 69).
Reserved Notation "'$*|' m '&' ns '|' Θ '↘' r" (at level 70, m at level 69, ns at level 69, Θ at level 69, r at level 69).
Reserved Notation "'$ᵐ|' h '&' n '|' Θ '↘' r" (at level 70, h at level 69, n at level 69, Θ at level 69, r at level 69).
Reserved Notation "h '·ₜ' x Θ '↘' r" (at level 70, x at level 0, Θ at level 69, r at level 69).
Reserved Notation "h '·ₘ' y Θ '↘' r" (at level 70, y at level 0, Θ at level 69, r at level 69).
Reserved Notation "h '·ₜ*' ch Θ '↘' r" (at level 70, ch at level 0, Θ at level 69, r at level 69).
Reserved Notation "h '·ₘ*' ch Θ '↘' r" (at level 70, ch at level 0, Θ at level 69, r at level 69).

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
(** A unit closure still lacking an argument. *)
Definition dm_unsat (h : dmod) : Prop :=
  match h with
  | dm_body _ Δ _ args | dm_alias _ Δ _ args => List.length args < List.length Δ
  | dm_member _ _ => False
  end.

Inductive eval_exp (Θ : gctx) : exp -> env -> domain -> Prop :=
(** A universe is its own value. *)
| eval_exp_typ :
  `( ⟦ Type@i ⟧ Θ ⍮ ρ ↘ 𝕌@i )
(** A variable is read off the environment. *)
| eval_exp_var :
  `( ⟦ #x ⟧ Θ ⍮ ρ ↘ ρ x )
(** [ℕ] is a value. *)
| eval_exp_nat :
  `( ⟦ ℕ ⟧ Θ ⍮ ρ ↘ ℕᵈ )
(** So is [zero]. *)
| eval_exp_zero :
  `( ⟦ zero ⟧ Θ ⍮ ρ ↘ zeroᵈ )
(** [succ] of the value of its argument. *)
| eval_exp_succ :
  `( ⟦ M ⟧ Θ ⍮ ρ ↘ m ->
     ⟦ succ M ⟧ Θ ⍮ ρ ↘ succᵈ m )
(** The eliminator evaluates its scrutinee, then recurses on the value. *)
| eval_exp_natrec :
  `( ⟦ M ⟧ Θ ⍮ ρ ↘ m ->
     ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r ->
     ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r )
(** [⊤] is a value. *)
| eval_exp_True :
  `( ⟦ ⊤ ⟧ Θ ⍮ ρ ↘ ⊤ᵈ )
(** So is [⋆]. *)
| eval_exp_true :
  `( ⟦ ⋆ ⟧ Θ ⍮ ρ ↘ ⋆ᵈ )
(** [⊥] is a value. *)
| eval_exp_False :
  `( ⟦ ⊥ ⟧ Θ ⍮ ρ ↘ ⊥ᵈ )
(** [⊥] has no canonical values, so the eliminator only meets a neutral. *)
| eval_exp_exfalso :
  `( ⟦ M ⟧ Θ ⍮ ρ ↘ ⇑ b m ->
     ⟦ A ⟧ Θ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦ efq M return A ⟧ Θ ⍮ ρ ↘ ⇑ a (efqᵈ m under ρ return A) )
(** A [Π] evaluates its domain and closes over its codomain. *)
| eval_exp_pi :
  `( ⟦ A ⟧ Θ ⍮ ρ ↘ a ->
     ⟦ Π A B ⟧ Θ ⍮ ρ ↘ Πᵈ a ρ B )
(** A function closes over its body. *)
| eval_exp_fn :
  `( ⟦ λ A M ⟧ Θ ⍮ ρ ↘ λᵈ ρ M )
(** An application applies the value of the function to that of the argument. *)
| eval_exp_app :
  `( ⟦ M ⟧ Θ ⍮ ρ ↘ m ->
     ⟦ N ⟧ Θ ⍮ ρ ↘ n ->
     $| m & n | Θ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ ρ ↘ r )
(** A local definition extends the environment by the value of its body;
    nothing is substituted. *)
| eval_exp_let :
  `( ⟦ M ⟧ Θ ⍮ ρ ↘ m ->
     ⟦ B ⟧ Θ ⍮ ρ ↦ m ↘ r ->
     ⟦ a_let (b_def oA M) B ⟧ Θ ⍮ ρ ↘ r )
(** A local module extends it by the unit's closure. *)
| eval_exp_let_mod :
  `( ⟦ B ⟧ Θ ⍮ ρ ↦ᵐ dm_of ρ U ↘ r ->
     ⟦ ℓₘ U in B ⟧ Θ ⍮ ρ ↘ r )
(** A member is read off the root of its module expression, then applied to
    the module's arguments: arguments commute with selection.  Without
    arguments this is selection from the module's value. *)
| eval_exp_mem :
  `( modexp_spine H = (R, args, pre) ->
     ⟦ R ⟧ᵐ Θ ⍮ ρ ↘ h ->
     h ·ₜ* (pre ++ x :: nil) Θ ↘ f ->
     ⟦ args ⟧* Θ ⍮ ρ ↘ ns ->
     $*| f & ns | Θ ↘ r ->
     ⟦ a_mem H x ⟧ Θ ⍮ ρ ↘ r )
(** A sealed constant, or an axiom, is a neutral at its type, which is
    closed. *)
| eval_exp_const :
  `( gc_const Θ c = Some (A, oM, b) ->
     b = false \/ oM = None ->
     ⟦ A ⟧ Θ ⍮ nil ↘ a ->
     ⟦ a_const c ⟧ Θ ⍮ ρ ↘ ⇑ a (d_glob c) )
(** An unsealed one is its body, which is closed. *)
| eval_exp_const_unfold :
  `( gc_const Θ c = Some (A, Some M, true) ->
     ⟦ M ⟧ Θ ⍮ nil ↘ r ->
     ⟦ a_const c ⟧ Θ ⍮ ρ ↘ r )
where "'⟦' e '⟧' Θ '⍮' ρ '↘' r" := (eval_exp Θ e ρ r)
with eval_natrec (Θ : gctx) : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
(** At [zero], the base case. *)
| eval_natrec_zero :
  `( ⟦ MZ ⟧ Θ ⍮ ρ ↘ mz ->
     ⟦rec zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ mz )
(** At a successor, the step case on the predecessor and the recursive result. *)
| eval_natrec_succ :
  `( ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r ->
     ⟦ MS ⟧ Θ ⍮ ρ ↦ b ↦ r ↘ ms ->
     ⟦rec succᵈ b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ ms )
(** At a neutral, a neutral at the motive's instance. *)
| eval_natrec_neut :
  `( ⟦ MZ ⟧ Θ ⍮ ρ ↘ mz ->
     ⟦ A ⟧ Θ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦rec ⇑ b m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ ⇑ a recᵈ m under ρ return A | zero -> mz | succ -> MS end )
where "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' ρ '↘' r" := (eval_natrec Θ A MZ MS m ρ r)
with eval_app (Θ : gctx) : domain -> domain -> domain -> Prop :=
(** A function's body, at the argument. *)
| eval_app_fn :
  `( ⟦ M ⟧ Θ ⍮ ρ ↦ n ↘ m ->
     $| λᵈ ρ M & n | Θ ↘ m )
(** A neutral applied, at the codomain's instance. *)
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a ρ B) m & n | Θ ↘ ⇑ b (m $ᵈ ⇓ a n) )
(** A member closure takes the next argument of its module, and selects again. *)
| eval_app_member :
  `( $ᵐ| h & n | Θ ↘ h' ->
     h' ·ₜ* ch Θ ↘ r ->
     $| d_member h ch & n | Θ ↘ r )
where "'$|' m '&' n '|' Θ '↘' r" := (eval_app Θ m n r)
with eval_exps (Θ : gctx) : list exp -> env -> list domain -> Prop :=
(** No terms. *)
| eval_exps_nil :
  `( ⟦ nil ⟧* Θ ⍮ ρ ↘ nil )
(** A term, then the rest. *)
| eval_exps_cons :
  `( ⟦ M ⟧ Θ ⍮ ρ ↘ m ->
     ⟦ Ms ⟧* Θ ⍮ ρ ↘ ms ->
     ⟦ M :: Ms ⟧* Θ ⍮ ρ ↘ m :: ms )
where "'⟦' Ms '⟧*' Θ '⍮' ρ '↘' ms" := (eval_exps Θ Ms ρ ms)
with eval_apps (Θ : gctx) : domain -> list domain -> domain -> Prop :=
(** No arguments. *)
| eval_apps_nil :
  `( $*| m & nil | Θ ↘ m )
(** The first argument, then the rest. *)
| eval_apps_cons :
  `( $| m & n | Θ ↘ m1 ->
     $*| m1 & args | Θ ↘ r ->
     $*| m & n :: args | Θ ↘ r )
where "'$*|' m '&' ns '|' Θ '↘' r" := (eval_apps Θ m ns r)
with eval_modexp (Θ : gctx) : modexp -> env -> dmod -> Prop :=
(** A module slot is read off the environment. *)
| eval_me_var :
  `( ⟦ me_var x ⟧ᵐ Θ ⍮ ρ ↘ env_mod ρ x )
(** A unit is the closure of the unit filed under its path, which is
    closed. *)
| eval_me_unit :
  `( gc_unit Θ fp = Some U ->
     ⟦ me_unit fp ⟧ᵐ Θ ⍮ ρ ↘ dm_of nil U )
(** A literal unit is its closure, with no argument yet. *)
| eval_me_lit :
  `( ⟦ me_lit U ⟧ᵐ Θ ⍮ ρ ↘ dm_of ρ U )
(** A submodule is selected from the module's value. *)
| eval_me_mem :
  `( ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h ->
     h ·ₘ y Θ ↘ r ->
     ⟦ me_mem H y ⟧ᵐ Θ ⍮ ρ ↘ r )
(** An application adds the argument's value to the module's. *)
| eval_me_app :
  `( ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h ->
     ⟦ N ⟧ Θ ⍮ ρ ↘ n ->
     $ᵐ| h & n | Θ ↘ r ->
     ⟦ me_app H N ⟧ᵐ Θ ⍮ ρ ↘ r )
where "'⟦' H '⟧ᵐ' Θ '⍮' ρ '↘' r" := (eval_modexp Θ H ρ r)
(** Applying a module value to one more argument, which it must still lack.
    A saturated alias is its target. *)
with eval_appm (Θ : gctx) : dmod -> domain -> dmod -> Prop :=
(** A body unit lacking arguments records it. *)
| eval_appm_body :
  `( List.length args < List.length Δ ->
     $ᵐ| dm_body ρ Δ Φ args & n | Θ ↘ dm_body ρ Δ Φ (args ++ n :: nil) )
(** So does an alias unit lacking arguments. *)
| eval_appm_alias_unsat :
  `( List.length args < List.length Δ ->
     $ᵐ| dm_alias ρ Δ E args & n | Θ ↘ dm_alias ρ Δ E (args ++ n :: nil) )
(** A saturated alias passes it to its target. *)
| eval_appm_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐ Θ ⍮ env_args ρ args ↘ h ->
     $ᵐ| h & n | Θ ↘ r ->
     $ᵐ| dm_alias ρ Δ E args & n | Θ ↘ r )
(** A submodule of an unsaturated module passes it to the module, then selects again. *)
| eval_appm_member :
  `( $ᵐ| h & n | Θ ↘ h' ->
     h' ·ₘ* ch Θ ↘ r ->
     $ᵐ| dm_member h ch & n | Θ ↘ r )
where "'$ᵐ|' h '&' n '|' Θ '↘' r" := (eval_appm Θ h n r)
(** Selecting a term member.  Selection is lazy: a definition of a
    saturated body is its body, evaluated with its self slot bound to the
    closure of the body before it, over the arguments; nothing else of the
    body is evaluated. *)
with eval_sel (Θ : gctx) : dmod -> string -> domain -> Prop :=
(** A member of an unsaturated module is a member closure. *)
| eval_sel_unsat :
  `( dm_unsat h ->
     h ·ₜ x Θ ↘ d_member h (x :: nil) )
(** A definition of a saturated body: its body, under its self slot. *)
| eval_sel_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def pv A (Some M))) ->
     ⟦ M ⟧ Θ ⍮ env_args ρ args ↦ᵐ dm_body (env_args ρ args) nil Φ' nil ↘ r ->
     dm_body ρ Δ Φ args ·ₜ x Θ ↘ r )
(** A member of a saturated alias is selected from its target. *)
| eval_sel_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐ Θ ⍮ env_args ρ args ↘ h ->
     h ·ₜ x Θ ↘ r ->
     dm_alias ρ Δ E args ·ₜ x Θ ↘ r )
(** A member of a submodule closure extends the chain. *)
| eval_sel_member :
  `( dm_member h ch ·ₜ x Θ ↘ d_member h (ch ++ x :: nil) )
where "h '·ₜ' x Θ '↘' r" := (eval_sel Θ h x r)
(** Selecting a submodule. *)
with eval_selm (Θ : gctx) : dmod -> string -> dmod -> Prop :=
(** A submodule of an unsaturated module is a submodule closure. *)
| eval_selm_unsat :
  `( dm_unsat h ->
     h ·ₘ y Θ ↘ dm_member h (y :: nil) )
(** A submodule of a saturated body is its unit's closure, under its self
    slot. *)
| eval_selm_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     dm_body ρ Δ Φ args ·ₘ y Θ ↘ dm_of (env_args ρ args ↦ᵐ dm_body (env_args ρ args) nil Φ' nil) Uy )
(** A submodule of a saturated alias is selected from its target. *)
| eval_selm_alias :
  `( List.length args = List.length Δ ->
     ⟦ E ⟧ᵐ Θ ⍮ env_args ρ args ↘ h ->
     h ·ₘ y Θ ↘ r ->
     dm_alias ρ Δ E args ·ₘ y Θ ↘ r )
(** A submodule of a submodule closure extends the chain. *)
| eval_selm_member :
  `( dm_member h ch ·ₘ y Θ ↘ dm_member h (ch ++ y :: nil) )
where "h '·ₘ' y Θ '↘' r" := (eval_selm Θ h y r)
(** Selecting along a chain: submodules, then a term member. *)
with eval_selc (Θ : gctx) : dmod -> list string -> domain -> Prop :=
(** The last selection is a term member. *)
| eval_selc_one :
  `( h ·ₜ x Θ ↘ r ->
     h ·ₜ* (x :: nil) Θ ↘ r )
(** The ones before it are submodules. *)
| eval_selc_cons :
  `( h ·ₘ y Θ ↘ h1 ->
     h1 ·ₜ* ch Θ ↘ r ->
     h ·ₜ* (y :: ch) Θ ↘ r )
where "h '·ₜ*' ch Θ '↘' r" := (eval_selc Θ h ch r)
with eval_selmc (Θ : gctx) : dmod -> list string -> dmod -> Prop :=
(** The empty chain is the module itself. *)
| eval_selmc_nil :
  `( h ·ₘ* nil Θ ↘ h )
(** A submodule, then the rest of the chain. *)
| eval_selmc_cons :
  `( h ·ₘ y Θ ↘ h1 ->
     h1 ·ₘ* ch Θ ↘ r ->
     h ·ₘ* (y :: ch) Θ ↘ r )
where "h '·ₘ*' ch Θ '↘' r" := (eval_selmc Θ h ch r).

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_exps_mut_ind := Induction for eval_exps Sort Prop
with eval_apps_mut_ind := Induction for eval_apps Sort Prop
with eval_modexp_mut_ind := Induction for eval_modexp Sort Prop
with eval_appm_mut_ind := Induction for eval_appm Sort Prop
with eval_sel_mut_ind := Induction for eval_sel Sort Prop
with eval_selm_mut_ind := Induction for eval_selm Sort Prop
with eval_selc_mut_ind := Induction for eval_selc Sort Prop
with eval_selmc_mut_ind := Induction for eval_selmc Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_natrec_mut_ind,
  eval_app_mut_ind,
  eval_exps_mut_ind,
  eval_apps_mut_ind,
  eval_modexp_mut_ind,
  eval_appm_mut_ind,
  eval_sel_mut_ind,
  eval_selm_mut_ind,
  eval_selc_mut_ind,
  eval_selmc_mut_ind.

#[export]
Hint Constructors eval_exp eval_natrec eval_app eval_exps eval_apps eval_modexp eval_appm eval_sel eval_selm
  eval_selc eval_selmc : mctt.

(** [eval_exp_var] with the value as a premise.  The value [ρ x] is a flexible
    application, so unifying against it directly can pick the wrong [ρ] and
    [x]. *)
Proposition eval_exp_var_eq : forall {Θ} x (ρ : env) m,
    ρ x = m ->
    ⟦ #x ⟧ Θ ⍮ ρ ↘ m.
Proof. intros * <-; apply eval_exp_var. Qed.

(** * Evaluation of Substitutions

    Evaluation of a substitution is pointwise: at every variable [x], [ρσ x]
    is the entry [σ x] denotes in [ρ]: the entry of a variable, the value of a
    term, or the value of a module expression.  Past its end [ρσ] reads the
    term [zeroᵈ], so a result exists only when, from some index on, every
    [σ x] denotes it, for example as a variable past the end of [ρ]. *)
Definition eval_sentry (Θ : gctx) (e : sentry) (ρ : env) (d : dentry) : Prop :=
  match e with
  | se_var y => d = env_entry ρ y
  | se_exp M => exists m, d = de_term m /\ ⟦ M ⟧ Θ ⍮ ρ ↘ m
  | se_mod H => exists h, d = de_mod h /\ ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h
  end.

Definition eval_sub (Θ : gctx) (σ : sub) (ρ ρσ : env) : Prop :=
  forall x, eval_sentry Θ (σ x) ρ (env_entry ρσ x).
Arguments eval_sub : simpl never.

Notation "'⟦' σ '⟧s' Θ '⍮' ρ '↘' ρσ" := (eval_sub Θ σ ρ ρσ) : mctt_scope.

Lemma eval_sub_id : forall {Θ} ρ, ⟦ Id ⟧s Θ ⍮ ρ ↘ ρ.
Proof. intros * x; reflexivity. Qed.

Lemma eval_sub_shift : forall {Θ} ρ, ⟦ Wk ⟧s Θ ⍮ ρ ↘ ρ↯.
Proof. intros * x; reflexivity. Qed.

Lemma eval_sub_extend : forall {Θ} σ ρ ρσ M m,
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ M ⟧ Θ ⍮ ρ ↘ m ->
    ⟦ σ,,M ⟧s Θ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H HM [| x]; [ exists m; split; [ reflexivity | assumption ] | apply H ].
Qed.

Lemma eval_sub_extend_mod : forall {Θ} σ ρ ρσ H h,
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h ->
    ⟦ σ ,,ₘ H ⟧s Θ ⍮ ρ ↘ ρσ ↦ᵐ h.
Proof.
  intros * Hσ HH [| x]; [ exists h; split; [ reflexivity | assumption ] | apply Hσ ].
Qed.

Corollary eval_sub_single : forall {Θ} ρ M m,
    ⟦ M ⟧ Θ ⍮ ρ ↘ m ->
    ⟦ Id,,M ⟧s Θ ⍮ ρ ↘ ρ ↦ m.
Proof.
  intros; apply eval_sub_extend; [ apply eval_sub_id | assumption ].
Qed.

Corollary eval_sub_single_mod : forall {Θ} ρ H h,
    ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h ->
    ⟦ Id ,,ₘ H ⟧s Θ ⍮ ρ ↘ ρ ↦ᵐ h.
Proof.
  intros; apply eval_sub_extend_mod; [ apply eval_sub_id | assumption ].
Qed.

Proposition eval_sub_intro : forall {Θ} σ (ρ ρσ : env),
    (forall x, eval_sentry Θ (σ x) ρ (env_entry ρσ x)) ->
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ.
Proof. intros * H. exact H. Qed.

Proposition eval_sub_index : forall {Θ} σ (ρ ρσ : env),
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ ->
    forall x, eval_sentry Θ (σ x) ρ (env_entry ρσ x).
Proof. intros * H. exact H. Qed.

(** The variables of a term and of a module expression read the entry their
    substitution denotes, at the right sort; at the wrong one both sides read
    the default. *)
Lemma eval_sub_var : forall {Θ} σ ρ ρσ x,
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ #x[σ] ⟧ Θ ⍮ ρ ↘ ρσ x.
Proof.
  intros * Hσ; specialize (Hσ x); cbn; unfold env_var.
  destruct (σ x) as [y | M | H]; cbn in Hσ |- *.
  - rewrite Hσ; apply eval_exp_var.
  - destruct Hσ as (m & -> & Hm); exact Hm.
  - destruct Hσ as (h & -> & _); constructor.
Qed.

(** For a module variable: the entry it denotes, or, if its substitution
    sends it to a term, the empty literal against the default. *)
Lemma eval_sub_mvar : forall {Θ} σ ρ ρσ x,
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ ->
    (⟦ (me_var x)[σ]ᵐ ⟧ᵐ Θ ⍮ ρ ↘ env_mod ρσ x) \/
    (⟦ (me_var x)[σ]ᵐ ⟧ᵐ Θ ⍮ ρ ↘ dm_body ρ nil gm_nil nil /\ env_mod ρσ x = dm_default).
Proof.
  intros * Hσ; specialize (Hσ x); cbn; unfold env_mod.
  destruct (σ x) as [y | M | H]; cbn in Hσ |- *.
  - left; rewrite Hσ; apply eval_me_var.
  - right; destruct Hσ as (m & -> & _); split; [ apply eval_me_lit | reflexivity ].
  - left; destruct Hσ as (h & -> & Hh); exact Hh.
Qed.

(** The substitution and the result environment may be replaced by
    pointwise-equal ones.  The input environment may not, since a closure
    captures it. *)
#[export]
Instance eval_sub_Proper : forall {Θ}, Proper (sb_eq ==> eq ==> env_eq ==> iff) (eval_sub Θ).
Proof.
  intros Θ σ σ' Hσ ρ ρ0 <- ρσ ρσ' Hρσ.
  split; intros H x; [ rewrite <- (Hσ x), <- (Hρσ x) | rewrite (Hσ x), (Hρσ x) ]; apply H.
Qed.

(** ** The Substitutions that Compute

    Evaluation of the substitutions that occur in practice:

    - the image under [ι] of an order-preserving weakening, for which
      [⟪φ⟫ ρ] is [ρ ∘ φ] at every index;
    - weakened extensions and lifts;
    - precomposition by a weakening. *)
Lemma eval_sub_of_wk : forall {Θ} φ ρ `{Hφ : WkMono φ},
    ⟦ ι φ ⟧s Θ ⍮ ρ ↘ ⟪φ⟫ ρ.
Proof.
  intros Θ φ ρ Hφ x; cbn; rewrite (eval_wk_entry _ _ Hφ x); reflexivity.
Qed.

(** A weakened extension. *)
Lemma eval_sub_wk_extend : forall {Θ} σ M φ ρ ρσ m,
    ⟦ sb_wk σ φ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ M[φ]ʷ ⟧ Θ ⍮ ρ ↘ m ->
    ⟦ sb_wk (σ,,M) φ ⟧s Θ ⍮ ρ ↘ ρσ ↦ m.
Proof. intros * ? ? [| x]; [ exists m; split; [ reflexivity | assumption ] | apply H ]. Qed.

(** A lifted substitution, plain and weakened.  [q σ] extends [σ[↑]] by the
    variable [0], so its head is the entry already in [ρ]. *)
Lemma eval_sub_q : forall {Θ} σ ρ ρσ,
    ⟦ sb_wk σ ↑ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ q σ ⟧s Θ ⍮ ρ ↘ env_entry ρ 0 :: ρσ.
Proof.
  intros * H [| x]; [ reflexivity |].
  rewrite sb_q_succ; exact (H x).
Qed.

Lemma eval_sub_wk_q : forall {Θ} σ φ ρ ρσ,
    ⟦ sb_wk (sb_wk σ ↑) φ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ sb_wk (q σ) φ ⟧s Θ ⍮ ρ ↘ env_entry ρ (φ 0) :: ρσ.
Proof.
  intros * H [| x]; cbn [sb_wk]; [ rewrite sb_q_zero; reflexivity |].
  rewrite sb_q_succ; exact (H x).
Qed.

(** Precomposition by a weakening reindexes the environment [σ] evaluates to. *)
Lemma eval_sub_wk_pre : forall {Θ} φ σ ρ ρσ `{Hφ : WkMono φ},
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ (ι φ) ⨟ σ ⟧s Θ ⍮ ρ ↘ ⟪φ⟫ ρσ.
Proof.
  intros Θ φ σ ρ ρσ Hφ H x; rewrite (eval_wk_entry _ _ Hφ x); exact (H (φ x)).
Qed.

Corollary eval_sub_shift_pre : forall {Θ} σ ρ ρσ,
    ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ ->
    ⟦ Wk ⨟ σ ⟧s Θ ⍮ ρ ↘ ρσ↯.
Proof. intros * H x; rewrite env_entry_drop; exact (H (S x)). Qed.

#[export]
Hint Resolve eval_sub_id eval_sub_shift eval_sub_extend eval_sub_extend_mod eval_sub_single
             eval_sub_single_mod eval_sub_wk_extend eval_sub_q eval_sub_wk_q eval_sub_shift_pre : mctt.
#[export]
Hint Resolve eval_sub_index : mctt.
