From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastEval Kinds.
From Mctt.Extraction Require Export Lookup.
Import Domain_Notations.

Generalizable All Variables.

(** * The Evaluator the Checker Runs

    The evaluator of the relation of [Extraction.FastEval]: the reference one
    ([Reference.Evaluation]) but for the eliminator of an inductive type,
    which at a constructor does not compute a recursive result that the
    branch does not read, one recursive argument at a time. *)

(** The termination orders mirror the evaluation relations, one for each, in
    the same global context.  A transparent global recurses into its resolved
    body, which [feeo_glob_delta] records; an alias recurses into its target.
    Each premise that uses a value is quantified over the values its earlier
    premises evaluate to. *)

Inductive feval_exp_order (Θ : gdeps) (Ξ : gstack) : exp -> env -> Prop :=
| feeo_typ :
  `( feval_exp_order Θ Ξ Typeω@i p )
(** A small universe evaluates its level. *)
| feeo_univ :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ Type⟨M⟩ p )
(** An environment is total, so a variable always terminates. *)
| feeo_var :
  `( feval_exp_order Θ Ξ #x p )
| feeo_level :
  `( feval_exp_order Θ Ξ (Level@n) p )
| feeo_llit :
  `( feval_exp_order Θ Ξ (𝕃ᵒ o) p )
| feeo_succl :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ (succl M) p )
| feeo_maxl :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ N p ->
     feval_exp_order Θ Ξ (maxl M N) p )
| feeo_True :
  `( feval_exp_order Θ Ξ ⊤ p )
| feeo_true :
  `( feval_exp_order Θ Ξ ⋆ p )
| feeo_False :
  `( feval_exp_order Θ Ξ ⊥ p )
(** The scrutinee of [efq] must evaluate to a neutral, since no other value
    has a rule. *)
| feeo_exfalso :
  `( feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> exists b n, m = ⇑ b n) ->
     (forall b m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ⇑ b m -> feval_exp_order Θ Ξ A (p ↦ ⇑ b m)) ->
     feval_exp_order Θ Ξ (efq M return A) p )
| feeo_pi :
  `( feval_exp_order Θ Ξ A p ->
     feval_exp_order Θ Ξ (Π A B) p )
| feeo_indty :
  `( feval_exp_order Θ Ξ (a_ind pq) p )
| feeo_con :
  `( feval_exp_order Θ Ξ (a_con pq c) p )
| feeo_elim :
  `( feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> feval_elim_order Θ Ξ p nm A Bs m) ->
     feval_exp_order Θ Ξ (a_elim nm A Bs M) p )
| feeo_fn :
  `( feval_exp_order Θ Ξ (λ A M) p )
| feeo_app :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ N p ->
     (forall m n, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n -> feval_app_order Θ Ξ m n) ->
     feval_exp_order Θ Ξ (M $ N) p )
| feeo_let :
  `( feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> feval_exp_order Θ Ξ B (p ↦ m)) ->
     feval_exp_order Θ Ξ (a_let (b_def oA M) B) p )
| feeo_let_mod :
  `( feval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_exp_order Θ Ξ B (p ↦ᵐ h)) ->
     feval_exp_order Θ Ξ (ℓₘ (gu_mk Δ D) in B) p )
| feeo_mem :
  `( modexp_spine H = (R, args, pre) ->
     feval_modexp_order Θ Ξ R p ->
     (forall h, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_selc_order Θ Ξ h (pre ++ x :: nil)) ->
     feval_exps_order Θ Ξ args p ->
     (forall h f ns, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> h ·ₜ*ᶠ (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
        ⟦ args ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ns -> feval_apps_order Θ Ξ f ns) ->
     feval_exp_order Θ Ξ (a_mem H x) p )

with feval_elim_order (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> domain -> Prop :=
| feelo_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_con D c = Some gs ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     brs_lookup Bs c = Some (n, B) ->
     n = (ind_nn D + List.length gs + cargs_nrec gs)%nat ->
     feval_ihs_order Θ Ξ p nm A Bs B gs (skipn (ind_np D) vs) ->
     (forall ihs, ⟦ihsᶠ skipn (ind_np D) vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs ->
        feval_exp_order Θ Ξ B (env_args p (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs))) ->
     feval_elim_order Θ Ξ p nm A Bs (d_con pq c vs) )
| feelo_neut :
  `( ind_lookup Θ Ξ pq = Some D ->
     List.length as' = ind_np D ->
     nm = S (ind_nn D) ->
     feval_exp_order Θ Ξ A (env_args p (skipn (ind_nu D) as' ++ ⇑ (d_ind pq as') m :: nil)) ->
     feval_elim_order Θ Ξ p nm A Bs (⇑ (d_ind pq as') m) )

with feval_ihs_order (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> exp -> list carg -> list domain -> Prop :=
| feiho_nil :
  `( feval_ihs_order Θ Ξ p nm A Bs B nil nil )
| feiho_arg :
  `( feval_ihs_order Θ Ξ p nm A Bs B gs vs ->
     feval_ihs_order Θ Ξ p nm A Bs B (ca_arg T :: gs) (v :: vs) )
| feiho_rec :
  `( exp_freshb (cargs_nrec gs) B = false ->
     feval_ih_order Θ Ξ p nm A Bs t v ->
     feval_ihs_order Θ Ξ p nm A Bs B gs vs ->
     feval_ihs_order Θ Ξ p nm A Bs B (ca_rec t :: gs) (v :: vs) )
| feiho_skip :
  `( exp_freshb (cargs_nrec gs) B = true ->
     feval_ihs_order Θ Ξ p nm A Bs B gs vs ->
     feval_ihs_order Θ Ξ p nm A Bs B (ca_rec t :: gs) (v :: vs) )

with feval_ih_order (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> ptyp -> domain -> Prop :=
| feio_self :
  `( feval_elim_order Θ Ξ p nm A Bs v ->
     feval_ih_order Θ Ξ p nm A Bs (pt_self k Ps) v )
| feio_pi :
  `( feval_ih_order Θ Ξ p nm A Bs (pt_pi B t) v )

with feval_shty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> Prop :=
| festo_self :
  `( feval_exps_order Θ Ξ Ps p ->
     feval_shty_order Θ Ξ pq ups p (pt_self k Ps) )
| festo_pi :
  `( feval_exp_order Θ Ξ B p ->
     feval_shty_order Θ Ξ pq ups p (pt_pi B t) )

with feval_ihty_order (Θ : gdeps) (Ξ : gstack) : env -> exp -> env -> ptyp -> domain -> Prop :=
| feityo_self :
  `( feval_exps_order Θ Ξ Ps p ->
     (forall bs, ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ bs -> feval_exp_order Θ Ξ A (env_args pm (bs ++ v :: nil))) ->
     feval_ihty_order Θ Ξ pm A p (pt_self k Ps) v )
| feityo_pi :
  `( feval_exp_order Θ Ξ B p ->
     feval_ihty_order Θ Ξ pm A p (pt_pi B t) v )

with feval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| feao_fn :
  `( feval_exp_order Θ Ξ M (p ↦ n) ->
     feval_app_order Θ Ξ λᵈ p M n )
| feao_neut :
  `( feval_exp_order Θ Ξ B (p ↦ n) ->
     feval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n )
| feao_indty :
  `( ind_lookup Θ Ξ pq = Some D ->
     List.length as' < ind_np D ->
     feval_app_order Θ Ξ (d_ind pq as') n )
| feao_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_con D c = Some gs ->
     List.length vs < (ind_np D + List.length gs)%nat ->
     feval_app_order Θ Ξ (d_con pq c vs) n )
| feao_ihfn :
  `( feval_app_order Θ Ξ f n ->
     (forall fn, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> feval_ih_order Θ Ξ p nm A Bs t fn) ->
     feval_app_order Θ Ξ (d_ihfn p nm A Bs t f) n )
| feao_shfam :
  `( feval_shty_order Θ Ξ pq ups (p ↦ n) t ->
     feval_app_order Θ Ξ (d_shfam pq ups p t) n )
| feao_ihfam :
  `( feval_app_order Θ Ξ f n ->
     (forall fn, $ᶠ| f & n | Θ ⍮ Ξ ↘ fn -> feval_ihty_order Θ Ξ pm A (p ↦ n) t fn) ->
     feval_app_order Θ Ξ (d_ihfam pm A p t f) n )
| feao_member :
  `( feval_appm_order Θ Ξ h n ->
     (forall h', $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' -> feval_selc_order Θ Ξ h' ch) ->
     feval_app_order Θ Ξ (d_member h ch) n )

with feval_exps_order (Θ : gdeps) (Ξ : gstack) : list exp -> env -> Prop :=
| feso_nil :
  `( feval_exps_order Θ Ξ nil p )
| feso_cons :
  `( feval_exp_order Θ Ξ M p ->
     feval_exps_order Θ Ξ Ms p ->
     feval_exps_order Θ Ξ (M :: Ms) p )

with feval_apps_order (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> Prop :=
| feaso_nil :
  `( feval_apps_order Θ Ξ m nil )
| feaso_cons :
  `( feval_app_order Θ Ξ m n ->
     (forall m1, $ᶠ| m & n | Θ ⍮ Ξ ↘ m1 -> feval_apps_order Θ Ξ m1 args) ->
     feval_apps_order Θ Ξ m (n :: args) )

with feval_modexp_order (Θ : gdeps) (Ξ : gstack) : modexp -> env -> Prop :=
| femo_var :
  `( feval_modexp_order Θ Ξ (me_var x) p )
| femo_unit :
  `( feval_modexp_order Θ Ξ (me_unit fp) p )
| femo_lit :
  `( feval_close_order Θ Ξ Δ D p ->
     feval_modexp_order Θ Ξ (me_lit (gu_mk Δ D)) p )
| femo_mem :
  `( feval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_selm_order Θ Ξ h y) ->
     feval_modexp_order Θ Ξ (me_mem H y) p )
| femo_app :
  `( feval_modexp_order Θ Ξ H p ->
     feval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n -> feval_appm_order Θ Ξ h n) ->
     feval_modexp_order Θ Ξ (me_app H N) p )

with feval_close_order (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> Prop :=
| feclo_body :
  `( feval_close_order Θ Ξ Δ (md_body sm Φ) p )
| feclo_alias :
  `( feval_close_order Θ Ξ (e :: Δ) (md_alias E) p )
| feclo_alias0 :
  `( feval_modexp_order Θ Ξ E p ->
     feval_close_order Θ Ξ nil (md_alias E) p )

with feval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
| feapo_global :
  `( feval_appm_order Θ Ξ (dm_global pq args) n )
(** The outermost missing parameter is split off as the evaluator splits
    it off ([tele_snoc]), so that the order of the rest is a premise of the
    order of the whole. *)
| feapo_local :
  `( tele_snoc Δ = Some (Δ0, ce_ass A) ->
     feval_close_order Θ Ξ Δ0 D (p ↦ n) ->
     feval_appm_order Θ Ξ (dm_local Δ D p) n )
| feapo_member :
  `( feval_appm_order Θ Ξ h n ->
     (forall h', $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' -> feval_selmc_order Θ Ξ h' ch) ->
     feval_appm_order Θ Ξ (dm_member h ch) n )

with feval_appms_order (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> Prop :=
| feamo_nil :
  `( feval_appms_order Θ Ξ h nil )
| feamo_cons :
  `( feval_appm_order Θ Ξ h n ->
     (forall h1, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h1 -> feval_appms_order Θ Ξ h1 ns) ->
     feval_appms_order Θ Ξ h (n :: ns) )

with feval_sel_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| feslo_global :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def true pv A (Some M)) ->
     feval_exp_order Θ Ξ M nil ->
     (forall f, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f -> feval_apps_order Θ Ξ f args) ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_global_neut :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     feval_exp_order Θ Ξ A nil ->
     (forall a, ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ a -> feval_apps_order Θ Ξ (⇑ a (d_glob (qname_app pq (x :: nil)))) args) ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_global_ind :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_lookup Θ Ξ (qname_app pq (x :: nil)) = Some D ->
     feval_apps_order Θ Ξ (d_ind (qname_app pq (x :: nil)) nil) args ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_global_ind_alias :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_alias_lookup Θ Ξ (qname_app pq (x :: nil)) = Some (Δ, pt, Ns) ->
     feval_exp_order Θ Ξ (ctx_fn Δ (apps (a_ind pt) Ns)) nil ->
     (forall f, ⟦ ctx_fn Δ (apps (a_ind pt) Ns) ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f -> feval_apps_order Θ Ξ f args) ->
     feval_sel_order Θ Ξ (dm_global pq args) x )
| feslo_unsat :
  `( feval_sel_order Θ Ξ (dm_local (e :: Δ) D p) x )
| feslo_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     feval_benv_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> feval_exp_order Θ Ξ M p') ->
     feval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
| feslo_member :
  `( feval_sel_order Θ Ξ (dm_member h ch) x )

with feval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| fesmo_global :
  `( gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     feval_selm_order Θ Ξ (dm_global pq args) y )
| fesmo_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     feval_close_order Θ Ξ Δ D nil ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ nil ↘ h -> feval_appms_order Θ Ξ h args) ->
     feval_selm_order Θ Ξ (dm_global pq args) y )
| fesmo_unsat :
  `( feval_selm_order Θ Ξ (dm_local (e :: Δ) D p) y )
| fesmo_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pm (gu_mk Δy Dy))) ->
     feval_benv_order Θ Ξ p Φ' ->
     (forall p', ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> feval_close_order Θ Ξ Δy Dy p') ->
     feval_selm_order Θ Ξ (dm_local nil (md_body sm Φ) p) y )
| fesmo_member :
  `( feval_selm_order Θ Ξ (dm_member h ch) y )

with feval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fesco_one :
  `( feval_sel_order Θ Ξ h x ->
     feval_selc_order Θ Ξ h (x :: nil) )
| fesco_cons :
  `( feval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 -> feval_selc_order Θ Ξ h1 (z :: ch)) ->
     feval_selc_order Θ Ξ h (y :: z :: ch) )

with feval_selmc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fesmco_nil :
  `( feval_selmc_order Θ Ξ h nil )
| fesmco_cons :
  `( feval_selm_order Θ Ξ h y ->
     (forall h1, h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 -> feval_selmc_order Θ Ξ h1 ch) ->
     feval_selmc_order Θ Ξ h (y :: ch) )

with feval_benv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| febo_nil :
  `( feval_benv_order Θ Ξ p gm_nil )
| febo_def :
  `( feval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> feval_exp_order Θ Ξ M p1) ->
     feval_benv_order Θ Ξ p (gm_ext Φ y (ge_def b pv A (Some M))) )
| febo_mod :
  `( feval_benv_order Θ Ξ p Φ ->
     (forall p1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p1 -> feval_close_order Θ Ξ Δy Dy p1) ->
     feval_benv_order Θ Ξ p (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) ).

#[local]
Hint Constructors feval_exp_order feval_elim_order feval_ihs_order feval_ih_order feval_shty_order feval_ihty_order feval_app_order feval_exps_order feval_apps_order
  feval_modexp_order feval_close_order feval_appm_order feval_appms_order feval_sel_order feval_selm_order feval_selc_order feval_selmc_order
  feval_benv_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_feval_all :=
  repeat match goal with
    | H1 : feval_exp ?T ?X ?M ?p ?m1, H2 : feval_exp ?T ?X ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_feval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_app ?T ?X ?m ?n ?r1, H2 : feval_app ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_exps ?T ?X ?M ?p ?r1, H2 : feval_exps ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (@functional_feval T X))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_apps ?T ?X ?m ?n ?r1, H2 : feval_apps ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_feval T X)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_modexp ?T ?X ?M ?p ?r1, H2 : feval_modexp ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_close ?T ?X ?Δ ?D ?p ?r1, H2 : feval_close ?T ?X ?Δ ?D ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))) _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_appm ?T ?X ?m ?n ?r1, H2 : feval_appm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_appms ?T ?X ?m ?n ?r1, H2 : feval_appms ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : kbody ?T ?X ?p ?Φ ?r1, H2 : kbody ?T ?X ?p ?Φ ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_kbody _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_sel ?T ?X ?m ?n ?r1, H2 : feval_sel ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selm ?T ?X ?m ?n ?r1, H2 : feval_selm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selc ?T ?X ?m ?n ?r1, H2 : feval_selc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selmc ?T ?X ?m ?n ?r1, H2 : feval_selmc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_benv ?T ?X ?m ?n ?r1, H2 : feval_benv ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_benv _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_elim ?T ?X ?p ?nm ?A ?Bs ?m ?r1, H2 : feval_elim ?T ?X ?p ?nm ?A ?Bs ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_elim _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_ihs ?T ?X ?p ?nm ?A ?Bs ?B ?gs ?vs ?r1, H2 : feval_ihs ?T ?X ?p ?nm ?A ?Bs ?B ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_ihs _ _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_ih ?T ?X ?p ?nm ?A ?Bs ?t ?v ?r1, H2 : feval_ih ?T ?X ?p ?nm ?A ?Bs ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_ih _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : feval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_shty _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r1, H2 : feval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_ihty _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : kgens ?T ?X ?p ?E ?its ?g1, H2 : kgens ?T ?X ?p ?E ?its ?g2 |- _ =>
        assert_fails (constr_eq g1 g2);
        pose proof (functional_kgens _ _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    end.

Lemma feval_order_sound : forall Θ Ξ,
    (forall m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_exp_order Θ Ξ m p) /\
    (forall m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> feval_app_order Θ Ξ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> feval_exps_order Θ Ξ Ms p) /\
    (forall m ns r, $*ᶠ| m & ns | Θ ⍮ Ξ ↘ r -> feval_apps_order Θ Ξ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_modexp_order Θ Ξ H p) /\
    (forall Δ D p h, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_close_order Θ Ξ Δ D p) /\
    (forall h n r, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r -> feval_appm_order Θ Ξ h n) /\
    (forall h ns r, $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r -> feval_appms_order Θ Ξ h ns) /\
    (forall h x r, h ·ₜᶠ x Θ ⍮ Ξ ↘ r -> feval_sel_order Θ Ξ h x) /\
    (forall h y r, h ·ₘᶠ y Θ ⍮ Ξ ↘ r -> feval_selm_order Θ Ξ h y) /\
    (forall h ch r, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r -> feval_selc_order Θ Ξ h ch) /\
    (forall h ch r, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r -> feval_selmc_order Θ Ξ h ch) /\
    (forall p Φ p', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> feval_benv_order Θ Ξ p Φ) /\
    (forall p nm A Bs m r, ⟦elimᶠ m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> feval_elim_order Θ Ξ p nm A Bs m) /\
    (forall p nm A Bs B gs vs ihs, ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs -> feval_ihs_order Θ Ξ p nm A Bs B gs vs) /\
    (forall p nm A Bs t v r, ⟦ihᶠ v of t under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> feval_ih_order Θ Ξ p nm A Bs t v) /\
    (forall pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_shty_order Θ Ξ pq ups p t) /\
    (forall pm A p t v a, ⟦ihtyᶠ v of t under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_ihty_order Θ Ξ pm A p t v).
Proof.
  intros Θ Ξ; apply feval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : feval_selc _ _ _ ?c _ |- feval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    solve [ eapply feslo_global_neut; eauto; intros; functional_feval_all; eauto
          | econstructor; try eassumption; intros; functional_feval_all; eauto using kgens_order_sound, tele_snoc_app ].
Qed.

Lemma feval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (feval_order_sound Θ Ξ)). Qed.

Lemma feval_app_order_sound : forall Θ Ξ m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> feval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (feval_order_sound Θ Ξ))). Qed.

Lemma feval_exps_order_sound : forall Θ Ξ Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> feval_exps_order Θ Ξ Ms p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (feval_order_sound Θ Ξ)))). Qed.

Lemma feval_modexp_order_sound : forall Θ Ξ H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_modexp_order Θ Ξ H p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (feval_order_sound Θ Ξ)))))). Qed.

Lemma feval_shty_order_sound : forall Θ Ξ pq ups p t a, ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_shty_order Θ Ξ pq ups p t.
Proof. intros Θ Ξ; pose proof (feval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma feval_ihty_order_sound : forall Θ Ξ pm A p t v a, ⟦ihtyᶠ v of t under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_ihty_order Θ Ξ pm A p t v.
Proof. intros Θ Ξ; pose proof (feval_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve feval_exp_order_sound feval_app_order_sound feval_exps_order_sound feval_modexp_order_sound
  feval_shty_order_sound feval_ihty_order_sound : mctt.

(** ** Constructors of the Shape of the Natural Numbers

    A constructor of a type without parameters that takes no argument, as
    [zero] does, or one recursive argument of the type itself, as [succ]
    does: [nat_cargs D gs] is [Some false] and [Some true] for these
    arguments [gs].  The evaluator takes such a constructor apart, and
    readback reads it ([Extraction.Readback]), without the lists of the
    general rule.  [con_view D c vs] is the constructor [c] at the values
    [vs]: [Some None] of the shape of [zero], [Some (Some v)] of the shape
    of [succ v]. *)
Definition nat_cargs (D : ind_decl) (gs : list carg) : option bool :=
  match ind_params D, ind_nu D, gs with
  | nil, 0, nil => Some false
  | nil, 0, ca_rec (pt_self _ nil) :: nil => Some true
  | _, _, _ => None
  end.

Definition con_view (D : ind_decl) (c : string) (vs : list domain) : option (option domain) :=
  match ind_con D c with
  | Some gs =>
      match nat_cargs D gs, vs with
      | Some false, nil => Some None
      | Some true, v :: nil => Some (Some v)
      | _, _ => None
      end
  | None => None
  end.

Lemma nat_cargs_zero : forall D gs,
    nat_cargs D gs = Some false -> ind_params D = nil /\ ind_nu D = 0 /\ gs = nil.
Proof.
  unfold nat_cargs; intros D gs H.
  destruct (ind_params D), (ind_nu D) as [|]; try discriminate.
  destruct gs as [| [? | [? [|] | ? ? | ? ?]] [|]]; try discriminate; auto.
Qed.

Lemma nat_cargs_succ : forall D gs,
    nat_cargs D gs = Some true -> ind_params D = nil /\ ind_nu D = 0 /\ exists k, gs = ca_rec (pt_self k nil) :: nil.
Proof.
  unfold nat_cargs; intros D gs H.
  destruct (ind_params D), (ind_nu D) as [|]; try discriminate.
  destruct gs as [| [? | [k [|] | ? ? | ? ?]] [|]]; try discriminate; eauto.
Qed.

Lemma con_view_zero : forall D c vs,
    con_view D c vs = Some None ->
    ind_con D c = Some nil /\ ind_params D = nil /\ ind_np D = 0 /\ ind_nu D = 0 /\ vs = nil.
Proof.
  unfold con_view; intros D c vs H.
  destruct (ind_con D c) as [gs |] eqn:Ec; [| discriminate ].
  destruct (nat_cargs D gs) as [[|] |] eqn:En, vs as [| ? [|]]; try discriminate.
  destruct (nat_cargs_zero _ _ En) as (Hp & Hu & ->); auto 6 using ind_np_nil.
Qed.

Lemma con_view_succ : forall D c vs v,
    con_view D c vs = Some (Some v) ->
    exists k, ind_con D c = Some (ca_rec (pt_self k nil) :: nil) /\ ind_params D = nil /\ ind_np D = 0 /\ ind_nu D = 0 /\ vs = v :: nil.
Proof.
  unfold con_view; intros D c vs v H.
  destruct (ind_con D c) as [gs |] eqn:Ec; [| discriminate ].
  destruct (nat_cargs D gs) as [[|] |] eqn:En, vs as [| ? [|]]; try discriminate.
  injection H as ->.
  destruct (nat_cargs_succ _ _ En) as (Hp & Hu & k & ->); eauto 7 using ind_np_nil.
Qed.

(** The type of a recursive argument at the type itself, without
    indices, is the type former at the uniform parameters. *)
Lemma feval_shty_self_nil : forall Θ Ξ p ups ρ k,
    ⟦shtyᶠ pt_self k nil of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_ind p ups.
Proof.
  intros; rewrite <- (app_nil_r ups) at 2; econstructor; constructor.
Qed.

(** The type of the recursive result of such an argument: the motive at the
    argument. *)
Lemma feval_ihty_self_nil : forall Θ Ξ pm A p k v a,
    ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ extend_env pm v ↘ a -> ⟦ihtyᶠ v of pt_self k nil under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a.
Proof. intros * Ha; econstructor; [ constructor | exact Ha ]. Qed.

#[local] Hint Resolve feval_shty_self_nil feval_ihty_self_nil : core.

(** The environment of a branch: the non-uniform parameters, the
    arguments and the recursive results ([feval_elim_con]).  Without
    parameters, the arguments are all the values, which are not copied. *)
Definition elim_env (p : env) (D : ind_decl) (vs ihs : list domain) : env :=
  match ind_params D with
  | nil => env_args (env_args p vs) ihs
  | _ => env_args p (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs)
  end.

Lemma elim_env_eq : forall p D vs ihs,
    elim_env p D vs ihs = env_args p (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs).
Proof.
  intros; unfold elim_env, ind_np.
  destruct (ind_params D); [| reflexivity ].
  cbn [List.length firstn skipn]; rewrite skipn_nil, app_nil_l, env_args_app; reflexivity.
Qed.

(** A prefix up to a name ends with the entry of that name. *)
Lemma gm_prefix_upto_ext : forall Φ y Φ1, gm_prefix_upto Φ y = Some Φ1 -> exists Φ0 E, Φ1 = gm_ext Φ0 y E.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * Hp; cbn in Hp; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> |]; [ injection Hp as <-; eauto | eauto ].
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

#[local] Hint Resolve kbody_order_sound : core.

Section EvalImpl.
  Variables (Θ : gdeps) (Ξ : gstack).
  Context {F : FCtx Θ Ξ}.


  (** A variable is looked up in the environment, without recursion. *)
  Definition feval_var_impl x p (H : feval_exp_order Θ Ξ #x p) : { d | ⟦ #x ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply feval_exp_var.
  Defined.



  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : feval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_exps_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_apps_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_modexp_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_close_order _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_appm_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_appms_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_sel_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selm_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selc_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selmc_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_benv_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_elim_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_ih_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_shty_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_ihty_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    end.

  (** The lookups recorded in the order are the ones computed, which either
      fixes what is looked up or rules the case out. *)
  #[local]
  Ltac impl_obl_glob :=
    repeat match goal with
      | H : gc_entry _ _ _ = Some (ge_def _ _ _ _) |- _ => apply gc_entry_def in H
      | H : gc_entry _ _ _ = Some (ge_ind _ _ _ _) |- _ =>
          let H1 := fresh "Hr" in let H2 := fresh "Hl" in destruct (gc_entry_ind _ _ _ _ _ _ H) as [H1 H2]; clear H
      | H : gc_entry ?T ?X ?p = _, H' : gc_resolve ?T ?X ?p = Some (ge_def _ _ _ _) |- _ =>
          apply gc_entry_def in H'; rewrite H in H'; discriminate H'
      | H : gc_entry ?T ?X ?p = _, H' : ind_lookup ?T ?X ?p = Some _ |- _ =>
          let He := fresh "He" in destruct (ind_lookup_entry _ _ _ _ H') as (? & ? & ? & He); rewrite H in He; discriminate He
      | H : gc_entry _ _ _ = Some (ge_ind_alias _ _ _ _) |- _ =>
          let H1 := fresh "Hr" in let H2 := fresh "Ha" in destruct (gc_entry_ind_alias _ _ _ _ _ _ _ H) as [H1 H2]; clear H
      | H : gc_entry ?T ?X ?p = _, H' : ind_alias_lookup ?T ?X ?p = Some _ |- _ =>
          rewrite ind_alias_lookup_entry, H in H'; cbn in H'; discriminate H'
      | H1 : ind_alias_lookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_alias_lookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_alias_lookup _ _ ?p = Some _ |- _ =>
          exfalso; rewrite (ind_lookup_not_ind_alias _ _ _ _ H1) in H2; discriminate H2
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ind_lookup _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some (mr_alias _) |- _ =>
          exfalso; exact (ind_lookup_not_alias _ _ _ _ _ H1 H2)
      | H1 : gc_loc _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some (mr_alias _) |- _ =>
          exfalso; exact (gc_loc_not_alias _ _ _ _ _ H1 H2)
      | H1 : kbody _ _ ?p ?Φ ?r1, H2 : kbody _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); pose proof (functional_kbody _ _ _ _ H1 H2); subst; clear H2
      | H : tele_snoc _ = None |- _ => rewrite tele_snoc_app in H; discriminate H
      | H1 : tele_snoc ?Δ = Some _, H2 : tele_snoc ?Δ = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : tele_snoc ?Δ = Some _, H2 : tele_snoc ?Δ = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H : tele_snoc (_ ++ _ :: nil) = _ |- _ =>
          rewrite tele_snoc_app in H; injection H; clear H; intros; subst
      | H : tele_snoc nil = _ |- _ => discriminate H
      | H : tele_snoc ?Δ = Some _ |- _ => is_var Δ; apply tele_snoc_some in H; subst Δ
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      (** A prefix up to a name ends with that name's entry. *)
      | H : gm_prefix_upto _ _ = Some gm_nil |- _ =>
          destruct (gm_prefix_upto_ext _ _ _ H) as (? & ? & ?); discriminate
      | H : gm_prefix_upto _ _ = Some (gm_open _ _ _) |- _ =>
          destruct (gm_prefix_upto_ext _ _ _ H) as (? & ? & ?); discriminate
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2
      | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H : Nat.compare _ _ = Eq |- _ => apply Nat.compare_eq in H
      | H : Nat.compare _ _ = Lt |- _ => apply Nat.compare_lt_iff in H
      | H : Nat.compare _ _ = Gt |- _ => apply Nat.compare_gt_iff in H
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = None |- _ =>
          rewrite H1 in H2; discriminate H2
      end.

  (** The [efq] case: the order says that the scrutinee evaluates to a
      neutral, which rules out every other value. *)
  #[local]
  Ltac impl_obl_exfalso :=
    repeat match goal with
      | H : forall m, feval_exp _ _ ?M ?p m -> exists _ _, m = ⇑ _ _, Hm : feval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ? & ?); clear H
      end.

  #[local]
  Ltac impl_obl_split :=
    match goal with
    | H : feval_exp_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_app_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_modexp_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_close_order _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_appm_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_appms_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_sel_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_selm_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_selc_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_benv_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_elim_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_ihs_order _ _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_ih_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_shty_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_ihty_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac impl_obl_finish :=
    impl_obl_exfalso;
    impl_obl_glob;
    cbn [gu_params] in *;
    try solve [ intuition discriminate ];
    (** The two rules of the eliminator at a successor exclude each other. *)
    try solve [ congruence ];
    try solve [ exfalso; lia ];
    try solve [ eapply feval_sel_global_neut; eauto ];
    try solve [ econstructor; [ intros ? ? Hc; congruence | .. ]; eauto ];
    (** A closure lacking a first parameter lacks one. *)
    try solve [ econstructor; cbn; lia ];
    try solve [ eauto ];
    try econstructor; eauto.


  (** The constructors of the shape of the natural numbers ([con_view]):
      the general rule at no parameter and at the lists the view fixes.  An
      order of the branch is the premise of the order at the recursive
      results computed, which the view fixes to none or one. *)
  #[local]
  Ltac ev_conview :=
    match goal with
    | Ev : con_view _ _ _ = Some None |- _ =>
        destruct (con_view_zero _ _ _ Ev) as (? & ? & ? & ? & ?); subst
    | Ev : con_view _ _ _ = Some (Some _) |- _ =>
        let Hc := fresh "Hc" in
        destruct (con_view_succ _ _ _ _ Ev) as (? & Hc & ? & ? & ? & ?); subst
    end;
    repeat impl_obl_tac1; impl_obl_glob;
    match goal with Hnp : ind_np ?D = 0, Hnu : ind_nu ?D = 0 |- _ =>
      rewrite Hnp, Hnu in * |-;
      cbn [skipn firstn app env_args fold_left extend_env] in * |-;
      repeat impl_obl_tac1; impl_obl_glob;
      try match goal with H : feval_ihs_order _ _ _ _ _ _ _ (_ :: _) _ |- _ => dependent destruction H end;
      cbn [cargs_nrec] in * |-;
      try solve [ congruence ];
      repeat impl_obl_tac1;
      first [ match goal with Hb : forall ihs, _ -> feval_exp_order _ _ ?B _ |- feval_exp_order _ _ ?B _ =>
                first [ refine (Hb nil _) | refine (Hb (_ :: nil) _) ]; eauto 6 with mctt end
            | eassumption
            | eapply feval_elim_con; try eassumption; rewrite ?Hnp, ?Hnu; cbn; eauto 6 with mctt ]
    end.

  #[local]
  Ltac ev_obl :=
    intros; cbv beta in *;
    rewrite ?elim_env_eq in *;
    first [ lazymatch goal with Ev : con_view _ _ _ = Some _ |- _ => solve [ ev_conview ] end | idtac ];
    repeat impl_obl_tac1;
    (** A recursive result's type without indices: the motive at no index. *)
    try match goal with Hq : forall bs, feval_exps _ _ nil _ bs -> feval_exp_order _ _ ?A _ |- feval_exp_order _ _ ?A _ =>
          solve [ apply (Hq nil); constructor ] end;
    first [ solve [ impl_obl_finish ]
          | solve [ impl_obl_split; impl_obl_finish ]
          | impl_obl_finish ].

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations feval_exp_impl m p (H : feval_exp_order Θ Ξ m p) : { d | ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
  | Typeω@i, p, H => exist _ 𝕌ω@i _
  | Type⟨M⟩, p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      exist _ 𝕌@m _
  | #x    , p, H => feval_var_impl x p H
  | Level@n, p, H => exist _ (Levelᵈ@n) _
  | 𝕃ᵒ o  , p, H => exist _ (dlvl_lit o) _
  | succl M, p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      exist _ (dlvl_suc m) _
  | maxl M N, p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      let (n , Hn) := feval_exp_impl N p _ in
      exist _ (dlvl_max m n) _
  | ⊤     , p, H => exist _ ⊤ᵈ _
  | ⋆     , p, H => exist _ ⋆ᵈ _
  | ⊥     , p, H => exist _ ⊥ᵈ _
  | efq M return A, p, H with feval_exp_impl M p _ := {
    | exist _ (⇑ b m) Hm =>
        let (a, Ha) := feval_exp_impl A (p ↦ ⇑ b m) _ in
        exist _ ⇑ a (efqᵈ m under p return A) _
    | exist _ _ Hm => False_rect _ _ }
  | Π A B , p, H =>
      let (r , Hr) := feval_exp_impl A p _ in
      exist _ Πᵈ r p B _
  | λ A M , p, H => exist _ λᵈ p M _
  | a_ind pq, p, H => exist _ (d_ind pq nil) _
  | a_con pq c, p, H => exist _ (d_con pq c nil) _
  (** A literal is generated before it is ever evaluated. *)
  | a_ntok, p, H => False_rect _ _
  | a_nlit _, p, H => False_rect _ _
  | a_elim nm A Bs M, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (r, Hr) := feval_elim_impl p nm A Bs m (@fc_seed Θ Ξ F) _ in
      exist _ r _
  | M $ N   , p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      let (n , Hn) := feval_exp_impl N p _ in
      let (a, Ha) := feval_app_impl m n _ in
      exist _ a _
  | a_let (b_def oA M) B, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (r, Hr) := feval_exp_impl B (p ↦ m) _ in
      exist _ r _
  | a_let (b_mod (gu_mk Δ D)) B, p, H =>
      let (h, Hh) := feval_close_impl Δ D p _ in
      let (r, Hr) := feval_exp_impl B (p ↦ᵐ h) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := feval_modexp_impl R p _ in
        let (f, Hf) := feval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := feval_exps_impl args p _ in
        let (r, Hr) := feval_apps_impl f ns _ in
        exist _ r _ }

  with feval_elim_impl p nm A Bs m (ck : lk_cache Θ Ξ) (H : feval_elim_order Θ Ξ p nm A Bs m) : { r | ⟦elimᶠ m under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r } by struct H :=
  | p, nm, A, Bs, d_con pq c vs, ck, H with cache_lookup Θ Ξ ck pq := {
    | exist _ (Some D) Ed with inspect (con_view D c vs) := {
      (** A constructor of the shape of [zero]: its branch at [p]. *)
      | exist _ (Some None) Ev with inspect (brs_lookup Bs c) := {
        | exist _ (Some (n, B)) Eb =>
            let (r, Hr) := feval_exp_impl B p _ in
            exist _ r _
        | exist _ None Eb => False_rect _ _ }
      (** Of the shape of [succ v]: its branch at [v] and the recursive
          result, if the branch reads it. *)
      | exist _ (Some (Some v)) Ev with inspect (brs_lookup Bs c) := {
        | exist _ (Some (n, B)) Eb with inspect (exp_freshb 0 B) := {
          | exist _ true Ef =>
              let (r, Hr) := feval_exp_impl B (extend_env (extend_env p v) 𝕌ω@0) _ in
              exist _ r _
          | exist _ false Ef =>
              let (ih, Hih) := feval_elim_impl p nm A Bs v (Some (exist _ (pq, D) Ed)) _ in
              let (r, Hr) := feval_exp_impl B (extend_env (extend_env p v) ih) _ in
              exist _ r _ }
        | exist _ None Eb => False_rect _ _ }
      | exist _ None Ev with inspect (ind_con D c) := {
        | exist _ (Some gs) Ec with inspect (brs_lookup Bs c) := {
          | exist _ (Some (n, B)) Eb =>
              let (ihs, Hihs) := feval_ihs_impl p nm A Bs B gs (skipn (ind_np D) vs) (Some (exist _ (pq, D) Ed)) _ in
              let (r, Hr) := feval_exp_impl B (elim_env p D vs ihs) _ in
              exist _ r _
          | exist _ None Eb => False_rect _ _ }
        | exist _ None Ec => False_rect _ _ } }
    | exist _ None Ed => False_rect _ _ }
  | p, nm, A, Bs, ⇑ (d_ind pq as') m, ck, H with cache_lookup Θ Ξ ck pq := {
    | exist _ (Some D) Ed =>
        let (a, Ha) := feval_exp_impl A (env_args p (skipn (ind_nu D) as' ++ ⇑ (d_ind pq as') m :: nil)) _ in
        exist _ (⇑ a (d_elim p nm A Bs pq as' m)) _
    | exist _ None Ed => False_rect _ _ }
  | p, nm, A, Bs, _, ck, H => False_rect _ _

  with feval_ihs_impl p nm A Bs B gs vs (ck : lk_cache Θ Ξ) (H : feval_ihs_order Θ Ξ p nm A Bs B gs vs) : { ihs | ⟦ihsᶠ vs of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ ihs } by struct H :=
  | p, nm, A, Bs, B, nil, nil, ck, H => exist _ nil _
  | p, nm, A, Bs, B, ca_arg T :: gs, v :: vs, ck, H =>
      let (ihs, Hihs) := feval_ihs_impl p nm A Bs B gs vs ck _ in
      exist _ ihs _
  | p, nm, A, Bs, B, ca_rec t :: gs, v :: vs, ck, H with inspect (exp_freshb (cargs_nrec gs) B) := {
    (** The branch does not read the recursive result: it is not
        computed. *)
    | exist _ true E =>
        let (ihs, Hihs) := feval_ihs_impl p nm A Bs B gs vs ck _ in
        exist _ (𝕌ω@0 :: ihs) _
    | exist _ false E =>
        let (ih, Hih) := feval_ih_impl p nm A Bs t v ck _ in
        let (ihs, Hihs) := feval_ihs_impl p nm A Bs B gs vs ck _ in
        exist _ (ih :: ihs) _ }
  | p, nm, A, Bs, B, _, _, ck, H => False_rect _ _

  with feval_ih_impl p nm A Bs t v (ck : lk_cache Θ Ξ) (H : feval_ih_order Θ Ξ p nm A Bs t v) : { r | ⟦ihᶠ v of t under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r } by struct H :=
  | p, nm, A, Bs, pt_self k Ps, v, ck, H =>
      let (r, Hr) := feval_elim_impl p nm A Bs v ck _ in
      exist _ r _
  | p, nm, A, Bs, pt_pi B t, v, ck, H => exist _ (d_ihfn p nm A Bs t v) _
  | p, nm, A, Bs, pt_aux k Ps, v, ck, H => False_rect _ _

  with feval_shty_impl pq ups p t (H : feval_shty_order Θ Ξ pq ups p t) : { a | ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } by struct H :=
  | pq, ups, p, pt_self k Ps, H =>
      let (bs, Hbs) := feval_exps_impl Ps p _ in
      exist _ (d_ind pq (ups ++ bs)) _
  | pq, ups, p, pt_pi B t, H =>
      let (b, Hb) := feval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_shfam pq ups p t) fam_cod) _
  | pq, ups, p, pt_aux k Ps, H => False_rect _ _

  with feval_ihty_impl pm A p t v (H : feval_ihty_order Θ Ξ pm A p t v) : { a | ⟦ihtyᶠ v of t under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } by struct H :=
  | pm, A, p, pt_self k Ps, v, H =>
      let (bs, Hbs) := feval_exps_impl Ps p _ in
      let (a, Ha) := feval_exp_impl A (env_args pm (bs ++ v :: nil)) _ in
      exist _ a _
  | pm, A, p, pt_pi B t, v, H =>
      let (b, Hb) := feval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_ihfam pm A p t v) fam_cod) _
  | pm, A, p, pt_aux k Ps, v, H => False_rect _ _

  with feval_app_impl m n (H : feval_app_order Θ Ξ m n) : { d | $ᶠ| m & n | Θ ⍮ Ξ ↘ d } by struct H :=
  | λᵈ p M        , n, H =>
      let (m, Hm) := feval_exp_impl M (p ↦ n) _ in
      exist _ m _
  | ⇑ (Πᵈ a p B) m, n, H =>
      let (b, Hb) := feval_exp_impl B (p ↦ n) _ in
      exist _ ⇑ b (m $ᵈ ⇓ a n) _
  | d_member h ch, n, H =>
      let (h', Hh') := feval_appm_impl h n _ in
      let (r, Hr) := feval_selc_impl h' ch _ in
      exist _ r _
  | d_ind pq as', n, H => exist _ (d_ind pq (as' ++ n :: nil)) _
  | d_con pq c vs, n, H => exist _ (d_con pq c (vs ++ n :: nil)) _
  | d_ihfn p nm A Bs t f, n, H =>
      let (fn, Hfn) := feval_app_impl f n _ in
      let (r, Hr) := feval_ih_impl p nm A Bs t fn (@fc_seed Θ Ξ F) _ in
      exist _ r _
  | d_shfam pq ups p t, n, H =>
      let (a, Ha) := feval_shty_impl pq ups (p ↦ n) t _ in
      exist _ a _
  | d_ihfam pm A p t f, n, H =>
      let (fn, Hfn) := feval_app_impl f n _ in
      let (a, Ha) := feval_ihty_impl pm A (p ↦ n) t fn _ in
      exist _ a _
  | _, n, H => False_rect _ _

  with feval_exps_impl Ms p (H : feval_exps_order Θ Ξ Ms p) : { ms | ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms } by struct H :=
  | nil, p, H => exist _ nil _
  | M :: Ms, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (ms, Hms) := feval_exps_impl Ms p _ in
      exist _ (m :: ms) _

  with feval_apps_impl m ns (H : feval_apps_order Θ Ξ m ns) : { r | $*ᶠ| m & ns | Θ ⍮ Ξ ↘ r } by struct H :=
  | m, nil, H => exist _ m _
  | m, n :: ns, H =>
      let (m1, Hm1) := feval_app_impl m n _ in
      let (r, Hr) := feval_apps_impl m1 ns _ in
      exist _ r _

  with feval_modexp_impl M p (H : feval_modexp_order Θ Ξ M p) : { h | ⟦ M ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | me_var x, p, H => exist _ (env_mod p x) _
  | me_unit fp, p, H => exist _ (dm_global (q_abs fp nil) nil) _
  | me_lit (gu_mk Δ D), p, H =>
      let (h, Hh) := feval_close_impl Δ D p _ in
      exist _ h _
  | me_mem M y, p, H =>
      let (h, Hh) := feval_modexp_impl M p _ in
      let (r, Hr) := feval_selm_impl h y _ in
      exist _ r _
  | me_app M N, p, H =>
      let (h, Hh) := feval_modexp_impl M p _ in
      let (n, Hn) := feval_exp_impl N p _ in
      let (r, Hr) := feval_appm_impl h n _ in
      exist _ r _

  with feval_close_impl Δ D p (H : feval_close_order Θ Ξ Δ D p) : { h | ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | Δ, md_body sm Φ, p, H => exist _ (dm_local Δ (md_body sm Φ) p) _
  | nil, md_alias E, p, H =>
      let (h, Hh) := feval_modexp_impl E p _ in
      exist _ h _
  | e :: Δ, md_alias E, p, H => exist _ (dm_local (e :: Δ) (md_alias E) p) _

  with feval_appm_impl h n (H : feval_appm_order Θ Ξ h n) : { r | $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, n, H => exist _ (dm_global pq (args ++ n :: nil)) _
  | dm_local Δ D p, n, H with inspect (tele_snoc Δ) := {
    | exist _ (Some (Δ0, ce_ass A)) Es =>
        let (r, Hr) := feval_close_impl Δ0 D (p ↦ n) _ in
        exist _ r _
    | exist _ _ Es => False_rect _ _ }
  | dm_member h ch, n, H =>
      let (h', Hh') := feval_appm_impl h n _ in
      let (r, Hr) := feval_selmc_impl h' ch _ in
      exist _ r _

  with feval_appms_impl h ns (H : feval_appms_order Θ Ξ h ns) : { r | $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r } by struct H :=
  | h, nil, H => exist _ h _
  | h, n :: ns, H =>
      let (h1, Hh1) := feval_appm_impl h n _ in
      let (r, Hr) := feval_appms_impl h1 ns _ in
      exist _ r _

  with feval_sel_impl h x (H : feval_sel_order Θ Ξ h x) : { r | h ·ₜᶠ x Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, x, H with gc_entry_f Θ Ξ (qname_app pq (x :: nil)) := {
    | exist _ (Some (ge_def true pv A (Some M))) E =>
        let (f, Hf) := feval_exp_impl M nil _ in
        let (r, Hr) := feval_apps_impl f args _ in
        exist _ r _
    | exist _ (Some (ge_def true _ A None)) E =>
        let (a, Ha) := feval_exp_impl A nil _ in
        let (r, Hr) := feval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_def false _ A B)) E =>
        let (a, Ha) := feval_exp_impl A nil _ in
        let (r, Hr) := feval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_mod _ _)) E => False_rect _ _
    | exist _ (Some (ge_ind _ _ D _)) E =>
        let (r, Hr) := feval_apps_impl (d_ind (qname_app pq (x :: nil)) nil) args _ in
        exist _ r _
    | exist _ (Some (ge_ind_alias _ Δ pt Ns)) E =>
        let (f, Hf) := feval_exp_impl (ctx_fn Δ (apps (a_ind pt) Ns)) nil _ in
        let (r, Hr) := feval_apps_impl f args _ in
        exist _ r _
    | exist _ None E => False_rect _ _ }
  | dm_local (e :: Δ) D p, x, H => exist _ (d_member (dm_local (e :: Δ) D p) (x :: nil)) _
  | dm_local nil (md_alias E) p, x, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, x, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx x) := {
      | exist _ (Some (gm_ext Φ' _ (ge_def b pv A (Some M)))) P =>
          let (p', Hp') := feval_benv_impl p Φ' _ in
          let (r, Hr) := feval_exp_impl M p' _ in
          exist _ r _
      | exist _ _ P => False_rect _ _ } }
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with feval_selm_impl h y (H : feval_selm_order Θ Ξ h y) : { r | h ·ₘᶠ y Θ ⍮ Ξ ↘ r } by struct H :=
  | dm_global pq args, y, H with gc_module_f Θ Ξ (qname_app pq (y :: nil)) := {
    | exist _ (Some (mr_alias (gu_mk Δ D))) E =>
        let (h, Hh) := feval_close_impl Δ D nil _ in
        let (r, Hr) := feval_appms_impl h args _ in
        exist _ r _
    | exist _ _ E => exist _ (dm_global (qname_app pq (y :: nil)) args) _ }
  | dm_local (e :: Δ) D p, y, H => exist _ (dm_member (dm_local (e :: Δ) D p) (y :: nil)) _
  | dm_local nil (md_alias E) p, y, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, y, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx y) := {
      | exist _ (Some (gm_ext Φ' _ (ge_mod pm (gu_mk Δy Dy)))) P =>
          let (p', Hp') := feval_benv_impl p Φ' _ in
          let (r, Hr) := feval_close_impl Δy Dy p' _ in
          exist _ r _
      | exist _ _ P => False_rect _ _ } }
  | dm_member h ch, y, H => exist _ (dm_member h (ch ++ y :: nil)) _

  with feval_selc_impl h ch (H : feval_selc_order Θ Ξ h ch) : { r | h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r } by struct H :=
  | h, x :: nil, H =>
      let (r, Hr) := feval_sel_impl h x _ in
      exist _ r _
  | h, y :: ch, H =>
      let (h1, Hh1) := feval_selm_impl h y _ in
      let (r, Hr) := feval_selc_impl h1 ch _ in
      exist _ r _
  | h, nil, H => False_rect _ _

  with feval_selmc_impl h ch (H : feval_selmc_order Θ Ξ h ch) : { r | h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r } by struct H :=
  | h, nil, H => exist _ h _
  | h, y :: ch, H =>
      let (h1, Hh1) := feval_selm_impl h y _ in
      let (r, Hr) := feval_selmc_impl h1 ch _ in
      exist _ r _

  with feval_benv_impl p Φ (H : feval_benv_order Θ Ξ p Φ) : { p' | ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y (ge_def b pv A (Some M)), H =>
      let (p1, Hp1) := feval_benv_impl p Φ _ in
      let (m, Hm) := feval_exp_impl M p1 _ in
      exist _ (p1 ↦ m) _
  | p, gm_ext Φ y (ge_def b pv A None), H => False_rect _ _
  | p, gm_ext Φ y (ge_mod _ (gu_mk Δy Dy)), H =>
      let (p1, Hp1) := feval_benv_impl p Φ _ in
      let (h, Hh) := feval_close_impl Δy Dy p1 _ in
      exist _ (p1 ↦ᵐ h) _
  | p, gm_open Φ E its, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([ev_obl]).  They are transparent: the order premises are the
    arguments of the structural recursion. *)
Solve All Obligations with ev_obl.

  (** The type of a recursive argument and of its recursive result, for an
      argument at the type itself without indices: the type former at the
      uniform parameters, and the motive at the argument, without
      evaluating an empty list of indices. *)
  Definition feval_shty_fast pq ups p t (H : feval_shty_order Θ Ξ pq ups p t) : { a | ⟦shtyᶠ t of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } :=
    match t as t0 return feval_shty_order Θ Ξ pq ups p t0 -> { a | ⟦shtyᶠ t0 of pq ups ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } with
    | pt_self k nil => fun _ => exist _ (d_ind pq ups) (feval_shty_self_nil _ _ _ _ _ _)
    | t0 => fun H0 => feval_shty_impl pq ups p t0 H0
    end H.

  Lemma feval_ihty_nil_order : forall pm A p k v,
      feval_ihty_order Θ Ξ pm A p (pt_self k nil) v -> feval_exp_order Θ Ξ A (extend_env pm v).
  Proof. intros * H; inversion H; subst; match goal with Hq : forall bs, _ -> _ |- _ => apply (Hq nil); constructor end. Qed.

  Definition feval_ihty_fast pm A p t v (H : feval_ihty_order Θ Ξ pm A p t v) : { a | ⟦ihtyᶠ v of t under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } :=
    match t as t0 return feval_ihty_order Θ Ξ pm A p t0 v -> { a | ⟦ihtyᶠ v of t0 under pm A ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a } with
    | pt_self k nil => fun H0 =>
        let (a, Ha) := feval_exp_impl A (extend_env pm v) (feval_ihty_nil_order _ _ _ _ _ H0) in
        exist _ a (feval_ihty_self_nil _ _ _ _ _ _ _ _ Ha)
    | t0 => fun H0 => feval_ihty_impl pm A p t0 v H0
    end H.
End EvalImpl.

Extraction Inline feval_exp_impl_functional
  feval_elim_impl_functional
  feval_ihs_impl_functional
  feval_ih_impl_functional
  feval_shty_impl_functional
  feval_ihty_impl_functional
  feval_app_impl_functional
  feval_exps_impl_functional
  feval_apps_impl_functional
  feval_modexp_impl_functional
  feval_close_impl_functional
  feval_appm_impl_functional
  feval_appms_impl_functional
  feval_sel_impl_functional
  feval_selm_impl_functional
  feval_selc_impl_functional
  feval_selmc_impl_functional
  feval_benv_impl_functional.

(** The [feval_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the evaluation orders and the functionality
    of evaluation. *)

#[local]
Ltac functional_feval_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_feval_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma feval_exp_impl_complete : forall Θ Ξ {F : FCtx Θ Ξ} M p m,
    ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m ->
    exists H H', feval_exp_impl Θ Ξ M p H = exist _ m H'.
Proof.
  intros; functional_feval_complete.
Qed.

Lemma feval_app_impl_complete : forall Θ Ξ {F : FCtx Θ Ξ} m n r,
    $ᶠ| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', feval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_feval_complete.
Qed.
