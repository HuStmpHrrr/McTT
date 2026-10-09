From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastEval.
Import Domain_Notations.

Generalizable All Variables.

(** * The Evaluator the Checker Runs

    The evaluator of the relation of [Extraction.FastEval]: the reference one
    ([Reference.Evaluation]) but for the eliminator at a successor, which
    does not compute the recursive result when the successor case does not
    read it. *)

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
| feeo_nat :
  `( feval_exp_order Θ Ξ ℕ p )
| feeo_zero :
  `( feval_exp_order Θ Ξ zero p )
| feeo_succ :
  `( feval_exp_order Θ Ξ M p ->
     feval_exp_order Θ Ξ succ M p )
| feeo_natrec :
  `( feval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m -> feval_natrec_order Θ Ξ A MZ MS m p) ->
     feval_exp_order Θ Ξ rec M return A | zero -> MZ | succ -> MS end p )
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
  `( feval_exp_order Θ Ξ B (p ↦ᵐ dm_local p U nil) ->
     feval_exp_order Θ Ξ (ℓₘ U in B) p )
| feeo_mem :
  `( modexp_spine H = (R, args, pre) ->
     feval_modexp_order Θ Ξ R p ->
     (forall h, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_selc_order Θ Ξ h (pre ++ x :: nil)) ->
     feval_exps_order Θ Ξ args p ->
     (forall h f ns, ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_selc Θ Ξ h (pre ++ x :: nil) f ->
        feval_exps Θ Ξ args p ns -> feval_apps_order Θ Ξ f ns) ->
     feval_exp_order Θ Ξ (a_mem H x) p )

with feval_natrec_order (Θ : gdeps) (Ξ : gstack) : exp -> exp -> exp -> domain -> env -> Prop :=
| feno_zero :
  `( feval_exp_order Θ Ξ MZ p ->
     feval_natrec_order Θ Ξ A MZ MS zeroᵈ p )
| feno_succ :
  `( exp_freshb 0 MS = false ->
     feval_natrec_order Θ Ξ A MZ MS b p ->
     (forall r, ⟦recᶠ b return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r -> feval_exp_order Θ Ξ MS (p ↦ b ↦ r)) ->
     feval_natrec_order Θ Ξ A MZ MS succᵈ b p )
| feno_skip :
  `( exp_freshb 0 MS = true ->
     feval_exp_order Θ Ξ MS (p ↦ b ↦ zeroᵈ) ->
     feval_natrec_order Θ Ξ A MZ MS succᵈ b p )
| feno_neut :
  `( feval_exp_order Θ Ξ MZ p ->
     feval_exp_order Θ Ξ A (p ↦ ⇑ a m) ->
     feval_natrec_order Θ Ξ A MZ MS ⇑ a m p )

with feval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| feao_fn :
  `( feval_exp_order Θ Ξ M (p ↦ n) ->
     feval_app_order Θ Ξ λᵈ p M n )
| feao_neut :
  `( feval_exp_order Θ Ξ B (p ↦ n) ->
     feval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n )
| feao_member :
  `( feval_appm_order Θ Ξ h n ->
     (forall h', feval_appm Θ Ξ h n h' -> feval_selc_order Θ Ξ h' ch) ->
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
  `( feval_modexp_order Θ Ξ (me_lit U) p )
| femo_mem :
  `( feval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_selm_order Θ Ξ h y) ->
     feval_modexp_order Θ Ξ (me_mem H y) p )
| femo_app :
  `( feval_modexp_order Θ Ξ H p ->
     feval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ n -> feval_appm_order Θ Ξ h n) ->
     feval_modexp_order Θ Ξ (me_app H N) p )

with feval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
| feapo_global :
  `( feval_appm_order Θ Ξ (dm_global pq args) n )
| feapo_body :
  `( List.length args < List.length Δ ->
     feval_appm_order Θ Ξ (dm_local p (gu_body Δ Φ) args) n )
| feapo_alias_unsat :
  `( List.length args < List.length Δ ->
     feval_appm_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) n )
| feapo_alias :
  `( List.length args = List.length Δ ->
     feval_modexp_order Θ Ξ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ env_args p args ↘ h -> feval_appm_order Θ Ξ h n) ->
     feval_appm_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) n )
| feapo_member :
  `( feval_appm_order Θ Ξ h n ->
     (forall h', feval_appm Θ Ξ h n h' -> feval_selmc_order Θ Ξ h' ch) ->
     feval_appm_order Θ Ξ (dm_member h ch) n )

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
| feslo_unsat :
  `( List.length args < List.length (gu_params U) ->
     feval_sel_order Θ Ξ (dm_local p U args) x )
| feslo_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     feval_benv_order Θ Ξ (env_args p args) Φ' ->
     (forall p', feval_benv Θ Ξ (env_args p args) Φ' p' -> feval_exp_order Θ Ξ M p') ->
     feval_sel_order Θ Ξ (dm_local p (gu_body Δ Φ) args) x )
| feslo_alias :
  `( List.length args = List.length Δ ->
     feval_modexp_order Θ Ξ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ env_args p args ↘ h -> feval_sel_order Θ Ξ h x) ->
     feval_sel_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) x )
| feslo_member :
  `( feval_sel_order Θ Ξ (dm_member h ch) x )

with feval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| fesmo_global :
  `( (forall U r, gc_module Θ Ξ (qname_app pq (y :: nil)) <> Some (mr_alias U r)) ->
     feval_selm_order Θ Ξ (dm_global pq args) y )
| fesmo_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U ch) ->
     feval_selmc_order Θ Ξ (dm_local nil U args) ch ->
     feval_selm_order Θ Ξ (dm_global pq args) y )
| fesmo_unsat :
  `( List.length args < List.length (gu_params U) ->
     feval_selm_order Θ Ξ (dm_local p U args) y )
| fesmo_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     feval_benv_order Θ Ξ (env_args p args) Φ' ->
     feval_selm_order Θ Ξ (dm_local p (gu_body Δ Φ) args) y )
| fesmo_alias :
  `( List.length args = List.length Δ ->
     feval_modexp_order Θ Ξ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ env_args p args ↘ h -> feval_selm_order Θ Ξ h y) ->
     feval_selm_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) y )
| fesmo_member :
  `( feval_selm_order Θ Ξ (dm_member h ch) y )

with feval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fesco_one :
  `( feval_sel_order Θ Ξ h x ->
     feval_selc_order Θ Ξ h (x :: nil) )
| fesco_cons :
  `( ch <> nil ->
     feval_selm_order Θ Ξ h y ->
     (forall h1, feval_selm Θ Ξ h y h1 -> feval_selc_order Θ Ξ h1 ch) ->
     feval_selc_order Θ Ξ h (y :: ch) )

with feval_selmc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| fesmco_nil :
  `( feval_selmc_order Θ Ξ h nil )
| fesmco_cons :
  `( feval_selm_order Θ Ξ h y ->
     (forall h1, feval_selm Θ Ξ h y h1 -> feval_selmc_order Θ Ξ h1 ch) ->
     feval_selmc_order Θ Ξ h (y :: ch) )

with feval_benv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| febo_nil :
  `( feval_benv_order Θ Ξ p gm_nil )
| febo_def :
  `( feval_benv_order Θ Ξ p Φ ->
     (forall p1, feval_benv Θ Ξ p Φ p1 -> feval_exp_order Θ Ξ M p1) ->
     feval_benv_order Θ Ξ p (gm_ext Φ y (ge_def b pv A (Some M))) )
| febo_mod :
  `( feval_benv_order Θ Ξ p Φ ->
     feval_benv_order Θ Ξ p (gm_ext Φ y (ge_mod pm Uy)) ).

#[local]
Hint Constructors feval_exp_order feval_natrec_order feval_app_order feval_exps_order feval_apps_order
  feval_modexp_order feval_appm_order feval_sel_order feval_selm_order feval_selc_order feval_selmc_order
  feval_benv_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_feval_all :=
  repeat match goal with
    | H1 : feval_exp ?T ?X ?M ?p ?m1, H2 : feval_exp ?T ?X ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_feval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_natrec ?T ?X ?A ?MZ ?MS ?m ?p ?r1, H2 : feval_natrec ?T ?X ?A ?MZ ?MS ?m ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_natrec _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_app ?T ?X ?m ?n ?r1, H2 : feval_app ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_exps ?T ?X ?M ?p ?r1, H2 : feval_exps ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_feval T X)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_apps ?T ?X ?m ?n ?r1, H2 : feval_apps ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_modexp ?T ?X ?M ?p ?r1, H2 : feval_modexp ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : feval_appm ?T ?X ?m ?n ?r1, H2 : feval_appm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_sel ?T ?X ?m ?n ?r1, H2 : feval_sel ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selm ?T ?X ?m ?n ?r1, H2 : feval_selm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selc ?T ?X ?m ?n ?r1, H2 : feval_selc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_selmc ?T ?X ?m ?n ?r1, H2 : feval_selmc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_feval T X))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : feval_benv ?T ?X ?m ?n ?r1, H2 : feval_benv ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_feval_benv _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    end.

Lemma feval_order_sound : forall Θ Ξ,
    (forall m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_exp_order Θ Ξ m p) /\
    (forall A MZ MS m p r, ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r ->
       feval_natrec_order Θ Ξ A MZ MS m p) /\
    (forall m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> feval_app_order Θ Ξ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ p ↘ ms -> feval_exps_order Θ Ξ Ms p) /\
    (forall m ns r, $*ᶠ| m & ns | Θ ⍮ Ξ ↘ r -> feval_apps_order Θ Ξ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h -> feval_modexp_order Θ Ξ H p) /\
    (forall h n r, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r -> feval_appm_order Θ Ξ h n) /\
    (forall h x r, h ·ₜᶠ x Θ ⍮ Ξ ↘ r -> feval_sel_order Θ Ξ h x) /\
    (forall h y r, h ·ₘᶠ y Θ ⍮ Ξ ↘ r -> feval_selm_order Θ Ξ h y) /\
    (forall h ch r, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r -> feval_selc_order Θ Ξ h ch) /\
    (forall h ch r, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r -> feval_selmc_order Θ Ξ h ch) /\
    (forall p Φ p', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ p ↘ p' -> feval_benv_order Θ Ξ p Φ).
Proof.
  intros Θ Ξ; apply feval_mut_ind; intros;
    try solve [ eapply feslo_global_neut; eauto; intros; functional_feval_all; eauto
              | econstructor; try eassumption; intros; functional_feval_all; eauto ].
  - (* a chain of one more selection is not empty *)
    eapply fesco_cons; [| eauto | intros; functional_feval_all; eauto ].
    match goal with H : feval_selc _ _ _ ?c _ |- ?c <> nil => inversion H; discriminate end.
Qed.

Lemma feval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ a -> feval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (feval_order_sound Θ Ξ)). Qed.

Lemma feval_natrec_order_sound : forall Θ Ξ A MZ MS m p r,
    ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r ->
    feval_natrec_order Θ Ξ A MZ MS m p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (feval_order_sound Θ Ξ))). Qed.

Lemma feval_app_order_sound : forall Θ Ξ m n r, $ᶠ| m & n | Θ ⍮ Ξ ↘ r -> feval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (feval_order_sound Θ Ξ)))). Qed.

#[export]
Hint Resolve feval_exp_order_sound feval_natrec_order_sound feval_app_order_sound : mctt.

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

Section EvalImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A variable is looked up in the environment, without recursion. *)
  Definition feval_var_impl x p (H : feval_exp_order Θ Ξ #x p) : { d | ⟦ #x ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply feval_exp_var.
  Defined.

  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : feval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_natrec_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : feval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_exps_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_apps_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_modexp_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_appm_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_sel_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selm_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selc_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_selmc_order _ _ _ _ |- _ => progressive_invert H
    | H : feval_benv_order _ _ _ _ |- _ => progressive_invert H
    end.

  (** The lookups recorded in the order are the ones computed, which either
      fixes what is looked up or rules the case out. *)
  #[local]
  Ltac impl_obl_glob :=
    repeat match goal with
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_module _ _ ?p = Some (mr_alias _ _), H2 : forall U r, gc_module _ _ ?p <> Some (mr_alias U r) |- _ =>
          exfalso; exact (H2 _ _ H1)
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H : Nat.compare _ _ = Eq |- _ => apply Nat.compare_eq in H
      | H : Nat.compare _ _ = Lt |- _ => apply Nat.compare_lt_iff in H
      | H : Nat.compare _ _ = Gt |- _ => apply Nat.compare_gt_iff in H
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
    | H : feval_natrec_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : feval_app_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_modexp_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_appm_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_sel_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_selm_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_selc_order _ _ _ _ |- _ => dependent destruction H
    | H : feval_benv_order _ _ _ _ |- _ => dependent destruction H
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
    try solve [ eauto ];
    try econstructor; eauto.


  #[local]
  Ltac ev_obl :=
    intros; cbv beta in *;
    repeat impl_obl_tac1;
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
  | ℕ     , p, H => exist _ ℕᵈ _
  | zero  , p, H => exist _ zeroᵈ _
  | succ m, p, H =>
      let (r , Hr) := feval_exp_impl m p _ in
      exist _ succᵈ r _
  | rec M return A | zero -> MZ | succ -> MS end, p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      let (r, Hr)  := feval_natrec_impl A MZ MS m p _ in
      exist _ r _
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
  | M $ N   , p, H =>
      let (m , Hm) := feval_exp_impl M p _ in
      let (n , Hn) := feval_exp_impl N p _ in
      let (a, Ha) := feval_app_impl m n _ in
      exist _ a _
  | a_let (b_def oA M) B, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (r, Hr) := feval_exp_impl B (p ↦ m) _ in
      exist _ r _
  | ℓₘ U in B, p, H =>
      let (r, Hr) := feval_exp_impl B (p ↦ᵐ dm_local p U nil) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := feval_modexp_impl R p _ in
        let (f, Hf) := feval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := feval_exps_impl args p _ in
        let (r, Hr) := feval_apps_impl f ns _ in
        exist _ r _ }

  with feval_natrec_impl A MZ MS m p (H : feval_natrec_order Θ Ξ A MZ MS m p) : { d | ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
  | A, MZ, MS, zeroᵈ  , p, H =>
      let (mz, Hmz) := feval_exp_impl MZ p _ in
      exist _ mz _
  | A, MZ, MS, succᵈ m, p, H with inspect (exp_freshb 0 MS) := {
    (** The step case does not read the recursive result: it is not
        computed. *)
    | exist _ true E =>
        let (r, Hr) := feval_exp_impl MS (p ↦ m ↦ zeroᵈ) _ in
        exist _ r _
    | exist _ false E =>
        let (mr, Hmr) := feval_natrec_impl A MZ MS m p _ in
        let (r, Hr) := feval_exp_impl MS (p ↦ m ↦ mr) _ in
        exist _ r _ }
  | A, MZ, MS, ⇑ a m , p, H =>
      let (mz, Hmz) := feval_exp_impl MZ p _ in
      let (mA, HmA) := feval_exp_impl A (p ↦ ⇑ a m) _ in
      exist _ ⇑ mA recᵈ m under p return A | zero -> mz | succ -> MS end _
  | A, MZ, MS, _, p, H => False_rect _ _

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
  | _, n, H => False_rect _ _

  with feval_exps_impl Ms p (H : feval_exps_order Θ Ξ Ms p) : { ms | feval_exps Θ Ξ Ms p ms } by struct H :=
  | nil, p, H => exist _ nil _
  | M :: Ms, p, H =>
      let (m, Hm) := feval_exp_impl M p _ in
      let (ms, Hms) := feval_exps_impl Ms p _ in
      exist _ (m :: ms) _

  with feval_apps_impl m ns (H : feval_apps_order Θ Ξ m ns) : { r | feval_apps Θ Ξ m ns r } by struct H :=
  | m, nil, H => exist _ m _
  | m, n :: ns, H =>
      let (m1, Hm1) := feval_app_impl m n _ in
      let (r, Hr) := feval_apps_impl m1 ns _ in
      exist _ r _

  with feval_modexp_impl M p (H : feval_modexp_order Θ Ξ M p) : { h | ⟦ M ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | me_var x, p, H => exist _ (env_mod p x) _
  | me_unit fp, p, H => exist _ (dm_global (q_abs fp nil) nil) _
  | me_lit U, p, H => exist _ (dm_local p U nil) _
  | me_mem M y, p, H =>
      let (h, Hh) := feval_modexp_impl M p _ in
      let (r, Hr) := feval_selm_impl h y _ in
      exist _ r _
  | me_app M N, p, H =>
      let (h, Hh) := feval_modexp_impl M p _ in
      let (n, Hn) := feval_exp_impl N p _ in
      let (r, Hr) := feval_appm_impl h n _ in
      exist _ r _

  with feval_appm_impl h n (H : feval_appm_order Θ Ξ h n) : { r | feval_appm Θ Ξ h n r } by struct H :=
  | dm_global pq args, n, H => exist _ (dm_global pq (args ++ n :: nil)) _
  | dm_local p (gu_mk Δ (md_body Φ)) args, n, H => exist _ (dm_local p (gu_body Δ Φ) (args ++ n :: nil)) _
  | dm_local p (gu_mk Δ (md_alias E)) args, n, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (dm_local p (gu_mk Δ (md_alias E)) (args ++ n :: nil)) _
    | exist _ Eq C =>
        let (h, Hh) := feval_modexp_impl E (env_args p args) _ in
        let (r, Hr) := feval_appm_impl h n _ in
        exist _ r _
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, n, H =>
      let (h', Hh') := feval_appm_impl h n _ in
      let (r, Hr) := feval_selmc_impl h' ch _ in
      exist _ r _

  with feval_sel_impl h x (H : feval_sel_order Θ Ξ h x) : { r | feval_sel Θ Ξ h x r } by struct H :=
  | dm_global pq args, x, H with inspect (gc_resolve Θ Ξ (qname_app pq (x :: nil))) := {
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
    | exist _ None E => False_rect _ _ }
  | dm_local p (gu_mk Δ D) args, x, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (d_member (dm_local p (gu_mk Δ D) args) (x :: nil)) _
    | exist _ Eq C with D := {
      | md_body Φ with inspect (gm_prefix_upto Φ x) := {
        | exist _ (Some (gm_ext Φ' _ (ge_def b pv A (Some M)))) P =>
            let (p', Hp') := feval_benv_impl (env_args p args) Φ' _ in
            let (r, Hr) := feval_exp_impl M p' _ in
            exist _ r _
        | exist _ _ P => False_rect _ _ }
      | md_alias E =>
          let (h, Hh) := feval_modexp_impl E (env_args p args) _ in
          let (r, Hr) := feval_sel_impl h x _ in
          exist _ r _ }
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with feval_selm_impl h y (H : feval_selm_order Θ Ξ h y) : { r | feval_selm Θ Ξ h y r } by struct H :=
  | dm_global pq args, y, H with inspect (gc_module Θ Ξ (qname_app pq (y :: nil))) := {
    | exist _ (Some (mr_alias U ch)) E =>
        let (r, Hr) := feval_selmc_impl (dm_local nil U args) ch _ in
        exist _ r _
    | exist _ _ E => exist _ (dm_global (qname_app pq (y :: nil)) args) _ }
  | dm_local p (gu_mk Δ D) args, y, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (dm_member (dm_local p (gu_mk Δ D) args) (y :: nil)) _
    | exist _ Eq C with D := {
      | md_body Φ with inspect (gm_prefix_upto Φ y) := {
        | exist _ (Some (gm_ext Φ' _ (ge_mod _ Uy))) P =>
            let (p', Hp') := feval_benv_impl (env_args p args) Φ' _ in
            exist _ (dm_local p' Uy nil) _
        | exist _ _ P => False_rect _ _ }
      | md_alias E =>
          let (h, Hh) := feval_modexp_impl E (env_args p args) _ in
          let (r, Hr) := feval_selm_impl h y _ in
          exist _ r _ }
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, y, H => exist _ (dm_member h (ch ++ y :: nil)) _

  with feval_selc_impl h ch (H : feval_selc_order Θ Ξ h ch) : { r | feval_selc Θ Ξ h ch r } by struct H :=
  | h, x :: nil, H =>
      let (r, Hr) := feval_sel_impl h x _ in
      exist _ r _
  | h, y :: ch, H =>
      let (h1, Hh1) := feval_selm_impl h y _ in
      let (r, Hr) := feval_selc_impl h1 ch _ in
      exist _ r _
  | h, nil, H => False_rect _ _

  with feval_selmc_impl h ch (H : feval_selmc_order Θ Ξ h ch) : { r | feval_selmc Θ Ξ h ch r } by struct H :=
  | h, nil, H => exist _ h _
  | h, y :: ch, H =>
      let (h1, Hh1) := feval_selm_impl h y _ in
      let (r, Hr) := feval_selmc_impl h1 ch _ in
      exist _ r _

  with feval_benv_impl p Φ (H : feval_benv_order Θ Ξ p Φ) : { p' | feval_benv Θ Ξ p Φ p' } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y (ge_def b pv A (Some M)), H =>
      let (p1, Hp1) := feval_benv_impl p Φ _ in
      let (m, Hm) := feval_exp_impl M p1 _ in
      exist _ (p1 ↦ m) _
  | p, gm_ext Φ y (ge_def b pv A None), H => False_rect _ _
  | p, gm_ext Φ y (ge_mod _ Uy), H =>
      let (p1, Hp1) := feval_benv_impl p Φ _ in
      exist _ (p1 ↦ᵐ dm_local p1 Uy nil) _
  | p, gm_open Φ _ _, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([ev_obl]).  They are transparent: the order premises are the
    arguments of the structural recursion. *)
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
Next Obligation. ev_obl. Defined.
End EvalImpl.

Extraction Inline feval_exp_impl_functional
  feval_natrec_impl_functional
  feval_app_impl_functional
  feval_exps_impl_functional
  feval_apps_impl_functional
  feval_modexp_impl_functional
  feval_appm_impl_functional
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

Lemma feval_exp_impl_complete : forall Θ Ξ M p m,
    ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ m ->
    exists H H', feval_exp_impl Θ Ξ M p H = exist _ m H'.
Proof.
  intros; functional_feval_complete.
Qed.

Lemma feval_natrec_impl_complete : forall Θ Ξ A MZ MS m p r,
    ⟦recᶠ m return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ p ↘ r ->
    exists H H', feval_natrec_impl Θ Ξ A MZ MS m p H = exist _ r H'.
Proof.
  intros; functional_feval_complete.
Qed.

Lemma feval_app_impl_complete : forall Θ Ξ m n r,
    $ᶠ| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', feval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_feval_complete.
Qed.
