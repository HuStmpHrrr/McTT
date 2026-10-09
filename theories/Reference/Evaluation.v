From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Semantic Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

(** * The Reference Evaluator

    The evaluator of [Core.Semantic.Evaluation], with its termination orders.
    It is not extracted: [Extraction.Evaluation] is the evaluator that is, of
    the relation of [Extraction.FastEval], and [Reference.Refinement] relates
    the two.  The orders here are those of the specification of
    normalization ([Extraction.NbE]). *)

(** The termination orders mirror the evaluation relations, one for each, in
    the same global context.  A transparent global recurses into its resolved
    body, which [eeo_glob_delta] records; an alias recurses into its target.
    Each premise that uses a value is quantified over the values its earlier
    premises evaluate to. *)

Inductive eval_exp_order (Θ : gdeps) (Ξ : gstack) : exp -> env -> Prop :=
| eeo_typ :
  `( eval_exp_order Θ Ξ Typeω@i p )
(** A small universe evaluates its level. *)
| eeo_univ :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ Type⟨M⟩ p )
(** An environment is total, so a variable always terminates. *)
| eeo_var :
  `( eval_exp_order Θ Ξ #x p )
| eeo_level :
  `( eval_exp_order Θ Ξ (Level@n) p )
| eeo_llit :
  `( eval_exp_order Θ Ξ (𝕃ᵒ o) p )
| eeo_succl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ (succl M) p )
| eeo_maxl :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ N p ->
     eval_exp_order Θ Ξ (maxl M N) p )
| eeo_nat :
  `( eval_exp_order Θ Ξ ℕ p )
| eeo_zero :
  `( eval_exp_order Θ Ξ zero p )
| eeo_succ :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ succ M p )
| eeo_natrec :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> eval_natrec_order Θ Ξ A MZ MS m p) ->
     eval_exp_order Θ Ξ rec M return A | zero -> MZ | succ -> MS end p )
| eeo_True :
  `( eval_exp_order Θ Ξ ⊤ p )
| eeo_true :
  `( eval_exp_order Θ Ξ ⋆ p )
| eeo_False :
  `( eval_exp_order Θ Ξ ⊥ p )
(** The scrutinee of [efq] must evaluate to a neutral, since no other value
    has a rule. *)
| eeo_exfalso :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> exists b n, m = ⇑ b n) ->
     (forall b m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ ⇑ b m -> eval_exp_order Θ Ξ A (p ↦ ⇑ b m)) ->
     eval_exp_order Θ Ξ (efq M return A) p )
| eeo_pi :
  `( eval_exp_order Θ Ξ A p ->
     eval_exp_order Θ Ξ (Π A B) p )
| eeo_fn :
  `( eval_exp_order Θ Ξ (λ A M) p )
| eeo_app :
  `( eval_exp_order Θ Ξ M p ->
     eval_exp_order Θ Ξ N p ->
     (forall m n, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_app_order Θ Ξ m n) ->
     eval_exp_order Θ Ξ (M $ N) p )
| eeo_let :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> eval_exp_order Θ Ξ B (p ↦ m)) ->
     eval_exp_order Θ Ξ (a_let (b_def oA M) B) p )
| eeo_let_mod :
  `( eval_exp_order Θ Ξ B (p ↦ᵐ dm_local p U nil) ->
     eval_exp_order Θ Ξ (ℓₘ U in B) p )
| eeo_mem :
  `( modexp_spine H = (R, args, pre) ->
     eval_modexp_order Θ Ξ R p ->
     (forall h, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selc_order Θ Ξ h (pre ++ x :: nil)) ->
     eval_exps_order Θ Ξ args p ->
     (forall h f ns, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selc Θ Ξ h (pre ++ x :: nil) f ->
        eval_exps Θ Ξ args p ns -> eval_apps_order Θ Ξ f ns) ->
     eval_exp_order Θ Ξ (a_mem H x) p )

with eval_natrec_order (Θ : gdeps) (Ξ : gstack) : exp -> exp -> exp -> domain -> env -> Prop :=
| eno_zero :
  `( eval_exp_order Θ Ξ MZ p ->
     eval_natrec_order Θ Ξ A MZ MS zeroᵈ p )
| eno_succ :
  `( eval_natrec_order Θ Ξ A MZ MS b p ->
     (forall r, ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ r -> eval_exp_order Θ Ξ MS (p ↦ b ↦ r)) ->
     eval_natrec_order Θ Ξ A MZ MS succᵈ b p )
| eno_neut :
  `( eval_exp_order Θ Ξ MZ p ->
     eval_exp_order Θ Ξ A (p ↦ ⇑ a m) ->
     eval_natrec_order Θ Ξ A MZ MS ⇑ a m p )

with eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| eao_fn :
  `( eval_exp_order Θ Ξ M (p ↦ n) ->
     eval_app_order Θ Ξ λᵈ p M n )
| eao_neut :
  `( eval_exp_order Θ Ξ B (p ↦ n) ->
     eval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n )
| eao_member :
  `( eval_appm_order Θ Ξ h n ->
     (forall h', eval_appm Θ Ξ h n h' -> eval_selc_order Θ Ξ h' ch) ->
     eval_app_order Θ Ξ (d_member h ch) n )

with eval_exps_order (Θ : gdeps) (Ξ : gstack) : list exp -> env -> Prop :=
| eso_nil :
  `( eval_exps_order Θ Ξ nil p )
| eso_cons :
  `( eval_exp_order Θ Ξ M p ->
     eval_exps_order Θ Ξ Ms p ->
     eval_exps_order Θ Ξ (M :: Ms) p )

with eval_apps_order (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> Prop :=
| easo_nil :
  `( eval_apps_order Θ Ξ m nil )
| easo_cons :
  `( eval_app_order Θ Ξ m n ->
     (forall m1, $| m & n | Θ ⍮ Ξ ↘ m1 -> eval_apps_order Θ Ξ m1 args) ->
     eval_apps_order Θ Ξ m (n :: args) )

with eval_modexp_order (Θ : gdeps) (Ξ : gstack) : modexp -> env -> Prop :=
| emo_var :
  `( eval_modexp_order Θ Ξ (me_var x) p )
| emo_unit :
  `( eval_modexp_order Θ Ξ (me_unit fp) p )
| emo_lit :
  `( eval_modexp_order Θ Ξ (me_lit U) p )
| emo_mem :
  `( eval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selm_order Θ Ξ h y) ->
     eval_modexp_order Θ Ξ (me_mem H y) p )
| emo_app :
  `( eval_modexp_order Θ Ξ H p ->
     eval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_appm_order Θ Ξ h n) ->
     eval_modexp_order Θ Ξ (me_app H N) p )

with eval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
| eapo_global :
  `( eval_appm_order Θ Ξ (dm_global pq args) n )
| eapo_body :
  `( List.length args < List.length Δ ->
     eval_appm_order Θ Ξ (dm_local p (gu_body Δ Φ) args) n )
| eapo_alias_unsat :
  `( List.length args < List.length Δ ->
     eval_appm_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) n )
| eapo_alias :
  `( List.length args = List.length Δ ->
     eval_modexp_order Θ Ξ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐ Θ ⍮ Ξ ⍮ env_args p args ↘ h -> eval_appm_order Θ Ξ h n) ->
     eval_appm_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) n )
| eapo_member :
  `( eval_appm_order Θ Ξ h n ->
     (forall h', eval_appm Θ Ξ h n h' -> eval_selmc_order Θ Ξ h' ch) ->
     eval_appm_order Θ Ξ (dm_member h ch) n )

with eval_sel_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| eslo_global :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def true pv A (Some M)) ->
     eval_exp_order Θ Ξ M nil ->
     (forall f, ⟦ M ⟧ Θ ⍮ Ξ ⍮ nil ↘ f -> eval_apps_order Θ Ξ f args) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
| eslo_global_neut :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     eval_exp_order Θ Ξ A nil ->
     (forall a, ⟦ A ⟧ Θ ⍮ Ξ ⍮ nil ↘ a -> eval_apps_order Θ Ξ (⇑ a (d_glob (qname_app pq (x :: nil)))) args) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
| eslo_unsat :
  `( List.length args < List.length (gu_params U) ->
     eval_sel_order Θ Ξ (dm_local p U args) x )
| eslo_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     eval_benv_order Θ Ξ (env_args p args) Φ' ->
     (forall p', eval_benv Θ Ξ (env_args p args) Φ' p' -> eval_exp_order Θ Ξ M p') ->
     eval_sel_order Θ Ξ (dm_local p (gu_body Δ Φ) args) x )
| eslo_alias :
  `( List.length args = List.length Δ ->
     eval_modexp_order Θ Ξ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐ Θ ⍮ Ξ ⍮ env_args p args ↘ h -> eval_sel_order Θ Ξ h x) ->
     eval_sel_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) x )
| eslo_member :
  `( eval_sel_order Θ Ξ (dm_member h ch) x )

with eval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| esmo_global :
  `( (forall U r, gc_module Θ Ξ (qname_app pq (y :: nil)) <> Some (mr_alias U r)) ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
| esmo_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U ch) ->
     eval_selmc_order Θ Ξ (dm_local nil U args) ch ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
| esmo_unsat :
  `( List.length args < List.length (gu_params U) ->
     eval_selm_order Θ Ξ (dm_local p U args) y )
| esmo_body :
  `( List.length args = List.length Δ ->
     gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     eval_benv_order Θ Ξ (env_args p args) Φ' ->
     eval_selm_order Θ Ξ (dm_local p (gu_body Δ Φ) args) y )
| esmo_alias :
  `( List.length args = List.length Δ ->
     eval_modexp_order Θ Ξ E (env_args p args) ->
     (forall h, ⟦ E ⟧ᵐ Θ ⍮ Ξ ⍮ env_args p args ↘ h -> eval_selm_order Θ Ξ h y) ->
     eval_selm_order Θ Ξ (dm_local p (gu_mk Δ (md_alias E)) args) y )
| esmo_member :
  `( eval_selm_order Θ Ξ (dm_member h ch) y )

with eval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| esco_one :
  `( eval_sel_order Θ Ξ h x ->
     eval_selc_order Θ Ξ h (x :: nil) )
| esco_cons :
  `( ch <> nil ->
     eval_selm_order Θ Ξ h y ->
     (forall h1, eval_selm Θ Ξ h y h1 -> eval_selc_order Θ Ξ h1 ch) ->
     eval_selc_order Θ Ξ h (y :: ch) )

with eval_selmc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| esmco_nil :
  `( eval_selmc_order Θ Ξ h nil )
| esmco_cons :
  `( eval_selm_order Θ Ξ h y ->
     (forall h1, eval_selm Θ Ξ h y h1 -> eval_selmc_order Θ Ξ h1 ch) ->
     eval_selmc_order Θ Ξ h (y :: ch) )

with eval_benv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| ebo_nil :
  `( eval_benv_order Θ Ξ p gm_nil )
| ebo_def :
  `( eval_benv_order Θ Ξ p Φ ->
     (forall p1, eval_benv Θ Ξ p Φ p1 -> eval_exp_order Θ Ξ M p1) ->
     eval_benv_order Θ Ξ p (gm_ext Φ y (ge_def b pv A (Some M))) )
| ebo_mod :
  `( eval_benv_order Θ Ξ p Φ ->
     eval_benv_order Θ Ξ p (gm_ext Φ y (ge_mod pm Uy)) ).

#[local]
Hint Constructors eval_exp_order eval_natrec_order eval_app_order eval_exps_order eval_apps_order
  eval_modexp_order eval_appm_order eval_sel_order eval_selm_order eval_selc_order eval_selmc_order
  eval_benv_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_eval_all :=
  repeat match goal with
    | H1 : eval_exp ?T ?X ?M ?p ?m1, H2 : eval_exp ?T ?X ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_eval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_natrec ?T ?X ?A ?MZ ?MS ?m ?p ?r1, H2 : eval_natrec ?T ?X ?A ?MZ ?MS ?m ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_natrec _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_app ?T ?X ?m ?n ?r1, H2 : eval_app ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_exps ?T ?X ?M ?p ?r1, H2 : eval_exps ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_eval T X)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_apps ?T ?X ?m ?n ?r1, H2 : eval_apps ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_modexp ?T ?X ?M ?p ?r1, H2 : eval_modexp ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_appm ?T ?X ?m ?n ?r1, H2 : eval_appm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_sel ?T ?X ?m ?n ?r1, H2 : eval_sel ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selm ?T ?X ?m ?n ?r1, H2 : eval_selm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selc ?T ?X ?m ?n ?r1, H2 : eval_selc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selmc ?T ?X ?m ?n ?r1, H2 : eval_selmc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_benv ?T ?X ?m ?n ?r1, H2 : eval_benv ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_benv _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    end.

Lemma eval_order_sound : forall Θ Ξ,
    (forall m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_exp_order Θ Ξ m p) /\
    (forall A MZ MS m p r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ r ->
       eval_natrec_order Θ Ξ A MZ MS m p) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms -> eval_exps_order Θ Ξ Ms p) /\
    (forall m ns r, $*| m & ns | Θ ⍮ Ξ ↘ r -> eval_apps_order Θ Ξ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_modexp_order Θ Ξ H p) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> eval_appm_order Θ Ξ h n) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> eval_sel_order Θ Ξ h x) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> eval_selm_order Θ Ξ h y) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> eval_selc_order Θ Ξ h ch) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> eval_selmc_order Θ Ξ h ch) /\
    (forall p Φ p', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' -> eval_benv_order Θ Ξ p Φ).
Proof.
  intros Θ Ξ; apply eval_mut_ind; intros;
    try solve [ eapply eslo_global_neut; eauto; intros; functional_eval_all; eauto
              | econstructor; try eassumption; intros; functional_eval_all; eauto ].
  - (* a chain of one more selection is not empty *)
    eapply esco_cons; [| eauto | intros; functional_eval_all; eauto ].
    match goal with H : eval_selc _ _ _ ?c _ |- ?c <> nil => inversion H; discriminate end.
Qed.

Lemma eval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (eval_order_sound Θ Ξ)). Qed.

Lemma eval_natrec_order_sound : forall Θ Ξ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ r ->
    eval_natrec_order Θ Ξ A MZ MS m p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (eval_order_sound Θ Ξ))). Qed.

Lemma eval_app_order_sound : forall Θ Ξ m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (eval_order_sound Θ Ξ)))). Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_natrec_order_sound eval_app_order_sound : mctt.

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

Section EvalImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A variable is looked up in the environment, without recursion. *)
  Definition eval_var_impl x p (H : eval_exp_order Θ Ξ #x p) : { d | ⟦ #x ⟧ Θ ⍮ Ξ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply eval_exp_var.
  Defined.

  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_natrec_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_exps_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_apps_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_modexp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_appm_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_sel_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selm_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selc_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selmc_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_benv_order _ _ _ _ |- _ => progressive_invert H
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
      | H : forall m, eval_exp _ _ ?M ?p m -> exists _ _, m = ⇑ _ _, Hm : eval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ? & ?); clear H
      end.

  #[local]
  Ltac impl_obl_split :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_natrec_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_app_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_modexp_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_appm_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_sel_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_selm_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_selc_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_benv_order _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac impl_obl_finish :=
    impl_obl_exfalso;
    impl_obl_glob;
    cbn [gu_params] in *;
    try solve [ intuition discriminate ];
    try solve [ exfalso; lia ];
    try solve [ eapply eval_sel_global_neut; eauto ];
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
  Equations eval_exp_impl m p (H : eval_exp_order Θ Ξ m p) : { d | ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
  | Typeω@i, p, H => exist _ 𝕌ω@i _
  | Type⟨M⟩, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      exist _ 𝕌@m _
  | #x    , p, H => eval_var_impl x p H
  | Level@n, p, H => exist _ (Levelᵈ@n) _
  | 𝕃ᵒ o  , p, H => exist _ (dlvl_lit o) _
  | succl M, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      exist _ (dlvl_suc m) _
  | maxl M N, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (n , Hn) := eval_exp_impl N p _ in
      exist _ (dlvl_max m n) _
  | ℕ     , p, H => exist _ ℕᵈ _
  | zero  , p, H => exist _ zeroᵈ _
  | succ m, p, H =>
      let (r , Hr) := eval_exp_impl m p _ in
      exist _ succᵈ r _
  | rec M return A | zero -> MZ | succ -> MS end, p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (r, Hr)  := eval_natrec_impl A MZ MS m p _ in
      exist _ r _
  | ⊤     , p, H => exist _ ⊤ᵈ _
  | ⋆     , p, H => exist _ ⋆ᵈ _
  | ⊥     , p, H => exist _ ⊥ᵈ _
  | efq M return A, p, H with eval_exp_impl M p _ := {
    | exist _ (⇑ b m) Hm =>
        let (a, Ha) := eval_exp_impl A (p ↦ ⇑ b m) _ in
        exist _ ⇑ a (efqᵈ m under p return A) _
    | exist _ _ Hm => False_rect _ _ }
  | Π A B , p, H =>
      let (r , Hr) := eval_exp_impl A p _ in
      exist _ Πᵈ r p B _
  | λ A M , p, H => exist _ λᵈ p M _
  | M $ N   , p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (n , Hn) := eval_exp_impl N p _ in
      let (a, Ha) := eval_app_impl m n _ in
      exist _ a _
  | a_let (b_def oA M) B, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ m) _ in
      exist _ r _
  | ℓₘ U in B, p, H =>
      let (r, Hr) := eval_exp_impl B (p ↦ᵐ dm_local p U nil) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := eval_modexp_impl R p _ in
        let (f, Hf) := eval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := eval_exps_impl args p _ in
        let (r, Hr) := eval_apps_impl f ns _ in
        exist _ r _ }

  with eval_natrec_impl A MZ MS m p (H : eval_natrec_order Θ Ξ A MZ MS m p) : { d | ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ d } by struct H :=
  | A, MZ, MS, zeroᵈ  , p, H =>
      let (mz, Hmz) := eval_exp_impl MZ p _ in
      exist _ mz _
  | A, MZ, MS, succᵈ m, p, H =>
      let (mr, Hmr) := eval_natrec_impl A MZ MS m p _ in
      let (r, Hr) := eval_exp_impl MS (p ↦ m ↦ mr) _ in
      exist _ r _
  | A, MZ, MS, ⇑ a m , p, H =>
      let (mz, Hmz) := eval_exp_impl MZ p _ in
      let (mA, HmA) := eval_exp_impl A (p ↦ ⇑ a m) _ in
      exist _ ⇑ mA recᵈ m under p return A | zero -> mz | succ -> MS end _
  | A, MZ, MS, _, p, H => False_rect _ _

  with eval_app_impl m n (H : eval_app_order Θ Ξ m n) : { d | $| m & n | Θ ⍮ Ξ ↘ d } by struct H :=
  | λᵈ p M        , n, H =>
      let (m, Hm) := eval_exp_impl M (p ↦ n) _ in
      exist _ m _
  | ⇑ (Πᵈ a p B) m, n, H =>
      let (b, Hb) := eval_exp_impl B (p ↦ n) _ in
      exist _ ⇑ b (m $ᵈ ⇓ a n) _
  | d_member h ch, n, H =>
      let (h', Hh') := eval_appm_impl h n _ in
      let (r, Hr) := eval_selc_impl h' ch _ in
      exist _ r _
  | _, n, H => False_rect _ _

  with eval_exps_impl Ms p (H : eval_exps_order Θ Ξ Ms p) : { ms | eval_exps Θ Ξ Ms p ms } by struct H :=
  | nil, p, H => exist _ nil _
  | M :: Ms, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (ms, Hms) := eval_exps_impl Ms p _ in
      exist _ (m :: ms) _

  with eval_apps_impl m ns (H : eval_apps_order Θ Ξ m ns) : { r | eval_apps Θ Ξ m ns r } by struct H :=
  | m, nil, H => exist _ m _
  | m, n :: ns, H =>
      let (m1, Hm1) := eval_app_impl m n _ in
      let (r, Hr) := eval_apps_impl m1 ns _ in
      exist _ r _

  with eval_modexp_impl M p (H : eval_modexp_order Θ Ξ M p) : { h | ⟦ M ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | me_var x, p, H => exist _ (env_mod p x) _
  | me_unit fp, p, H => exist _ (dm_global (q_abs fp nil) nil) _
  | me_lit U, p, H => exist _ (dm_local p U nil) _
  | me_mem M y, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (r, Hr) := eval_selm_impl h y _ in
      exist _ r _
  | me_app M N, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (n, Hn) := eval_exp_impl N p _ in
      let (r, Hr) := eval_appm_impl h n _ in
      exist _ r _

  with eval_appm_impl h n (H : eval_appm_order Θ Ξ h n) : { r | eval_appm Θ Ξ h n r } by struct H :=
  | dm_global pq args, n, H => exist _ (dm_global pq (args ++ n :: nil)) _
  | dm_local p (gu_mk Δ (md_body Φ)) args, n, H => exist _ (dm_local p (gu_body Δ Φ) (args ++ n :: nil)) _
  | dm_local p (gu_mk Δ (md_alias E)) args, n, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (dm_local p (gu_mk Δ (md_alias E)) (args ++ n :: nil)) _
    | exist _ Eq C =>
        let (h, Hh) := eval_modexp_impl E (env_args p args) _ in
        let (r, Hr) := eval_appm_impl h n _ in
        exist _ r _
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, n, H =>
      let (h', Hh') := eval_appm_impl h n _ in
      let (r, Hr) := eval_selmc_impl h' ch _ in
      exist _ r _

  with eval_sel_impl h x (H : eval_sel_order Θ Ξ h x) : { r | eval_sel Θ Ξ h x r } by struct H :=
  | dm_global pq args, x, H with inspect (gc_resolve Θ Ξ (qname_app pq (x :: nil))) := {
    | exist _ (Some (ge_def true pv A (Some M))) E =>
        let (f, Hf) := eval_exp_impl M nil _ in
        let (r, Hr) := eval_apps_impl f args _ in
        exist _ r _
    | exist _ (Some (ge_def true _ A None)) E =>
        let (a, Ha) := eval_exp_impl A nil _ in
        let (r, Hr) := eval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_def false _ A B)) E =>
        let (a, Ha) := eval_exp_impl A nil _ in
        let (r, Hr) := eval_apps_impl (⇑ a (d_glob (qname_app pq (x :: nil)))) args _ in
        exist _ r _
    | exist _ (Some (ge_mod _ _)) E => False_rect _ _
    | exist _ None E => False_rect _ _ }
  | dm_local p (gu_mk Δ D) args, x, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (d_member (dm_local p (gu_mk Δ D) args) (x :: nil)) _
    | exist _ Eq C with D := {
      | md_body Φ with inspect (gm_prefix_upto Φ x) := {
        | exist _ (Some (gm_ext Φ' _ (ge_def b pv A (Some M)))) P =>
            let (p', Hp') := eval_benv_impl (env_args p args) Φ' _ in
            let (r, Hr) := eval_exp_impl M p' _ in
            exist _ r _
        | exist _ _ P => False_rect _ _ }
      | md_alias E =>
          let (h, Hh) := eval_modexp_impl E (env_args p args) _ in
          let (r, Hr) := eval_sel_impl h x _ in
          exist _ r _ }
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with eval_selm_impl h y (H : eval_selm_order Θ Ξ h y) : { r | eval_selm Θ Ξ h y r } by struct H :=
  | dm_global pq args, y, H with inspect (gc_module Θ Ξ (qname_app pq (y :: nil))) := {
    | exist _ (Some (mr_alias U ch)) E =>
        let (r, Hr) := eval_selmc_impl (dm_local nil U args) ch _ in
        exist _ r _
    | exist _ _ E => exist _ (dm_global (qname_app pq (y :: nil)) args) _ }
  | dm_local p (gu_mk Δ D) args, y, H with inspect (Nat.compare (List.length args) (List.length Δ)) := {
    | exist _ Lt C => exist _ (dm_member (dm_local p (gu_mk Δ D) args) (y :: nil)) _
    | exist _ Eq C with D := {
      | md_body Φ with inspect (gm_prefix_upto Φ y) := {
        | exist _ (Some (gm_ext Φ' _ (ge_mod _ Uy))) P =>
            let (p', Hp') := eval_benv_impl (env_args p args) Φ' _ in
            exist _ (dm_local p' Uy nil) _
        | exist _ _ P => False_rect _ _ }
      | md_alias E =>
          let (h, Hh) := eval_modexp_impl E (env_args p args) _ in
          let (r, Hr) := eval_selm_impl h y _ in
          exist _ r _ }
    | exist _ Gt C => False_rect _ _ }
  | dm_member h ch, y, H => exist _ (dm_member h (ch ++ y :: nil)) _

  with eval_selc_impl h ch (H : eval_selc_order Θ Ξ h ch) : { r | eval_selc Θ Ξ h ch r } by struct H :=
  | h, x :: nil, H =>
      let (r, Hr) := eval_sel_impl h x _ in
      exist _ r _
  | h, y :: ch, H =>
      let (h1, Hh1) := eval_selm_impl h y _ in
      let (r, Hr) := eval_selc_impl h1 ch _ in
      exist _ r _
  | h, nil, H => False_rect _ _

  with eval_selmc_impl h ch (H : eval_selmc_order Θ Ξ h ch) : { r | eval_selmc Θ Ξ h ch r } by struct H :=
  | h, nil, H => exist _ h _
  | h, y :: ch, H =>
      let (h1, Hh1) := eval_selm_impl h y _ in
      let (r, Hr) := eval_selmc_impl h1 ch _ in
      exist _ r _

  with eval_benv_impl p Φ (H : eval_benv_order Θ Ξ p Φ) : { p' | eval_benv Θ Ξ p Φ p' } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y (ge_def b pv A (Some M)), H =>
      let (p1, Hp1) := eval_benv_impl p Φ _ in
      let (m, Hm) := eval_exp_impl M p1 _ in
      exist _ (p1 ↦ m) _
  | p, gm_ext Φ y (ge_def b pv A None), H => False_rect _ _
  | p, gm_ext Φ y (ge_mod _ Uy), H =>
      let (p1, Hp1) := eval_benv_impl p Φ _ in
      exist _ (p1 ↦ᵐ dm_local p1 Uy nil) _
  | p, gm_open Φ _ _, H => False_rect _ _.

(** Each of the 190 holes is discharged by name rather than by Equations'
    automatic tactic, so that one obligation can never make the whole
    definition retry: [ev_obl] is an order premise read off the order of the
    whole by inversion, the evaluation itself by its rule, or a branch the
    order rules out. *)
Obligation 1. ev_obl. Qed.
Obligation 2. ev_obl. Defined.
Obligation 3. ev_obl. Qed.
Obligation 4. ev_obl. Qed.
Obligation 5. ev_obl. Qed.
Obligation 6. ev_obl. Defined.
Obligation 7. ev_obl. Qed.
Obligation 8. ev_obl. Defined.
Obligation 9. ev_obl. Defined.
Obligation 10. ev_obl. Qed.
Obligation 11. ev_obl. Qed.
Obligation 12. ev_obl. Qed.
Obligation 13. ev_obl. Defined.
Obligation 14. ev_obl. Qed.
Obligation 15. ev_obl. Defined.
Obligation 16. ev_obl. Defined.
Obligation 17. ev_obl. Qed.
Obligation 18. ev_obl. Qed.
Obligation 19. ev_obl. Qed.
Obligation 20. ev_obl. Qed.
Obligation 21. ev_obl. Defined.
Obligation 22. ev_obl. Qed.
Obligation 23. ev_obl. Qed.
Obligation 24. ev_obl. Qed.
Obligation 25. ev_obl. Qed.
Obligation 26. ev_obl. Qed.
Obligation 27. ev_obl. Qed.
Obligation 28. ev_obl. Qed.
Obligation 29. ev_obl. Qed.
Obligation 30. ev_obl. Qed.
Obligation 31. ev_obl. Qed.
Obligation 32. ev_obl. Qed.
Obligation 33. ev_obl. Qed.
Obligation 34. ev_obl. Defined.
Obligation 35. ev_obl. Qed.
Obligation 36. ev_obl. Qed.
Obligation 37. ev_obl. Defined.
Obligation 38. ev_obl. Qed.
Obligation 39. ev_obl. Qed.
Obligation 40. ev_obl. Defined.
Obligation 41. ev_obl. Defined.
Obligation 42. ev_obl. Defined.
Obligation 43. ev_obl. Qed.
Obligation 44. ev_obl. Defined.
Obligation 45. ev_obl. Defined.
Obligation 46. ev_obl. Qed.
Obligation 47. ev_obl. Defined.
Obligation 48. ev_obl. Qed.
Obligation 49. ev_obl. Defined.
Obligation 50. ev_obl. Defined.
Obligation 51. ev_obl. Defined.
Obligation 52. ev_obl. Defined.
Obligation 53. ev_obl. Qed.
Obligation 54. ev_obl. Qed.
Obligation 55. ev_obl. Qed.
Obligation 56. ev_obl. Qed.
Obligation 57. ev_obl. Qed.
Obligation 58. ev_obl. Qed.
Obligation 59. ev_obl. Qed.
Obligation 60. ev_obl. Defined.
Obligation 61. ev_obl. Qed.
Obligation 62. ev_obl. Defined.
Obligation 63. ev_obl. Defined.
Obligation 64. ev_obl. Qed.
Obligation 65. ev_obl. Qed.
Obligation 66. ev_obl. Qed.
Obligation 67. ev_obl. Qed.
Obligation 68. ev_obl. Qed.
Obligation 69. ev_obl. Defined.
Obligation 70. ev_obl. Defined.
Obligation 71. ev_obl. Qed.
Obligation 72. ev_obl. Qed.
Obligation 73. ev_obl. Qed.
Obligation 74. ev_obl. Qed.
Obligation 75. ev_obl. Qed.
Obligation 76. ev_obl. Qed.
Obligation 77. ev_obl. Qed.
Obligation 78. ev_obl. Qed.
Obligation 79. ev_obl. Qed.
Obligation 80. ev_obl. Qed.
Obligation 81. ev_obl. Qed.
Obligation 82. ev_obl. Qed.
Obligation 83. ev_obl. Qed.
Obligation 84. ev_obl. Defined.
Obligation 85. ev_obl. Qed.
Obligation 86. ev_obl. Qed.
Obligation 87. ev_obl. Defined.
Obligation 88. ev_obl. Qed.
Obligation 89. ev_obl. Qed.
Obligation 90. ev_obl. Qed.
Obligation 91. ev_obl. Qed.
Obligation 92. ev_obl. Qed.
Obligation 93. ev_obl. Qed.
Obligation 94. ev_obl. Qed.
Obligation 95. ev_obl. Qed.
Obligation 96. ev_obl. Qed.
Obligation 97. ev_obl. Qed.
Obligation 98. ev_obl. Qed.
Obligation 99. ev_obl. Qed.
Obligation 100. ev_obl. Qed.
Obligation 101. ev_obl. Defined.
Obligation 102. ev_obl. Defined.
Obligation 103. ev_obl. Qed.
Obligation 104. ev_obl. Qed.
Obligation 105. ev_obl. Defined.
Obligation 106. ev_obl. Defined.
Obligation 107. ev_obl. Qed.
Obligation 108. ev_obl. Qed.
Obligation 109. ev_obl. Defined.
Obligation 110. ev_obl. Defined.
Obligation 111. ev_obl. Qed.
Obligation 112. ev_obl. Qed.
Obligation 113. ev_obl. Qed.
Obligation 114. ev_obl. Defined.
Obligation 115. ev_obl. Defined.
Obligation 116. ev_obl. Qed.
Obligation 117. ev_obl. Defined.
Obligation 118. ev_obl. Defined.
Obligation 119. ev_obl. Defined.
Obligation 120. ev_obl. Qed.
Obligation 121. ev_obl. Qed.
Obligation 122. ev_obl. Qed.
Obligation 123. ev_obl. Qed.
Obligation 124. ev_obl. Defined.
Obligation 125. ev_obl. Defined.
Obligation 126. ev_obl. Qed.
Obligation 127. ev_obl. Qed.
Obligation 128. ev_obl. Qed.
Obligation 129. ev_obl. Defined.
Obligation 130. ev_obl. Defined.
Obligation 131. ev_obl. Qed.
Obligation 132. ev_obl. Defined.
Obligation 133. ev_obl. Defined.
Obligation 134. ev_obl. Qed.
Obligation 135. ev_obl. Defined.
Obligation 136. ev_obl. Defined.
Obligation 137. ev_obl. Qed.
Obligation 138. ev_obl. Defined.
Obligation 139. ev_obl. Defined.
Obligation 140. ev_obl. Qed.
Obligation 141. ev_obl. Qed.
Obligation 142. ev_obl. Qed.
Obligation 143. ev_obl. Qed.
Obligation 144. ev_obl. Defined.
Obligation 145. ev_obl. Defined.
Obligation 146. ev_obl. Qed.
Obligation 147. ev_obl. Qed.
Obligation 148. ev_obl. Qed.
Obligation 149. ev_obl. Qed.
Obligation 150. ev_obl. Qed.
Obligation 151. ev_obl. Defined.
Obligation 152. ev_obl. Defined.
Obligation 153. ev_obl. Qed.
Obligation 154. ev_obl. Qed.
Obligation 155. ev_obl. Qed.
Obligation 156. ev_obl. Qed.
Obligation 157. ev_obl. Qed.
Obligation 158. ev_obl. Defined.
Obligation 159. ev_obl. Qed.
Obligation 160. ev_obl. Qed.
Obligation 161. ev_obl. Qed.
Obligation 162. ev_obl. Qed.
Obligation 163. ev_obl. Defined.
Obligation 164. ev_obl. Qed.
Obligation 165. ev_obl. Qed.
Obligation 166. ev_obl. Qed.
Obligation 167. ev_obl. Defined.
Obligation 168. ev_obl. Defined.
Obligation 169. ev_obl. Qed.
Obligation 170. ev_obl. Qed.
Obligation 171. ev_obl. Qed.
Obligation 172. ev_obl. Qed.
Obligation 173. ev_obl. Qed.
Obligation 174. ev_obl. Defined.
Obligation 175. ev_obl. Qed.
Obligation 176. ev_obl. Defined.
Obligation 177. ev_obl. Defined.
Obligation 178. ev_obl. Qed.
Obligation 179. ev_obl. Qed.
Obligation 180. ev_obl. Defined.
Obligation 181. ev_obl. Defined.
Obligation 182. ev_obl. Qed.
Obligation 183. ev_obl. Qed.
Obligation 184. ev_obl. Defined.
Obligation 185. ev_obl. Defined.
Obligation 186. ev_obl. Qed.
Obligation 187. ev_obl. Qed.
Obligation 188. ev_obl. Defined.
Obligation 189. ev_obl. Qed.
Obligation 190. ev_obl. Qed.
End EvalImpl.

(** The [eval_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the evaluation orders and the functionality
    of evaluation. *)

#[local]
Ltac functional_eval_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_eval_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma eval_exp_impl_complete : forall Θ Ξ M p m,
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
    exists H H', eval_exp_impl Θ Ξ M p H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_natrec_impl_complete : forall Θ Ξ A MZ MS m p r,
    ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ p ↘ r ->
    exists H H', eval_natrec_impl Θ Ξ A MZ MS m p H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_app_impl_complete : forall Θ Ξ m n r,
    $| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', eval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.
