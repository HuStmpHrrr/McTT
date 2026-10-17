From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import Kinds.
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
    body, which [eslo_global] records; a saturated alias recurses into its
    target.  Each premise that uses a value is quantified over the values its
    earlier premises evaluate to.  The orders split their cases as the
    evaluator does: a closure lacking a first parameter, a chain of two
    selections or more, the outermost missing parameter as [tele_snoc]
    splits it off. *)

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
| eeo_indty :
  `( eval_exp_order Θ Ξ (a_ind pq) p )
| eeo_con :
  `( eval_exp_order Θ Ξ (a_con pq c) p )
| eeo_elim :
  `( eval_exp_order Θ Ξ M p ->
     (forall m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m -> eval_elim_order Θ Ξ p nm A Bs m) ->
     eval_exp_order Θ Ξ (a_elim nm A Bs M) p )
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
  `( eval_close_order Θ Ξ Δ D p ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h -> eval_exp_order Θ Ξ B (p ↦ᵐ h)) ->
     eval_exp_order Θ Ξ (ℓₘ (gu_mk Δ D) in B) p )
| eeo_mem :
  `( modexp_spine H = (R, args, pre) ->
     eval_modexp_order Θ Ξ R p ->
     (forall h, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selc_order Θ Ξ h (pre ++ x :: nil)) ->
     eval_exps_order Θ Ξ args p ->
     (forall h f ns, ⟦ R ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selc Θ Ξ h (pre ++ x :: nil) f ->
        eval_exps Θ Ξ args p ns -> eval_apps_order Θ Ξ f ns) ->
     eval_exp_order Θ Ξ (a_mem H x) p )

with eval_elim_order (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> domain -> Prop :=
| eelo_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_con D c = Some gs ->
     List.length vs = (ind_np D + List.length gs)%nat ->
     brs_lookup Bs c = Some (n, B) ->
     n = (ind_nn D + List.length gs + cargs_nrec gs)%nat ->
     eval_ihs_order Θ Ξ p nm A Bs gs (skipn (ind_np D) vs) ->
     (forall ihs, ⟦ihs skipn (ind_np D) vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs ->
        eval_exp_order Θ Ξ B (env_args p (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs))) ->
     eval_elim_order Θ Ξ p nm A Bs (d_con pq c vs) )
| eelo_neut :
  `( ind_lookup Θ Ξ pq = Some D ->
     List.length as' = ind_np D ->
     nm = S (ind_nn D) ->
     eval_exp_order Θ Ξ A (env_args p (skipn (ind_nu D) as' ++ ⇑ (d_ind pq as') m :: nil)) ->
     eval_elim_order Θ Ξ p nm A Bs (⇑ (d_ind pq as') m) )

with eval_ihs_order (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> list carg -> list domain -> Prop :=
| eiho_nil :
  `( eval_ihs_order Θ Ξ p nm A Bs nil nil )
| eiho_arg :
  `( eval_ihs_order Θ Ξ p nm A Bs gs vs ->
     eval_ihs_order Θ Ξ p nm A Bs (ca_arg T :: gs) (v :: vs) )
| eiho_rec :
  `( eval_ih_order Θ Ξ p nm A Bs t v ->
     eval_ihs_order Θ Ξ p nm A Bs gs vs ->
     eval_ihs_order Θ Ξ p nm A Bs (ca_rec t :: gs) (v :: vs) )

with eval_ih_order (Θ : gdeps) (Ξ : gstack) : env -> nat -> exp -> list (string * nat * exp) -> ptyp -> domain -> Prop :=
| eio_self :
  `( eval_elim_order Θ Ξ p nm A Bs v ->
     eval_ih_order Θ Ξ p nm A Bs (pt_self k Ps) v )
| eio_pi :
  `( eval_ih_order Θ Ξ p nm A Bs (pt_pi B t) v )

with eval_shty_order (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> Prop :=
| esto_self :
  `( eval_exps_order Θ Ξ Ps p ->
     eval_shty_order Θ Ξ pq ups p (pt_self k Ps) )
| esto_pi :
  `( eval_exp_order Θ Ξ B p ->
     eval_shty_order Θ Ξ pq ups p (pt_pi B t) )

with eval_ihty_order (Θ : gdeps) (Ξ : gstack) : env -> exp -> env -> ptyp -> domain -> Prop :=
| eityo_self :
  `( eval_exps_order Θ Ξ Ps p ->
     (forall bs, ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ p ↘ bs -> eval_exp_order Θ Ξ A (env_args pm (bs ++ v :: nil))) ->
     eval_ihty_order Θ Ξ pm A p (pt_self k Ps) v )
| eityo_pi :
  `( eval_exp_order Θ Ξ B p ->
     eval_ihty_order Θ Ξ pm A p (pt_pi B t) v )

with eval_app_order (Θ : gdeps) (Ξ : gstack) : domain -> domain -> Prop :=
| eao_fn :
  `( eval_exp_order Θ Ξ M (p ↦ n) ->
     eval_app_order Θ Ξ λᵈ p M n )
| eao_neut :
  `( eval_exp_order Θ Ξ B (p ↦ n) ->
     eval_app_order Θ Ξ ⇑ (Πᵈ a p B) m n )
| eao_indty :
  `( ind_lookup Θ Ξ pq = Some D ->
     List.length as' < ind_np D ->
     eval_app_order Θ Ξ (d_ind pq as') n )
| eao_con :
  `( ind_lookup Θ Ξ pq = Some D ->
     ind_con D c = Some gs ->
     List.length vs < (ind_np D + List.length gs)%nat ->
     eval_app_order Θ Ξ (d_con pq c vs) n )
| eao_ihfn :
  `( eval_app_order Θ Ξ f n ->
     (forall fn, $| f & n | Θ ⍮ Ξ ↘ fn -> eval_ih_order Θ Ξ p nm A Bs t fn) ->
     eval_app_order Θ Ξ (d_ihfn p nm A Bs t f) n )
| eao_shfam :
  `( eval_shty_order Θ Ξ pq ups (p ↦ n) t ->
     eval_app_order Θ Ξ (d_shfam pq ups p t) n )
| eao_ihfam :
  `( eval_app_order Θ Ξ f n ->
     (forall fn, $| f & n | Θ ⍮ Ξ ↘ fn -> eval_ihty_order Θ Ξ pm A (p ↦ n) t fn) ->
     eval_app_order Θ Ξ (d_ihfam pm A p t f) n )
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
  `( eval_close_order Θ Ξ Δ D p ->
     eval_modexp_order Θ Ξ (me_lit (gu_mk Δ D)) p )
| emo_mem :
  `( eval_modexp_order Θ Ξ H p ->
     (forall h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_selm_order Θ Ξ h y) ->
     eval_modexp_order Θ Ξ (me_mem H y) p )
| emo_app :
  `( eval_modexp_order Θ Ξ H p ->
     eval_exp_order Θ Ξ N p ->
     (forall h n, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> ⟦ N ⟧ Θ ⍮ Ξ ⍮ p ↘ n -> eval_appm_order Θ Ξ h n) ->
     eval_modexp_order Θ Ξ (me_app H N) p )

with eval_close_order (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> Prop :=
| eclo_body :
  `( eval_close_order Θ Ξ Δ (md_body sm Φ) p )
| eclo_alias :
  `( eval_close_order Θ Ξ (e :: Δ) (md_alias E) p )
| eclo_alias0 :
  `( eval_modexp_order Θ Ξ E p ->
     eval_close_order Θ Ξ nil (md_alias E) p )

with eval_appm_order (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> Prop :=
| eapo_global :
  `( eval_appm_order Θ Ξ (dm_global pq args) n )
(** The outermost missing parameter is split off as the evaluator splits
    it off ([tele_snoc]), so that the order of the rest is a premise of the
    order of the whole. *)
| eapo_local :
  `( tele_snoc Δ = Some (Δ0, ce_ass A) ->
     eval_close_order Θ Ξ Δ0 D (p ↦ n) ->
     eval_appm_order Θ Ξ (dm_local Δ D p) n )
| eapo_member :
  `( eval_appm_order Θ Ξ h n ->
     (forall h', eval_appm Θ Ξ h n h' -> eval_selmc_order Θ Ξ h' ch) ->
     eval_appm_order Θ Ξ (dm_member h ch) n )

with eval_appms_order (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> Prop :=
| eamo_nil :
  `( eval_appms_order Θ Ξ h nil )
| eamo_cons :
  `( eval_appm_order Θ Ξ h n ->
     (forall h1, eval_appm Θ Ξ h n h1 -> eval_appms_order Θ Ξ h1 ns) ->
     eval_appms_order Θ Ξ h (n :: ns) )

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
| eslo_global_ind :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_lookup Θ Ξ (qname_app pq (x :: nil)) = Some D ->
     eval_apps_order Θ Ξ (d_ind (qname_app pq (x :: nil)) nil) args ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
| eslo_global_ind_alias :
  `( gc_resolve Θ Ξ (qname_app pq (x :: nil)) = None ->
     ind_alias_lookup Θ Ξ (qname_app pq (x :: nil)) = Some (Δ, pt, Ns) ->
     eval_exp_order Θ Ξ (ctx_fn Δ (apps (a_ind pt) Ns)) nil ->
     (forall f, ⟦ ctx_fn Δ (apps (a_ind pt) Ns) ⟧ Θ ⍮ Ξ ⍮ nil ↘ f -> eval_apps_order Θ Ξ f args) ->
     eval_sel_order Θ Ξ (dm_global pq args) x )
| eslo_unsat :
  `( eval_sel_order Θ Ξ (dm_local (e :: Δ) D p) x )
| eslo_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) ->
     eval_benv_order Θ Ξ p Φ' ->
     (forall p', eval_benv Θ Ξ p Φ' p' -> eval_exp_order Θ Ξ M p') ->
     eval_sel_order Θ Ξ (dm_local nil (md_body sm Φ) p) x )
| eslo_member :
  `( eval_sel_order Θ Ξ (dm_member h ch) x )

with eval_selm_order (Θ : gdeps) (Ξ : gstack) : dmod -> string -> Prop :=
| esmo_global :
  `( gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
| esmo_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     eval_close_order Θ Ξ Δ D nil ->
     (forall h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ nil ↘ h -> eval_appms_order Θ Ξ h args) ->
     eval_selm_order Θ Ξ (dm_global pq args) y )
| esmo_unsat :
  `( eval_selm_order Θ Ξ (dm_local (e :: Δ) D p) y )
| esmo_body :
  `( kbody Θ Ξ p Φ Φx ->
     gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pm (gu_mk Δy Dy))) ->
     eval_benv_order Θ Ξ p Φ' ->
     (forall p', eval_benv Θ Ξ p Φ' p' -> eval_close_order Θ Ξ Δy Dy p') ->
     eval_selm_order Θ Ξ (dm_local nil (md_body sm Φ) p) y )
| esmo_member :
  `( eval_selm_order Θ Ξ (dm_member h ch) y )

with eval_selc_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| esco_one :
  `( eval_sel_order Θ Ξ h x ->
     eval_selc_order Θ Ξ h (x :: nil) )
| esco_cons :
  `( eval_selm_order Θ Ξ h y ->
     (forall h1, eval_selm Θ Ξ h y h1 -> eval_selc_order Θ Ξ h1 (z :: ch)) ->
     eval_selc_order Θ Ξ h (y :: z :: ch) )

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
     (forall p1, eval_benv Θ Ξ p Φ p1 -> eval_close_order Θ Ξ Δy Dy p1) ->
     eval_benv_order Θ Ξ p (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) ).

#[local]
Hint Constructors eval_exp_order eval_elim_order eval_ihs_order eval_ih_order eval_shty_order eval_ihty_order eval_app_order eval_exps_order eval_apps_order
  eval_modexp_order eval_close_order eval_appm_order eval_appms_order eval_sel_order eval_selm_order eval_selc_order eval_selmc_order
  eval_benv_order : mctt.

(** Determinism of every evaluation relation, as rewriting. *)
Ltac functional_eval_all :=
  repeat match goal with
    | H1 : eval_exp ?T ?X ?M ?p ?m1, H2 : eval_exp ?T ?X ?M ?p ?m2 |- _ =>
        assert_fails (constr_eq m1 m2);
        pose proof (functional_eval_exp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_app ?T ?X ?m ?n ?r1, H2 : eval_app ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_app _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_exps ?T ?X ?M ?p ?r1, H2 : eval_exps ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (@functional_eval T X))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_apps ?T ?X ?m ?n ?r1, H2 : eval_apps ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (@functional_eval T X)))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_modexp ?T ?X ?M ?p ?r1, H2 : eval_modexp ?T ?X ?M ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_modexp _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_close ?T ?X ?Δ ?D ?p ?r1, H2 : eval_close ?T ?X ?Δ ?D ?p ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))) _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_appm ?T ?X ?m ?n ?r1, H2 : eval_appm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_appms ?T ?X ?m ?n ?r1, H2 : eval_appms ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : kbody ?T ?X ?p ?Φ ?r1, H2 : kbody ?T ?X ?p ?Φ ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_kbody _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_sel ?T ?X ?m ?n ?r1, H2 : eval_sel ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selm ?T ?X ?m ?n ?r1, H2 : eval_selm ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selc ?T ?X ?m ?n ?r1, H2 : eval_selc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_selmc ?T ?X ?m ?n ?r1, H2 : eval_selmc ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@functional_eval T X)))))))))))) _ _ _ H1 _ H2); subst; clear H2
    | H1 : eval_benv ?T ?X ?m ?n ?r1, H2 : eval_benv ?T ?X ?m ?n ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_benv _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_elim ?T ?X ?p ?nm ?A ?Bs ?m ?r1, H2 : eval_elim ?T ?X ?p ?nm ?A ?Bs ?m ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_elim _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ihs ?T ?X ?p ?nm ?A ?Bs ?gs ?vs ?r1, H2 : eval_ihs ?T ?X ?p ?nm ?A ?Bs ?gs ?vs ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ihs _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ih ?T ?X ?p ?nm ?A ?Bs ?t ?v ?r1, H2 : eval_ih ?T ?X ?p ?nm ?A ?Bs ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ih _ _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : eval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_shty _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : eval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r1, H2 : eval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
        assert_fails (constr_eq r1 r2);
        pose proof (functional_eval_ihty _ _ _ _ _ _ _ H1 H2); subst; clear H2
    | H1 : kgens ?T ?X ?p ?E ?its ?g1, H2 : kgens ?T ?X ?p ?E ?its ?g2 |- _ =>
        assert_fails (constr_eq g1 g2);
        pose proof (functional_kgens _ _ _ _ _ H1 H2); subst; clear H2
    | H : d_neut _ _ = d_neut _ _ |- _ => injection H; clear H; intros; subst
    end.

Lemma eval_order_sound : forall Θ Ξ,
    (forall m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_exp_order Θ Ξ m p) /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n) /\
    (forall Ms p ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms -> eval_exps_order Θ Ξ Ms p) /\
    (forall m ns r, $*| m & ns | Θ ⍮ Ξ ↘ r -> eval_apps_order Θ Ξ m ns) /\
    (forall H p h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_modexp_order Θ Ξ H p) /\
    (forall Δ D p h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h -> eval_close_order Θ Ξ Δ D p) /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> eval_appm_order Θ Ξ h n) /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> eval_appms_order Θ Ξ h ns) /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> eval_sel_order Θ Ξ h x) /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> eval_selm_order Θ Ξ h y) /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> eval_selc_order Θ Ξ h ch) /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> eval_selmc_order Θ Ξ h ch) /\
    (forall p Φ p', ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ p ↘ p' -> eval_benv_order Θ Ξ p Φ) /\
    (forall p nm A Bs m r, ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ p ↘ r -> eval_elim_order Θ Ξ p nm A Bs m) /\
    (forall p nm A Bs gs vs ihs, ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs -> eval_ihs_order Θ Ξ p nm A Bs gs vs) /\
    (forall p nm A Bs t v r, eval_ih Θ Ξ p nm A Bs t v r -> eval_ih_order Θ Ξ p nm A Bs t v) /\
    (forall pq ups p t a, eval_shty Θ Ξ pq ups p t a -> eval_shty_order Θ Ξ pq ups p t) /\
    (forall pm A p t v a, eval_ihty Θ Ξ pm A p t v a -> eval_ihty_order Θ Ξ pm A p t v).
Proof.
  intros Θ Ξ; apply eval_mut_ind; intros;
    (** A closure lacking a parameter lacks a first one, and a chain of one
        more selection is not empty. *)
    try match goal with H : 0 < List.length ?Δ |- _ => destruct Δ; [ cbn in H; lia |] end;
    try match goal with H : eval_selc _ _ _ ?c _ |- eval_selc_order _ _ _ (_ :: ?c) =>
          destruct c; [ inversion H |] end;
    solve [ eapply eslo_global_neut; eauto; intros; functional_eval_all; eauto
          | econstructor; try eassumption; intros; functional_eval_all; eauto using kgens_order_sound, tele_snoc_app ].
Qed.

Lemma eval_exp_order_sound : forall Θ Ξ m p a, ⟦ m ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> eval_exp_order Θ Ξ m p.
Proof. intros Θ Ξ; exact (proj1 (eval_order_sound Θ Ξ)). Qed.

Lemma eval_app_order_sound : forall Θ Ξ m n r, $| m & n | Θ ⍮ Ξ ↘ r -> eval_app_order Θ Ξ m n.
Proof. intros Θ Ξ; exact (proj1 (proj2 (eval_order_sound Θ Ξ))). Qed.

Lemma eval_exps_order_sound : forall Θ Ξ Ms p ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ p ↘ ms -> eval_exps_order Θ Ξ Ms p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (eval_order_sound Θ Ξ)))). Qed.

Lemma eval_modexp_order_sound : forall Θ Ξ H p h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> eval_modexp_order Θ Ξ H p.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (eval_order_sound Θ Ξ)))))). Qed.

Lemma eval_shty_order_sound : forall Θ Ξ pq ups p t a, eval_shty Θ Ξ pq ups p t a -> eval_shty_order Θ Ξ pq ups p t.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma eval_ihty_order_sound : forall Θ Ξ pm A p t v a, eval_ihty Θ Ξ pm A p t v a -> eval_ihty_order Θ Ξ pm A p t v.
Proof. intros Θ Ξ; pose proof (eval_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_app_order_sound eval_exps_order_sound eval_modexp_order_sound
  eval_shty_order_sound eval_ihty_order_sound : mctt.

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

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

  (** A variable is looked up in the environment, without recursion. *)
  Definition eval_var_impl x p (H : eval_exp_order Θ Ξ #x p) : { d | ⟦ #x ⟧ Θ ⍮ Ξ ⍮ p ↘ d }.
  Proof.
    exists (env_var p x); apply eval_exp_var.
  Defined.

  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_app_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_exps_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_apps_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_modexp_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_close_order _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_appm_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_appms_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_sel_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selm_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selc_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_selmc_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_benv_order _ _ _ _ |- _ => progressive_invert H
    | H : eval_elim_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ihs_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ih_order _ _ _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_shty_order _ _ _ _ _ _ |- _ => progressive_invert H
    | H : eval_ihty_order _ _ _ _ _ _ _ |- _ => progressive_invert H
    end.

  (** The lookups recorded in the order are the ones computed, which either
      fixes what is looked up or rules the case out. *)
  #[local]
  Ltac impl_obl_glob :=
    repeat match goal with
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
      | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
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
      | H : forall m, eval_exp _ _ ?M ?p m -> exists _ _, m = ⇑ _ _, Hm : eval_exp _ _ ?M ?p _ |- _ =>
          destruct (H _ Hm) as (? & ? & ?); clear H
      end.

  #[local]
  Ltac impl_obl_split :=
    match goal with
    | H : eval_exp_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_app_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_modexp_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_close_order _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_appm_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_appms_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_sel_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_selm_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_selc_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_benv_order _ _ _ _ |- _ => dependent destruction H
    | H : eval_elim_order _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ihs_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ih_order _ _ _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_shty_order _ _ _ _ _ _ |- _ => dependent destruction H
    | H : eval_ihty_order _ _ _ _ _ _ _ |- _ => dependent destruction H
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
    (** A closure lacking a first parameter lacks one. *)
    try solve [ econstructor; cbn; lia ];
    try solve [ eauto ];
    try econstructor; eauto.

  #[local]
  Ltac ev_obl :=
    intros; cbv beta in *;
    repeat impl_obl_tac1;
    first [ solve [ impl_obl_finish ]
          | solve [ impl_obl_split; impl_obl_finish ]
          | impl_obl_finish ].

  (** An obligation whose conclusion is an order stays transparent, since
      the guard condition sees it in the recursive calls; any other is
      proved opaquely. *)
  #[local]
  Ltac ev_obl_auto :=
    intros;
    lazymatch goal with
    | |- eval_exp_order _ _ _ _ => ev_obl
    | |- eval_app_order _ _ _ _ => ev_obl
    | |- eval_exps_order _ _ _ _ => ev_obl
    | |- eval_apps_order _ _ _ _ => ev_obl
    | |- eval_modexp_order _ _ _ _ => ev_obl
    | |- eval_close_order _ _ _ _ _ => ev_obl
    | |- eval_appm_order _ _ _ _ => ev_obl
    | |- eval_appms_order _ _ _ _ => ev_obl
    | |- eval_sel_order _ _ _ _ => ev_obl
    | |- eval_selm_order _ _ _ _ => ev_obl
    | |- eval_selc_order _ _ _ _ => ev_obl
    | |- eval_selmc_order _ _ _ _ => ev_obl
    | |- eval_benv_order _ _ _ _ => ev_obl
    | |- eval_elim_order _ _ _ _ _ _ _ => ev_obl
    | |- eval_ihs_order _ _ _ _ _ _ _ _ => ev_obl
    | |- eval_ih_order _ _ _ _ _ _ _ _ => ev_obl
    | |- eval_shty_order _ _ _ _ _ _ => ev_obl
    | |- eval_ihty_order _ _ _ _ _ _ _ => ev_obl
    | |- _ => abstract ev_obl
    end.

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
  | a_ind pq, p, H => exist _ (d_ind pq nil) _
  | a_con pq c, p, H => exist _ (d_con pq c nil) _
  (** A literal is generated before it is ever evaluated. *)
  | a_ntok, p, H => False_rect _ _
  | a_nlit _, p, H => False_rect _ _
  | a_elim nm A Bs M, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (r, Hr) := eval_elim_impl p nm A Bs m _ in
      exist _ r _
  | M $ N   , p, H =>
      let (m , Hm) := eval_exp_impl M p _ in
      let (n , Hn) := eval_exp_impl N p _ in
      let (a, Ha) := eval_app_impl m n _ in
      exist _ a _
  | a_let (b_def oA M) B, p, H =>
      let (m, Hm) := eval_exp_impl M p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ m) _ in
      exist _ r _
  | a_let (b_mod (gu_mk Δ D)) B, p, H =>
      let (h, Hh) := eval_close_impl Δ D p _ in
      let (r, Hr) := eval_exp_impl B (p ↦ᵐ h) _ in
      exist _ r _
  | a_mem M x, p, H with inspect (modexp_spine M) := {
    | exist _ (R, args, pre) E =>
        let (h, Hh) := eval_modexp_impl R p _ in
        let (f, Hf) := eval_selc_impl h (pre ++ x :: nil) _ in
        let (ns, Hns) := eval_exps_impl args p _ in
        let (r, Hr) := eval_apps_impl f ns _ in
        exist _ r _ }

  with eval_elim_impl p nm A Bs m (H : eval_elim_order Θ Ξ p nm A Bs m) : { r | ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ p ↘ r } by struct H :=
  | p, nm, A, Bs, d_con pq c vs, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed with inspect (ind_con D c) := {
      | exist _ (Some gs) Ec with inspect (brs_lookup Bs c) := {
        | exist _ (Some (n, B)) Eb =>
            let (ihs, Hihs) := eval_ihs_impl p nm A Bs gs (skipn (ind_np D) vs) _ in
            let (r, Hr) := eval_exp_impl B (env_args p (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs)) _ in
            exist _ r _
        | exist _ None Eb => False_rect _ _ }
      | exist _ None Ec => False_rect _ _ }
    | exist _ None Ed => False_rect _ _ }
  | p, nm, A, Bs, ⇑ (d_ind pq as') m, H with inspect (ind_lookup Θ Ξ pq) := {
    | exist _ (Some D) Ed =>
        let (a, Ha) := eval_exp_impl A (env_args p (skipn (ind_nu D) as' ++ ⇑ (d_ind pq as') m :: nil)) _ in
        exist _ (⇑ a (d_elim p nm A Bs pq as' m)) _
    | exist _ None Ed => False_rect _ _ }
  | p, nm, A, Bs, _, H => False_rect _ _

  with eval_ihs_impl p nm A Bs gs vs (H : eval_ihs_order Θ Ξ p nm A Bs gs vs) : { ihs | ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ p ↘ ihs } by struct H :=
  | p, nm, A, Bs, nil, nil, H => exist _ nil _
  | p, nm, A, Bs, ca_arg T :: gs, v :: vs, H =>
      let (ihs, Hihs) := eval_ihs_impl p nm A Bs gs vs _ in
      exist _ ihs _
  | p, nm, A, Bs, ca_rec t :: gs, v :: vs, H =>
      let (ih, Hih) := eval_ih_impl p nm A Bs t v _ in
      let (ihs, Hihs) := eval_ihs_impl p nm A Bs gs vs _ in
      exist _ (ih :: ihs) _
  | p, nm, A, Bs, _, _, H => False_rect _ _

  with eval_ih_impl p nm A Bs t v (H : eval_ih_order Θ Ξ p nm A Bs t v) : { r | eval_ih Θ Ξ p nm A Bs t v r } by struct H :=
  | p, nm, A, Bs, pt_self k Ps, v, H =>
      let (r, Hr) := eval_elim_impl p nm A Bs v _ in
      exist _ r _
  | p, nm, A, Bs, pt_pi B t, v, H => exist _ (d_ihfn p nm A Bs t v) _
  | p, nm, A, Bs, pt_aux k Ps, v, H => False_rect _ _

  with eval_shty_impl pq ups p t (H : eval_shty_order Θ Ξ pq ups p t) : { a | eval_shty Θ Ξ pq ups p t a } by struct H :=
  | pq, ups, p, pt_self k Ps, H =>
      let (bs, Hbs) := eval_exps_impl Ps p _ in
      exist _ (d_ind pq (ups ++ bs)) _
  | pq, ups, p, pt_pi B t, H =>
      let (b, Hb) := eval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_shfam pq ups p t) fam_cod) _
  | pq, ups, p, pt_aux k Ps, H => False_rect _ _

  with eval_ihty_impl pm A p t v (H : eval_ihty_order Θ Ξ pm A p t v) : { a | eval_ihty Θ Ξ pm A p t v a } by struct H :=
  | pm, A, p, pt_self k Ps, v, H =>
      let (bs, Hbs) := eval_exps_impl Ps p _ in
      let (a, Ha) := eval_exp_impl A (env_args pm (bs ++ v :: nil)) _ in
      exist _ a _
  | pm, A, p, pt_pi B t, v, H =>
      let (b, Hb) := eval_exp_impl B p _ in
      exist _ (Πᵈ b (nil ↦ d_ihfam pm A p t v) fam_cod) _
  | pm, A, p, pt_aux k Ps, v, H => False_rect _ _

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
  | d_ind pq as', n, H => exist _ (d_ind pq (as' ++ n :: nil)) _
  | d_con pq c vs, n, H => exist _ (d_con pq c (vs ++ n :: nil)) _
  | d_ihfn p nm A Bs t f, n, H =>
      let (fn, Hfn) := eval_app_impl f n _ in
      let (r, Hr) := eval_ih_impl p nm A Bs t fn _ in
      exist _ r _
  | d_shfam pq ups p t, n, H =>
      let (a, Ha) := eval_shty_impl pq ups (p ↦ n) t _ in
      exist _ a _
  | d_ihfam pm A p t f, n, H =>
      let (fn, Hfn) := eval_app_impl f n _ in
      let (a, Ha) := eval_ihty_impl pm A (p ↦ n) t fn _ in
      exist _ a _
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
  | me_lit (gu_mk Δ D), p, H =>
      let (h, Hh) := eval_close_impl Δ D p _ in
      exist _ h _
  | me_mem M y, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (r, Hr) := eval_selm_impl h y _ in
      exist _ r _
  | me_app M N, p, H =>
      let (h, Hh) := eval_modexp_impl M p _ in
      let (n, Hn) := eval_exp_impl N p _ in
      let (r, Hr) := eval_appm_impl h n _ in
      exist _ r _

  with eval_close_impl Δ D p (H : eval_close_order Θ Ξ Δ D p) : { h | ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ p ↘ h } by struct H :=
  | Δ, md_body sm Φ, p, H => exist _ (dm_local Δ (md_body sm Φ) p) _
  | nil, md_alias E, p, H =>
      let (h, Hh) := eval_modexp_impl E p _ in
      exist _ h _
  | e :: Δ, md_alias E, p, H => exist _ (dm_local (e :: Δ) (md_alias E) p) _

  with eval_appm_impl h n (H : eval_appm_order Θ Ξ h n) : { r | eval_appm Θ Ξ h n r } by struct H :=
  | dm_global pq args, n, H => exist _ (dm_global pq (args ++ n :: nil)) _
  | dm_local Δ D p, n, H with inspect (tele_snoc Δ) := {
    | exist _ (Some (Δ0, ce_ass A)) Es =>
        let (r, Hr) := eval_close_impl Δ0 D (p ↦ n) _ in
        exist _ r _
    | exist _ _ Es => False_rect _ _ }
  | dm_member h ch, n, H =>
      let (h', Hh') := eval_appm_impl h n _ in
      let (r, Hr) := eval_selmc_impl h' ch _ in
      exist _ r _

  with eval_appms_impl h ns (H : eval_appms_order Θ Ξ h ns) : { r | eval_appms Θ Ξ h ns r } by struct H :=
  | h, nil, H => exist _ h _
  | h, n :: ns, H =>
      let (h1, Hh1) := eval_appm_impl h n _ in
      let (r, Hr) := eval_appms_impl h1 ns _ in
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
    | exist _ (Some (ge_ind _ _ _ _)) E => False_rect _ _
    | exist _ (Some (ge_ind_alias _ _ _ _)) E => False_rect _ _
    | exist _ None E with inspect (ind_lookup Θ Ξ (qname_app pq (x :: nil))) := {
      | exist _ (Some D) Ed =>
          let (r, Hr) := eval_apps_impl (d_ind (qname_app pq (x :: nil)) nil) args _ in
          exist _ r _
      | exist _ None Ed with inspect (ind_alias_lookup Θ Ξ (qname_app pq (x :: nil))) := {
        | exist _ (Some (Δ, pt, Ns)) Ea =>
            let (f, Hf) := eval_exp_impl (ctx_fn Δ (apps (a_ind pt) Ns)) nil _ in
            let (r, Hr) := eval_apps_impl f args _ in
            exist _ r _
        | exist _ None Ea => False_rect _ _ } } }
  | dm_local (e :: Δ) D p, x, H => exist _ (d_member (dm_local (e :: Δ) D p) (x :: nil)) _
  | dm_local nil (md_alias E) p, x, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, x, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx x) := {
      | exist _ (Some (gm_ext Φ' _ (ge_def b pv A (Some M)))) P =>
          let (p', Hp') := eval_benv_impl p Φ' _ in
          let (r, Hr) := eval_exp_impl M p' _ in
          exist _ r _
      | exist _ _ P => False_rect _ _ } }
  | dm_member h ch, x, H => exist _ (d_member h (ch ++ x :: nil)) _

  with eval_selm_impl h y (H : eval_selm_order Θ Ξ h y) : { r | eval_selm Θ Ξ h y r } by struct H :=
  | dm_global pq args, y, H with inspect (gc_module Θ Ξ (qname_app pq (y :: nil))) := {
    | exist _ (Some (mr_alias (gu_mk Δ D))) E =>
        let (h, Hh) := eval_close_impl Δ D nil _ in
        let (r, Hr) := eval_appms_impl h args _ in
        exist _ r _
    | exist _ _ E => exist _ (dm_global (qname_app pq (y :: nil)) args) _ }
  | dm_local (e :: Δ) D p, y, H => exist _ (dm_member (dm_local (e :: Δ) D p) (y :: nil)) _
  | dm_local nil (md_alias E) p, y, H => False_rect _ _
  | dm_local nil (md_body sm Φ) p, y, H with kbody_impl Θ Ξ p Φ _ := {
    | exist _ Φx HΦx with inspect (gm_prefix_upto Φx y) := {
      | exist _ (Some (gm_ext Φ' _ (ge_mod pm (gu_mk Δy Dy)))) P =>
          let (p', Hp') := eval_benv_impl p Φ' _ in
          let (r, Hr) := eval_close_impl Δy Dy p' _ in
          exist _ r _
      | exist _ _ P => False_rect _ _ } }
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
  | p, gm_ext Φ y (ge_mod _ (gu_mk Δy Dy)), H =>
      let (p1, Hp1) := eval_benv_impl p Φ _ in
      let (h, Hh) := eval_close_impl Δy Dy p1 _ in
      exist _ (p1 ↦ᵐ h) _
  | p, gm_open Φ E its, H => False_rect _ _.

(** Each hole is an order premise read off the order of the whole by
    inversion, the evaluation itself by its rule, or a branch the order rules
    out ([ev_obl]); one whose conclusion is not an order is proved
    opaquely ([ev_obl_auto]). *)
Solve All Obligations with ev_obl_auto.
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

Lemma eval_app_impl_complete : forall Θ Ξ m n r,
    $| m & n | Θ ⍮ Ξ ↘ r ->
    exists H H', eval_app_impl Θ Ξ m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.
