(** * PER Lemmas: Module Values

    The fourth part of [Core.Semantic.PER.Lemmas]: the module PER
    [per_dmod] is a PER; module expressions evaluating to related
    values; closures. *)
From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions PER.Tele.
From Mctt.Core.Semantic.PER.Lemmas Require Export UniverseSubtyping.
Import Domain_Notations Fixed_Notations.
Import ListNotations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Module Values *)

Lemma functional_eval_appm : forall h n r1 r2,
    $ᵐ| h & n | gc_deps ⍮ gc_stack ↘ r1 -> $ᵐ| h & n | gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros * H1 H2; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_close : forall Δ D ρ h1 h2,
    ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h1 -> ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h2 -> h1 = h2.
Proof. intros * H1 H2; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma next_param_functional : forall h a1, next_param h a1 -> forall a2, next_param h a2 -> a1 = a2.
Proof.
  induction 1; intros a2 Hn2; inversion Hn2; subst; auto.
  - match goal with H : _ ++ _ :: nil = _ ++ _ :: nil |- _ => apply app_inj_tail in H as [<- [= _ <-]] end.
    eapply functional_eval_exp; eassumption.
  - match goal with H1 : gc_loc _ _ ?p = Some _, H2 : gc_loc _ _ ?p = Some _ |- _ => rewrite H1 in H2; injection H2 as <- <- end.
    match goal with H1 : nth_error ?l ?n = Some _, H2 : nth_error ?l ?n = Some _ |- _ => rewrite H1 in H2; injection H2 as _ -> end.
    eapply functional_eval_exp; eassumption.
Qed.

(** The member of a value lacking a parameter takes arguments of the kind
    of that parameter's type, when it is evaluated: the entry's tag. *)
Lemma next_param_kind : forall h a, next_param h a -> evaluated_kind (domain_kind a) ->
    dmod_param_kind gc_deps gc_stack h = domain_kind a.
Proof.
  induction 1 as [Δ κ A D ρ a _ <- | p T Φ args κ A a Hm Hn _ <- | h ch a _ IH]; intros Hk; cbn [dmod_param_kind].
  - unfold tele_param_kind; rewrite List.rev_app_distr; cbn.
    destruct Hk; reflexivity.
  - rewrite Hm; unfold tele_param_kind; rewrite Hn; destruct Hk; reflexivity.
  - exact (IH Hk).
Qed.

(** A saturated value lacks no parameter. *)
Lemma next_param_global_sat : forall p T Φ args a,
    gc_loc gc_deps gc_stack p = Some (T, Φ) -> List.length args = List.length T ->
    next_param (dm_global p args) a -> False.
Proof.
  intros * Hm Hl Hn; inversion Hn; subst.
  match goal with H1 : gc_loc _ _ ?p = Some _ |- _ => rewrite Hm in H1; injection H1 as <- <- end.
  match goal with Hx : nth_error _ _ = Some _ |- _ =>
    assert (Hx' : nth_error (rev T) (length args) <> None) by congruence end.
  apply nth_error_Some in Hx'; rewrite length_rev in Hx'; lia.
Qed.

Lemma next_param_body_nil : forall sm Φ ρ a, next_param (dm_local nil (md_body sm Φ) ρ) a -> False.
Proof. intros * Hn; inversion Hn; subst; destruct Δ; discriminate. Qed.

Lemma per_tele_args_len_eq : forall ts ρ ρ' args args', per_tele_args ts ρ ρ' args args' -> length args = length args'.
Proof. induction 1; cbn; congruence. Qed.

(** The environment of one body read twice is one. *)
Ltac solve_mid_body :=
  repeat match goal with
    | H1 : eval_body_env _ _ ?ρ ?Φ ?r1, H2 : eval_body_env _ _ ?ρ ?Φ ?r2 |- _ =>
        assert_fails (constr_eq r1 r2); assert (r1 = r2) by (eapply functional_eval_body_env; eassumption); subst r2
    end.

(** ** Symmetry *)

Lemma per_dmod_sym_all :
  (forall m m', per_dmod m m' -> per_dmod m' m) /\
  (forall ts ρ ρ' args args', per_tele_args ts ρ ρ' args args' -> per_tele_args ts ρ' ρ args' args) /\
  (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> per_body ρ' Φ' ρ Φ).
Proof.
  apply per_dmod_mut_ind_all; intros;
    try match goal with Hr : rel_typ _ _ _ _ _ _ |- _ => destruct (rel_typ_sym Hr) as [? Hs] end;
    try solve [ econstructor; eauto using rel_elem_sym, rel_elem_at_sym, rel_elem_tag_sym, rel_typ_kind_right ].
  - assert (Hl : length args = length args') by (eapply per_tele_args_len_eq; eassumption).
    econstructor; [ eassumption | congruence | assumption ].
  - (* a missing parameter *)
    match goal with Hu : per_univ_elem _ _ _ _ |- _ => destruct (per_univ_elem_sym _ _ _ _ Hu) as [Hu' Hs] end.
    eapply per_dmod_fun; [ eassumption | eassumption | exact Hu' | | |].
    1,2: intros c c' Hc; apply Hs in Hc; eauto.
    intros c c' hc hc' Hc Hh Hh'.
    match goal with IH : forall c c' hc hc', R c c' -> _ -> _ -> per_dmod hc' hc |- _ => apply (IH c' c hc' hc) end;
      [ apply Hs, Hc | assumption | assumption ].
Qed.

Corollary per_dmod_sym : forall m m', per_dmod m m' -> per_dmod m' m.
Proof. exact (proj1 per_dmod_sym_all). Qed.

Corollary per_body_sym : forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> per_body ρ' Φ' ρ Φ.
Proof. exact (proj2 (proj2 per_dmod_sym_all)). Qed.

(** ** Transitivity *)

Lemma per_dmod_trans_all :
  (forall m1 m2, per_dmod m1 m2 -> forall m3, per_dmod m2 m3 -> per_dmod m1 m3) /\
  (forall ts ρ1 ρ2 a1 a2, per_tele_args ts ρ1 ρ2 a1 a2 ->
     forall ρ3 a3, per_tele_args ts ρ2 ρ3 a2 a3 -> per_tele_args ts ρ1 ρ3 a1 a3) /\
  (forall ρ1 Φ1 ρ2 Φ2, per_body ρ1 Φ1 ρ2 Φ2 -> forall ρ3 Φ3, per_body ρ2 Φ2 ρ3 Φ3 -> per_body ρ1 Φ1 ρ3 Φ3).
Proof.
  apply per_dmod_mut_ind_all; intros.
  - (* global *)
    match goal with H : per_dmod _ _ |- _ => inversion H; subst; clear H end.
    + match goal with H1 : gc_loc _ _ ?p = Some _, H2 : gc_loc _ _ ?p = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as <- <- end.
      econstructor; eauto.
    + match goal with HL : List.length ?args = _, HG : per_tele_args _ _ _ ?args ?args' |- _ =>
        exfalso; eapply next_param_global_sat; [ eassumption | | eassumption ];
        rewrite <- HL; symmetry; eapply per_tele_args_len_eq; exact HG end.
  - (* bodies *)
    match goal with H : per_dmod _ _ |- _ => inversion H; subst; clear H end.
    + econstructor; eauto.
    + exfalso; eapply next_param_body_nil; eassumption.
  - (* a missing parameter: the middle side is quantified against itself *)
    match goal with H : per_dmod _ _ |- _ => inversion H; subst; clear H end.
    + exfalso; eapply next_param_global_sat; eassumption.
    + exfalso; eapply next_param_body_nil; eassumption.
    + match goal with H1 : next_param ?h ?a1, H2 : next_param ?h ?a2 |- _ =>
        pose proof (next_param_functional _ _ H1 _ H2) as <-; clear H2 end.
      match goal with H1 : per_univ_elem ?i ?R ?a ?a', H2 : per_univ_elem ?j ?R' ?a' ?a'' |- _ =>
        rename H1 into Hu1; rename H2 into Hu2 end.
      destruct (per_univ_elem_sym _ _ _ _ Hu1) as [Hu1s Hs1].
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hu1s Hu2) as Eq.
      assert (Hu2' : per_univ_elem _ R _ _) by (eapply per_univ_elem_resp_iff; [ exact Hu2 | symmetry; exact Eq ]).
      destruct (per_univ_elem_trans _ _ _ _ Hu1) as [Ht Htr].
      eapply per_dmod_fun; [ eassumption | eassumption | exact (Ht _ _ Hu2') | | |].
      { intros c c3 Hc; assert (Hcc : R c c) by (eapply Htr; [ exact Hc | apply Hs1; exact Hc ]).
        match goal with E : forall c c', R c c' -> exists hc, eval_appm _ _ h c hc |- _ => exact (E _ _ Hcc) end. }
      { intros c c3 Hc; assert (Hc3 : R c3 c3) by (eapply Htr; [ apply Hs1; exact Hc | exact Hc ]).
        match goal with |- exists hc', eval_appm _ _ ?h3 c3 hc' =>
          match goal with E : forall c c', ?R2 c c' -> exists hc', eval_appm _ _ h3 c' hc' |- _ =>
            exact (E _ _ (ltac:(apply Eq; exact Hc3))) end end. }
      intros c c3 hc hc3 Hc Hh Hh3.
      assert (Hc3 : R c3 c3) by (eapply Htr; [ apply Hs1; exact Hc | exact Hc ]).
      match goal with Hex : forall c c', R c c' -> exists hc', eval_appm _ _ ?h2 c' hc', Hh3' : eval_appm _ _ ?h3 c3 hc3,
                      H2 : forall c c' hc hc', _ -> eval_appm _ _ ?h2 c hc -> eval_appm _ _ ?h3 c' hc' -> per_dmod hc hc' |- _ =>
        destruct (Hex c3 c3 Hc3) as (hc2 & Hh2);
        assert (Hm23 : per_dmod hc2 hc3) by (apply (H2 c3 c3); [ apply Eq; exact Hc3 | exact Hh2 | exact Hh3' ]) end.
      match goal with IH : forall c c' hc hc', R c c' -> _ -> _ -> forall m3, per_dmod hc' m3 -> per_dmod hc m3 |- _ =>
        exact (IH c c3 hc hc2 Hc Hh Hh2 _ Hm23) end.
  - (* global arguments *)
    match goal with H : per_tele_args _ _ _ _ _ |- _ => inversion H; subst; clear H end; constructor.
  - match goal with H : per_tele_args _ _ _ (_ :: _) _ |- _ => inversion H; subst; clear H end.
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; [ exact HT | eapply Ht; [ eassumption | apply HRR; eassumption ] | eauto ].
  - match goal with H : per_body _ _ _ _ |- _ => inversion H; subst; clear H end; constructor.
  - (* a definition: the middle expansion and environment are one *)
    match goal with H : per_body _ (gm_ext _ _ _) _ _ |- _ => inversion H; subst; clear H end.
    solve_mid_body.
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; eauto using rel_elem_tag_trans.
  - (* a module: the middle closure is one value *)
    match goal with H : per_body _ (gm_ext _ _ _) _ _ |- _ => inversion H; subst; clear H end.
    solve_mid_body.
    match goal with H1 : eval_close _ _ ?Δ ?D ?ρ ?h1, H2 : eval_close _ _ ?Δ ?D ?ρ ?h2 |- _ =>
      assert_fails (constr_eq h1 h2); assert (h1 = h2) by (eapply functional_eval_close; eassumption); subst end.
    econstructor; eauto.
  - (* a definition with a module part: as a definition and as a module *)
    match goal with H : per_body _ (gm_ext _ _ _) _ _ |- _ => inversion H; subst; clear H end.
    solve_mid_body.
    match goal with H1 : eval_close _ _ ?Δ ?D ?ρ ?h1, H2 : eval_close _ _ ?Δ ?D ?ρ ?h2 |- _ =>
      assert_fails (constr_eq h1 h2); assert (h1 = h2) by (eapply functional_eval_close; eassumption); subst end.
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; eauto using rel_elem_at_trans.
Qed.

Corollary per_dmod_trans : forall m1 m2 m3, per_dmod m1 m2 -> per_dmod m2 m3 -> per_dmod m1 m3.
Proof. intros; eapply (proj1 per_dmod_trans_all); eassumption. Qed.

Corollary per_body_trans : forall ρ1 Φ1 ρ2 Φ2 ρ3 Φ3, per_body ρ1 Φ1 ρ2 Φ2 -> per_body ρ2 Φ2 ρ3 Φ3 -> per_body ρ1 Φ1 ρ3 Φ3.
Proof. intros; eapply (proj2 (proj2 per_dmod_trans_all)); eassumption. Qed.

#[export] Instance per_dmod_PER : PER per_dmod.
Proof. split; [ exact per_dmod_sym | exact per_dmod_trans ]. Qed.

(** ** Module Expressions Evaluating to Related Values *)

Lemma rel_modexp_evals_sym : forall H ρ H' ρ', rel_modexp_evals H ρ H' ρ' -> rel_modexp_evals H' ρ' H ρ.
Proof. intros * [h h' Hh Hh' Hr]; exists h' h; [ exact Hh' | exact Hh | apply per_dmod_sym, Hr ]. Qed.

Lemma rel_modexp_evals_trans : forall H1 ρ1 H2 ρ2 H3 ρ3, rel_modexp_evals H1 ρ1 H2 ρ2 -> rel_modexp_evals H2 ρ2 H3 ρ3 -> rel_modexp_evals H1 ρ1 H3 ρ3.
Proof.
  intros * [h1 h2 Hh1 Hh2 Hr] [h2' h3 Hh2' Hh3 Hr'].
  pose proof (functional_eval_modexp _ _ _ _ Hh2 Hh2') as <-.
  exists h1 h3; [ exact Hh1 | exact Hh3 | eapply per_dmod_trans; eassumption ].
Qed.

Lemma tie_mod_move : forall m H ρ H' ρ', tie_mod m H ρ -> rel_modexp_evals H ρ H' ρ' -> tie_mod m H' ρ'.
Proof.
  intros * (h & Hh & Hm) [h1 h' Hh1 Hh' Hr].
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh1) as <-.
  exists h'; split; [ exact Hh' | eapply per_dmod_trans; eassumption ].
Qed.

Lemma tie_mod_rel : forall m H ρ m' H' ρ', tie_mod m H ρ -> tie_mod m' H' ρ' -> rel_modexp_evals H ρ H' ρ' -> per_dmod m m'.
Proof.
  intros * (h & Hh & Hm) (h' & Hh' & Hm') [h1 h1' Hh1 Hh1' Hr].
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh1) as <-; pose proof (functional_eval_modexp _ _ _ _ Hh' Hh1') as <-.
  eapply per_dmod_trans; [ exact Hm | eapply per_dmod_trans; [ exact Hr | apply per_dmod_sym, Hm' ] ].
Qed.

(** The values of two module expressions related over related tails, read
    at two related tails in either combination. *)
Lemma rel_modexp_evals_move : forall (T : relation env) H H' ρ1 ρ2,
    PER T -> T ρ1 ρ2 ->
    (forall ρ ρ', T ρ ρ' -> rel_modexp_evals H ρ H' ρ') ->
    rel_modexp_evals H ρ1 H ρ2 /\ rel_modexp_evals H ρ1 H' ρ2 /\ rel_modexp_evals H' ρ1 H ρ2 /\ rel_modexp_evals H' ρ1 H' ρ2.
Proof.
  intros * HT H12 HP.
  assert (H11 : T ρ1 ρ1) by (etransitivity; [ exact H12 | symmetry; exact H12 ]).
  assert (H22 : T ρ2 ρ2) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
  pose proof (HP _ _ H12) as A; pose proof (HP _ _ H11) as B; pose proof (HP _ _ H22) as C.
  assert (D1 : rel_modexp_evals H ρ1 H ρ2) by (eapply rel_modexp_evals_trans; [ exact A | apply rel_modexp_evals_sym; exact C ]).
  split; [ exact D1 | split; [ exact A | split ] ].
  - eapply rel_modexp_evals_trans; [ apply rel_modexp_evals_sym; exact B | exact D1 ].
  - eapply rel_modexp_evals_trans; [ apply rel_modexp_evals_sym; exact B | exact A ].
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity; mautosolve.
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> (@relation_equivalence ctx) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

(** ** Closures *)

(** A closure given its outermost argument is the closure of the rest over
    the environment extended by it. *)
Lemma appm_local_inv : forall Δ κ A D ρ c hc h,
    $ᵐ| dm_local (Δ ++ ce_ass κ A :: nil) D ρ & c | gc_deps ⍮ gc_stack ↘ hc ->
    ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↦ c ⦂ entry_type_closure A ρ ↘ h -> hc = h.
Proof.
  intros * Ha Hc; inversion Ha; subst.
  match goal with H : _ ++ _ :: nil = _ ++ _ :: nil |- _ => apply app_inj_tail in H as [<- HA]; injection HA as <- <- end.
  eapply functional_eval_close; eassumption.
Qed.

(** Two closures lacking their outermost parameter are related when, at
    every related pair of arguments, the closures of the rest over the
    environments extended by them evaluate to related values.  Each
    parameter's type is of the kind its entry is tagged with. *)
Lemma per_dmod_closure_step : forall ρ ρ' Δ Δ' κ κ' A A' D D' i R a a',
    ⟦ A ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a -> ⟦ A' ⟧ gc_deps ⍮ gc_stack ⍮ ρ' ↘ a' -> per_univ_elem i R a a' ->
    domain_kind a = κ -> domain_kind a' = κ' ->
    (forall c c', R c c' -> exists h h', ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↦ c ⦂ entry_type_closure A ρ ↘ h /\
                                     ⟦ Δ' ⊢ D' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↦ c' ⦂ entry_type_closure A' ρ' ↘ h' /\
                                     per_dmod h h') ->
    per_dmod (dm_local (Δ ++ ce_ass κ A :: nil) D ρ) (dm_local (Δ' ++ ce_ass κ' A' :: nil) D' ρ').
Proof.
  intros * Ha Ha' HR Hk Hk' HD.
  destruct (per_univ_elem_sym _ _ _ _ HR) as [_ Hs].
  destruct (per_univ_elem_trans _ _ _ _ HR) as [_ Htr].
  eapply per_dmod_fun; [ constructor; [ exact Ha | exact Hk ] | constructor; [ exact Ha' | exact Hk' ] | exact HR | | |].
  - intros c c' Hc; destruct (HD _ _ Hc) as (h & _ & Hh & _); eexists; constructor; exact Hh.
  - intros c c' Hc; destruct (HD _ _ Hc) as (_ & h' & _ & Hh' & _); eexists; constructor; exact Hh'.
  - intros c c' hc hc' Hc Hh Hh'.
    destruct (HD _ _ Hc) as (h & h' & Hc1 & Hc2 & Hr).
    rewrite (appm_local_inv _ _ _ _ _ _ _ _ Hh Hc1), (appm_local_inv _ _ _ _ _ _ _ _ Hh' Hc2); exact Hr.
Qed.


End Fixed_GCtx.

#[export] Existing Instance per_ctx_env_morphism_iff_Proper.
#[export] Existing Instance per_ctx_env_morphism_relation_equivalence_Proper.

