(** * The Eliminator in the Gluing Model: Generic Lemmas

    Lemmas the gluing of the eliminator ([Inductives/Elim.v]) uses that do
    not depend on a group: substitutions glued at fresh variables, the
    fresh variables of readback position by position, and the syntax of
    function shapes. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.LogicalRelation Require Instance.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon IndElim.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Fresh Variables, Glued

    The substitution [q^n σ] past a telescope [C], at variables related to
    the fresh ones of the types of [C], is glued at the extension. *)
Lemma glu_sub_qn : forall C Γb Sb_b, tele_ass C -> EG Γb ∈ glu_ctx_env ↘ Sb_b ->
    forall Sb, EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ xs, Δ ⊢ˢ σ ® ρ ∈ Sb_b -> List.length xs = List.length C ->
    (forall k A a (i : uidx) R, List.nth_error (List.rev C) k = Some (ce_ass A) -> ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a ->
       DF a ≈ a ∈ per_univ_elem i ↘ R -> exists x, List.nth_error xs k = Some x /\ R (⇑! a (List.length Δ + k)) x) ->
    tele_sub C σ ++ Δ ⊢ˢ sb_qn (List.length C) σ ® env_args ρ xs ∈ Sb.
Proof.
  induction C as [| e C IH]; intros * Hass HΓb Sb HC * Hσ Hl Hx.
  - destruct xs; [| discriminate ]; cbn.
    apply (functional_glu_ctx_env HΓb HC); exact Hσ.
  - inversion Hass as [| ? ? [A ->] Hass']; subst.
    destruct (List.exists_last (l := xs)) as (xs' & x & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Hl; cbn in Hl.
    cbn [List.app] in HC.
    assert (HC' : exists TSb, EG C ++ Γb ∈ glu_ctx_env ↘ TSb) by (inversion HC; subst; eauto).
    destruct HC' as [TSb HTSb].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HC) as (i & HA & HT & HSb).
    assert (Hx' : forall k A0 a (i0 : uidx) R, List.nth_error (List.rev C) k = Some (ce_ass A0) ->
              ⟦ A0 ⟧ env_args ρ (List.firstn k xs') ↘ a -> DF a ≈ a ∈ per_univ_elem i0 ↘ R ->
              exists x0, List.nth_error xs' k = Some x0 /\ R (⇑! a (List.length Δ + k)) x0).
    { intros * HA0 Ea HR.
      assert (Hk : k < List.length C) by (rewrite <- List.length_rev; apply List.nth_error_Some; congruence).
      assert (HA1 : List.nth_error (List.rev (C ▹ A)) k = Some (ce_ass A0))
        by (cbn [List.rev]; rewrite List.nth_error_app1 by (rewrite List.length_rev; lia); exact HA0).
      assert (Ea1 : ⟦ A0 ⟧ env_args ρ (List.firstn k (xs' ++ x :: nil)) ↘ a)
        by (rewrite List.firstn_app, (proj2 (Nat.sub_0_le k (List.length xs'))) by lia; cbn; rewrite List.app_nil_r; exact Ea).
      destruct (Hx k A0 a i0 R HA1 Ea1 HR) as (x0 & Hx0 & HRx).
      exists x0; split; [ rewrite List.nth_error_app1 in Hx0 by lia; exact Hx0 | exact HRx ]. }
    pose proof (IH _ _ Hass' HΓb _ HTSb Δ σ ρ xs' Hσ ltac:(lia) Hx') as Hτ.
    cbn [tele_sub List.length sb_qn List.app centry_sub].
    rewrite env_args_app; cbn [env_args List.fold_left].
    apply HSb.
    destruct (HT _ _ _ Hτ) as [a P El Ea Hg HTP].
    assert (Hxk : List.nth_error (List.rev (C ▹ A)) (List.length C) = Some (ce_ass A))
      by (cbn [List.rev]; rewrite List.nth_error_app2 by (rewrite List.length_rev; lia); rewrite List.length_rev, Nat.sub_diag; reflexivity).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [Ra HRa].
    assert (Ea' : ⟦ A ⟧ env_args ρ (List.firstn (List.length C) (xs' ++ x :: nil)) ↘ a)
      by (rewrite firstn_app_exact by lia; exact Ea).
    destruct (Hx _ _ _ _ _ Hxk Ea' HRa) as (x0 & Hx0 & Hrx).
    rewrite List.nth_error_app2 in Hx0 by lia; replace (List.length C - List.length xs') with 0 in Hx0 by lia; cbn in Hx0; injection Hx0 as <-.
    assert (HΔC : ⊢ tele_sub C σ ++ Δ) by (pose proof (glu_ctx_env_sub_escape HTSb _ _ _ Hτ); gen_presups; assumption).
    assert (HAτ : tele_sub C σ ++ Δ ⊢ A[sb_qn (List.length C) σ] : Typeω@i)
      by (pose proof (glu_ctx_env_sub_escape HTSb _ _ _ Hτ); mauto 3).
    assert (HΔA : ⊢ (tele_sub C σ ++ Δ) ▹ A[sb_qn (List.length C) σ]) by mauto 3.
    unfold sb_q; eapply cons_glu_sub_pred_helper_gen; [ exact HTSb | | exact HA | exact Ea | exact Hg | ].
    + eapply glu_ctx_env_sub_monotone; [ exact HTSb | exact Hτ | mauto 3 ].
    + cbn [sentry_exp]; rewrite <- exp_wk_sub.
      pose proof (var0_glu_elem Hg HTP) as Hv.
      eapply glu_univ_elem_trm_resp_per_elem; [ exact Hg | exact HRa | exact Hv |].
      rewrite List.length_app, length_tele_sub, Nat.add_comm; exact Hrx.
Qed.

(** A substitution glued to an environment extended by values is glued to
    it extended by values related to them at the telescope. *)
Lemma glu_sub_resp_args : forall C Γb Sb_b, tele_ass C -> EG Γb ∈ glu_ctx_env ↘ Sb_b ->
    forall Sb, EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall Δ τ ρ ys xs, List.length ys = List.length C -> per_gargs (List.rev C) ρ ρ ys xs ->
      Δ ⊢ˢ τ ® env_args ρ ys ∈ Sb -> Δ ⊢ˢ τ ® env_args ρ xs ∈ Sb.
Proof.
  induction C as [| e C IH]; intros * Hass HΓb Sb HC * Hl Hg Hτ.
  - destruct ys; [| discriminate ]; inversion Hg; subst; exact Hτ.
  - inversion Hass as [| ? ? [A ->] Hass']; subst.
    destruct (List.exists_last (l := ys)) as (ys' & y & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Hl; cbn in Hl.
    pose proof (Decl.per_gargs_length _ _ _ _ _ Hg) as [Lyx _].
    destruct (List.exists_last (l := xs)) as (xs' & x & ->); [ intros ->; rewrite List.length_app in Lyx; cbn in Lyx; lia |].
    rewrite !List.length_app in Lyx; cbn in Lyx.
    cbn [List.rev] in Hg.
    destruct (Decl.per_gargs_app (List.rev C) (ce_ass A :: nil) _ _ ys' xs' (y :: nil) (x :: nil)
                ltac:(rewrite List.length_rev; lia) Hg ltac:(rewrite List.length_rev; lia)) as [Hg1 Hg2].
    inversion Hg2 as [| ? ? ? ? ? ? ? ? ? ? HA Hyx _]; subst.
    destruct HA as [a1 a1' Ea1 Ea1' HR1].
    cbn [List.app] in HC.
    assert (HC' : exists TSb, EG C ++ Γb ∈ glu_ctx_env ↘ TSb) by (inversion HC; subst; eauto).
    destruct HC' as [TSb HTSb].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HC) as (ic & _ & _ & HSb).
    rewrite env_args_app in Hτ |- *; cbn [env_args List.fold_left] in Hτ |- *.
    apply HSb in Hτ; apply HSb.
    inversion Hτ as [? ? ? a P El Hτt Ea Hga HEl Htail]; subst.
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hga) as [Ra HRa].
    destruct (Instance.per_univ_elem_trans_any _ _ _ _ _ _ _ HRa HR1) as (R2 & HR2 & _).
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R2 HR2) Hga) as Hga'.
    econstructor; [ exact Hτt | exact Ea1' | exact Hga' | | exact (IH _ _ Hass' HΓb _ HTSb _ _ _ ys' xs' ltac:(lia) Hg1 Htail) ].
    cbn.
    eapply glu_univ_elem_trm_resp_per_elem; [ exact Hga | exact HRa | exact HEl |].
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HRa); exact Hyx.
Qed.

(** The substitution [q^n σ] past a telescope [C], at variables of types
    related to those of [C], is glued at the extension. *)
Lemma glu_sub_fresh : forall C Γb Sb_b, tele_ass C -> EG Γb ∈ glu_ctx_env ↘ Sb_b ->
    forall Sb, EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ xs, Δ ⊢ˢ σ ® ρ ∈ Sb_b -> List.length xs = List.length C ->
    (forall k A a, List.nth_error (List.rev C) k = Some (ce_ass A) -> ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a ->
       exists b (j : nat), List.nth_error xs k = Some (⇑! b (List.length Δ + k)) /\ Dom a ≈ b ∈ per_univ j) ->
    tele_sub C σ ++ Δ ⊢ˢ sb_qn (List.length C) σ ® env_args ρ xs ∈ Sb.
Proof.
  intros * Hass HΓb Sb HC * Hσ Hl Hx.
  eapply glu_sub_qn; [ exact Hass | exact HΓb | exact HC | exact Hσ | exact Hl |].
  intros k A a i R HA Ea HR.
  destruct (Hx k A a HA Ea) as (b & j & Hxk & [R' HR']).
  exists (⇑! b (List.length Δ + k)); split; [ exact Hxk |].
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR' HR); exact (var_per_elem _ HR').
Qed.

(** A substitution of a list of terms past a telescope [C] is glued when
    each term is glued at its instance's type, at any gluing of the
    type's value at which the instance is glued: the substitution of the
    terms before it is glued, so the type is. *)
Lemma glu_sub_of_list_by : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    tele_ass C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 -> List.length Ms = List.length C -> List.length vs = List.length C ->
    (forall k M T v A a (i : nat) P El, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C σ0 Ms) k = Some T ->
       List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass A) ->
       ⟦ A ⟧ env_args ρ0 (List.firstn k vs) ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ T ® P ->
       Δ ⊢ M : T ® v ∈ El) ->
    Δ ⊢ˢ sb_of_list σ0 Ms ® env_args ρ0 vs ∈ Sb.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass HC H0 Hσ L1 L2 Hby.
  - destruct Ms; [| discriminate ]; destruct vs; [| discriminate ]; cbn.
    apply (functional_glu_ctx_env H0 HC); exact Hσ.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M0 Ms]; [ cbn in L1; lia |]; destruct vs as [| v0 vs]; [ cbn in L2; lia |].
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (glu_ctx_env_suffix _ _ _ Hass HC) as [Sb1 HC1].
    destruct (glu_ctx_env_cons_clean_inversion H0 HC1) as (i' & HA & HT & HSb1).
    destruct (HT _ _ _ Hσ) as [a' P' El' Ha' Hglu' HP'].
    assert (HM0 : Δ ⊢ M0 : A[σ0] ® v0 ∈ El').
    { apply (Hby 0 M0 A[σ0] v0 A a' i' P' El'); try reflexivity; try assumption.
      - rewrite tele_insts_snoc; reflexivity.
      - rewrite List.rev_app_distr; reflexivity. }
    assert (Hσ1 : Δ ⊢ˢ σ0,,M0 ® ρ0 ↦ v0 ∈ Sb1)
      by (apply HSb1; eapply cons_glu_sub_pred_helper; eassumption).
    cbn [sb_of_list env_args List.fold_left].
    cbn [List.length] in L1, L2.
    refine (IH _ _ _ _ _ _ Ms vs Hass HC HC1 Hσ1 ltac:(lia) ltac:(lia) _).
    intros k M T v A0 a i P El HM HT0 Hv HA0 Ea Hg HTP.
    apply (Hby (S k) M T v A0 a i P El); try assumption.
    + rewrite tele_insts_snoc; exact HT0.
    + rewrite List.rev_app_distr; exact HA0.
Qed.

(** A variable of a context, at a type glued at the gluing of a type's
    value, is glued at it to the fresh variable of its level. *)
Lemma var_glu_elem_at : forall (i : uidx) a P El Δ T x, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ T ® P ->
    Δ ⊢ #x : T -> x < List.length Δ -> Δ ⊢ #x : T ® ⇑! a (List.length Δ - 1 - x) ∈ El.
Proof.
  intros * Hg HT Hx Hlt.
  eapply realize_glu_elem_bot; [ exact Hg |].
  econstructor; [ exact Hx | exact Hg | exact HT | apply var_per_bot |].
  intros Δ' φ M' Hφ HR.
  inversion HR; subst.
  destruct (kripke_shiftn _ _ _ Hφ) as [Hle _].
  pose proof (wk_var_kripke _ _ _ x Hφ) as Hφx.
  change (#x[φ]ʷ) with (a_var (φ x)); rewrite Hφx.
  cbn [ne_to_exp].
  replace (List.length Δ' - (List.length Δ - 1 - x) - 1) with (x + (List.length Δ' - List.length Δ)) by lia.
  apply wf_exp_eq_refl.
  rewrite <- Hφx; change (a_var (φ x)) with (#x[φ]ʷ).
  exact (kripke_preserves_exp _ _ _ _ _ Hx Hφ).
Qed.

Lemma nth_rev_tele_sub : forall C1 e Pre σ,
    List.nth_error (List.rev (tele_sub (C1 ++ e :: Pre) σ)) (List.length Pre) = Some (centry_sub e (sb_qn (List.length Pre) σ)).
Proof.
  intros; rewrite tele_sub_app; cbn [tele_sub]; rewrite !List.rev_app_distr; cbn [List.rev].
  rewrite <- List.app_assoc; rewrite List.nth_error_app2 by (rewrite List.length_rev, length_tele_sub; lia).
  rewrite List.length_rev, length_tele_sub, Nat.sub_diag; reflexivity.
Qed.

(** ** The Recursive Results, Position by Position *)

Lemma ihs_rev_nth : forall nn As Us na gs k e,
    List.nth_error (List.rev (ihs_ctx_aux nn As Us na nil 0 gs)) k = Some e ->
    exists gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 /\ cargs_nrec gs1 = k /\
      e = ce_ass (ptyp_ihty As (sb_of_wk (wk_shiftn (k + na + nn))) (ihs_sub nn Us na (cargs_pat gs1) k)
                    (a_var (k + na - 1 - List.length (cargs_pat gs1))) t).
Proof.
  intros nn As Us na gs; induction gs as [| g gs IH] using List.rev_ind; intros k e H; [ cbn in H; destruct k; discriminate |].
  pose proof (Views.ihs_ctx_aux_app nn As Us na gs (g :: nil) nil 0) as E.
  rewrite List.app_nil_r in E; cbn [Nat.add] in E; rewrite E in H; clear E.
  destruct g as [B | t]; cbn [ihs_ctx_aux List.app] in H.
  - destruct (IH k e H) as (gs1 & t & gs2 & -> & Hk & ->).
    exists gs1, t, (gs2 ++ ca_arg B :: nil); split; [ rewrite <- List.app_assoc; reflexivity | split; [ exact Hk | reflexivity ] ].
  - cbn [List.rev] in H.
    destruct (Nat.lt_ge_cases k (List.length (ihs_ctx_aux nn As Us na nil 0 gs))) as [Hlt | Hge].
    + rewrite List.nth_error_app1 in H by (rewrite List.length_rev; exact Hlt).
      destruct (IH k e H) as (gs1 & t' & gs2 & -> & Hk & ->).
      exists gs1, t', (gs2 ++ ca_rec t :: nil); split; [ rewrite <- List.app_assoc; reflexivity | split; [ exact Hk | reflexivity ] ].
    + rewrite List.nth_error_app2 in H by (rewrite List.length_rev; exact Hge).
      rewrite List.length_rev in H; rewrite length_ihs_ctx_aux in H, Hge.
      destruct (k - cargs_nrec gs) as [| k'] eqn:Ek; cbn in H; [| destruct k'; discriminate ].
      injection H as <-.
      assert (k = cargs_nrec gs) as -> by (pose proof (proj1 (Nat.sub_0_le k (cargs_nrec gs)) Ek); lia).
      exists gs, t, nil; split; [ reflexivity | split; [ reflexivity |] ].
      try rewrite List.app_nil_r; reflexivity.
Qed.

Lemma ihs_ctx_nth : forall nn As Us na gs gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (List.rev (ihs_ctx_aux nn As Us na nil 0 gs)) (cargs_nrec gs1)
    = Some (ce_ass (ptyp_ihty As (sb_of_wk (wk_shiftn (cargs_nrec gs1 + na + nn))) (ihs_sub nn Us na (cargs_pat gs1) (cargs_nrec gs1))
                      (a_var (cargs_nrec gs1 + na - 1 - List.length (cargs_pat gs1))) t)).
Proof.
  intros * ->.
  rewrite Views.ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux Nat.add].
  rewrite !List.rev_app_distr; cbn [List.rev List.app].
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_ihs_ctx_aux; lia).
  rewrite List.length_rev, length_ihs_ctx_aux, Nat.sub_diag; reflexivity.
Qed.

Lemma elim_ihs_nth : forall pq D oq Us Bks gs1 σ gs t gs2 As N, gs = gs1 ++ ca_rec t :: gs2 -> List.length As = List.length gs ->
    List.nth_error As (List.length gs1) = Some N ->
    List.nth_error (elim_ihs pq D oq Us Bks σ gs As) (cargs_nrec gs1) = Some (ptyp_ih pq D oq Us Bks (cargs_sub σ gs1 As) N t).
Proof.
  intros pq D oq Us Bks gs1; induction gs1 as [| g gs1 IH]; intros σ gs t gs2 As N -> Hl HN;
    destruct As as [| N0 As]; cbn in *; try discriminate; [ injection HN as ->; reflexivity |].
  destruct g; cbn; [ apply (IH _ _ t gs2); auto | apply (IH _ _ t gs2); auto ].
Qed.

Lemma eval_ihs_nth : forall ρ p ups Bks gs1 gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
    forall t gs2 v, gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
    exists r, List.nth_error ihs (cargs_nrec gs1) = Some r /\ ⟦ih v of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r.
Proof.
  intros ρ p ups Bks gs1; induction gs1 as [| g gs1 IH]; intros gs vs ihs H t gs2 v -> Hv; inversion H; subst; cbn in *.
  - injection Hv as ->; eauto.
  - eapply IH; eauto.
  - edestruct (IH _ _ _ ltac:(eassumption) _ _ _ eq_refl Hv) as (r & Hr & Er); exists r; split; [ exact Hr | exact Er ].
Qed.

(** ** Fresh Variables of Readback, Position by Position *)

Lemma fresh_tele_nth : forall E T s vs, Ftele T in gc_deps ⍮ gc_stack ⍮ E ⍮ s ↘ vs ->
    forall k A, List.nth_error T k = Some (ce_ass A) ->
      exists b, ⟦ A ⟧ env_args E (List.firstn k vs) ↘ b /\ List.nth_error vs k = Some (⇑! b (s + k)).
Proof.
  induction 1 as [| ? ? ? ? ? ? Ea Hr IH]; intros k A0 Hk; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in Hk |- *.
  - injection Hk as <-; exists a; rewrite Nat.add_0_r; split; [ exact Ea | reflexivity ].
  - destruct (IH k A0 Hk) as (b & Eb & Hb); exists b; split; [ exact Eb |].
    rewrite Hb; do 3 f_equal; lia.
Qed.

Lemma fresh_cargs_nth : forall p ups E gs s vs, Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ E ⍮ s ↘ vs ->
    forall gs1 g gs2, gs = gs1 ++ g :: gs2 ->
    (forall A, g = ca_arg A -> exists a, ⟦ A ⟧ env_args E (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
       List.nth_error vs (List.length gs1) = Some (⇑! a (s + List.length gs1))) /\
    (forall t, g = ca_rec t -> exists a, ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args E (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
       List.nth_error vs (List.length gs1) = Some (⇑! a (s + List.length gs1))).
Proof.
  intros p ups E gs s vs H gs1; revert E gs s vs H; induction gs1 as [| g1 gs1 IH]; intros * H g gs2 Heq; cbn in Heq.
  - subst; split; intros * ->; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto.
  - subst; inversion H; subst;
      lazymatch goal with Hr1 : fresh_cargs _ _ _ _ _ (gs1 ++ _) _ _ |- _ => destruct (IH _ _ _ _ Hr1 g gs2 eq_refl) as [IHa IHr] end.
    + split.
      * intros A0 ->; destruct (IHa A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros t0 ->; destruct (IHr t0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
    + split.
      * intros A0 ->; destruct (IHa A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros t0 ->; destruct (IHr t0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
Qed.

(** The fresh recursive results of arguments recursive in both kinds:
    one per such argument, after those before. *)
Lemma fresh_ihs_nth : forall ρm As ρa gs vs s ihs, Fihs vs at gs gs under ρm As in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ ihs ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists v a, List.nth_error vs (List.length gs1) = Some v /\
      ⟦ihty v of t under ρm As ⟧ gc_deps ⍮ gc_stack ⍮ env_args ρa (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
      List.nth_error ihs (cargs_nrec gs1) = Some (⇑! a (s + cargs_nrec gs1)).
Proof.
  intros ρm As ρa gs vs s ihs H gs1; revert ρa gs vs s ihs H; induction gs1 as [| g1 gs1 IH]; intros * H t gs2 Heq; cbn in Heq.
  - subst; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto 10.
  - subst; inversion H; subst;
      lazymatch goal with Hr1 : fresh_ihs _ _ _ _ _ (gs1 ++ _) (gs1 ++ _) _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ Hr1 t gs2 eq_refl) as (v0 & a0 & Hv & Ea & Hi) end.
    + exists v0, a0; cbn; auto.
    + exists v0, a0; cbn.
      split; [ exact Hv | split; [ exact Ea |] ].
      rewrite Hi; do 3 f_equal; lia.
Qed.

(** ** Function Shapes: Values *)

Lemma eval_fam_cod_ihfam_inv : forall ρm As ρ0 t f x a,
    ⟦ fam_cod ⟧ nil ↦ d_ihfam ρm As ρ0 t f ↦ x ↘ a ->
    exists fx, $| f & x | gc_deps ⍮ gc_stack ↘ fx /\ ⟦ihty fx of t under ρm As ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↦ x ↘ a.
Proof.
  intros * H; unfold fam_cod in H; inversion H; subst.
  match goal with H1 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
  match goal with H0 : ⟦ #0 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H0; subst end.
  match goal with Ha : $| _ & _ | _ ⍮ _ ↘ _ |- _ => cbn in Ha; inversion Ha; subst; eauto end.
Qed.

Lemma eval_ih_pi_inv : forall ρ0 p ups Bks0 B t v r, ⟦ih v of pt_pi B t under p ups Bks0 ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ r ->
    r = d_ihfn ρ0 Bks0 p ups t v.
Proof. intros * H; inversion H; reflexivity. Qed.

Lemma eval_ihty_pi_inv : forall ρm As ρ0 B t v a, ⟦ihty v of pt_pi B t under ρm As ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ a ->
    exists b, ⟦ B ⟧ ρ0 ↘ b /\ a = Πᵈ b (nil ↦ d_ihfam ρm As ρ0 t v) fam_cod.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma eval_app_ihfn_inv : forall ρ0 Bks0 p ups t f c r, $| d_ihfn ρ0 Bks0 p ups t f & c | gc_deps ⍮ gc_stack ↘ r ->
    exists fc, $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ ⟦ih fc of t under p ups Bks0 ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ r.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma per_gargs_nth_el : forall ts ρ ρ' xs xs' k A, per_gargs ts ρ ρ' xs xs' ->
    List.nth_error ts k = Some (ce_ass A) -> k < List.length xs ->
    exists (i : nat) R a a' x x', ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a /\ ⟦ A ⟧ env_args ρ' (List.firstn k xs') ↘ a' /\
      DF a ≈ a' ∈ per_univ_elem i ↘ R /\ List.nth_error xs k = Some x /\ List.nth_error xs' k = Some x' /\ R x x'.
Proof.
  intros * H; revert k; induction H as [| ? ? ? ? ? ? ? ? ? ? HA Ha Hr IH]; intros k Hk Hl; [ cbn in Hl; lia |].
  destruct k as [| k]; cbn in Hk, Hl |- *.
  - injection Hk as <-; destruct HA as [a0 a0' E E' HR]; eauto 15.
  - exact (IH k Hk ltac:(lia)).
Qed.

(** ** Function Shapes: Syntax *)

(** [β] after a Kripke weakening. *)
Lemma fn_wk_beta : forall Δ' Δ IT OT M b φ (i : nat),
    Δ' ⊢ IT : Typeω@i -> Δ' ▹ IT ⊢ OT : Typeω@i -> Δ' ▹ IT ⊢ M : OT -> Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ->
    Δ ⊢ (λ IT M)[φ]ʷ $ b ≈ M[(ι φ),,b] : OT[(ι φ),,b].
Proof.
  intros * HIT HOT HM Hφ Hb; cbn [exp_wk].
  rewrite <- (exp_sub_wk_q_extend M), <- (exp_sub_wk_q_extend OT).
  eapply wf_exp_eq_pi_beta;
    [ exact (kripke_preserves_typ _ _ _ _ _ HIT Hφ) | exact (kripke_preserves_typ_q _ _ _ _ _ _ _ HOT HIT Hφ)
    | exact (kripke_preserves_exp_q _ _ _ _ _ _ _ HM HIT Hφ) | exact Hb ].
Qed.

Lemma app_wk_typed : forall Δ' Δ IT OT N b φ, Δ' ⊢ N : Π IT OT -> Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ->
    Δ ⊢ N[φ]ʷ $ b : OT[(ι φ),,b].
Proof.
  intros * HN Hφ Hb; rewrite <- exp_sub_wk_q_extend.
  eapply wf_app'; [ exact (kripke_preserves_exp _ _ _ _ _ HN Hφ) | exact Hb ].
Qed.

Lemma sub_typ_extend : forall Δ' Δ IT OT φ b (j : nat), Δ' ⊢ IT : Typeω@j -> Δ' ▹ IT ⊢ OT : Typeω@j -> Δ ⊢ᵏ φ : Δ' ->
    Δ ⊢ b : IT[φ]ʷ -> Δ ⊢ OT[(ι φ),,b] : Typeω@j.
Proof.
  intros * HIT HOT Hφ Hb; rewrite <- exp_sub_wk_q_extend.
  pose proof (kripke_preserves_typ_q _ _ _ _ _ _ _ HOT HIT Hφ) as H.
  pose proof (kripke_preserves_typ _ _ _ _ _ HIT Hφ) as HIT'.
  assert (Hs : Δ ⊢ˢ Id,,b : Δ ▹ IT[φ]ʷ) by mauto 3.
  exact (sub_preserves_exp _ _ _ _ _ _ _ H Hs).
Qed.

(** ** Glued Arguments along Related Types *)

Lemma tele_insts_base_agree : forall Δ k σ σ' Ms, tele_ass Δ -> ctx_scoped k Δ ->
    (forall x, x < k -> σ x = σ' x) -> tele_insts Δ σ Ms = tele_insts Δ σ' Ms.
Proof.
  intros * Hass Hs Hσ.
  pose proof (tele_insts_sub Δ k σ σ' Id Ms Hass Hs ltac:(intros x Hx; rewrite sentry_sub_id; apply Hσ; exact Hx)) as H.
  rewrite (List.map_ext _ (fun T => T) (fun T => exp_sub_id T)), List.map_id in H.
  rewrite (List.map_ext _ (fun M => M) (fun M => exp_sub_id M)), List.map_id in H.
  exact H.
Qed.

(** Glued arguments of a telescope are glued arguments of another one
    whose types, at the same arguments, have values related to its own. *)
Lemma glu_args_link : forall Δ C C' τ τ' ρ1 ρ2 Ms vs, List.length C = List.length C' ->
    tele_insts C τ Ms = tele_insts C' τ' Ms -> glu_args Δ C τ ρ1 Ms vs ->
    (forall k A A' a, List.nth_error (List.rev C) k = Some (ce_ass A) -> List.nth_error (List.rev C') k = Some (ce_ass A') ->
       k < List.length vs -> ⟦ A ⟧ env_args ρ1 (List.firstn k vs) ↘ a ->
       exists a' (i : nat), ⟦ A' ⟧ env_args ρ2 (List.firstn k vs) ↘ a' /\ Dom a' ≈ a ∈ per_univ i) ->
    (forall k e', List.nth_error (List.rev C') k = Some e' -> exists A, List.nth_error (List.rev C) k = Some (ce_ass A) /\ exists A', e' = ce_ass A') ->
    glu_args Δ C' τ' ρ2 Ms vs.
Proof.
  intros * HlC HT [L1 L2 H] Hlink Hass.
  constructor; [ congruence | congruence |].
  intros k M T v A' HM HT' Hv HA'.
  destruct (Hass _ _ HA') as (A & HA & A'' & E); injection E as <-.
  rewrite <- HT in HT'.
  destruct (H _ _ _ _ _ HM HT' Hv HA) as [j a P El Ea Hg HP HMg].
  assert (Hk : k < List.length vs) by (apply List.nth_error_Some; congruence).
  destruct (Hlink _ _ _ _ HA HA' Hk Ea) as (a' & i & Ea' & Hr).
  destruct (glu_transfer_per_elem j i a a' P El Δ T M v Hg (per_univ_sym' _ _ _ Hr) HP HMg) as (k' & P' & El' & Hg' & HP' & HM').
  exact (mk_glu_arg _ _ _ _ _ _ k' a' P' El' Ea' Hg' HP' HM').
Qed.

End Fixed_GCtx.
