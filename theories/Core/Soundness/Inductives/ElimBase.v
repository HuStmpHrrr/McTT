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

(** ** Fresh Variables, Glued *)

(** A telescope's environment reads only as many entries as there are
    values. *)
Lemma env_tele_app_long : forall ρ T X vs, List.length vs <= List.length T -> env_tele ρ (T ++ X) vs = env_tele ρ T vs.
Proof.
  intros * Hl; rewrite env_tele_firstn, (env_tele_firstn ρ T), List.firstn_app, (proj2 (Nat.sub_0_le _ _) Hl).
  cbn [List.firstn]; rewrite List.app_nil_r; reflexivity.
Qed.

(** [sb_extend σ en] into an assumption entry, its head stored at the type
    as a closure in the tail's environment, as the arguments of a
    telescope are ([env_tele]). *)
Lemma cons_glu_sub_pred_helper_closure_gen : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El en c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ sentry_exp en : A[σ] ® c ∈ El ->
    Δ ⊢ˢ sb_extend σ en ® ρ ↦ c ⦂ entry_type_closure A ρ ∈ cons_glu_sub_pred i Γ κ A Sb.
Proof.
  intros * HSb Hσg HA Ha Hglu Hc.
  pose proof (cons_glu_sub_pred_helper_gen HSb Hσg HA Ha Hglu Hc) as Hx.
  inversion Hx as [? ? ? ? P' El' Hσt Ha' Hg' Hh _ _ Htl]; subst.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ Hc HR) as Hcc.
  econstructor; [ exact Hσt | exact Ha' | exact Hg' | exact Hh | | | exact Htl ].
  - (** The stored type is the type's closure, of the type's value *)
    exists (entry_type_closure A ρ); split; [ reflexivity |].
    refine (mk_glu_stored_type _ _ _ _ (entry_type_closure A ρ) i a P El ltac:(apply eval_entry_type_closure; exact Ha) Hglu _).
    rewrite exp_sub_shift_extend; exact Hc.
  - split; [ exact (proj1 (entry_readable_of_elem_closure Ha Ha HR Hcc)) | cbn; lia ].
Qed.

(** Stored types glued at [τ] stay glued along a weakening, at [τ]
    weakened ([glu_univ_elem_exp_monotone]). *)
Lemma glu_tele_stored_monotone : forall C Δ τ ρ, glu_tele_stored Δ C τ ρ ->
    forall Δ' φ, Δ' ⊢ᵏ φ : Δ -> glu_tele_stored Δ' C (sb_wk τ φ) ρ.
Proof.
  induction C as [| e C IH]; intros * Hst * Hφ; [ exact I |].
  destruct e as [κ A | | |]; cbn [glu_tele_stored] in Hst |- *; try exact I.
  destruct Hst as [(t & Het & [j b Pb Elb Hb Hgb HEb]) Htl].
  split.
  - exists t; split; [ exact Het |].
    econstructor; [ exact Hb | exact Hgb |].
    rewrite <- !exp_wk_sub; eapply glu_univ_elem_exp_monotone; eassumption.
  - change (Wk ⨟ sb_wk τ φ) with (sb_wk (Wk ⨟ τ) φ); exact (IH _ _ _ Htl _ _ Hφ).
Qed.

(** A substitution at fresh variables, glued along a telescope [C] at [σ]
    and along a witness telescope [C'] at [σ'] of the same instances. *)
Record glu_fresh_substitution (C : ctx) (σ : sub) (ρ : env) (Sb : glu_sub_pred) (C' : ctx) (σ' : sub) (ρ' : env)
    (Sb' : glu_sub_pred) (Δ : ctx) (xs : list domain) : Prop := mk_glu_fresh_substitution
  { (** Glued at the environment of [C] *)
    glu_fresh_target : tele_sub C σ ++ Δ ⊢ˢ sb_qn (List.length C) σ ® env_tele ρ (List.rev C) xs ∈ Sb
    (** Glued at the environment of [C'] *)
  ; glu_fresh_witness : tele_sub C' σ' ++ Δ ⊢ˢ sb_qn (List.length C) σ' ® env_tele ρ' (List.rev C') xs ∈ Sb'
    (** At any typed extension of [ρ] by the fresh variables whose stored
        types evaluate to the values of [C']'s types, the stored types are
        glued, the variables at their values ([glu_tele_stored]) *)
  ; glu_fresh_stored : forall vts, List.map fst vts = xs ->
      (forall k t κ' A' b, List.nth_error (List.map snd vts) k = Some t -> List.nth_error (List.rev C') k = Some (ce_ass κ' A') ->
         ⟦ A' ⟧ env_tele ρ' (List.rev C') (List.firstn k xs) ↘ b -> eval_entry_type gc_deps gc_stack t b) ->
      glu_tele_stored (tele_sub C σ ++ Δ) C (sb_qn (List.length C) σ) (env_extend_typed ρ vts) }.

(** The substitution [q^n σ] past a telescope [C], at the fresh variables
    of the types of a telescope [C'] with the same instances
    ([tele_sub C σ = tele_sub C' σ']), is glued at the extension of [C'] at
    [σ'], and at that of [C] at [σ]: each variable is glued at the value of
    the type of [C'] it is fresh at, and moves to the value of the type of
    [C] at its position, related to it, by the type's gluing at [σ]
    ([glu_univ_elem_exp_conv_universe_index]).  Use it when a telescope
    [C'] annotates the variables exactly (the declared non-uniform
    parameters); otherwise give a witness per position
    ([glu_sub_fresh_at]). *)
Lemma glu_sub_fresh : forall C Γb Sb_b C' Γ' Sb'_b, all_assumptions C -> all_assumptions C' ->
    EG Γb ∈ glu_ctx_env ↘ Sb_b -> EG Γ' ∈ glu_ctx_env ↘ Sb'_b ->
    forall Sb Sb', EG C ++ Γb ∈ glu_ctx_env ↘ Sb -> EG C' ++ Γ' ∈ glu_ctx_env ↘ Sb' ->
    forall Δ σ ρ σ' ρ' xs, Δ ⊢ˢ σ ® ρ ∈ Sb_b -> Δ ⊢ˢ σ' ® ρ' ∈ Sb'_b -> tele_sub C σ = tele_sub C' σ' ->
    List.length xs = List.length C ->
    (** The variables are the fresh ones of the types of [C'] *)
    (forall k κ' A' b, List.nth_error (List.rev C') k = Some (ce_ass κ' A') ->
       ⟦ A' ⟧ env_tele ρ' (List.rev C') (List.firstn k xs) ↘ b -> List.nth_error xs k = Some (⇑! b (List.length Δ + k))) ->
    (** whose values are related to those of the types of [C] *)
    (forall k κ A a κ' A' b, List.nth_error (List.rev C) k = Some (ce_ass κ A) -> List.nth_error (List.rev C') k = Some (ce_ass κ' A') ->
       ⟦ A ⟧ env_tele ρ (List.rev C) (List.firstn k xs) ↘ a -> ⟦ A' ⟧ env_tele ρ' (List.rev C') (List.firstn k xs) ↘ b ->
       exists j : nat, Dom b ≈ a ∈ per_univ j) ->
    glu_fresh_substitution C σ ρ Sb C' σ' ρ' Sb' Δ xs.
Proof.
  induction C as [| e C IH]; intros Γb Sb_b C' Γ' Sb'_b Hass Hass' HΓb HΓ' Sb Sb' HC HC' Δ σ ρ σ' ρ' xs Hσ Hσ' Etl Hl Hx Hrel.
  - destruct C' as [| e' C']; [| discriminate ].
    destruct xs; [| discriminate ]; cbn.
    constructor; [ apply (functional_glu_ctx_env HΓb HC); exact Hσ | apply (functional_glu_ctx_env HΓ' HC'); exact Hσ' |].
    intros vts _ _; exact I.
  - destruct C' as [| e' C']; [ discriminate |].
    apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass0].
    apply List.Forall_cons_iff in Hass' as [(κ' & A' & ->) Hass0'].
    cbn [tele_sub centry_sub] in Etl; injection Etl as <- EA Etl.
    assert (HlC : List.length C' = List.length C)
      by (rewrite <- (length_tele_sub C σ), <- (length_tele_sub C' σ'), Etl; reflexivity).
    rewrite HlC in EA.
    destruct (List.exists_last (l := xs)) as (xs' & x & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Hl; cbn in Hl.
    cbn [List.app] in HC, HC'.
    assert (HC0 : exists TSb, EG C ++ Γb ∈ glu_ctx_env ↘ TSb) by (inversion HC; subst; eauto).
    destruct HC0 as [TSb HTSb].
    assert (HC0' : exists TSb', EG C' ++ Γ' ∈ glu_ctx_env ↘ TSb') by (inversion HC'; subst; eauto).
    destruct HC0' as [TSb' HTSb'].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HC) as (i & HA & HT & HSb).
    destruct (glu_ctx_env_cons_clean_inversion HTSb' HC') as (i' & HA' & HT' & HSb').
    assert (ErC : List.rev (ce_ass κ A :: C) = List.rev C ++ ce_ass κ A :: nil) by reflexivity.
    assert (ErC' : List.rev (ce_ass κ A' :: C') = List.rev C' ++ ce_ass κ A' :: nil) by reflexivity.
    assert (Ef : forall k, k <= List.length xs' -> List.firstn k (xs' ++ x :: nil) = List.firstn k xs')
      by (intros k Hk; rewrite List.firstn_app, (proj2 (Nat.sub_0_le k (List.length xs'))) by lia; cbn; apply List.app_nil_r).
    (** The prefix *)
    assert (Hx' : forall k κ0 A0 b, List.nth_error (List.rev C') k = Some (ce_ass κ0 A0) ->
              ⟦ A0 ⟧ env_tele ρ' (List.rev C') (List.firstn k xs') ↘ b -> List.nth_error xs' k = Some (⇑! b (List.length Δ + k))).
    { intros * HA0 Eb.
      assert (Hk : k < List.length C') by (rewrite <- List.length_rev; apply List.nth_error_Some; congruence).
      pose proof (Hx k κ0 A0 b ltac:(rewrite ErC', List.nth_error_app1 by (rewrite List.length_rev; lia); exact HA0)
                    ltac:(rewrite (Ef k ltac:(lia)), ErC', env_tele_app_long by (rewrite List.length_firstn, List.length_rev; lia); exact Eb))
        as H0.
      rewrite List.nth_error_app1 in H0 by lia; exact H0. }
    assert (Hrel' : forall k κ0 A0 a κ1 A1 b, List.nth_error (List.rev C) k = Some (ce_ass κ0 A0) ->
              List.nth_error (List.rev C') k = Some (ce_ass κ1 A1) ->
              ⟦ A0 ⟧ env_tele ρ (List.rev C) (List.firstn k xs') ↘ a -> ⟦ A1 ⟧ env_tele ρ' (List.rev C') (List.firstn k xs') ↘ b ->
              exists j : nat, Dom b ≈ a ∈ per_univ j).
    { intros * HA0 HA1 Ea Eb.
      assert (Hk : k < List.length C) by (rewrite <- List.length_rev; apply List.nth_error_Some; congruence).
      exact (Hrel k κ0 A0 a κ1 A1 b
               ltac:(rewrite ErC, List.nth_error_app1 by (rewrite List.length_rev; lia); exact HA0)
               ltac:(rewrite ErC', List.nth_error_app1 by (rewrite List.length_rev; lia); exact HA1)
               ltac:(rewrite (Ef k ltac:(lia)), ErC, env_tele_app_long by (rewrite List.length_firstn, List.length_rev; lia); exact Ea)
               ltac:(rewrite (Ef k ltac:(lia)), ErC', env_tele_app_long by (rewrite List.length_firstn, List.length_rev; lia); exact Eb)). }
    destruct (IH Γb Sb_b C' Γ' Sb'_b Hass0 Hass0' HΓb HΓ' TSb TSb' HTSb HTSb' Δ σ ρ σ' ρ' xs' Hσ Hσ' Etl ltac:(lia) Hx' Hrel')
      as [Hτ Hτ' Hst].
    (** The types at the prefixes, glued *)
    destruct (HT _ _ _ Hτ) as [a P El Ea Hg HTP].
    rewrite <- HlC in Hτ'.
    destruct (HT' _ _ _ Hτ') as [b P' El' Eb Hg' HTP'].
    (** The last variable is fresh at [b], related to [a] *)
    assert (Lx : List.length xs' = List.length C) by lia.
    assert (Eb' : ⟦ A' ⟧ env_tele ρ' (List.rev (ce_ass κ A' :: C')) (List.firstn (List.length C') (xs' ++ x :: nil)) ↘ b)
      by (rewrite HlC, <- Lx, firstn_app_exact, ErC', env_tele_app_long by (rewrite ?List.length_rev; lia); exact Eb).
    assert (Ea' : ⟦ A ⟧ env_tele ρ (List.rev (ce_ass κ A :: C)) (List.firstn (List.length C) (xs' ++ x :: nil)) ↘ a)
      by (rewrite <- Lx, firstn_app_exact, ErC, env_tele_app_long by (rewrite ?List.length_rev; lia); exact Ea).
    assert (Hxk' : List.nth_error (List.rev (ce_ass κ A' :: C')) (List.length C') = Some (ce_ass κ A'))
      by (rewrite ErC', List.nth_error_app2 by (rewrite List.length_rev; lia); rewrite List.length_rev, Nat.sub_diag; reflexivity).
    assert (Hxk : List.nth_error (List.rev (ce_ass κ A :: C)) (List.length C) = Some (ce_ass κ A))
      by (rewrite ErC, List.nth_error_app2 by (rewrite List.length_rev; lia); rewrite List.length_rev, Nat.sub_diag; reflexivity).
    pose proof (Hx _ _ _ _ Hxk' Eb') as Hx0.
    rewrite List.nth_error_app2 in Hx0 by lia; replace (List.length C' - List.length xs') with 0 in Hx0 by lia.
    cbn in Hx0; injection Hx0 as ->.
    destruct (Hrel _ _ _ _ _ _ _ Hxk (eq_trans (f_equal (fun n => List.nth_error _ n) (eq_sym HlC)) Hxk') Ea'
                ltac:(rewrite <- HlC; exact Eb')) as [j Hba].
    (** The variable, glued at [b], and at [a] *)
    assert (HAτ' : tele_sub C' σ' ++ Δ ⊢ A'[sb_qn (List.length C') σ'] : abs_kind_sort κ Typeω@i')
      by (pose proof (glu_ctx_env_sub_escape HTSb' _ _ _ Hτ');
          replace (abs_kind_sort κ Typeω@i') with (abs_kind_sort κ Typeω@i')[sb_qn (List.length C') σ']
            by (rewrite abs_kind_sort_sub; reflexivity); mauto 3).
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hg' HTP' HAτ') as [Hkb Hnb].
    pose proof (var0_glu_elem Hg' Hnb HTP') as Hv; rewrite Hkb in Hv.
    rewrite List.length_app, length_tele_sub, Nat.add_comm, HlC in Hv.
    assert (Hwk : (tele_sub C σ ++ Δ) ▹{κ} A[sb_qn (List.length C) σ] ⊢ᵏ ↑ : tele_sub C σ ++ Δ).
    { pose proof (glu_ctx_env_sub_escape HTSb _ _ _ Hτ).
      assert (tele_sub C σ ++ Δ ⊢ A[sb_qn (List.length C) σ] : abs_kind_sort κ Typeω@i)
        by (replace (abs_kind_sort κ Typeω@i) with (abs_kind_sort κ Typeω@i)[sb_qn (List.length C) σ]
              by (rewrite abs_kind_sort_sub; reflexivity); mauto 3).
      assert (⊢ (tele_sub C σ ++ Δ) ▹{κ} A[sb_qn (List.length C) σ])
        by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
      mauto 3. }
    assert (Hwk' : (tele_sub C' σ' ++ Δ) ▹{κ} A'[sb_qn (List.length C') σ'] ⊢ᵏ ↑ : tele_sub C' σ' ++ Δ).
    { assert (⊢ (tele_sub C' σ' ++ Δ) ▹{κ} A'[sb_qn (List.length C') σ'])
        by (econstructor; [ exact HAτ' | apply sort_kind_abs_kind_sort ]).
      mauto 3. }
    pose proof (glu_univ_elem_exp_conv_universe_index Hba Hg' Hg
                  ltac:(rewrite <- EA, <- Etl in Hv; exact Hv) (glu_univ_elem_typ_monotone _ _ _ _ Hg _ _ _ _ HTP Hwk)) as Hva.
    rewrite HlC in *.
    constructor; cbn [tele_sub List.length sb_qn List.app centry_sub].
    + rewrite ErC, !env_tele_snoc by (rewrite List.length_rev; lia).
      apply HSb.
      unfold sb_q; eapply cons_glu_sub_pred_helper_closure_gen;
        [ exact HTSb | exact (glu_ctx_env_sub_monotone _ _ HTSb _ _ _ _ _ Hτ Hwk) | exact HA | exact Ea | exact Hg | ].
      cbn [sentry_exp]; rewrite <- exp_wk_sub; exact Hva.
    + rewrite ?HlC, ErC', !env_tele_snoc by (rewrite List.length_rev; lia).
      apply HSb'.
      unfold sb_q; eapply cons_glu_sub_pred_helper_closure_gen;
        [ exact HTSb' | exact (glu_ctx_env_sub_monotone _ _ HTSb' _ _ _ _ _ Hτ' Hwk') | exact HA' | exact Eb | exact Hg' | ].
      cbn [sentry_exp]; rewrite <- exp_wk_sub; exact Hv.
    + (** The stored types: the last variable at its value [b], the rest
          along the weakening. *)
      intros vts Hvts Hts.
      destruct (List.exists_last (l := vts)) as (vts' & [x' t] & ->).
      { intros ->; apply (f_equal (@List.length _)) in Hvts; rewrite List.length_app in Hvts; cbn in Hvts; lia. }
      rewrite List.map_app in Hvts; cbn in Hvts; apply List.app_inj_tail in Hvts as [Hvts' ->].
      assert (Lv' : List.length vts' = List.length C) by (rewrite <- (List.length_map fst), Hvts'; lia).
      rewrite env_extend_typed_app; cbn [env_extend_typed List.fold_left glu_tele_stored].
      split.
      * exists t; split; [ reflexivity |].
        assert (Et : eval_entry_type gc_deps gc_stack t b).
        { apply (Hts (List.length C) t κ A' b).
          - rewrite List.map_app, List.nth_error_app2 by (rewrite List.length_map; lia).
            rewrite List.length_map, Lv', Nat.sub_diag; reflexivity.
          - exact Hxk'.
          - rewrite <- Lx, firstn_app_exact, ErC', env_tele_app_long by (rewrite ?List.length_rev; lia); exact Eb. }
        refine (mk_glu_stored_type _ _ _ _ t i' b P' El' Et Hg' _).
        unfold sb_q; cbn [exp_sub sentry_exp]; rewrite exp_sub_shift_extend, <- exp_wk_sub.
        rewrite <- EA, <- Etl in Hv; exact Hv.
      * change (Wk ⨟ sb_q (sb_qn (List.length C) σ)) with (sb_wk (sb_qn (List.length C) σ) ↑).
        assert (Hts' : forall k t0 κ0 A0 b0, List.nth_error (List.map snd vts') k = Some t0 ->
                         List.nth_error (List.rev C') k = Some (ce_ass κ0 A0) ->
                         ⟦ A0 ⟧ env_tele ρ' (List.rev C') (List.firstn k xs') ↘ b0 -> eval_entry_type gc_deps gc_stack t0 b0).
        { intros k t0 κ0 A0 b0 Ht0 HA0 Eb0.
          assert (Hk : k < List.length C') by (rewrite <- List.length_rev; apply List.nth_error_Some; congruence).
          apply (Hts k t0 κ0 A0 b0).
          - rewrite List.map_app, List.nth_error_app1 by (rewrite List.length_map; lia); exact Ht0.
          - rewrite ErC', List.nth_error_app1 by (rewrite List.length_rev; lia); exact HA0.
          - rewrite (Ef k ltac:(lia)), ErC', env_tele_app_long by (rewrite List.length_firstn, List.length_rev; lia); exact Eb0. }
        exact (glu_tele_stored_monotone _ _ _ _ (Hst vts' Hvts' Hts') _ _ Hwk).
Qed.

(** Past [q^n σ] glued at fresh variables [xs] of a telescope [C], the
    next variable, fresh at a value [d] related to the value [a] of the
    head type [A] at [xs], with [A] at [q^n σ] glued at [d] (the typed
    witness): the extension is glued at [a] (the variable glued at [d],
    then moved to [a] by [glu_univ_elem_exp_conv_universe_index]), and a
    stored type of value [d] at it is glued (the variable at [d]
    itself). *)
Lemma glu_sub_fresh_cons_at : forall C Γb κ A TSb Sb,
    EG C ++ Γb ∈ glu_ctx_env ↘ TSb -> EG (ce_ass κ A :: C) ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ xs (i : nat) d P El, List.length xs = List.length C ->
    tele_sub C σ ++ Δ ⊢ˢ sb_qn (List.length C) σ ® env_tele ρ (List.rev C) xs ∈ TSb ->
    DG d ∈ glu_univ_elem i ↘ P ↘ El ->
    tele_sub C σ ++ Δ ⊢ A[sb_qn (List.length C) σ] ® P ->
    (forall a, ⟦ A ⟧ env_tele ρ (List.rev C) xs ↘ a -> exists j : nat, Dom d ≈ a ∈ per_univ j) ->
    tele_sub (ce_ass κ A :: C) σ ++ Δ ⊢ˢ sb_qn (List.length (ce_ass κ A :: C)) σ
      ® env_tele ρ (List.rev (ce_ass κ A :: C)) (xs ++ ⇑! d (List.length Δ + List.length C) :: nil) ∈ Sb /\
    (forall vts t, List.map fst vts = xs -> eval_entry_type gc_deps gc_stack t d ->
       glu_tele_stored (tele_sub C σ ++ Δ) C (sb_qn (List.length C) σ) (env_extend_typed ρ vts) ->
       glu_tele_stored (tele_sub (ce_ass κ A :: C) σ ++ Δ) (ce_ass κ A :: C) (sb_qn (List.length (ce_ass κ A :: C)) σ)
         (env_extend_typed ρ (vts ++ (⇑! d (List.length Δ + List.length C), t) :: nil))).
Proof.
  intros * HTSb HSb0 * Lx Hτ Hg HTP Hrel.
  cbn [List.app] in HSb0.
  destruct (glu_ctx_env_cons_clean_inversion HTSb HSb0) as (i0 & HA & HT & HSb).
  destruct (HT _ _ _ Hτ) as [a Pa Ela Ea Hga HTPa].
  destruct (Hrel a Ea) as [j Hda].
  (** The head type at [q^n σ], typed *)
  assert (HAτ : tele_sub C σ ++ Δ ⊢ A[sb_qn (List.length C) σ] : abs_kind_sort κ Typeω@i0)
    by (pose proof (glu_ctx_env_sub_escape HTSb _ _ _ Hτ);
        replace (abs_kind_sort κ Typeω@i0) with (abs_kind_sort κ Typeω@i0)[sb_qn (List.length C) σ]
          by (rewrite abs_kind_sort_sub; reflexivity); mauto 3).
  (** The variable, glued at [d], and at [a] *)
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hg HTP HAτ) as [Hkd Hnd].
  pose proof (var0_glu_elem Hg Hnd HTP) as Hv; rewrite Hkd in Hv.
  rewrite List.length_app, length_tele_sub, Nat.add_comm in Hv.
  assert (Hwk : (tele_sub C σ ++ Δ) ▹{κ} A[sb_qn (List.length C) σ] ⊢ᵏ ↑ : tele_sub C σ ++ Δ).
  { assert (⊢ (tele_sub C σ ++ Δ) ▹{κ} A[sb_qn (List.length C) σ])
      by (econstructor; [ exact HAτ | apply sort_kind_abs_kind_sort ]).
    mauto 3. }
  pose proof (glu_univ_elem_exp_conv_universe_index Hda Hg Hga Hv
                (glu_univ_elem_typ_monotone _ _ _ _ Hga _ _ _ _ HTPa Hwk)) as Hva.
  split.
  - cbn [tele_sub List.length sb_qn List.app centry_sub].
    assert (ErC : List.rev (ce_ass κ A :: C) = List.rev C ++ ce_ass κ A :: nil) by reflexivity.
    rewrite ErC, env_tele_snoc by (rewrite List.length_rev; lia).
    apply HSb.
    unfold sb_q; eapply cons_glu_sub_pred_helper_closure_gen;
      [ exact HTSb | exact (glu_ctx_env_sub_monotone _ _ HTSb _ _ _ _ _ Hτ Hwk) | exact HA | exact Ea | exact Hga | ].
    cbn [sentry_exp]; rewrite <- exp_wk_sub; exact Hva.
  - (** The stored types: the last variable at [d], the rest along the
        weakening. *)
    intros vts t Hvts Et Hst.
    rewrite env_extend_typed_app; cbn [env_extend_typed List.fold_left glu_tele_stored tele_sub List.length sb_qn List.app centry_sub].
    split.
    + exists t; split; [ reflexivity |].
      refine (mk_glu_stored_type _ _ _ _ t i d P El Et Hg _).
      unfold sb_q; cbn [exp_sub sentry_exp]; rewrite exp_sub_shift_extend, <- exp_wk_sub.
      exact Hv.
    + change (Wk ⨟ sb_q (sb_qn (List.length C) σ)) with (sb_wk (sb_qn (List.length C) σ) ↑).
      exact (glu_tele_stored_monotone _ _ _ _ Hst _ _ Hwk).
Qed.

(** The witness a fresh variable of the type [A] of a telescope is glued
    by, at its annotation [d]: [d] glued, [A] glued there (the typed
    witness [glu_sub_fresh_cons_at] moves the variable by), and [d]
    related to the value [a] of [A] in the context's environment. *)
Record glu_fresh_variable_witness (Δ : ctx) (A : typ) (a d : domain) (i : nat) (P : glu_typ_pred) (El : glu_exp_pred) : Prop :=
  mk_glu_fresh_variable_witness
  { (** The annotation's gluing *)
    fresh_witness_univ : DG d ∈ glu_univ_elem i ↘ P ↘ El
    (** The type, glued at it *)
  ; fresh_witness_typ : Δ ⊢ A ® P
    (** The annotation, related to the context's value *)
  ; fresh_witness_rel : exists j : nat, Dom d ≈ a ∈ per_univ j }.

(** Past [q^n σ] glued at the entries [vtsb] of a telescope [Cb], a
    telescope [Ct] of fresh variables [vts], each at its annotation in
    [ds], its stored type of that value, and its type glued there given
    the variables before it ([glu_fresh_variable_witness]): the extension
    is glued, position by position ([glu_sub_fresh_cons_at]), and so are
    its stored types.  Use it where no telescope annotates the variables
    exactly (a constructor's arguments, the recursive results), on top of
    a base glued by [glu_sub_fresh]. *)
Lemma glu_sub_fresh_at : forall Ct Cb Γb Sbb, all_assumptions Ct -> EG Cb ++ Γb ∈ glu_ctx_env ↘ Sbb ->
    forall Δ σ ρ vtsb vts ds, List.length vtsb = List.length Cb -> List.length vts = List.length Ct -> List.length ds = List.length Ct ->
    tele_sub Cb σ ++ Δ ⊢ˢ sb_qn (List.length Cb) σ ® env_tele ρ (List.rev Cb) (List.map fst vtsb) ∈ Sbb ->
    glu_tele_stored (tele_sub Cb σ ++ Δ) Cb (sb_qn (List.length Cb) σ) (env_extend_typed ρ vtsb) ->
    (** Each variable is fresh at its annotation, its stored type of it *)
    (forall k v t d, List.nth_error vts k = Some (v, t) -> List.nth_error ds k = Some d ->
       v = ⇑! d (List.length Δ + List.length Cb + k) /\ eval_entry_type gc_deps gc_stack t d) ->
    (** Each type is glued at its annotation, given the variables before *)
    (forall Cpost κ A Cpre d a, Ct = Cpost ++ ce_ass κ A :: Cpre -> List.nth_error ds (List.length Cpre) = Some d ->
       ⟦ A ⟧ env_tele ρ (List.rev (Cpre ++ Cb)) (List.map fst (vtsb ++ List.firstn (List.length Cpre) vts)) ↘ a ->
       (forall Sbk, EG (Cpre ++ Cb) ++ Γb ∈ glu_ctx_env ↘ Sbk ->
          tele_sub (Cpre ++ Cb) σ ++ Δ ⊢ˢ sb_qn (List.length (Cpre ++ Cb)) σ
            ® env_tele ρ (List.rev (Cpre ++ Cb)) (List.map fst (vtsb ++ List.firstn (List.length Cpre) vts)) ∈ Sbk) ->
       glu_tele_stored (tele_sub (Cpre ++ Cb) σ ++ Δ) (Cpre ++ Cb) (sb_qn (List.length (Cpre ++ Cb)) σ)
         (env_extend_typed ρ (vtsb ++ List.firstn (List.length Cpre) vts)) ->
       exists i P El, glu_fresh_variable_witness (tele_sub (Cpre ++ Cb) σ ++ Δ) A[sb_qn (List.length (Cpre ++ Cb)) σ] a d i P El) ->
    forall Sb, EG (Ct ++ Cb) ++ Γb ∈ glu_ctx_env ↘ Sb ->
    tele_sub (Ct ++ Cb) σ ++ Δ ⊢ˢ sb_qn (List.length (Ct ++ Cb)) σ ® env_tele ρ (List.rev (Ct ++ Cb)) (List.map fst (vtsb ++ vts)) ∈ Sb /\
    glu_tele_stored (tele_sub (Ct ++ Cb) σ ++ Δ) (Ct ++ Cb) (sb_qn (List.length (Ct ++ Cb)) σ) (env_extend_typed ρ (vtsb ++ vts)).
Proof.
  induction Ct as [| e Ct IH]; intros Cb Γb Sbb Hass HCb Δ σ ρ vtsb vts ds Lb Lv Ld Hτb Hstb Hx Hw Sb HSb.
  - destruct vts; [| discriminate ]; cbn [List.app]; rewrite !List.app_nil_r.
    split; [ apply (functional_glu_ctx_env HCb HSb); exact Hτb | exact Hstb ].
  - apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass0].
    destruct (List.exists_last (l := vts)) as (vts' & [y t] & ->); [ intros ->; discriminate |].
    destruct (List.exists_last (l := ds)) as (ds' & d & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Lv, Ld; cbn in Lv, Ld.
    cbn [List.app] in HSb.
    assert (HC0 : exists TSb, EG (Ct ++ Cb) ++ Γb ∈ glu_ctx_env ↘ TSb) by (inversion HSb; subst; eauto).
    destruct HC0 as [TSb HTSb].
    assert (Ef : forall k, k <= List.length Ct -> List.firstn k (vts' ++ (y, t) :: nil) = List.firstn k vts')
      by (intros k Hk; apply firstn_app_le; lia).
    (** The prefix *)
    assert (Hx' : forall k v t0 d0, List.nth_error vts' k = Some (v, t0) -> List.nth_error ds' k = Some d0 ->
                    v = ⇑! d0 (List.length Δ + List.length Cb + k) /\ eval_entry_type gc_deps gc_stack t0 d0).
    { intros k v t0 d0 Hv0 Hd0.
      assert (Hk : k < List.length ds') by (apply List.nth_error_Some; congruence).
      apply (Hx k); rewrite List.nth_error_app1 by lia; assumption. }
    assert (Hw' : forall Cpost κ0 A0 Cpre d0 a0, Ct = Cpost ++ ce_ass κ0 A0 :: Cpre -> List.nth_error ds' (List.length Cpre) = Some d0 ->
       ⟦ A0 ⟧ env_tele ρ (List.rev (Cpre ++ Cb)) (List.map fst (vtsb ++ List.firstn (List.length Cpre) vts')) ↘ a0 ->
       (forall Sbk, EG (Cpre ++ Cb) ++ Γb ∈ glu_ctx_env ↘ Sbk ->
          tele_sub (Cpre ++ Cb) σ ++ Δ ⊢ˢ sb_qn (List.length (Cpre ++ Cb)) σ
            ® env_tele ρ (List.rev (Cpre ++ Cb)) (List.map fst (vtsb ++ List.firstn (List.length Cpre) vts')) ∈ Sbk) ->
       glu_tele_stored (tele_sub (Cpre ++ Cb) σ ++ Δ) (Cpre ++ Cb) (sb_qn (List.length (Cpre ++ Cb)) σ)
         (env_extend_typed ρ (vtsb ++ List.firstn (List.length Cpre) vts')) ->
       exists i P El, glu_fresh_variable_witness (tele_sub (Cpre ++ Cb) σ ++ Δ) A0[sb_qn (List.length (Cpre ++ Cb)) σ] a0 d0 i P El).
    { intros Cpost κ0 A0 Cpre d0 a0 Heq Hd0 Ea0 Hτ0 Hst0.
      assert (Hk : List.length Cpre < List.length Ct) by (rewrite Heq, List.length_app; cbn; lia).
      assert (Ek := Ef _ (Nat.lt_le_incl _ _ Hk)).
      apply (Hw (ce_ass κ A :: Cpost) κ0 A0 Cpre d0 a0 ltac:(rewrite Heq; reflexivity)
               ltac:(rewrite List.nth_error_app1 by lia; exact Hd0)); rewrite Ek; assumption. }
    pose proof (fun Sb' HSb' => IH Cb Γb Sbb Hass0 HCb Δ σ ρ vtsb vts' ds' Lb ltac:(lia) ltac:(lia) Hτb Hstb Hx' Hw' Sb' HSb') as HIH.
    destruct (HIH TSb HTSb) as [Hτ Hst].
    (** The last variable: its annotation, and its type's witness *)
    destruct (Hx (List.length Ct) y t d
                ltac:(rewrite List.nth_error_app2 by lia; replace (List.length Ct - List.length vts') with 0 by lia; reflexivity)
                ltac:(rewrite List.nth_error_app2 by lia; replace (List.length Ct - List.length ds') with 0 by lia; reflexivity))
      as [-> Et].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HSb) as (i0 & _ & HT & _).
    destruct (HT _ _ _ Hτ) as [a P0 El0 Ea _ _].
    assert (Ea' : ⟦ A ⟧ env_tele ρ (List.rev (Ct ++ Cb)) (List.map fst (vtsb ++ List.firstn (List.length Ct) (vts' ++ (⇑! d (List.length Δ + List.length Cb + List.length Ct), t) :: nil))) ↘ a)
      by (rewrite (Ef _ (le_n _)), List.firstn_all2 by lia; exact Ea).
    destruct (Hw nil κ A Ct d a eq_refl
                ltac:(rewrite List.nth_error_app2 by lia; replace (List.length Ct - List.length ds') with 0 by lia; reflexivity) Ea'
                ltac:(intros Sbk HSbk; rewrite (Ef _ (le_n _)), List.firstn_all2 by lia; exact (proj1 (HIH Sbk HSbk)))
                ltac:(rewrite (Ef _ (le_n _)), List.firstn_all2 by lia; exact Hst))
      as (i & P & El & [Hg HTP Hrel]).
    destruct (glu_sub_fresh_cons_at (Ct ++ Cb) Γb κ A TSb Sb HTSb HSb Δ σ ρ (List.map fst (vtsb ++ vts')) i d P El
                ltac:(rewrite List.length_map, !List.length_app; lia) Hτ Hg HTP
                ltac:(intros a' Ea0; assert (a' = a) as -> by (eapply functional_eval_exp; eassumption); exact Hrel))
      as [Hτc Hstc].
    replace (List.length Δ + List.length (Ct ++ Cb)) with (List.length Δ + List.length Cb + List.length Ct) in Hτc, Hstc
      by (rewrite List.length_app; lia).
    split.
    + rewrite List.app_assoc, List.map_app; exact Hτc.
    + rewrite List.app_assoc.
      exact (Hstc (vtsb ++ vts') t eq_refl Et Hst).
Qed.

(** A variable of a context, at a type glued at the gluing of a type's
    value other than [LevelSort], is glued at it to the fresh variable of
    its level. *)
Lemma var_glu_elem_at : forall (i : universe_index) a P El Δ T x, DG a ∈ glu_univ_elem i ↘ P ↘ El -> not_level_sort a ->
    Δ ⊢ T ® P -> Δ ⊢ #x : T -> x < List.length Δ -> Δ ⊢ #x : T ® ⇑! a (List.length Δ - 1 - x) ∈ El.
Proof.
  intros * Hg Hn HT Hx Hlt.
  eapply realize_glu_elem_bot; [ exact Hg |].
  econstructor; [ exact Hx | exact Hg | exact HT | apply var_neutral_at; exact Hn |].
  intros Δ' φ M' Hφ HR.
  inversion HR; subst.
  destruct (kripke_shiftn _ _ _ Hφ) as [Hle _].
  pose proof (wk_var_kripke _ _ _ x Hφ) as Hφx.
  unfold glu_ne_eq; cbn [ne_annotate_proofs ne_to_exp].
  replace (List.length Δ' - (List.length Δ - 1 - x) - 1) with (φ x) by lia.
  apply wf_exp_eq_refl; change (a_var (φ x)) with (#x[φ]ʷ).
  exact (kripke_preserves_exp _ _ _ _ _ Hx Hφ).
Qed.

Lemma nth_rev_tele_sub : forall C1 e Pre σ,
    List.nth_error (List.rev (tele_sub (C1 ++ e :: Pre) σ)) (List.length Pre) = Some (centry_sub e (sb_qn (List.length Pre) σ)).
Proof.
  intros; rewrite tele_sub_app; cbn [tele_sub]; rewrite !List.rev_app_distr; cbn [List.rev].
  rewrite <- List.app_assoc; rewrite List.nth_error_app2 by (rewrite List.length_rev, length_tele_sub; lia).
  rewrite List.length_rev, length_tele_sub, Nat.sub_diag; reflexivity.
Qed.

(** ** The Recursive Results, Leaf Path by Leaf Path

    A position among the recursive results of arguments of kinds [gs]: the
    leaf path [leaf_pos_index] of the recursive argument [leaf_pos_shape],
    after those of the arguments before it ([leaf_pos_before]). *)
#[warnings="-cannot-define-projection"]
Record rec_leaf_pos (D : ind_decl) (gs : list carg) (k : nat) : Prop := mk_rec_leaf_pos
  { (** The arguments before the recursive one *)
    leaf_pos_before : list carg
    (** The recursive argument's shape *)
  ; leaf_pos_shape : ptyp
    (** The arguments after it *)
  ; leaf_pos_after : list carg
    (** The leaf path's index among the shape's *)
  ; leaf_pos_index : nat
    (** The kinds, split at the argument *)
  ; leaf_pos_split : gs = leaf_pos_before ++ ca_rec leaf_pos_shape :: leaf_pos_after
    (** The index is one of a leaf path of the shape *)
  ; leaf_pos_bound : leaf_pos_index < List.length (shape_leaves (rview_leaves D) 0 leaf_pos_shape)
    (** The position, after the results of the arguments before *)
  ; leaf_pos_at : k = cargs_nrec D leaf_pos_before + leaf_pos_index }.

(** Every position below the number of the recursive results is one. *)
Lemma rec_leaf_pos_of_lt : forall D gs k, k < cargs_nrec D gs -> rec_leaf_pos D gs k.
Proof.
  intros D gs; induction gs as [| [r A | t] gs IH]; intros k Hk; cbn [cargs_nrec] in Hk; [ lia | |].
  - destruct (IH k Hk) as [gs1 t gs2 idx Heq Hb Hat].
    exact (mk_rec_leaf_pos D (ca_arg r A :: gs) k (ca_arg r A :: gs1) t gs2 idx ltac:(rewrite Heq; reflexivity) Hb Hat).
  - destruct (Nat.lt_ge_cases k (List.length (shape_leaves (rview_leaves D) 0 t))) as [Hlt | Hge].
    + exact (mk_rec_leaf_pos D (ca_rec t :: gs) k nil t gs k eq_refl Hlt eq_refl).
    + destruct (IH (k - List.length (shape_leaves (rview_leaves D) 0 t)) ltac:(lia)) as [gs1 t' gs2 idx Heq Hb Hat].
      refine (mk_rec_leaf_pos D (ca_rec t :: gs) k (ca_rec t :: gs1) t' gs2 idx ltac:(rewrite Heq; reflexivity) Hb _).
      cbn [cargs_nrec]; lia.
Qed.

(** The recursive results' telescope at the leaf path [idx] of a
    recursive argument: after the results of the arguments before it and
    of the paths before it, the type of the path's result. *)
Lemma ihs_ctx_nth : forall r D nn As Us na gs gs1 t gs2 idx l, gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + nn) t) idx = Some l ->
    List.nth_error (List.rev (ihs_ctx_aux r (rview_leaves D) nn As Us na nil 0 gs)) (cargs_nrec D gs1 + idx)
    = Some (ce_ass r (leaf_ihty r As (sb_of_wk (wk_shiftn ((cargs_nrec D gs1 + idx) + na + nn)))
                        (ihs_sub nn Us na (cargs_pat gs1) (cargs_nrec D gs1 + idx))
                        (a_var ((cargs_nrec D gs1 + idx) + na - 1 - List.length (cargs_pat gs1))) l)).
Proof.
  intros * -> Hl.
  rewrite Views.ihs_ctx_aux_app; cbn [ihs_ctx_aux]; rewrite !List.app_nil_r; cbn [Nat.add].
  rewrite (Views.leaves_ctx_split _ _ _ _ _ _ _ _ _ _ Hl).
  rewrite !List.rev_app_distr; cbn [List.rev]; rewrite <- !List.app_assoc.
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_ihs_ctx_aux; lia).
  rewrite List.length_rev, length_ihs_ctx_aux.
  replace (cargs_nrec D gs1 + idx - cargs_nrec D gs1) with idx by lia.
  rewrite List.nth_error_app2
    by (rewrite List.length_rev, length_leaves_ctx, List.length_firstn; apply nth_error_lt_length in Hl; lia).
  rewrite List.length_rev, length_leaves_ctx, List.length_firstn.
  replace (idx - Nat.min idx (List.length (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + nn) t))) with 0
    by (apply nth_error_lt_length in Hl; lia).
  reflexivity.
Qed.

(** The recursive results of the arguments [As], at the leaf path [idx]
    of a recursive argument [N]: its recursive result along the path, over
    the non-recursive arguments before it. *)
Lemma elim_ihs_nth : forall r pq D Us Bks σ m gs gs1 t gs2 As N idx l, gs = gs1 ++ ca_rec t :: gs2 ->
    List.length As = List.length gs -> List.nth_error As (List.length gs1) = Some N ->
    List.nth_error (shape_leaves (rview_leaves D) (m + List.length (cargs_nonrec gs1)) t) idx = Some l ->
    List.nth_error (elim_ihs r pq D Us Bks σ m gs As) (cargs_nrec D gs1 + idx)
    = Some (leaf_ih r pq Us Bks (cargs_sub σ gs1 As) N l).
Proof.
  intros r pq D Us Bks σ m gs gs1; revert σ m gs; induction gs1 as [| g gs1 IH]; intros σ m gs t gs2 As N idx l -> Hl HN Hlf;
    destruct As as [| N0 As]; cbn in Hl, HN; try discriminate.
  - injection HN as ->; cbn [cargs_nonrec List.length] in Hlf; rewrite Nat.add_0_r in Hlf.
    cbn [elim_ihs cargs_nrec Nat.add List.app cargs_sub].
    rewrite List.nth_error_app1 by (rewrite List.length_map; apply nth_error_lt_length in Hlf; exact Hlf).
    rewrite List.nth_error_map, Hlf; reflexivity.
  - destruct g as [r0 A | t0]; cbn [elim_ihs cargs_nrec cargs_sub List.app].
    + cbn [cargs_nonrec List.length] in Hlf.
      apply (IH (σ ,, N0) (S m) _ t gs2 As N idx l eq_refl ltac:(injection Hl as Hl; exact Hl) HN).
      replace (S m + List.length (cargs_nonrec gs1)) with (m + S (List.length (cargs_nonrec gs1))) by lia; exact Hlf.
    + rewrite List.nth_error_app2 by (rewrite List.length_map, (length_shape_leaves _ _ _ 0); lia).
      rewrite List.length_map, (length_shape_leaves _ _ m 0).
      replace (List.length (shape_leaves (rview_leaves D) 0 t0) + cargs_nrec D gs1 + idx - List.length (shape_leaves (rview_leaves D) 0 t0))
        with (cargs_nrec D gs1 + idx) by lia.
      cbn [cargs_nonrec] in Hlf.
      exact (IH σ m _ t gs2 As N idx l eq_refl ltac:(injection Hl as Hl; exact Hl) HN Hlf).
Qed.

(** The values of the recursive results of the arguments [vs], at a
    recursive argument [v]: those of [v], after those of the arguments
    before it. *)
Lemma eval_ihs_nth : forall ρ p D ups Bks gs vs ihs, ind_lookup gc_deps gc_stack p = Some D -> leaves_coherent D ->
    ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
    forall gs1 t gs2 v, gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
    exists rs, ⟦ih v of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rs /\
      forall idx, idx < List.length rs -> List.nth_error ihs (cargs_nrec D gs1 + idx) = List.nth_error rs idx.
Proof.
  intros ρ p D ups Bks gs vs ihs Hl Hco H gs1; revert gs vs ihs H; induction gs1 as [| g gs1 IH]; intros gs vs ihs H t gs2 v -> Hv;
    inversion H; subst; cbn [List.app List.length] in *; try discriminate.
  - injection Hv as ->.
    match goal with Hr : ⟦ih _ of _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?r1 |- _ => exists r1; split; [ exact Hr |] end.
    intros idx Hidx; cbn [cargs_nrec Nat.add]; rewrite List.nth_error_app1 by exact Hidx; reflexivity.
  - edestruct IH as (rs & Er & Hrs); [ eassumption | reflexivity | exact Hv |]; exists rs; split; [ exact Er |].
    intros idx Hidx; cbn [cargs_nrec]; exact (Hrs idx Hidx).
  - edestruct IH as (rs & Er & Hrs); [ eassumption | reflexivity | exact Hv |]; exists rs; split; [ exact Er |].
    intros idx Hidx; cbn [cargs_nrec].
    lazymatch goal with
    | |- List.nth_error (?r1 ++ _) _ = _ =>
        match goal with Hr : ⟦ih _ of _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ r1 |- _ =>
          pose proof (proj1 (proj2 (@eval_ih_length_all gc_deps gc_stack)) _ _ _ _ _ _ _ Hr _ Hl Hco) as Lr1 end
    end.
    rewrite List.nth_error_app2 by lia.
    rewrite <- Lr1, <- Nat.add_assoc, Nat.add_comm, Nat.add_sub; exact (Hrs idx Hidx).
Qed.

(** ** Fresh Variables of Readback, Position by Position *)

Lemma fresh_tele_nth : forall E T s vs, Ftele T in gc_deps ⍮ gc_stack ⍮ E ⍮ s ↘ vs ->
    forall k κ A, List.nth_error T k = Some (ce_ass κ A) ->
      exists b, ⟦ A ⟧ env_tele E T (List.firstn k vs) ↘ b /\ List.nth_error vs k = Some (⇑! b (s + k)).
Proof.
  induction 1 as [| ? ? ? ? ? ? ? Ea Hr IH]; intros k κ0 A0 Hk; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in Hk |- *.
  - injection Hk as <- <-; exists a; rewrite Nat.add_0_r; split; [ exact Ea | reflexivity ].
  - destruct (IH k κ0 A0 Hk) as (b & Eb & Hb); exists b; split; [ exact Eb |].
    rewrite Hb; do 3 f_equal; lia.
Qed.

Lemma fresh_cargs_nth : forall p ups E gs s vs, Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ E ⍮ s ↘ vs ->
    forall gs1 g gs2, gs = gs1 ++ g :: gs2 ->
    (forall r A, g = ca_arg r A ->
       exists a, ⟦ A ⟧ env_tele E (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
         List.nth_error vs (List.length gs1) = Some (⇑! a (s + List.length gs1))) /\
    (forall t, g = ca_rec t ->
       exists a, ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮
                   env_tele E (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
         List.nth_error vs (List.length gs1) = Some (⇑! a (s + List.length gs1))).
Proof.
  intros p ups E gs s vs H gs1; revert E gs s vs H; induction gs1 as [| g1 gs1 IH]; intros * H g gs2 Heq; cbn in Heq.
  - subst; split; intros * ->; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto.
  - subst; inversion H; subst;
      lazymatch goal with Hr1 : fresh_cargs _ _ _ _ _ (gs1 ++ _) _ _ |- _ => destruct (IH _ _ _ _ Hr1 g gs2 eq_refl) as [IHa IHr] end.
    + split.
      * intros r0 A0 ->; destruct (IHa r0 A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros t0 ->; destruct (IHr t0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
    + split.
      * intros r0 A0 ->; destruct (IHa r0 A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros t0 ->; destruct (IHr t0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
Qed.

(** ** Function Shapes: Values *)

(** The recursive results of an argument of a function shape: one family
    per leaf path of the rest of the shape. *)
Lemma eval_ih_pi_inv : forall ρ0 p D ups Bks0 B t v r, ind_lookup gc_deps gc_stack p = Some D ->
    ⟦ih v of pt_pi B t under p ups Bks0 ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ r ->
    r = List.map (fun i => d_ihfn ρ0 Bks0 p ups t i v) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t))).
Proof.
  intros * Hl H; inversion H; subst.
  match goal with H' : ind_lookup _ _ p = Some ?D' |- _ => rewrite Hl in H'; injection H' as <- end; reflexivity.
Qed.

(** The [i]-th recursive result of a function shape, applied: the
    [i]-th recursive result of the rest at the function's value. *)
Lemma eval_app_ihfn_inv : forall ρ0 Bks0 p ups t i f c r fc, $| d_ihfn ρ0 Bks0 p ups t i f & c | gc_deps ⍮ gc_stack ↘ r ->
    $| f & c | gc_deps ⍮ gc_stack ↘ fc ->
    exists rs, ⟦ih fc of t under p ups Bks0 ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ rs /\ List.nth_error rs i = Some r.
Proof.
  intros * H Ef; inversion H; subst.
  match goal with Ef' : $| f & c | _ ⍮ _ ↘ ?fc' |- _ => assert_fails constr_eq fc' fc; pose proof (functional_eval_app _ _ _ _ Ef Ef') as <- end.
  eauto.
Qed.

(** ** Function Shapes: Syntax *)

(** The domains of function shapes are relevant: these are at
    [ak_relevant]. *)

(** [β] after a Kripke weakening. *)
Lemma fn_wk_beta : forall Δ' Δ IT OT M b φ (i : nat),
    Δ' ⊢ IT : Typeω@i -> Δ' ▹{ak_relevant} IT ⊢ OT : Typeω@i -> Δ' ▹{ak_relevant} IT ⊢ M : OT -> Δ ⊢ᵏ φ : Δ' ->
    Δ ⊢ b : IT[φ]ʷ -> Δ ⊢ (λ IT M)[φ]ʷ $ b ≈ M[(ι φ),,b] : OT[(ι φ),,b].
Proof.
  intros * HIT HOT HM Hφ Hb; cbn [exp_wk].
  rewrite <- (exp_sub_wk_q_extend M), <- (exp_sub_wk_q_extend OT).
  eapply wf_exp_eq_pi_beta with (κc := ak_relevant);
    [ exact (kripke_preserves_typ _ _ _ _ _ HIT Hφ) | constructor
    | exact (kripke_preserves_typ_q _ _ _ _ _ _ _ _ HOT HIT ltac:(constructor) Hφ) | constructor
    | exact (kripke_preserves_exp_q _ _ _ _ _ _ _ _ HM HIT ltac:(constructor) Hφ) | exact Hb ].
Qed.

Lemma app_wk_typed : forall Δ' Δ IT OT N b φ, Δ' ⊢ N : Π{ak_relevant} IT OT -> Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ->
    Δ ⊢ N[φ]ʷ $ b : OT[(ι φ),,b].
Proof.
  intros * HN Hφ Hb; rewrite <- exp_sub_wk_q_extend.
  eapply wf_app'; [ exact (kripke_preserves_exp _ _ _ _ _ HN Hφ) | exact Hb ].
Qed.

Lemma sub_typ_extend : forall Δ' Δ IT OT φ b (j : nat), Δ' ⊢ IT : Typeω@j -> Δ' ▹{ak_relevant} IT ⊢ OT : Typeω@j ->
    Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ -> Δ ⊢ OT[(ι φ),,b] : Typeω@j.
Proof.
  intros * HIT HOT Hφ Hb; rewrite <- exp_sub_wk_q_extend.
  pose proof (kripke_preserves_typ_q _ _ _ _ _ _ _ _ HOT HIT ltac:(constructor) Hφ) as H.
  pose proof (kripke_preserves_typ _ _ _ _ _ HIT Hφ) as HIT'.
  assert (Hs : Δ ⊢ˢ Id,,b : Δ ▹{ak_relevant} IT[φ]ʷ) by mauto 3.
  exact (sub_preserves_exp _ _ _ _ _ _ _ H Hs).
Qed.

(** ** Weakening Then Extending

    A substitution weakened past one variable, then extended by a term at
    a weakening: the substitution at the weakening. *)
Lemma sb_wk_shift_extend : forall σ φ e, sb_eq (sb_wk σ ↑ ⨟ sb_extend (ι φ) e) (sb_wk σ φ).
Proof.
  intros σ φ e x; unfold sb_wk; cbn [sb_compose].
  rewrite sentry_sub_wk, (sentry_sub_sb_eq _ _ (ι φ)) by (intros y; reflexivity).
  apply sentry_sub_of_wk.
Qed.

Lemma exp_shift_extend_wk_e : forall U φ e, U[↑]ʷ[sb_extend (ι φ) e] = U[φ]ʷ.
Proof. intros; rewrite exp_sub_shift; apply exp_sub_of_wk_ext; intros [|?]; reflexivity. Qed.

Lemma blocks_step : forall Bks σ φ e,
    blocks_sub (blocks_wk (blocks_sub Bks σ) ↑) (sb_extend (ι φ) e) = blocks_sub Bks (sb_wk σ φ).
Proof.
  intros; rewrite <- blocks_sub_of_wk, !blocks_sub_sub; apply blocks_sub_sb_eq.
  etransitivity; [ apply sb_compose_cong_r; intros x; reflexivity | symmetry; apply sb_wk_compose ].
Qed.

(** Substitutions with the same terms at every variable act alike on the
    terms of a shape, which have no free module variable. *)
Definition sb_exp_agree (σ τ : sub) : Prop := forall x, sentry_exp (σ x) = sentry_exp (τ x).

Lemma sb_exp_agree_q : forall σ τ, sb_exp_agree σ τ -> sb_exp_agree (q σ) (q τ).
Proof. intros σ τ H; exact (sb_q_exp_agree σ τ H). Qed.

Lemma sb_exp_agree_var0 : forall σ, sb_exp_agree (q σ ⨟ ((ι ↑),,#0)) (q σ ⨟ sb_extend (ι ↑) (se_var 0)).
Proof.
  intros σ [| y]; cbn [sb_compose]; [ reflexivity |].
  f_equal; change ((q σ) (S y)) with (sentry_wk (σ y) ↑).
  rewrite !sentry_sub_wk; apply sentry_sub_sb_eq; intros z; reflexivity.
Qed.

(** ** Glued Arguments along Related Types *)

Lemma tele_insts_base_agree : forall Δ k σ σ' Ms, all_assumptions Δ -> ctx_scoped k Δ ->
    (forall x, x < k -> σ x = σ' x) -> tele_insts Δ σ Ms = tele_insts Δ σ' Ms.
Proof.
  intros * Hass Hs Hσ.
  pose proof (tele_insts_sub Δ k σ σ' Id Ms Hass Hs ltac:(intros x Hx; rewrite sentry_sub_id; apply Hσ; exact Hx)) as H.
  rewrite (List.map_ext _ (fun T => T) (fun T => exp_sub_id T)), List.map_id in H.
  rewrite (List.map_ext _ (fun M => M) (fun M => exp_sub_id M)), List.map_id in H.
  exact H.
Qed.

End Fixed_GCtx.
