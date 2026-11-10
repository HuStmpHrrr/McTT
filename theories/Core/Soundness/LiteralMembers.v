(** * Members of Module Literals in the Gluing Model

    A member of a module literal is read off the literal's closure: the
    body evaluated at the environment ([eval_body_env]), and the member's
    body at the environment of the entries before it ([eval_sel_body]).
    The body's environment is glued along the body's context, entry by
    entry, at the substitution filling the entries in ([gm_fill]): each
    entry's head is its body's value, glued by the body context's gluing,
    and stored at the closure of its type as the body's environment stores
    it.  The member is then glued at the type's value in the body's
    environment, and moved to the filled-in type's value by C4 with the
    filled-in type's gluing as the witness, the two related by the
    completeness of the fill ([fill_rel]); its term is moved by δ, an
    equation of terms. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases UnitCases.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Values.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases Instances LetCases.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [σ,,M[σ]] into a definition entry, the head stored at the closure of
    the type as a body's environment stores it ([eval_body_env_def]), as
    [cons_def_glu_sub_pred_helper] at the type's value. *)
Lemma cons_def_glu_sub_pred_closure : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El M m},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    Γ ⊢ M : A ->
    ⟦ A ⟧ ρ ↘ a ->
    glu_term_value M ρ (domain_kind a) m ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M[σ] : A[σ] ® m ∈ El ->
    Δ ⊢ˢ σ,,M[σ] ® ρ ↦ m ⦂ entry_type_closure A ρ ∈ cons_def_glu_sub_pred i Γ A M Sb.
Proof.
  intros * HSb Hσg HA HM Ha Hm Hglu HMσ.
  assert (Hσ : Δ ⊢ˢ σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  assert (HMσt : Δ ⊢ M[σ] : A[σ]) by (eapply glu_univ_elem_trm_escape; eassumption).
  assert (Δ ⊢ˢ σ,,M[σ] : Γ ▸ A ≔ M)
    by (eapply wf_sub_extend_def; [ exact Hσ | exact HA | apply type_sort_abs_kind; constructor | exact HM
                                  | exact HMσt | apply wf_exp_eq_refl; exact HMσt ]).
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMσ HR) as Hmm.
  econstructor; [ eassumption | exact Ha | exact Hglu | | | | | ].
  - rewrite exp_sub_shift_extend; exact HMσ.
  - intros Hev; exists m; split; [ destruct (domain_kind a); [ exact Hm | inversion Hev | exact Hm ] |].
    exact (per_head_of Ha Ha HR Hmm).
  - (** The stored type is the closure of the type, of the type's value *)
    eexists; split; [ reflexivity |].
    refine (mk_glu_stored_type _ _ _ _ _ i a P El _ Hglu _); [ econstructor; exact Ha | rewrite exp_sub_shift_extend; exact HMσ ].
  - split; [ exact (proj1 (entry_readable_of_elem_closure Ha Ha HR Hmm)) | cbn; lia ].
  - first [ exact Hσg | cbn; exact Hσg | eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | exact Hσg | mauto 3 ] ].
Qed.

(** The environment of a body that can be filled in, over a glued
    environment of its context, is glued along the body's context at the
    substitution filling the body in after the context's: entry by entry,
    a definition's head its body's value there at the kind its type has
    ([body_sorts_valid]), a module's its unit's closure there, related to
    itself (the completeness of the unit's literal). *)
Lemma glu_body_env : forall Φ Γ TSb,
    EG Γ ∈ glu_ctx_env ↘ TSb ->
    body_sorts_valid Φ Γ ->
    forall ζ, gm_fill Φ = Some ζ ->
    forall Sb, EG body_ctx Φ ++ Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ TSb ->
    exists σ' ρ', sb_eq σ' (ζ ⨟ σ) /\ ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' /\ Δ ⊢ˢ σ' ® ρ' ∈ Sb.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros Γ TSb HΓ Hsv ζ Hf Sb HSb Δ σ ρ Hσ; cbn in Hf; [| | discriminate ].
  - injection Hf as <-; cbn in HSb.
    assert (E : TSb <∙> Sb) by (eapply functional_glu_ctx_env; eassumption).
    exists σ, ρ; split; [ intros x; reflexivity | split; [ constructor | apply E; exact Hσ ] ].
  - cbn [body_sorts_valid] in Hsv; destruct Hsv as [Hsv HsvE].
    destruct E as [b pv κ A [M |] | pv [Δy Dy] | ? ? ? ? ? | pv A M [Δy Dy] | ? ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [ζ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HSb.
    + (** A definition *)
      destruct (glu_rel_ctx_tail (ex_intro _ _ HSb)) as [TSb0 HTSb0].
      destruct (IH _ _ HΓ Hsv _ eq_refl _ HTSb0 _ _ _ Hσ) as (σ0 & ρ0 & Eσ0 & Hb0 & Hσ0).
      destruct (glu_ctx_env_cons_def_clean_inversion HTSb0 HSb) as (i & κ' & HA & HM & _ & HMg & ESb).
      destruct (HMg _ _ _ Hσ0) as [a m P El Ea Hm Hglu HMσ].
      (** The kind of the type is the definition's tag *)
      destruct (HsvE A M eq_refl) as [iA HAv].
      destruct (glu_ctx_env_per_ctx_env HTSb0) as [R0 HR0].
      pose proof (glu_ctx_env_per_env HTSb0 HR0 Hσ0) as Hρ0.
      destruct (rel_exp_of_abs_kind_sort_at HR0 HAv _ _ Hρ0) as (a' & Ea' & Hka).
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      cbn [entry_kind] in Hka.
      exists (σ0 ,, M[σ0]), (ρ0 ↦ m ⦂ entry_type_closure A ρ0); split; [| split ].
      * intros [| x]; cbn; [ f_equal; rewrite exp_sub_sub; apply exp_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity
                           | exact (Eσ0 x) ].
      * destruct (evaluated_kind_or_propositional κ) as [Hk | ->].
        -- eapply eval_body_env_def; [ exact Hk | exact Hb0 |].
           rewrite Hka in Hm; destruct Hk; exact Hm.
        -- rewrite Hka in Hm; cbn in Hm; subst m; apply eval_body_env_def_proof; exact Hb0.
      * apply ESb; eapply cons_def_glu_sub_pred_closure; eassumption.
    + (** A submodule *)
      inversion HSb as [| | | ? ? TSb0 ? HTSb0 HU ESb |]; subst.
      destruct (IH _ _ HΓ Hsv _ eq_refl _ HTSb0 _ _ _ Hσ) as (σ0 & ρ0 & Eσ0 & Hb0 & Hσ0).
      destruct (glu_ctx_env_per_ctx_env HTSb0) as [R0 HR0].
      pose proof (glu_ctx_env_per_env HTSb0 HR0 Hσ0) as Hρ0.
      pose proof (glu_ctx_env_sub_escape HTSb0 _ _ _ Hσ0) as Hσ0s.
      assert (HUl : gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ Γ ⊢ᵐ me_lit (gu_mk Δy Dy) ≈ me_lit (gu_mk Δy Dy))
        by (apply wf_me_lit; exact HU).
      destruct (rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HUl) HR0 _ _ Hρ0)
        as (h & h' & Hh & Hh' & Hhh).
      pose proof (functional_eval_modexp _ _ _ _ Hh' Hh) as ->.
      exists (σ0 ,,ₘ me_lit (gu_mk Δy Dy)[σ0]ᵘ), (ρ0 ↦ᵐ h ⦂ gu_mk Δy Dy); split; [| split ].
      * intros [| x]; cbn; [ f_equal; f_equal; rewrite gunit_sub_sub; apply gunit_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity
                           | exact (Eσ0 x) ].
      * eapply eval_body_env_mod; [ exact Hb0 | apply eval_me_lit_iff; exact Hh ].
      * apply ESb; econstructor.
        -- apply wf_sub_extend_mod; [ exact Hσ0s | exact HU | eapply sub_preserves_unit; eassumption ].
        -- exists h; split; [ exact Hh | exact Hhh ].
        -- eexists; reflexivity.
        -- split; [ apply mod_entry_readable | cbn; exact (gunit_scoped_free_bound _ _ (wf_unit_eq_scoped_left _ _ _ _ _ HU)) ].
        -- exact Hσ0.
    + (** A definition with a module part: as a definition and as a
          submodule *)
      destruct (glu_rel_ctx_tail (ex_intro _ _ HSb)) as [TSb0 HTSb0].
      destruct (IH _ _ HΓ Hsv _ eq_refl _ HTSb0 _ _ _ Hσ) as (σ0 & ρ0 & Eσ0 & Hb0 & Hσ0).
      destruct (glu_ctx_env_cons_dm_clean_inversion HTSb0 HSb) as (i & HA & HM & Hwe & _ & HMg & ESb).
      destruct (HMg _ _ _ Hσ0) as [a m P El Ea Hm Hglu HMσ].
      destruct (glu_ctx_env_per_ctx_env HTSb0) as [R0 HR0].
      pose proof (glu_ctx_env_per_env HTSb0 HR0 Hσ0) as Hρ0.
      pose proof (glu_ctx_env_sub_escape HTSb0 _ _ _ Hσ0) as Hσ0s.
      inversion Hwe; subst.
      match goal with H : _ ⍮ _ ⍮ _ ⊢ᵘ gu_mk nil (md_alias _) ≈ _ |- _ => rename H into HU end.
      destruct (HsvE A M eq_refl) as [iA HAv].
      destruct (rel_exp_of_abs_kind_sort_at HR0 HAv _ _ Hρ0) as (a' & Ea' & Hka).
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      cbn [entry_kind] in Hka; rewrite Hka in Hm; cbn in Hm.
      assert (HUl : gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ Γ ⊢ᵐ me_lit (gu_mk nil (md_alias E)) ≈ me_lit (gu_mk nil (md_alias E)))
        by (apply wf_me_lit; exact HU).
      destruct (rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HUl) HR0 _ _ Hρ0)
        as (h & h' & Hh & Hh' & Hhh).
      pose proof (functional_eval_modexp _ _ _ _ Hh' Hh) as ->.
      exists (σ0 ,,ᵈ M[σ0] ‖ me_lit (gu_mk nil (md_alias E))[σ0]ᵘ),
             (ρ0 ↦ᵈ m ⦂ entry_type_closure A ρ0 ‖ h ⦂ gu_mk nil (md_alias E)); split; [| split ].
      * intros [| x]; cbn; [ f_equal; [ rewrite exp_sub_sub; apply exp_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity
                                      | f_equal; rewrite gunit_sub_sub; apply gunit_sub_sb_eq; intros z; rewrite (Eσ0 z); reflexivity ]
                           | exact (Eσ0 x) ].
      * eapply eval_body_env_dm; [ exact Hb0 | exact Hm | apply eval_me_lit_iff; exact Hh ].
      * assert (HMσt : Δ ⊢ M[σ0] : A[σ0]) by (eapply glu_univ_elem_trm_escape; eassumption).
        destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
        pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMσ HR) as Hmm.
        apply ESb; econstructor;
          [ eapply wf_sub_extend_dm; eauto; first [ apply wf_exp_eq_refl; exact HMσt | eapply sub_preserves_unit; eassumption ]
          | exact Ea | exact Hglu | rewrite exp_sub_shift_extend; exact HMσ
          | exists m; split; [ exact Hm | exact (per_head_of Ea Ea HR Hmm) ]
          | exists h; split; [ exact Hh | exact Hhh ]
          | eexists; split; [ reflexivity |];
            refine (mk_glu_stored_type _ _ _ _ _ i a P El _ Hglu _);
            [ apply eval_entry_type_closure; exact Ea | rewrite exp_sub_shift_extend; exact HMσ ]
          | split; [ exact (proj1 (dm_entry_readable_of_elem_closure Ea Ea HR Hmm h h (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E))))
                   | cbn; exact (gunit_scoped_free_bound _ _ (wf_unit_eq_scoped_left _ _ _ _ _ HU)) ]
          | exact Hσ0 ].
Qed.

(** A type over a body's context, filled in, at an environment of the
    context, and the type at the body's environment there: related types,
    by the completeness of the fill ([fill_rel]).  This relates the two
    type values a C4 moves between; it moves no gluing. *)
Lemma fill_type_per : forall Φ Γ ζ A (i : nat),
    gm_nopens Φ = 0 -> gm_fill Φ = Some ζ -> ⊨ body_ctx Φ ++ Γ -> body_sorts_valid Φ Γ ->
    gmod_scoped (List.length Γ) Φ ->
    body_ctx Φ ++ Γ ⊨ᵗ A ≈ A at i ->
    forall RΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
    forall ρ', ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' ->
    exists c a, ⟦ A[ζ] ⟧ ρ ↘ c /\ ⟦ A ⟧ ρ' ↘ a /\ Dom c ≈ a ∈ per_univ i.
Proof.
  intros * Hn Hf HC Hsv Hs HA RΓ HRΓ ρ Hρ ρ' Hb.
  destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
  destruct (fill_rel _ _ _ Hn Hf HC Hsv Hs _ _ HRΓ HR _ Hρ) as (ρσ & ρ1 & Eζ & Hb1 & Hρσ1).
  assert (ρ1 = ρ') as -> by (eapply functional_eval_body_env; eassumption).
  pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf HC Hs)) as Hζ.
  pose proof HA as [Rt HRt HAb _].
  destruct (HAb _ _ HRΓ _ _ Hζ _ _ _ _ Hρ Eζ Eζ) as [c a1 a1' c' Ec Ea1 _ _ [Hca1 _]].
  destruct (rel_type_inversion_simple_at HR HA _ _ Hρσ1)
    as (a2 & a & Ea2 & Ea & Ha2a).
  assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption).
  exists c, a; repeat split; [ exact Ec | exact Ea | eapply per_univ_trans'; eassumption ].
Qed.

(** A definition of a module literal under no parameters, of an evaluated
    kind, unapplied: glued at its type filled in.  At a glued environment,
    its value is its body's value at the body's environment there
    ([eval_sel_body]), glued along the body's context ([glu_body_env]); the
    body's gluing there is moved to the filled-in type's value by C4, with
    the filled-in type's gluing as the witness and [fill_type_per] as the
    relation of the two type values, and to the member's term by δ, an
    equation of terms. *)
Lemma glu_rel_exp_mem_lit_def : forall Γ sm Φ x Φ' b pv κ A M ζ (j : nat),
    gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x (ge_def b pv κ A (Some M))) ->
    evaluated_kind κ ->
    gm_fill Φ' = Some ζ ->
    ⊩ (body_ctx Φ' ++ Γ) ▸ A ≔ M ->
    ⊨ body_ctx Φ' ++ Γ ->
    body_sorts_valid (gm_ext Φ' x (ge_def b pv κ A (Some M))) Γ ->
    gmod_scoped (List.length Γ) Φ' ->
    Γ ⊢ a_mem (me_lit (gu_mk nil (md_body sm Φ))) x ≈ M[ζ] : A[ζ] ->
    Γ ⊩ A[ζ] : abs_kind_sort κ Typeω@j ->
    Γ ⊩ a_mem (me_lit (gu_mk nil (md_body sm Φ))) x : A[ζ].
Proof.
  intros * Hp Hκ Hf [SbE HSbE] HC Hsv Hs Hδ HW.
  cbn [body_sorts_valid] in Hsv; destruct Hsv as [Hsv HsvE].
  assert (Hn : gm_nopens Φ' = 0).
  { clear - Hf; revert ζ Hf; induction Φ' as [| Φ0 IH y E | ? ? ? ? ? ?]; intros ζ Hf; cbn in *; [ reflexivity | | discriminate ].
    destruct E as [? ? ? ? [] | | | | ]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ0) eqn:Hf0; cbn in Hf; try discriminate; exact (IH _ eq_refl). }
  destruct (glu_rel_exp_sort_typ HW (sort_kind_abs_kind_sort κ j)) as (SbW & iW & HSbW & _ & HAg).
  destruct (glu_rel_ctx_tail (ex_intro _ _ HSbE)) as [SbB HSbB].
  destruct (glu_ctx_env_cons_def_clean_inversion HSbB HSbE) as (i0 & κ0 & HA0 & HM0 & _ & HMg & _).
  destruct (HsvE A M eq_refl) as [iA HAv]; cbn [entry_kind] in HAv.
  pose proof (rel_type_of_abs_kind_sort HAv) as HAt.
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := iW); [ exact HSbW |]; intros Δ σ ρ Hσ.
  destruct (HAg _ _ _ Hσ) as [c Pc Elc Ec HPc HTPc].
  pose proof (glu_ctx_env_sub_escape HSbW _ _ _ Hσ) as Hσt.
  destruct (glu_ctx_env_per_ctx_env HSbW) as [RΓ HRΓ].
  pose proof (glu_ctx_env_per_env HSbW HRΓ Hσ) as Hρ.
  (** The body's environment, glued *)
  destruct (glu_body_env _ _ _ HSbW Hsv _ Hf _ HSbB _ _ _ Hσ) as (σ' & ρ' & Eσ' & Hb & Hσ').
  destruct (HMg _ _ _ Hσ') as [a m P El Ea Hm Hglu HMσ].
  (** The two type values are related *)
  destruct (fill_type_per _ _ _ _ _ Hn Hf HC Hsv Hs HAt _ HRΓ _ Hρ _ Hb) as (c' & a' & Ec' & Ea' & Hca).
  assert (c' = c) as -> by (eapply functional_eval_exp; eassumption).
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  (** The kinds: the type's at the body's environment is the tag *)
  destruct (glu_ctx_env_per_ctx_env HSbB) as [RB HRB].
  pose proof (glu_ctx_env_per_env HSbB HRB Hσ') as Hρ'.
  destruct (rel_exp_of_abs_kind_sort_at HRB HAv _ _ Hρ') as (a'' & Ea'' & Hka).
  assert (a'' = a) as -> by (eapply functional_eval_exp; eassumption).
  rewrite Hka in Hm; assert (Em : ⟦ M ⟧ ρ' ↘ m) by (destruct Hκ; exact Hm).
  destruct Hca as [Rca Hca].
  pose proof (per_univ_elem_kind _ _ _ _ Hca) as Hkc.
  (** The member's value is the body's *)
  assert (Ev : ⟦ a_mem (me_lit (gu_mk nil (md_body sm Φ))) x ⟧ ρ ↘ m).
  { eapply eval_mem_of_sel; [ apply eval_me_lit_iff; constructor |].
    eapply eval_sel_body; [ rewrite (gm_expand_noopen _ (gm_noopen_expand Φ)); exact Hp | reflexivity | exact Hκ | exact Hb | exact Em ]. }
  econstructor; [ exact Ec | rewrite Hkc, Hka; destruct Hκ; exact Ev | exact HPc |].
  (** The body's gluing, at the filled-in type, then at the member *)
  assert (EA : A[σ'] = A[ζ][σ]) by (rewrite exp_sub_sub; apply exp_sub_sb_eq; exact Eσ').
  assert (EM : M[σ'] = M[ζ][σ]) by (rewrite exp_sub_sub; apply exp_sub_sb_eq; exact Eσ').
  rewrite EA, EM in HMσ.
  pose proof (glu_univ_elem_exp_conv (per_univ_sym' _ _ _ (ex_intro _ Rca Hca)) Hglu HPc HMσ HTPc) as HMc.
  eapply glu_univ_elem_trm_resp_exp_eq; [ exact HPc | exact HMc |].
  apply wf_exp_eq_sym; eapply sub_preserves_exp_eq; [ exact Hδ | exact Hσt ].
Qed.

End Fixed_GCtx.
