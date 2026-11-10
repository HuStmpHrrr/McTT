(** * Module [let]s in the Gluing Model

    Module values are not glued.  A module slot glues by its syntactic typing
    and by the tie of its value to the closure of its unit
    ([cons_mod_glu_sub_pred]).  A module [let] glues through its body, at the
    environment extended by the unit's closure: the term is equal to the
    body's instance syntactically ([glu_univ_elem_trm_resp_exp_eq]), its
    value is the body's, and it is moved from the body's type's value to the
    related value of its own type at that type's gluing, its witness
    ([glu_univ_elem_exp_conv]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LetCases UnitCases UniverseCases.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  VariableCases
  Instances.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The value of a type under the module [let] of a unit: the value of the
    type substituted by the unit's literal is related to the value of the
    type at the environment extended by the unit's closure
    ([rel_exp_let_mod_gen] at the type, a term of its sort). *)
Lemma let_mod_typ_value : forall {Γ U C R},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    gc_deps ⍮ gc_stack ⍮ Γ ▹ₘ U ⊢ᵗ C ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    exists (i : nat), forall ρ h,
      Dom ρ ≈ ρ ∈ R ->
      ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
      exists c' c, ⟦ C[Id ,,ₘ me_lit U] ⟧ ρ ↘ c' /\ ⟦ C ⟧ ρ ↦ᵐ h ⦂ U ↘ c /\ Dom c' ≈ c ∈ per_univ i.
Proof.
  intros * HU HCt HR.
  inversion HCt as [? S HS HCs | ?]; subst.
  - pose proof (proj1 (proj2 completeness_fundamental_modules) _ _ _ HU) as HUc.
    pose proof (completeness_fundamental_exp _ _ _ HCs) as HCc.
    pose proof (wf_unit_eq_scoped_left _ _ _ _ _ HU) as HUs.
    pose proof (rel_exp_let_mod_gen HUc HCc HUs HUs) as Hz.
    assert (HSs : S[Id ,,ₘ me_lit U] = S) by (destruct HS; reflexivity).
    rewrite HSs in Hz.
    destruct (rel_type_of_sort HS Hz) as [i Hi].
    exists i; intros ρ h Hρ Hh.
    destruct (rel_type_inversion_simple_at HR Hi _ _ Hρ) as (c' & c0 & Ec' & Ec0 & Hc).
    exists c', c0; split; [ exact Ec' | split; [| exact Hc ] ].
    destruct U as [Δu Du]; inversion Ec0; subst.
    match goal with Hcl : ⟦ Δu ⊢ Du ⟧ᶜ _ ⍮ _ ⍮ ρ ↘ ?h0 |- _ =>
      assert (h0 = h) as -> by (eapply functional_eval_modexp; [ apply eval_me_lit_iff; exact Hcl | exact Hh ]) end.
    assumption.
  - (** [LevelSort], substituted or not *)
    exists 0; intros ρ h _ _; exists LevelSortᵈ, LevelSortᵈ; repeat split; [ constructor | constructor |].
    eexists; apply per_univ_elem_level_sort_univ; exact I.
Qed.

(** ζ for a module [let]: [σ,,ₘ⌜U[σ]⌝] glues with [ρ ↦ᵐ ⟦⌜U⌝⟧ρ] into
    [Γ ▹ₘ U], the tie being the unit's closure related to itself. *)
Lemma glu_rel_exp_let_mod : forall {Γ U C S B},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    Γ ▹ₘ U ⊢ C : S ->
    type_sort S ->
    module_body_sort S ->
    Γ ▹ₘ U ⊢ B : C ->
    Γ ▹ₘ U ⊩ B : C ->
    Γ ⊩ C[Id ,,ₘ me_lit U] : S ->
    Γ ⊩ ℓₘ U in B : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HCs HS HSm HBt HB HW.
  assert (HCt : Γ ▹ₘ U ⊢ᵗ C) by (econstructor; eassumption).
  pose proof HB as [SbU HΓU k HBi].
  inversion HΓU as [| | | ? ? TSb ? HΓ _ HSbU |]; subst.
  destruct (glu_ctx_env_per_ctx_env HΓ) as [R HR].
  destruct (let_mod_typ_value HU HCt HR) as [i HCv].
  assert (HSk : exists κ, sort_kind S κ) by (destruct HS; eexists; constructor).
  destruct HSk as [κW HSk].
  destruct (glu_rel_exp_sort_typ HW HSk) as (SbW & kW & HSbW & _ & HWg).
  assert (EW : TSb <∙> SbW) by (eapply functional_glu_ctx_env; eassumption).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := kW); [ exact HΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HΓ _ _ _ Hσ) as Hσs.
  pose proof (glu_ctx_env_per_env HΓ HR Hσ) as Hρ.
  (* the unit's closure, related to itself *)
  assert (HUl : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U) by (apply wf_me_lit; exact HU).
  destruct (rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HUl) HR _ _ Hρ)
    as (h & h' & Hh & Hh' & Hhh).
  pose proof (functional_eval_modexp _ _ _ _ Hh' Hh) as ->.
  assert (Hσ' : Δ ⊢ˢ σ ,,ₘ me_lit U[σ]ᵘ ® ρ ↦ᵐ h ⦂ U ∈ SbU).
  { apply HSbU; econstructor.
    - apply wf_sub_extend_mod; [ exact Hσs | exact HU | eapply sub_preserves_unit; eassumption ].
    - exists h; split; [ exact Hh | exact Hhh ].
    - eexists; reflexivity.
    - split; [ apply mod_entry_readable | cbn; exact (gunit_scoped_free_bound _ _ (wf_unit_eq_scoped_left _ _ _ _ _ HU)) ].
    - exact Hσ. }
  destruct (HBi _ _ _ Hσ') as [c b Pc Elc Hc Hb Hgluc HBσ].
  destruct (HCv _ _ Hρ Hh) as (c' & c'' & Hc' & Hc'' & Hcc).
  functional_eval_rewrite_clear.
  (** The witness: the type glued at its value *)
  destruct (HWg _ _ _ (proj1 (EW _ _ _) Hσ)) as [c0 Pw Elw Ec0 Hglu'' HWσ].
  assert (c0 = c') by (eapply functional_eval_exp; eassumption); subst c0; clear Ec0.
  destruct Hcc as [Rc Hcc].
  assert (Hζ0 : Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U]) by (eapply wf_exp_eq_let_mod_zeta; eassumption).
  assert (Hζ : Δ ⊢ (ℓₘ U in B)[σ] ≈ B[Id ,,ₘ me_lit U][σ] : C[Id ,,ₘ me_lit U][σ])
    by (eapply sub_preserves_exp_eq; [ exact Hζ0 | eassumption ]).
  rewrite (exp_sub_extend_mod_sub B), (exp_sub_extend_mod_sub C) in Hζ.
  change ((me_lit U)[σ]ᵐ) with (me_lit U[σ]ᵘ) in *.
  assert (HN0 : Δ ⊢ (ℓₘ U in B)[σ] : C[Id ,,ₘ me_lit U][σ] ® b ∈ Elc).
  { rewrite (exp_sub_extend_mod_sub C).
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hgluc | exact HBσ | apply wf_exp_eq_sym; exact Hζ ]. }
  assert (Hcc' : Dom c ≈ c' ∈ per_univ i) by (eexists; symmetry; exact Hcc).
  pose proof (glu_univ_elem_exp_conv Hcc' Hgluc Hglu'' HN0 HWσ) as HN.
  (** The term's value at the kind of its type *)
  assert (Hevb : evaluated_kind (domain_kind c') -> ⟦ ℓₘ U in B ⟧ ρ ↘ b).
  { intros Hev.
    rewrite (per_univ_elem_kind _ _ _ _ Hcc) in Hev.
    destruct (domain_kind c); cbn in Hb; try solve [ inversion Hev ];
      destruct U as [Δu Du]; apply eval_me_lit_iff in Hh; eapply eval_exp_let_mod; eassumption. }
  destruct (glu_term_value_intro Hglu'' HΓ Hσ (presup_exp_eq_left Hζ0) Hevb HN) as (m' & Hm' & HMg).
  econstructor; [ exact Hc' | exact Hm' | exact Hglu'' | exact HMg ].
Qed.

(** The value of a type under a [let] with a module part: the value of
    the type instantiated by the definiens and the unit's literal is
    related to the value of the type at the environment extended by both
    ([rel_exp_under_ctx_let_dm_zeta] at the type, a term of its sort). *)
Lemma let_dm_typ_value : forall {Γ A M U C S R} {i : nat},
    Γ ⊢ A : Typeω@i ->
    Γ ⊢ M : A ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    Γ ▸ₘ A ≔ M ‖ U ⊢ C : S ->
    type_sort S ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    exists j : nat, forall ρ a m h,
      Dom ρ ≈ ρ ∈ R ->
      ⟦ A ⟧ ρ ↘ a ->
      ⟦ M ⟧ ρ ↘ m ->
      ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
      exists c c', ⟦ C[Id ,,ᵈ M ‖ me_lit U] ⟧ ρ ↘ c /\ ⟦ C ⟧ ρ ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ U ↘ c' /\
              Dom c ≈ c' ∈ per_univ j.
Proof.
  intros * HA HM HU HC HS HR.
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAc.
  pose proof (completeness_fundamental_exp _ _ _ HM) as HMc.
  pose proof (proj1 (proj2 completeness_fundamental_modules) _ _ _ HU) as HUc.
  pose proof (completeness_fundamental_exp _ _ _ HC) as HCc.
  assert (HMs : exp_scoped (List.length Γ) M) by exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HM))).
  pose proof (wf_unit_eq_scoped_left _ _ _ _ _ HU) as HUs.
  pose proof (rel_exp_under_ctx_let_dm_zeta HAc HMc HUc HMs HUs HCc) as Hz.
  assert (HSs : S[Id ,,ᵈ M ‖ me_lit U] = S) by (destruct HS; reflexivity).
  rewrite HSs in Hz.
  destruct (rel_type_of_sort HS Hz) as [j Hj].
  exists j; intros ρ a m h Hρ Ha Hm Hh.
  destruct (rel_type_inversion_simple_at HR Hj _ _ Hρ) as (c1 & c & Ec1 & Ec & Hc).
  exists c, c1; split; [ exact Ec | split; [| symmetry; exact Hc ] ].
  inversion Ec1; subst; functional_eval_rewrite_clear; assumption.
Qed.

(** ζ for a [let] with a module part: [σ ,,ᵈ M[σ] ‖ ⌜U[σ]⌝] glues with [ρ]
    extended by [M]'s value and the unit's closure into the context, as a
    definition's head and as a slot's. *)
Lemma glu_rel_exp_let_dm : forall {Γ A M E C S B} {i : nat},
    Γ ⊩ A : Typeω@i ->
    Γ ⊩ M : A ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊢ C : S ->
    type_sort S ->
    module_body_sort S ->
    Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊩ B : C ->
    Γ ⊩ C[Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))] : S ->
    Γ ⊩ ℓᵈ A ≔ M ‖ (gu_mk nil (md_alias E)) in B : C[Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))].
Proof.
  intros * HA HM HU HCt HS HSm HB HW.
  set (U := gu_mk nil (md_alias E)) in *.
  assert (HSk : exists κ, sort_kind S κ) by (destruct HS; eexists; constructor).
  destruct HSk as [κW HSk].
  destruct (glu_rel_exp_sort_typ HW HSk) as (SbW & kW & HSbW & _ & HWg).
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  pose proof (glu_rel_exp_to_wf_exp HB) as HBt.
  destruct (presup_ctx_glu_rel_exp HA) as [SbΓ HSbΓ].
  destruct (presup_ctx_glu_rel_exp HB) as [SbD HSbD].
  destruct (glu_ctx_env_cons_dm_clean_inversion HSbΓ HSbD) as (i' & HAi & _ & _ & _ & HMg & ESb).
  destruct (glu_rel_exp_clean_inversion1 HSbD HB) as [k HBk].
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [R HR].
  destruct (let_dm_typ_value HAt HMt HU HCt HS HR) as [j HCv].
  assert (Hζ0 : Γ ⊢ ℓᵈ A ≔ M ‖ U in B ≈ B[Id ,,ᵈ M ‖ me_lit U] : C[Id ,,ᵈ M ‖ me_lit U])
    by (eapply wf_exp_eq_let_dm_zeta; [ exact HAt | exact HMt | exact HU | exact HCt | exact HS | exact HSm | exact HBt ]).
  pose proof (wf_unit_eq_scoped_left _ _ _ _ _ HU) as HUs.
  assert (HUl : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U) by (apply wf_me_lit; exact HU).
  assert (EW : SbΓ <∙> SbW) by (eapply functional_glu_ctx_env; eassumption).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := kW); [ exact HSbΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
  pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
  destruct (HMg _ _ _ Hσ) as [a m P El Ea Hm Hglu HMσ].
  (** The type is of a universe, so the definiens' value is evaluated *)
  assert (Hka : domain_kind a = ak_relevant).
  { assert (HAσ : Δ ⊢ A[σ] : abs_kind_sort ak_relevant Typeω@i') by (cbn; exact (sub_preserves_exp _ _ _ _ _ _ _ HAi Hσt)).
    exact (proj1 (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu (glu_univ_elem_trm_typ _ _ _ _ Hglu _ _ _ _ HMσ) HAσ)). }
  rewrite Hka in Hm; cbn in Hm.
  destruct (rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HUl) HR _ _ Hρ)
    as (h & h' & Hh & Hh' & Hhh).
  pose proof (functional_eval_modexp _ _ _ _ Hh' Hh) as ->.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Ra HRa].
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HMσ HRa) as Hmm.
  pose proof (glu_univ_elem_trm_escape _ _ _ _ Hglu _ _ _ _ HMσ) as HMσt.
  assert (Hc : Δ ⊢ˢ σ ,,ᵈ M[σ] ‖ me_lit U[σ]ᵘ ® ρ ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ U ∈ SbD).
  { apply ESb; econstructor; [ | exact Ea | exact Hglu | | | | | | ].
    - eapply wf_sub_extend_dm; [ exact Hσt | exact HAi | exact HMt | exact HU | exact HMσt | apply wf_exp_eq_refl; exact HMσt
                               | eapply sub_preserves_unit; eassumption ].
    - rewrite exp_sub_shift_extend; exact HMσ.
    - exists m; split; [ exact Hm | exact (per_head_of Ea Ea HRa Hmm) ].
    - exists h; split; [ exact Hh | exact Hhh ].
    - (** The stored type is the type's value *)
      eexists; split; [ reflexivity |].
      refine (mk_glu_stored_type _ _ _ _ _ i' a P El ltac:(constructor) Hglu _).
      rewrite exp_sub_shift_extend; exact HMσ.
    - split; [| cbn; exact (gunit_scoped_free_bound _ _ HUs) ].
      intros s; destruct (proj1 (entry_readable_of_elem HRa Hmm) s) as [b Hb].
      inversion Hb; subst; eexists; eapply read_entry_dm; eassumption.
    - first [ exact Hσ | cbn; exact Hσ | eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | exact Hσ | mauto 3 ] ]. }
  destruct (HBk _ _ _ Hc) as [c' b Pc Elc Ec' Hb Hgc HBσ].
  destruct (HCv _ _ _ _ Hρ Ea Hm Hh) as (c & c'' & Ec & Ec'' & Hcc).
  functional_eval_rewrite_clear.
  (** The witness: the type glued at its value *)
  destruct (HWg _ _ _ (proj1 (EW _ _ _) Hσ)) as [c0 Pw Elw Ec0 Hglu'' HWσ].
  assert (c0 = c) by (eapply functional_eval_exp; eassumption); subst c0; clear Ec0.
  destruct Hcc as [Rc Hcc].
  assert (Hζ : Δ ⊢ (ℓᵈ A ≔ M ‖ U in B)[σ] ≈ B[Id ,,ᵈ M ‖ me_lit U][σ] : C[Id ,,ᵈ M ‖ me_lit U][σ])
    by (eapply sub_preserves_exp_eq; [ exact Hζ0 | exact Hσt ]).
  rewrite (exp_sub_extend_dm_sub B), (exp_sub_extend_dm_sub C) in Hζ.
  change ((me_lit U)[σ]ᵐ) with (me_lit U[σ]ᵘ) in *.
  assert (HN0 : Δ ⊢ (ℓᵈ A ≔ M ‖ U in B)[σ] : C[Id ,,ᵈ M ‖ me_lit U][σ] ® b ∈ Elc).
  { rewrite (exp_sub_extend_dm_sub C).
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hgc | exact HBσ | apply wf_exp_eq_sym; exact Hζ ]. }
  assert (Hc'c : Dom c' ≈ c ∈ per_univ j) by (eexists; symmetry; exact Hcc).
  pose proof (glu_univ_elem_exp_conv Hc'c Hgc Hglu'' HN0 HWσ) as HN.
  (** The term's value at the kind of its type *)
  assert (Hevb : evaluated_kind (domain_kind c) -> ⟦ ℓᵈ A ≔ M ‖ U in B ⟧ ρ ↘ b).
  { intros Hev.
    rewrite (per_univ_elem_kind _ _ _ _ Hcc) in Hev.
    destruct (domain_kind c'); cbn in Hb; try solve [ inversion Hev ];
      eapply eval_exp_let_dm; eassumption. }
  destruct (glu_term_value_intro Hglu'' HSbΓ Hσ (presup_exp_eq_left Hζ0) Hevb HN) as (m' & Hm' & HMg').
  econstructor; [ exact Ec | exact Hm' | exact Hglu'' | exact HMg' ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_ctx_tail glu_rel_ctx_extend_mod glu_rel_exp_let_mod : mctt.

(** ** The Rules

    A module slot and a module [let] read their syntactic premises at the
    target, moved along the embedding. *)

#[local] Generalizable All Variables.

Lemma glu_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵘ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ C : Srt ->
     type_sort Srt ->
     module_body_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof.
  glu_inst_intro.
  match goal with HU : Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U |- _ => pose proof (Hwu _ _ _ HU) as HU2 end.
  assert (HUτ : Θ2 ⍮ Ξ2 ⍮ Γ' ⊢ᵘ U[τ]ᵘ ≈ U[τ]ᵘ) by (eapply sub_preserves_unit; [ exact HU2 | apply Hτ ]).
  assert (Hq : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) (Γ' ▹ₘ U[τ]ᵘ) (q τ) (Γ ▹ₘ U))
    by (eapply glu_rel_sub_inst_q_mod; eassumption).
  (** The type's instance at the unit's literal, the witness *)
  assert (Hext : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) Γ' (τ ,,ₘ me_lit U[τ]ᵘ) (Γ ▹ₘ U))
    by (eapply glu_rel_sub_inst_extend_mod; eassumption).
  rewrite exp_sub_extend_mod_sub, <- exp_sub_q_extend_mod.
  match goal with HS : type_sort Srt |- _ => rename HS into HSt end.
  eapply (glu_rel_exp_let_mod (C := C[q τ]) (S := Srt)); try glu_inst_premise.
  - rewrite <- (type_sort_sub Srt (q τ) HSt).
    eapply sub_preserves_exp; [ apply Hwe; eassumption | apply Hq ].
  - eapply sub_preserves_exp; [ apply Hwe; eassumption | apply Hq ].
  - rewrite exp_sub_q_extend_mod; glu_inst.
Qed.

Lemma glu_let_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵘ gu_mk nil (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊢ C : Srt ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊩ C : Srt ->
     type_sort Srt ->
     module_body_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊩ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓᵈ A ≔ M ‖ (gu_mk nil (md_alias E)) in B : C[Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))] ).
Proof.
  glu_inst_intro.
  match goal with HU : Θ ⍮ Ξ ⍮ Γ ⊢ᵘ _ ≈ _ |- _ => pose proof (Hwu _ _ _ HU) as HU2 end.
  assert (HUτ : Θ2 ⍮ Ξ2 ⍮ Γ' ⊢ᵘ (gu_mk nil (md_alias E))[τ]ᵘ ≈ (gu_mk nil (md_alias E))[τ]ᵘ)
    by (eapply sub_preserves_unit; [ exact HU2 | apply Hτ ]).
  assert (HAt : Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A : Typeω@i) by (eapply (@glu_rel_exp_under_sub_wf (gc_mk Θ2 Ξ2)); eassumption).
  assert (Hq : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) (Γ' ▸ₘ A[τ] ≔ M[τ] ‖ gu_mk nil (md_alias E[τ]ᵐ)) (q τ)
                 (Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)))
    by (eapply glu_rel_sub_inst_q_dm; [ exact Hτ | eassumption | eassumption | exact HU2 | exact HUτ | eassumption ]).
  (** The type's instance at the definiens and the unit's literal, the
      witness *)
  assert (Hext : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) Γ' (τ ,,ᵈ M[τ] ‖ me_lit (gu_mk nil (md_alias E))[τ]ᵘ)
                   (Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)))
    by (eapply glu_rel_sub_inst_extend_dm; [ exact Hτ | exact HAt | eassumption | exact HU2 | exact HUτ | eassumption ]).
  rewrite exp_sub_extend_dm_sub, <- exp_sub_q_extend_dm.
  match goal with HS : type_sort Srt |- _ => rename HS into HSt end.
  eapply (glu_rel_exp_let_dm (A := A[τ]) (M := M[τ]) (E := E[τ]ᵐ) (C := C[q τ]) (S := Srt)); try glu_inst_premise.
  - rewrite <- (type_sort_sub Srt (q τ) HSt).
    eapply sub_preserves_exp; [ apply Hwe; eassumption | apply Hq ].
  - rewrite exp_sub_q_extend_dm; glu_inst.
Qed.

Lemma glu_exp_eq_let_dm_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_let_dm_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_let_mod_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_let_mod_zeta :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ C : Srt ->
     type_sort Srt ->
     module_body_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ B : C ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
