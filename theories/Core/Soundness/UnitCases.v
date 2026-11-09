(** * Module Slots, Module [let]s and Members in the Gluing Model

    Module values are not glued.  A module slot glues by its syntactic typing
    and by the tie of its value to the closure of its unit
    ([cons_mod_glu_sub_pred]).  A member is glued through its δ-reduct, a
    member of an applied module through the application it commutes with,
    and a module [let] through its body: in each case the term is equal to
    one that glues, syntactically and in the PER model, and gluing respects
    both ([glu_univ_elem_trm_resp_exp_eq], [glu_univ_elem_trm_resp_per_elem]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LetCases UnitCases UniverseCases.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  VariableCases.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A term equal to one that glues glues. *)
Lemma glu_rel_exp_of_eq : forall {Γ M N A},
    Γ ⊩ N : A ->
    Γ ⊢ M ≈ N : A ->
    Γ ⊩ M : A.
Proof.
  intros * HN Heq.
  pose proof HN as [Sb HΓ i HNi].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HΓ |].
  intros Δ σ ρ Hσ.
  destruct (HNi _ _ _ Hσ) as [a n P El Ha Hn Hglu HNσ].
  assert (Hσs : Δ ⊢ˢ σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ Heq) as Hc.
  destruct (glu_ctx_env_per_ctx_env HΓ) as [R HR].
  pose proof (glu_ctx_env_per_env HΓ HR Hσ) as Hρ.
  destruct (rel_exp_under_ctx_simple_full_at HR Hc) as [j Hj].
  destruct (Hj _ _ Hρ) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & Hcase).
  functional_eval_rewrite_clear.
  assert (HMσ : Δ ⊢ M[σ] : A[σ] ® n ∈ El).
  { eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hglu | exact HNσ |].
    apply wf_exp_eq_sym; eapply sub_preserves_exp_eq; eassumption. }
  pose proof (presup_exp_eq_left Heq) as HMt.
  (** The term's value: at a proposition the proof kept, at an evaluated
      kind the value related to [N]'s ([glu_term_value_intro]) *)
  destruct Hcase as [Hk | (m & n' & Hm & Hn' & Hmn)].
  - destruct (glu_term_value_intro (m := n) Hglu HMt HR Hρ ltac:(rewrite Hk; intros Hev; inversion Hev) HMσ)
      as (m' & Hm' & HMg).
    econstructor; [ exact Ha | exact Hm' | exact Hglu | exact HMg ].
  - destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Ri HRi].
    (** The two element PERs are of the same value at two indices;
        irrelevance identifies them without lifting either. *)
    pose proof HRi as HRi'.
    pose proof HR1 as HR1'.
    assert (E : Ri <~> R1) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRi' HR1').
    assert (HP1 : PER R1) by (eapply per_elem_PER; exact HR1).
    assert (Hnn : n' = n \/ domain_kind a = ak_propositional).
    { destruct (domain_kind a) eqn:Hka; cbn in Hn; [ left | right; reflexivity | left ];
        eapply functional_eval_exp; eassumption. }
    destruct Hnn as [-> | Hk].
    + assert (HMg : Δ ⊢ M[σ] : A[σ] ® m ∈ El)
        by (eapply (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hglu _ HRi); [ exact HMσ | apply E; symmetry; exact Hmn ]).
      destruct (glu_term_value_intro (m := m) Hglu HMt HR Hρ (fun _ => Hm) HMg) as (m' & Hm' & HMg').
      econstructor; [ exact Ha | exact Hm' | exact Hglu | exact HMg' ].
    + destruct (glu_term_value_intro (m := n) Hglu HMt HR Hρ ltac:(rewrite Hk; intros Hev; inversion Hev) HMσ)
        as (m' & Hm' & HMg).
      econstructor; [ exact Ha | exact Hm' | exact Hglu | exact HMg ].
Qed.

(** The tail of a glued context glues. *)
Lemma glu_rel_ctx_tail : forall {e Γ}, ⊩ e :: Γ -> ⊩ Γ.
Proof. intros * [Sb H]; inversion H; subst; eexists; eassumption. Qed.

Lemma glu_rel_ctx_extend_mod : forall {Γ U},
    ⊩ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    ⊩ Γ ▹ₘ U.
Proof.
  intros * [Sb HΓ] HU.
  exists (cons_mod_glu_sub_pred Γ U Sb).
  econstructor; [ exact HΓ | exact HU | reflexivity ].
Qed.

(** A definition with a module part glues when its term part does as a
    definition and its unit is well formed. *)
Lemma glu_rel_ctx_extend_dm : forall {Γ A M E} {i : nat},
    ⊩ Γ ->
    Γ ⊩ A : Typeω@i ->
    Γ ⊩ M : A ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    ⊩ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E).
Proof.
  intros * _ HA HM HU.
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt; pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  destruct (glu_rel_exp_sort_typ (κ := ak_relevant) HA ltac:(constructor)) as (Sb & j & HSb & HAt' & HAg).
  pose proof (glu_rel_exp_at_typ_index HSb HAg HM) as HMg.
  eexists; econstructor;
    [ exact HSb | exact HAt' | exact HMt | eapply wf_ctx_extend_dm; eassumption | exact HAg | exact HMg | reflexivity ].
Qed.

(** δ for a member: it glues as its δ-reduct, which glues by the premise of
    [wf_mem] on it. *)
Lemma glu_rel_exp_mem : forall {Γ H x R A M},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A -> mdesc_reduct R = Some M ->
    Γ ⊩ M : A ->
    Γ ⊩ a_mem H x : A.
Proof.
  intros * HH Hm Ht Hr HMg.
  eapply glu_rel_exp_of_eq; [ exact HMg | eapply wf_exp_eq_mem_delta; eassumption ].
Qed.

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
    Γ ⊩ ℓₘ U in B : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HCs HS HSm HBt HB.
  assert (HCt : Γ ▹ₘ U ⊢ᵗ C) by (econstructor; eassumption).
  pose proof HB as [SbU HΓU k HBi].
  inversion HΓU as [| | | ? ? TSb ? HΓ _ HSbU |]; subst.
  destruct (glu_ctx_env_per_ctx_env HΓ) as [R HR].
  destruct (let_mod_typ_value HU HCt HR) as [i HCv].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := max k i); [ exact HΓ |].
  intros Δ σ ρ Hσ.
  assert (Hσs : Δ ⊢ˢ σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
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
  (** Both at the larger index *)
  destruct (glu_univ_elem_cumu_max_left (j := i) Hgluc) as (P' & El' & Hglu').
  assert (HBσ' : Δ ⊢ B[σ ,,ₘ me_lit U[σ]ᵘ] : C[σ ,,ₘ me_lit U[σ]ᵘ] ® b ∈ El')
    by (eapply glu_univ_elem_exp_cumu_max_left; [ exact Hgluc | exact Hglu' | exact HBσ ]).
  destruct Hcc as [Rc Hcc].
  assert (Hglu'' : DG c' ∈ glu_univ_elem (max k i) ↘ P' ↘ El').
  { eapply glu_univ_elem_resp_per_univ; [| exact Hglu' ].
    eexists; symmetry; eapply per_univ_elem_cumu_max_right; exact Hcc. }
  assert (Hζ0 : Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U]) by (eapply wf_exp_eq_let_mod_zeta; eassumption).
  assert (Hζ : Δ ⊢ (ℓₘ U in B)[σ] ≈ B[Id ,,ₘ me_lit U][σ] : C[Id ,,ₘ me_lit U][σ])
    by (eapply sub_preserves_exp_eq; [ exact Hζ0 | eassumption ]).
  rewrite (exp_sub_extend_mod_sub B), (exp_sub_extend_mod_sub C) in Hζ.
  change ((me_lit U)[σ]ᵐ) with (me_lit U[σ]ᵘ) in *.
  assert (HN : Δ ⊢ (ℓₘ U in B)[σ] : C[Id ,,ₘ me_lit U][σ] ® b ∈ El').
  { rewrite (exp_sub_extend_mod_sub C).
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hglu'' | exact HBσ' | apply wf_exp_eq_sym; exact Hζ ]. }
  (** The term's value at the kind of its type *)
  assert (Hevb : evaluated_kind (domain_kind c') -> ⟦ ℓₘ U in B ⟧ ρ ↘ b).
  { intros Hev.
    rewrite (per_univ_elem_kind _ _ _ _ Hcc) in Hev.
    destruct (domain_kind c); cbn in Hb; try solve [ inversion Hev ];
      destruct U as [Δu Du]; apply eval_me_lit_iff in Hh; eapply eval_exp_let_mod; eassumption. }
  destruct (glu_term_value_intro Hglu'' (presup_exp_eq_left Hζ0) HR Hρ Hevb HN) as (m' & Hm' & HMg).
  econstructor; [ exact Hc' | exact Hm' | exact Hglu'' | exact HMg ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_ctx_tail glu_rel_ctx_extend_mod glu_rel_exp_mem glu_rel_exp_let_mod : mctt.

(** ** The Rules

    A module slot and a module [let] read their syntactic premises at the
    target, moved along the embedding. *)

#[local] Generalizable All Variables.

(** A slot glues when the context does and its unit is well formed. *)
Lemma glu_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ).
Proof. glu_intro; glu_gctx_embedding_wf; eapply (@glu_rel_ctx_extend_mod (gc_mk _ _)); [ eassumption | apply Hwu; eassumption ]. Qed.

(** A definition with a module part glues when its term part does and its
    unit is well formed. *)
Lemma glu_ctx_extend_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ).
Proof.
  glu_intro; glu_gctx_embedding_wf.
  eapply (@glu_rel_ctx_extend_dm (gc_mk _ _)); [ eapply presup_ctx_glu_rel_exp; eassumption | eassumption | eassumption | apply Hwu; eassumption ].
Qed.

Lemma glu_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ C : Srt ->
     type_sort Srt ->
     module_body_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof.
  glu_intro; glu_gctx_embedding_wf.
  eapply (@glu_rel_exp_let_mod (gc_mk _ _));
    [ apply Hwu; eassumption | apply Hwe; eassumption | eassumption | eassumption | apply Hwe; eassumption | eassumption ].
Qed.

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
