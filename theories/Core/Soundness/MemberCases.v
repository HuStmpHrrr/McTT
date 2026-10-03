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
From Mctt.Core.Completeness Require Import FundamentalTheorem LetCases UnitCases.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  TermStructureCases.
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
  pose proof HN as [Sb [HΓ [i HNi]]].
  exists Sb; split; [ exact HΓ |]; exists i.
  intros Δ σ ρ Hσ.
  destruct (HNi _ _ _ Hσ) as [a n P El Ha Hn Hglu HNσ].
  assert (Hσs : Δ ⊢s σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ Heq) as Hc.
  destruct (glu_ctx_env_per_ctx_env HΓ) as [R HR].
  pose proof (glu_ctx_env_per_env HΓ HR Hσ) as Hρ.
  destruct (rel_exp_under_ctx_simple_full_at HR Hc) as [j Hj].
  destruct (Hj _ _ Hρ) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m & n' & Hm & Hn' & Hmn).
  functional_eval_rewrite_clear.
  econstructor; [ exact Ha | exact Hm | exact Hglu |].
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Ri HRi].
  pose proof (per_univ_elem_cumu_max_left _ j _ _ _ HRi) as HRi'.
  pose proof (per_univ_elem_cumu_max_right i _ _ _ _ HR1) as HR1'.
  assert (E : Ri <~> R1) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRi' HR1').
  assert (HP1 : PER R1) by (eapply per_elem_PER; exact HR1).
  eapply (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hglu _ HRi); [| apply E; symmetry; exact Hmn ].
  eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hglu | exact HNσ |].
  apply wf_exp_eq_sym; eapply sub_preserves_exp_eq; eassumption.
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

(** δ for a member. *)
Lemma glu_rel_exp_mem : forall {Γ H x A i M},
    me_noargs H ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H (x :: nil) mk_term A ->
    Γ ⊢ A : Type@i ->
    member_unfold gc_deps gc_stack Γ H x = Some M ->
    Γ ⊢ M : A ->
    Γ ⊩ M : A ->
    Γ ⊩ a_mem H x : A.
Proof.
  intros * Hn HH Hm HA HM HMt HMg.
  eapply glu_rel_exp_of_eq; [ exact HMg | eapply wf_exp_eq_mem_delta; eassumption ].
Qed.

(** A member of an applied module is its root's member applied. *)
Lemma glu_rel_exp_mem_app : forall {Γ H R args pre i A x},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    modexp_spine H = (R, args, pre) ->
    args <> nil ->
    Γ ⊢ A : Type@i ->
    Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A ->
    Γ ⊩ apps (member_ref R (pre ++ x :: nil)) args : A ->
    Γ ⊩ a_mem H x : A.
Proof.
  intros * HH Hs Hargs HA Ht Hg.
  eapply glu_rel_exp_of_eq; [ exact Hg | eapply wf_exp_eq_mem_app; eassumption ].
Qed.

(** ζ for a module [let]: [σ,,ₘ⌜U[σ]⌝] glues with [ρ ↦ᵐ ⟦⌜U⌝⟧ρ] into
    [Γ ▹ₘ U], the tie being the unit's closure related to itself. *)
Lemma glu_rel_exp_let_mod : forall {Γ U C B},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    Γ ▹ₘ U ⊢ B : C ->
    Γ ▹ₘ U ⊩ B : C ->
    Γ ⊩ ℓₘ U in B : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HBt HB.
  destruct (presup_typ_glu_rel_exp HB) as [k HCg].
  pose proof (glu_rel_exp_to_wf_exp HCg) as HC.
  pose proof (proj1 (proj2 completeness_fundamental_modules) _ _ _ HU) as HUc.
  pose proof (completeness_fundamental_exp _ _ _ HC) as HCc.
  pose proof HB as [SbU [HΓU _]].
  pose proof (glu_rel_exp_clean_inversion2 HΓU HCg HB) as HBi.
  inversion HΓU as [| | | ? ? TSb ? HΓ _ HSbU]; subst.
  destruct (glu_ctx_env_per_ctx_env HΓ) as [R HR].
  exists TSb; split; [ exact HΓ |]; exists k.
  intros Δ σ ρ Hσ.
  assert (Hσs : Δ ⊢s σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  pose proof (glu_ctx_env_per_env HΓ HR Hσ) as Hρ.
  assert (Hσ' : Δ ⊢s σ ,,ₘ me_lit U[σ]ᵘ ® ρ ↦ᵐ dm_local ρ U nil ∈ SbU).
  { apply HSbU; econstructor.
    - apply wf_sub_extend_mod; [ exact Hσs | exact HU | eapply sub_preserves_unit; eassumption ].
    - exact (unit_chain_at (proj1 HUc) HR _ _ Hρ).
    - exact Hσ. }
  destruct (HBi _ _ _ Hσ') as [c b Pc Elc Hc Hb Hgluc HBσ].
  destruct (per_univ_of_instance_mod HR HUc HCc _ Hρ) as (c' & c'' & Hc' & Hc'' & _ & Hcc).
  functional_eval_rewrite_clear.
  assert (Hgluc' : DG c' ∈ glu_univ_elem k ↘ Pc ↘ Elc)
    by (eapply glu_univ_elem_resp_per_univ; [ symmetry |]; eassumption).
  econstructor; [ exact Hc' | eapply eval_exp_let_mod; exact Hb | exact Hgluc' |].
  assert (Hζ : Δ ⊢ (ℓₘ U in B)[σ] ≈ B[Id ,,ₘ me_lit U][σ] : C[Id ,,ₘ me_lit U][σ])
    by (eapply sub_preserves_exp_eq; [ eapply wf_exp_eq_let_mod_zeta; eassumption | eassumption ]).
  rewrite (exp_sub_extend_mod_sub B), (exp_sub_extend_mod_sub C) in Hζ.
  rewrite (exp_sub_extend_mod_sub C).
  change ((me_lit U)[σ]ᵐ) with (me_lit U[σ]ᵘ) in *.
  eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hgluc' | | apply wf_exp_eq_sym; exact Hζ ].
  eapply glu_univ_elem_exp_conv; [ symmetry; exact Hcc | exact Hgluc | exact Hgluc' | exact HBσ |].
  eapply glu_univ_elem_trm_typ; eassumption.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_ctx_tail glu_rel_ctx_extend_mod glu_rel_exp_mem glu_rel_exp_mem_app glu_rel_exp_let_mod : mctt.
