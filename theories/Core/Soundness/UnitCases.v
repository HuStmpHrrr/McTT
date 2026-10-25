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
  destruct (Hj _ _ Hρ) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m & n' & Hm & Hn' & Hmn).
  functional_eval_rewrite_clear.
  econstructor; [ exact Ha | exact Hm | exact Hglu |].
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Ri HRi].
  (** The two element PERs are of the same value at two indices; irrelevance
      identifies them without lifting either. *)
  pose proof HRi as HRi'.
  pose proof HR1 as HR1'.
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

(** A definition with a module part glues when its term part does as a
    definition and its unit is well formed. *)
Lemma glu_rel_ctx_extend_dm : forall {Γ A M U} {i : nat},
    ⊩ Γ ->
    Γ ⊩ A : Typeω@i ->
    Γ ⊩ M : A ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    ⊩ Γ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * [Sb] HA HM HU.
  assert (Γ ⊢ A : Typeω@i) by mauto 3.
  assert (Γ ⊢ M : A) by mauto 3.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HA.
  eexists.
  econstructor; mauto 3; reflexivity.
Qed.

(** δ for a member: it glues as its δ-reduct, which glues by the premise of
    [wf_mem] on it. *)
Lemma glu_rel_exp_mem : forall {Γ H x R A M},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> ds_ty R = Some A -> ds_red R = Some M ->
    Γ ⊩ M : A ->
    Γ ⊩ a_mem H x : A.
Proof.
  intros * HH Hm Ht Hr HMg.
  eapply glu_rel_exp_of_eq; [ exact HMg | eapply wf_exp_eq_mem_delta; eassumption ].
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
  pose proof HB as [SbU HΓU _ _].
  pose proof (glu_rel_exp_clean_inversion2 HΓU HCg HB) as HBi.
  inversion HΓU as [| | | ? ? TSb ? HΓ _ HSbU |]; subst.
  destruct (glu_ctx_env_per_ctx_env HΓ) as [R HR].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := k); [ exact HΓ |].
  intros Δ σ ρ Hσ.
  assert (Hσs : Δ ⊢ˢ σ : Γ) by (eapply glu_ctx_env_sub_escape; eassumption).
  pose proof (glu_ctx_env_per_env HΓ HR Hσ) as Hρ.
  (* the unit's closure, related to itself *)
  assert (HUl : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U) by (apply wf_me_lit; exact HU).
  destruct (rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HUl) HR _ _ Hρ)
    as (h & h' & Hh & Hh' & Hhh).
  pose proof (functional_eval_modexp _ _ _ _ Hh' Hh) as ->.
  assert (Hσ' : Δ ⊢ˢ σ ,,ₘ me_lit U[σ]ᵘ ® ρ ↦ᵐ h ∈ SbU).
  { apply HSbU; econstructor.
    - apply wf_sub_extend_mod; [ exact Hσs | exact HU | eapply sub_preserves_unit; eassumption ].
    - exists h; split; [ exact Hh | exact Hhh ].
    - exact Hσ. }
  destruct (HBi _ _ _ Hσ') as [c b Pc Elc Hc Hb Hgluc HBσ].
  destruct (per_univ_of_instance_mod HR HUc HCc _ _ Hρ Hh) as (c' & c'' & Hc' & Hc'' & _ & Hcc).
  functional_eval_rewrite_clear.
  assert (Hgluc' : DG c' ∈ glu_univ_elem k ↘ Pc ↘ Elc)
    by (eapply glu_univ_elem_resp_per_univ; [ symmetry |]; eassumption).
  econstructor; [ exact Hc'
                | clear - Hh Hb; destruct U as [Δu Du]; apply eval_me_lit_iff in Hh; eapply eval_exp_let_mod; [ exact Hh | exact Hb ]
                | exact Hgluc' |].
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
Proof. glu_intro; glu_emb_wf; eapply (@glu_rel_ctx_extend_mod (gc_mk _ _)); [ eassumption | apply Hwu; eassumption ]. Qed.

(** A definition with a module part glues when its term part does and its
    unit is well formed. *)
Lemma glu_ctx_extend_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ).
Proof.
  glu_intro; glu_emb_wf.
  eapply (@glu_rel_ctx_extend_dm (gc_mk _ _)); [ eapply presup_ctx_glu_rel_exp; eassumption | eassumption | eassumption | apply Hwu; eassumption ].
Qed.

Lemma glu_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof.
  glu_intro; glu_emb_wf.
  eapply (@glu_rel_exp_let_mod (gc_mk _ _)); [ apply Hwu; eassumption | apply Hwe; eassumption | eassumption ].
Qed.

Lemma glu_exp_eq_let_mod_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_let_mod_zeta :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ B : C ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
