(** * Propositions and Proofs in the Gluing Model

    [Prop] is a type of the least small universe, glued by its clause.  A
    proposition ([⊤], [⊥], [Σₚ]) glues as a term of [Prop] by its value,
    glued as a proposition: by its readback, built from its parts'
    ([glu_rel_exp_of_prop]).  A proof glues by its typing alone, kept
    ([glu_rel_exp_proof]): the introductions and eliminations of [⊤] and
    [Σₚ] are proofs.  Ex falso into a proposition is a proof too; into a
    type of a universe it is a neutral of its type, glued by realisability
    at the proof of [⊥] kept ([realize_glu_elem_bot]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem PropCases UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LogicalRelation
  SubtypingCases
  UniverseCases
  VariableCases.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** [Prop] *)

(** [Prop] is a type of the least small universe, reading back as
    itself. *)
Lemma glu_rel_exp_prop_univ : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ Propₘ : Type@0.
Proof.
  intros * [Sb HSb].
  eapply (glu_rel_exp_of_univ (u := us (0, 0))); [ exact HSb |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSb _ _ _ Hσ) as Hσt.
  assert (⊢ Δ) by (gen_presups; assumption).
  split; [ cbn; apply wf_prop; assumption |].
  exists Propᵈ; split; [ constructor |].
  split; [ eexists; apply per_univ_elem_prop_univ |].
  split.
  - intros P El Hg.
    basic_invert_glu_univ_elem Hg; apply_predicate_equivalence.
    cbn; apply wf_exp_eq_refl; eapply wf_exp_subtyp'; [ apply wf_prop; assumption |].
    eapply wf_subtyp_small_large; [ assumption | apply wf_llit_ordinal; assumption ].
  - intros Δ' φ W Hφ HW.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    inversion HW; subst.
    eapply glu_nf_eq_proof_free; [ cbn; repeat constructor | cbn; apply wf_exp_eq_refl, wf_prop; assumption ].
Qed.

(** ** The Constant Propositions *)

Lemma glu_rel_exp_True : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ ⊤ : Propₘ.
Proof.
  intros * [Sb HSb].
  eapply glu_rel_exp_of_prop; [ exact HSb |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSb _ _ _ Hσ) as Hσt.
  assert (⊢ Δ) by (gen_presups; assumption).
  exists ⊤ᵈ; split; [ constructor | split; [ exact per_prop_True |] ].
  split; [ cbn; apply wf_True; assumption |].
  intros Δ' φ W Hφ HW.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  inversion HW; subst.
  eapply glu_nf_eq_proof_free; [ cbn; repeat constructor | cbn; apply wf_exp_eq_refl, wf_True; assumption ].
Qed.

Lemma glu_rel_exp_False : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ ⊥ : Propₘ.
Proof.
  intros * [Sb HSb].
  eapply glu_rel_exp_of_prop; [ exact HSb |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSb _ _ _ Hσ) as Hσt.
  assert (⊢ Δ) by (gen_presups; assumption).
  exists ⊥ᵈ; split; [ constructor | split; [ exact per_prop_False |] ].
  split; [ cbn; apply wf_False; assumption |].
  intros Δ' φ W Hφ HW.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  inversion HW; subst.
  eapply glu_nf_eq_proof_free; [ cbn; repeat constructor | cbn; apply wf_exp_eq_refl, wf_False; assumption ].
Qed.

(** The introduction of [⊤], a proof. *)
Lemma glu_rel_exp_tt : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ a_tt : ⊤.
Proof.
  intros * HΓ.
  apply glu_rel_exp_proof; [ exact (glu_rel_exp_True HΓ) |].
  destruct HΓ as [Sb HSb]; apply wf_tt; exact (glu_ctx_env_wf_ctx HSb).
Qed.

(** ** Conjunction *)

(** The readback equations of a conjunction, from its components'. *)
Lemma glu_nf_eq_and : forall {Γ P Q WP WQ},
    Γ ⊢ P : Propₘ ->
    glu_nf_eq Γ P WP Propₘ ->
    glu_nf_eq (Γ ▹{ak_propositional} P) Q WQ Propₘ ->
    glu_nf_eq Γ (Σₚ P Q) (nf_and WP WQ) Propₘ.
Proof.
  intros * HP (WP' & EP & HP') (WQ' & EQ & HQ').
  exists (nf_and WP' WQ'); split; [ apply nf_and_upto_proofs; assumption |].
  cbn; eapply wf_exp_eq_and_cong; eassumption.
Qed.

(** A conjunction is glued by its readback, its second component's at the
    fresh variable of the first, glued at the extended substitution. *)
Lemma glu_rel_exp_and : forall {Γ P Q},
    Γ ⊩ P : Propₘ ->
    Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
    Γ ⊩ Σₚ P Q : Propₘ.
Proof.
  intros * HP HQ.
  destruct (presup_ctx_glu_rel_exp HP) as [SbΓ HSbΓ].
  destruct (presup_ctx_glu_rel_exp HQ) as [SbQ HSbQ].
  pose proof (glu_rel_exp_to_wf_exp HP) as HPt.
  pose proof (glu_rel_exp_to_wf_exp HQ) as HQt.
  assert (HΣt : Γ ⊢ Σₚ P Q : Propₘ) by (apply wf_and; assumption).
  pose proof (completeness_fundamental_exp _ _ _ HΣt) as HΣc.
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [R HR].
  eapply glu_rel_exp_of_prop; [ exact HSbΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
  pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
  destruct (sub_preserves_codomain (κd := ak_propositional) (κc := ak_propositional) (n := 0) Hσt HPt HQt) as [HPσ HQσ].
  destruct (glu_rel_exp_prop_inversion HSbΓ HP _ _ _ Hσ) as (p & Ep & Hpp & HpP).
  exists (Σₚᵈ p ρ Q); split; [ constructor; exact Ep |].
  destruct (rel_exp_of_prop_inversion_simple_at HR HΣc _ _ Hρ) as (s & s' & Es & Es' & Hs).
  inversion Es; inversion Es'; subst; functional_eval_rewrite_clear.
  split; [ exact Hs |].
  split; [ cbn [exp_sub]; apply wf_and; assumption |].
  intros Δ' φ W Hφ HW.
  inversion HW; subst.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  pose proof HpP as [_ HpR].
  pose proof (HpR _ _ _ Hφ ltac:(eassumption)) as HPrd.
  assert (Hgp : DG p ∈ glu_univ_elem 0 ↘ prop_glu_typ_pred p ↘ proof_glu_exp_pred p)
    by (simp glu_univ_elem; eapply glu_univ_elem_core_prop; [ exact Hpp | reflexivity | reflexivity ]).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_propositional 0 Hgp HpP HPσ) as [Hkp Hnp].
  pose proof (prop_glu_typ_pred_wk _ _ _ _ _ HpP Hφ) as HPφ.
  pose proof (var0_glu_elem Hgp Hnp HPφ) as Hv.
  rewrite Hkp in Hv.
  pose proof (kripke_preserves_exp _ _ _ _ _ HPσ Hφ) as HPφt.
  assert (⊢ Δ' ▹{ak_propositional} P[σ][φ]ʷ) by (econstructor; [ exact HPφt | constructor ]).
  assert (Hk : Δ' ▹{ak_propositional} P[σ][φ]ʷ ⊢ᵏ φ ⊙ ↑ : Δ) by mauto 3.
  rewrite exp_wk_wk in Hv.
  pose proof (glu_cons_sub_of_elem HSbΓ HSbQ Hσ Ep Hgp Hk Hv) as Hc.
  destruct (glu_rel_exp_prop_inversion HSbQ HQ _ _ _ Hc) as (b' & Eb' & _ & [_ HbR]).
  functional_eval_rewrite_clear.
  pose proof (HbR _ wk_id _ ltac:(mauto 3) ltac:(eassumption)) as HQW; rewrite exp_wk_id in HQW.
  pose proof (kripke_q_var_eq _ _ _ _ _ _ _ Propₘ HQσ HPσ sort_kind_prop Hφ) as Hq.
  rewrite exp_sub_q_extend_wk in Hq.
  cbn [exp_sub exp_wk].
  eapply glu_nf_eq_and; [ exact HPφt | exact HPrd |].
  eapply glu_nf_eq_exp_eq; [ apply wf_exp_eq_sym; exact Hq | exact HQW ].
Qed.

(** The proofs of a conjunction and of its components, kept. *)
Lemma glu_rel_exp_conj : forall {Γ P Q M N},
    Γ ⊩ P : Propₘ ->
    Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
    Γ ⊩ M : P ->
    Γ ⊩ N : Q[Id,,M] ->
    Γ ⊩ a_conj P Q M N : Σₚ P Q.
Proof.
  intros * HP HQ HM HN.
  apply glu_rel_exp_proof; [ exact (glu_rel_exp_and HP HQ) |].
  apply wf_conj; apply glu_rel_exp_to_wf_exp; assumption.
Qed.

Lemma glu_rel_exp_left : forall {Γ P Q M},
    Γ ⊩ P : Propₘ ->
    Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
    Γ ⊩ M : Σₚ P Q ->
    Γ ⊩ a_left M : P.
Proof.
  intros * HP HQ HM.
  apply glu_rel_exp_proof; [ exact HP |].
  eapply wf_left; apply glu_rel_exp_to_wf_exp; [ exact HP | exact HQ | exact HM ].
Qed.

Lemma glu_rel_exp_right : forall {Γ P Q M},
    Γ ⊩ P : Propₘ ->
    Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
    Γ ⊩ M : Σₚ P Q ->
    Γ ⊩ Q[Id,,a_left M] : Propₘ ->
    Γ ⊩ a_right M : Q[Id,,a_left M].
Proof.
  intros * HP HQ HM HQM.
  apply glu_rel_exp_proof; [ exact HQM |].
  eapply wf_right; apply glu_rel_exp_to_wf_exp; [ exact HP | exact HQ | exact HM | exact HQM ].
Qed.

(** ** Ex Falso *)

(** Into a type of a universe: the neutral of the type's value at the
    proof of [⊥] kept, whose readback is the type's and the proof as a
    term, which is irrelevant up to proofs. *)
Lemma glu_rel_exp_absurd_univ : forall {Γ C M} {i : nat},
    Γ ⊩ C : Typeω@i ->
    Γ ⊩ M : ⊥ ->
    Γ ⊩ efq M return C : C.
Proof.
  intros * HC HM.
  destruct (presup_ctx_glu_rel_exp HC) as [SbΓ HSbΓ].
  pose proof (glu_rel_exp_to_wf_exp HC) as HCt.
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  assert (Hefq : Γ ⊢ efq M return C : C)
    by (eapply wf_absurd; [ exact HCt | constructor | constructor | exact HMt ]).
  assert (HMs : exp_scoped (List.length Γ) M) by exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HMt))).
  pose proof (glu_rel_exp_kind_sort_large_inversion (κ := ak_relevant) HSbΓ HC) as HCg.
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [R HR].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HSbΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
  pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
  destruct (HCg _ _ _ Hσ) as [HCσ (c & Ec & [Rc HRc] & HcP)].
  destruct (per_univ_glu_univ_elem _ _ (ex_intro _ Rc HRc)) as (P & El & Hg).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant i Hg (HcP _ _ Hg) HCσ) as [Hk Hn].
  destruct (per_ctx_env_kept_proof_readable _ _ _ M HR (exp_scoped_free_bound _ _ HMs) _ _ Hρ) as [Hpr _].
  econstructor; [ exact Ec | rewrite Hk; cbn; apply eval_exp_absurd; exact Ec | exact Hg |].
  eapply realize_glu_elem_bot; [ exact Hg |].
  econstructor; [ exact (sub_preserves_exp _ _ _ _ _ _ _ Hefq Hσt) | exact Hg | exact (HcP _ _ Hg) | |].
  - apply per_bot_neutral_at; [ exact Hn | rewrite Hk; discriminate |].
    apply per_bot_absurd; [ exact (per_univ_then_per_top_typ HRc) | exact Hpr | exact Hpr ].
  - intros Δ' φ W Hφ HW.
    inversion HW; subst.
    destruct (realize_glu_typ_top _ _ _ _ Hg Hn _ _ (HcP _ _ Hg)) as [_ _ Hrd].
    rewrite Hk in Hrd.
    destruct (Hrd _ _ _ Hφ ltac:(eassumption)) as (C'' & EC & HCeq).
    exists (efqⁿ M[σ][φ]ʷ return C''); split; [ unfold ne_eq_upto_proofs; cbn; exact EC |].
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HMt Hσt) as HMσ.
    cbn [exp_sub exp_wk ne_annotate_proofs ne_to_exp].
    eapply wf_exp_eq_absurd_cong;
      [ exact (kripke_preserves_exp _ _ _ _ _ HCσ Hφ) | constructor | constructor | exact HCeq
      | exact (kripke_preserves_exp _ _ _ _ _ HMσ Hφ) | exact (kripke_preserves_exp _ _ _ _ _ HMσ Hφ) ].
Qed.

(** Ex falso ([wf_absurd]): into a type of a universe, or a proof of a
    proposition. *)
Lemma glu_rel_exp_absurd : forall {Γ C Srt M},
    Γ ⊩ C : Srt ->
    type_sort Srt ->
    level_closed_sort Propₘ Srt ->
    Γ ⊩ M : ⊥ ->
    Γ ⊩ efq M return C : C.
Proof.
  intros * HC HS Hcl HM.
  inversion Hcl; subst.
  - exact (glu_rel_exp_absurd_univ HC HM).
  - apply glu_rel_exp_proof; [ exact HC |].
    eapply wf_absurd; [ exact (glu_rel_exp_to_wf_exp HC) | exact HS | exact Hcl | exact (glu_rel_exp_to_wf_exp HM) ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_prop_univ glu_rel_exp_True glu_rel_exp_False glu_rel_exp_tt : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

Lemma glu_prop :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Propₘ : Type@0 ).
Proof. glu_intro; apply glu_rel_exp_prop_univ; assumption. Qed.

Lemma glu_True :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊤ : Propₘ ).
Proof. glu_intro; apply glu_rel_exp_True; assumption. Qed.

Lemma glu_tt :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_tt : ⊤ ).
Proof. glu_intro; apply glu_rel_exp_tt; assumption. Qed.

Lemma glu_False :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊥ : Propₘ ).
Proof. glu_intro; apply glu_rel_exp_False; assumption. Qed.

Lemma glu_absurd :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ C : Srt ->
     type_sort Srt ->
     level_closed_sort Propₘ Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ efq M return C : C ).
Proof. glu_intro; eapply (glu_rel_exp_absurd (C := C)); eassumption. Qed.

Lemma glu_and :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Σₚ P Q : Propₘ ).
Proof. glu_intro; eapply glu_rel_exp_and; eassumption. Qed.

Lemma glu_conj :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : Q[Id,,M] ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_conj P Q M N : Σₚ P Q ).
Proof. glu_intro; eapply (glu_rel_exp_conj (P := P) (Q := Q)); eassumption. Qed.

Lemma glu_left :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_left M : P ).
Proof. glu_intro; eapply (glu_rel_exp_left (P := P) (Q := Q)); eassumption. Qed.

Lemma glu_right :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Q[Id,,a_left M] : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_right M : Q[Id,,a_left M] ).
Proof. glu_intro; eapply (glu_rel_exp_right (P := P) (Q := Q)); eassumption. Qed.

(** The equations glue their context. *)
Lemma glu_exp_eq_prop_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_True_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_False_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_absurd_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ C : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_and_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_irrelevant :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
