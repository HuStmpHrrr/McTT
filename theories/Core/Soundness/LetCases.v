(** * Local Definitions in the Gluing Model

    A [let] is glued through its body: [⟦ℓ A ≔ M in B⟧ρ] is [B]'s value at
    [ρ] extended by [M]'s value at its kind, a proof kept at a proposition
    ([eval_exp_let], [eval_exp_let_proof]), and [σ,,M[σ]] glues with that
    extension into [Γ ▸ A ≔ M] ([cons_def_glu_sub_pred_helper]).  The type
    [C[Id,,M]] is related to [C]'s value at the extension by [ζ] at the type
    ([let_typ_value]), and the term is moved from [B[σ,,M[σ]]] to
    [(ℓ A ≔ M in B)[σ]] by [ζ]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LetCases UniverseCases.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  VariableCases
  Instances.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [σ,,M[σ]] into a definition entry, as [cons_glu_sub_pred_helper] for an
    assumption entry: the head is [M]'s value at its kind, tied to it at an
    evaluated kind. *)
Lemma cons_def_glu_sub_pred_helper : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El M m},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    Γ ⊢ M : A ->
    ⟦ A ⟧ ρ ↘ a ->
    glu_term_value M ρ (domain_kind a) m ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M[σ] : A[σ] ® m ∈ El ->
    Δ ⊢ˢ σ,,M[σ] ® ρ ↦ m ⦂ entry_type_value a ∈ cons_def_glu_sub_pred i Γ A M Sb.
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
  - (** The stored type is the type's value *)
    eexists; split; [ reflexivity |].
    refine (mk_glu_stored_type _ _ _ _ _ i a P El ltac:(constructor) Hglu _).
    rewrite exp_sub_shift_extend; exact HMσ.
  - split; [ exact (proj1 (entry_readable_of_elem HR Hmm)) | cbn; lia ].
  - first [ exact Hσg | cbn; exact Hσg | eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | exact Hσg | mauto 3 ] ].
Qed.

(** The sort of a [let]'s type is a sort of types. *)
Lemma level_closed_sort_type_sort : forall S SC, level_closed_sort S SC -> type_sort SC.
Proof. intros * []; constructor. Qed.

(** The value of the type of a [let] at one environment: the value of the
    type instantiated by the definiens is related to the value of the type
    at the environment extended by the definiens' value at its kind
    ([rel_exp_under_ctx_let_zeta] at the type, a term of its sort). *)
Lemma let_typ_value : forall {Γ A S M C SC R},
    type_sort S ->
    Γ ⊢ A : S ->
    Γ ⊢ M : A ->
    Γ ▸ A ≔ M ⊢ C : SC ->
    type_sort SC ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    exists i : nat, forall ρ a m,
      Dom ρ ≈ ρ ∈ R ->
      ⟦ A ⟧ ρ ↘ a ->
      glu_term_value M ρ (domain_kind a) m ->
      exists c c', ⟦ C[Id,,M] ⟧ ρ ↘ c /\ ⟦ C ⟧ ρ ↦ m ⦂ entry_type_value a ↘ c' /\ Dom c ≈ c' ∈ per_univ i.
Proof.
  intros * HS HA HM HC HSC HR.
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAc.
  pose proof (completeness_fundamental_exp _ _ _ HM) as HMc.
  pose proof (completeness_fundamental_exp _ _ _ HC) as HCc.
  assert (HMs : exp_scoped (List.length Γ) M) by exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HM))).
  pose proof (rel_exp_under_ctx_let_zeta HS HAc HMc HMs HCc) as Hz.
  assert (HSs : SC[Id,,M] = SC) by (destruct HSC; reflexivity).
  rewrite HSs in Hz.
  destruct (rel_type_of_sort HSC Hz) as [i Hi].
  exists i; intros ρ a m Hρ Ha Hm.
  destruct (rel_type_inversion_simple_at HR Hi _ _ Hρ) as (c1 & c & Ec1 & Ec & Hc).
  exists c, c1; split; [ exact Ec | split; [| symmetry; exact Hc ] ].
  destruct (evaluated_kind_or_propositional (domain_kind a)) as [Hev | Hp].
  - assert (HmE : ⟦ M ⟧ ρ ↘ m) by (destruct (domain_kind a); [ exact Hm | inversion Hev | exact Hm ]).
    inversion Ec1; subst; functional_eval_rewrite_clear; [ assumption |].
    match goal with H : domain_kind a = ak_propositional |- _ => rewrite H in Hev; inversion Hev end.
  - rewrite Hp in Hm; cbn in Hm; subst m.
    inversion Ec1; subst; functional_eval_rewrite_clear; [| assumption ].
    match goal with H : evaluated_kind (domain_kind a) |- _ => rewrite Hp in H; inversion H end.
Qed.

(** A [let] ([wf_let]): glued as its body at the extended substitution, up
    to [ζ], then moved from the body's type's value to the related value of
    its type, at the type's gluing, its witness ([glu_univ_elem_exp_conv]). *)
Lemma glu_rel_exp_let : forall {Γ A S M C SC B},
    Γ ⊩ A : S ->
    type_sort S ->
    Γ ⊩ M : A ->
    Γ ▸ A ≔ M ⊢ C : SC ->
    level_closed_sort S SC ->
    Γ ▸ A ≔ M ⊩ B : C ->
    Γ ⊩ C[Id,,M] : SC ->
    Γ ⊩ ℓ A ≔ M in B : C[Id,,M].
Proof.
  intros * HA HS HM HCt HSC HB HW.
  assert (HSk : exists κ, sort_kind SC κ) by (destruct HSC; eexists; constructor).
  destruct HSk as [κW HSk].
  destruct (glu_rel_exp_sort_typ HW HSk) as (SbW & kW & HSbW & _ & HWg).
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  pose proof (glu_rel_exp_to_wf_exp HB) as HBt.
  destruct (presup_ctx_glu_rel_exp HA) as [SbΓ HSbΓ].
  destruct (presup_ctx_glu_rel_exp HB) as [SbD HSbD].
  destruct (glu_ctx_env_cons_def_clean_inversion HSbΓ HSbD) as (i & κ & HAi & _ & _ & HMg & ESb).
  destruct (glu_rel_exp_clean_inversion1 HSbD HB) as [k HBk].
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [R HR].
  destruct (let_typ_value HS HAt HMt HCt (level_closed_sort_type_sort _ _ HSC) HR) as [j HCv].
  assert (Hζ0 : Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M]) by (eapply wf_exp_eq_let_zeta; [ exact HAt | exact HS | exact HMt | exact HCt | exact HSC | exact HBt ]).
  assert (EW : SbΓ <∙> SbW) by (eapply functional_glu_ctx_env; eassumption).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := kW); [ exact HSbΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
  pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
  destruct (HMg _ _ _ Hσ) as [a m P El Ea Hm Hglu HMσ].
  assert (Hc : Δ ⊢ˢ σ,,M[σ] ® ρ ↦ m ⦂ entry_type_value a ∈ SbD)
    by (apply ESb; eapply cons_def_glu_sub_pred_helper; eassumption).
  destruct (HBk _ _ _ Hc) as [c' b Pc Elc Ec' Hb Hgc HBσ].
  destruct (HCv _ _ _ Hρ Ea Hm) as (c & c'' & Ec & Ec'' & Hcc).
  functional_eval_rewrite_clear.
  (** The witness: the type glued at its value *)
  destruct (HWg _ _ _ (proj1 (EW _ _ _) Hσ)) as [c0 Pw Elw Ec0 Hgw HWσ].
  assert (c0 = c) by (eapply functional_eval_exp; eassumption); subst c0; clear Ec0.
  assert (Hζ : Δ ⊢ (ℓ A ≔ M in B)[σ] ≈ B[Id,,M][σ] : C[Id,,M][σ]) by (eapply sub_preserves_exp_eq; eassumption).
  rewrite !exp_sub_extend_sub in Hζ.
  assert (HN0 : Δ ⊢ (ℓ A ≔ M in B)[σ] : C[Id,,M][σ] ® b ∈ Elc).
  { rewrite exp_sub_extend_sub.
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hgc | exact HBσ | apply wf_exp_eq_sym; exact Hζ ]. }
  destruct Hcc as [Rc Hcc].
  assert (Hc'c : Dom c' ≈ c ∈ per_univ j) by (eexists; symmetry; exact Hcc).
  pose proof (glu_univ_elem_exp_conv Hc'c Hgc Hgw HN0 HWσ) as HN.
  (** The term's value at the kind of its type *)
  assert (Hevb : evaluated_kind (domain_kind c) -> ⟦ ℓ A ≔ M in B ⟧ ρ ↘ b).
  { intros Hev.
    rewrite (per_univ_elem_kind _ _ _ _ Hcc) in Hev.
    assert (Hb' : ⟦ B ⟧ ρ ↦ m ⦂ entry_type_value a ↘ b)
      by (destruct (domain_kind c'); [ exact Hb | inversion Hev | exact Hb ]).
    destruct (evaluated_kind_or_propositional (domain_kind a)) as [Hea | Hpa].
    - eapply eval_exp_let; [ exact Ea | exact Hea | | exact Hb' ].
      destruct (domain_kind a); [ exact Hm | inversion Hea | exact Hm ].
    - rewrite Hpa in Hm; cbn in Hm; subst m.
      eapply eval_exp_let_proof; [ exact Ea | exact Hpa | exact Hb' ]. }
  destruct (glu_term_value_intro Hgw HSbΓ Hσ (presup_exp_eq_left Hζ0) Hevb HN) as (m' & Hm' & HMg').
  econstructor; [ exact Ec | exact Hm' | exact Hgw | exact HMg' ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_let : mctt.

(** ** The Rules

    A [let] reads the syntactic premise on its type at the target, moved
    along the embedding. *)

#[local] Generalizable All Variables.

Lemma glu_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ C : SrtC ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊩ C : SrtC ->
     level_closed_sort Srt SrtC ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊩ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓ A ≔ M in B : C[Id,,M] ).
Proof.
  glu_inst_intro.
  match goal with HSC : level_closed_sort _ _ |- _ => pose proof (level_closed_sort_type_sort _ _ HSC) as HSCt end.
  assert (Hq : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) (Γ' ▸ A[τ] ≔ M[τ]) (q τ) (Γ ▸ A ≔ M))
    by (eapply glu_rel_sub_inst_q_def; eassumption).
  (** The type's instance at the definiens, the witness *)
  assert (Hext : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) Γ' (τ,,M[τ]) (Γ ▸ A ≔ M))
    by (eapply glu_rel_sub_inst_extend_def; [ exact Hτ | eapply glu_rel_exp_under_sub_wf; eassumption | eassumption | eassumption ]).
  rewrite <- exp_sub_extend_comm.
  eapply (glu_rel_exp_let (A := A[τ]) (S := Srt) (C := C[q τ])); try glu_inst_premise.
  - rewrite <- (type_sort_sub SrtC (q τ) HSCt).
    eapply sub_preserves_exp; [ apply Hwe; eassumption | apply Hq ].
  - rewrite exp_sub_q_extend; glu_inst.
Qed.

(** The equations glue their context, which their annotation's premise
    does. *)
Lemma glu_exp_eq_let_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
