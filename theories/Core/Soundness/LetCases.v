(** * The Rules of Lets

    The rules of the three lets in the gluing model: of a term, of a module
    and of a definition with a module part, their congruences and their
    [ζ]-rules.  The lemmas they rest on are in [LogicalRelation/Lets.v]
    and, for the module lets, [Modules/Slots.v]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LogicalRelation.Lets Modules.Slots LogicalRelation.Universes.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Contexts LogicalRelation.Variables
  Modules.ModuleValues LogicalRelation.Instance LogicalRelation.Lets Modules.Slots.
Import Domain_Notations Wk_Notations Fixed_Notations.
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

Lemma glu_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     glu_unit_eq Θ Ξ Γ U U ->
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
     glu_unit_eq Θ Ξ Γ (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E)) ->
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
  `( glu_unit_eq Θ Ξ Γ U U' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_let_mod_zeta :
  `( glu_unit_eq Θ Ξ Γ U U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
