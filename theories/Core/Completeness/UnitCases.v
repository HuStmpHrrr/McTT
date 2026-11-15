(** * The Rules of Extensions and Units

    The rules of [⊢ˣ] (equal extensions) and of [⊢ᵘ] (equal units) in the
    PER model.  The lemmas they rest on are in [Modules/Slots.v] and
    [Modules/ModuleLemmas.v]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup Paths DescTyping LookupSound.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Contexts Functions Lets Levels Subtyping Props
  Universes Variables Instance Telescope.
From Mctt.Core.Completeness.Modules Require Import Slots MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Con Elim ElimViewRule Iota Decl.
From Mctt.Core.Completeness.Modules Require Import ModuleValues Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Mem Canon App Sel ModuleLemmas.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Fixed_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Lemma sem_ext_eq_nil :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ ⋅ ≈ ⋅ ).
Proof.
  intros * H; sem_intro; [ assumption | | assumption | assumption ].
  constructor; [ exact H | exact H | exact (rel_ctx_wf_per_ctx H) ].
Qed.

(** The heads, each below the other, are equal types in the PER model
    ([rel_type_of_mutual_subtyp]). *)
Lemma sem_ext_eq_ass :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Srt ->
     sort_kind Srt κ ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Srt' ->
     sort_kind Srt' κ ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A' ⊆ A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▹{κ} A ≈ Ψ' ▹{κ} A' ).
Proof.
  intros * HΨ HA HS HA' HS' HAA' HA'A; sem_intro0.
  assert (Hr : Γ ⊨ˣ Ψ ▹{κ} A ≈ Ψ' ▹{κ} A').
  { destruct HΨ as [H1 H2 H3].
    constructor; cbn [app].
    - exact (rel_ctx_wf_extend_sort H1 HS HA).
    - exact (rel_ctx_wf_extend_sort H2 HS' HA').
    - destruct (rel_type_of_mutual_subtyp HAA' HA'A (rel_type_not_level_sort_of_sort (sort_kind_type_sort _ _ HS) HA))
        as [k Hk]; exact (per_ctx_extend_type H3 Hk). }
  constructor; [ assumption | exact Hr | apply valid_ctx_ass | apply valid_ctx_ass ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

(** The same at a definition, the bodies equal. *)
Lemma sem_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Srt' ->
     type_sort Srt' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A' ⊆ A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M' ).
Proof.
  intros * HΨ HA HS HA' HS' HAA' HA'A HM HMM' HM'; sem_intro0.
  assert (Hr : Γ ⊨ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M').
  { destruct HΨ as [H1 H2 [R HR]].
    destruct (rel_type_of_mutual_subtyp HAA' HA'A (rel_type_not_level_sort_of_sort HS HA)) as [k Hk].
    constructor; cbn [app].
    - exact (rel_ctx_wf_extend_def_sort H1 HS HA HM).
    - exact (rel_ctx_wf_extend_def_sort H2 HS' HA' HM').
    - exact (per_ctx_env_extend_def_cross HS HR HA Hk HMM'). }
  constructor; [ assumption | exact Hr | apply valid_ctx_def | apply valid_ctx_def ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

Lemma sem_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U' ).
Proof.
  intros * HΨ HUU' HU'U'; sem_intro0.
  (** The literals are scoped by their contexts, as valid units. *)
  assert (Hs1 : gunit_scoped (List.length (Ψ ++ Γ)) U)
    by (match goal with Hk : valid_unit _ _ (Ψ ++ Γ) (me_lit U) |- _ => exact (valid_unit_lit_scoped _ _ _ _ Hk) end).
  assert (Hs2 : gunit_scoped (List.length (Ψ' ++ Γ)) U')
    by (match goal with Hk : valid_unit _ _ (Ψ' ++ Γ) (me_lit U') |- _ => exact (valid_unit_lit_scoped _ _ _ _ Hk) end).
  assert (Hr : Γ ⊨ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U').
  { destruct HΨ as [H1 H2 [Rx HRx]]; destruct HUU' as [HU HsU _]; destruct HU'U' as [HU' HsU' _].
    destruct (rel_ctx_wf_per_ctx_env H1) as [R HR].
    destruct (rel_ctx_wf_per_ctx_env H2) as [R' HR'].
    pose proof (rel_modexp_refl_left HU) as HUU.
    constructor; cbn [app].
    - econstructor; [ exact H1 | exact (per_ctx_env_of_mod HR HUU Hs1 Hs1) | exact HUU | exact HsU ].
    - econstructor; [ exact H2 | exact (per_ctx_env_of_mod HR' HU' Hs2 Hs2) | exact HU' | exact HsU' ].
    - assert (E : Rx <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
      exists (per_ctx_env_mod_rel Rx (List.length (Ψ ++ Γ)) U U').
      eapply per_ctx_env_cons_mod;
        [ exact HRx | eapply per_env_PER; exact HRx | exact (gunit_scoped_free_bound _ _ Hs1)
        | exact (gunit_scoped_free_bound _ _ Hs2) | | reflexivity ].
      intros ρ ρ' Hρ; eapply unit_chain_at; [ exact HU | exact HR | apply E, Hρ ]. }
  constructor; [ assumption | exact Hr | apply valid_ctx_mod | apply valid_ctx_mod ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

Lemma sem_ext_eq_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ M' : A' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▸ₘ A ≔ M ‖ U ≈ Ψ' ▸ₘ A' ≔ M' ‖ U' ).
Proof.
  intros * HΨ HA HAA' HM HMM' HA' HM' HUU' HU'U'; sem_intro0.
  (** The literals are scoped by their contexts, as valid units. *)
  assert (Hs1 : gunit_scoped (List.length (Ψ ++ Γ)) U)
    by (match goal with Hk : valid_unit _ _ (Ψ ++ Γ) (me_lit U) |- _ => exact (valid_unit_lit_scoped _ _ _ _ Hk) end).
  assert (Hs2 : gunit_scoped (List.length (Ψ' ++ Γ)) U')
    by (match goal with Hk : valid_unit _ _ (Ψ' ++ Γ) (me_lit U') |- _ => exact (valid_unit_lit_scoped _ _ _ _ Hk) end).
  assert (Hr : Γ ⊨ˣ Ψ ▸ₘ A ≔ M ‖ U ≈ Ψ' ▸ₘ A' ≔ M' ‖ U').
  { destruct HΨ as [H1 H2 [Rx HRx]]; destruct HUU' as [HU HsU _]; destruct HU'U' as [HU' HsU' _].
    destruct (rel_ctx_wf_per_ctx_env H1) as [R HR].
    destruct (rel_ctx_wf_per_ctx_env H2) as [R' HR'].
    pose proof (rel_modexp_refl_left HU) as HUU.
    constructor; cbn [app].
    - econstructor; [ exact H1 | exact (per_ctx_env_of_dm HR HA HM HUU Hs1) | exact HA | exact HM | exact HUU | exact HsU ].
    - econstructor; [ exact H2 | exact (per_ctx_env_of_dm HR' HA' HM' HU' Hs2) | exact HA' | exact HM' | exact HU' | exact HsU' ].
    - exact (per_ctx_env_extend_dm_cross HRx HAA' HMM' HU Hs1 Hs2). }
  constructor; [ assumption | exact Hr | apply valid_ctx_dm | apply valid_ctx_dm ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

Lemma sem_unit_eq_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
     body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
     body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' ->
     (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        sort_kind (entry_sort y) (entry_kind E)) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : entry_sort y) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊨ A'[σ'] : entry_sort y) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
     (forall y Φ0 E U Φ0' E' U' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
     (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
     (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ ⊨ᵐ H' ≈ H') ->
     all_assumptions Δ ->
     all_assumptions Δ' ->
     List.length Δ = List.length Δ' ->
     body_shape Φ Φ' ->
     body_shape Φx Φx' ->
     List.NoDup (gm_names Φ) ->
     (forall k, parameter_sort param_level (param_sorts k)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     (forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ).
Proof.
  intros * Hu Hx Hx' HΔ HC HC' Htag HA HA' HM HU Ho Ho' Ha Ha' Hl Hs Hsxx Hnd Hps HP HP' Θ2 Ξ2 He.
  destruct (HΔ _ _ He) as [HKctx HΔr _ _].
  destruct (HC _ _ He) as [_ HCr HKC _].
  destruct (HC' _ _ He) as [_ HCr' HKC' _].
  destruct (rel_unit_under_ctx_body_of_embedding _ _ _ _ _ _ _ _ _ _ _ _ _ _ He Hu Hx Hx' HΔr (valid_ctx_rel_ctx_wf HKctx)
              HCr (proj2 (proj1 (valid_ctx_iff _ _ _) HKC)) HCr' (proj2 (proj1 (valid_ctx_iff _ _ _) HKC'))
              Htag HA HA' HM HU Ho Ho' Ha Ha' Hl Hs Hsxx Hnd Hps HP HP') as (HR & HV & HV').
  constructor; assumption.
Qed.

Lemma sem_unit_eq_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ' ->
     all_assumptions Δ ->
     all_assumptions Δ' ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵐ E ≈ E' ->
     Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊨ᵐ E' ≈ E' ->
     (forall k, parameter_sort param_level (param_sorts k)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     (forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ).
Proof.
  intros * Hu HΔw HΔ Ha Ha' HE HE' Hps HP HP'; sem_intro0.
  match goal with He : valid_gctx_embedding _ _ _ _ |- _ =>
    assert (HPr : rel_params_evaluated Γ Δ param_level)
      by (intros ? ? ? ? HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP _ _ _ _ HE0 _ _ He))));
    assert (HPr' : rel_params_evaluated Γ Δ' param_level)
      by (intros ? ? ? ? HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP' _ _ _ _ HE0 _ _ He))))
  end.
  close_unit rel_unit_under_ctx_alias.
Qed.

Lemma sem_unit_eq_flatten :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ ->
     all_assumptions Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
     (forall k, parameter_sort param_level (param_sorts k)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : param_sorts (List.length Δ2)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ).
Proof.
  intros * Hu HΔ Ha HU Hps HPw HP; sem_intro0.
  pose proof (params_evaluated_of_sorts _ _ _ _ _ _ Hps HPw) as HPw'.
  match goal with He : valid_gctx_embedding _ _ _ _ |- _ =>
    assert (HPr : rel_params_evaluated Γ Δ param_level)
      by (intros ? ? ? ? HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP _ _ _ _ HE0 _ _ He))))
  end.
  close_unit rel_unit_under_ctx_flatten.
Qed.

(** A body unit is equivalent to its expansion ([wf_unit_eq_expand]). *)
Lemma sem_unit_eq_expand :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ (gm_expand Φ) ).
Proof.
  intros * Hw HU; sem_intro0.
  close_unit rel_unit_under_ctx_expand.
Qed.

Lemma sem_unit_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U' ≈ U ).
Proof.
  intros * HU; sem_intro; try assumption.
  destruct HU as [HL Hl Hr]; constructor; [ apply rel_modexp_under_ctx_sym; exact HL | assumption .. ].
Qed.

Lemma sem_unit_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U' ≈ U'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U'' ).
Proof.
  intros * HU HU'; sem_intro; try assumption.
  destruct HU as [HL Hl _]; destruct HU' as [HL' _ Hr'].
  constructor; [ eapply rel_modexp_under_ctx_trans; eassumption | assumption .. ].
Qed.
