(** * Units: Slots, Module Expressions and Module Lets

    The context PER of an extension by a slot ties the slot's value to the
    value of its unit, as a literal, over the tail ([per_ctx_env_mod_rel]).  This
    file builds such PERs, the semantic substitutions into slots, the
    symmetry and transitivity of the module judgment, the extensions of a
    context, and the module [let]s.  The closures of related units are
    related in [Modules/Body.v]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Import LookupSound.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Context PERs of Extended Contexts *)

Lemma per_ctx_env_app_tail : forall Ψ Ψ' Γ Γ' R,
    List.length Ψ = List.length Ψ' ->
    EF Ψ ++ Γ ≈ Ψ' ++ Γ' ∈ per_ctx_env ↘ R ->
    exists RΓ, EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ.
Proof.
  induction Ψ as [| e Ψ IH]; intros [| e' Ψ'] * Hl H; cbn in *; try discriminate; eauto.
  inversion H; subst; eauto.
Qed.

Lemma rel_ctx_wf_app_r : forall Ψ Γ, ⊨ Ψ ++ Γ -> ⊨ Γ.
Proof. induction Ψ; intros * H; cbn in *; [ exact H | apply IHΨ; eapply rel_ctx_wf_tail; exact H ]. Qed.

(** ** Slots *)

(** The relation of an extension by a slot over the tail relation [R] is
    [per_ctx_env_mod_rel R n U U'], at the tail's length [n]: the heads are
    tied to the values of both units over their own tails, and read back
    with their stored units scoped by the tail. *)

(** The relation of an extension by a slot, with its tail relation fixed. *)
Lemma per_ctx_env_cons_mod_inversion : forall {Γ Γ' U U' RΓ R},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF Γ ▹ₘ U ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', RΓ ρ ρ' -> rel_modexp_evals (me_lit U) ρ (me_lit U') ρ') /\
      (R <~> per_ctx_env_mod_rel RΓ (List.length Γ) U U').
Proof.
  intros * HΓ H; inversion H; subst.
  match goal with Ht : per_ctx_env ?T Γ Γ' |- _ =>
    assert (HT : T <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption) end.
  match goal with
  | Hu : forall ρ ρ', _ -> rel_modexp_evals _ _ _ _, He : R <~> _ |- _ =>
      split;
      [ intros ρ ρ' Hρ; apply Hu, HT, Hρ
      | intros ρ ρ'; split; intros Hρ;
        [ apply He in Hρ as [Ht ? ? ? ? ? ? ? ?]; constructor; [ apply HT; assumption | assumption .. ]
        | apply He; destruct Hρ as [Ht ? ? ? ? ? ? ? ?]; constructor; [ apply HT; assumption | assumption .. ] ] ]
  end.
Qed.

(** A valid module expression, at environments a context PER relates. *)
Lemma rel_modexp_at : forall Γ Γ' H H' R,
    Γ ⊨ᵐ H ≈ H' -> EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' ->
      exists h h', ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\ ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h'.
Proof.
  intros * [RE HΓE HEg] HR ρ ρ' Hρ.
  assert (Ex : R <~> RE) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (eval_sub_id_rel HΓE (proj1 (Ex _ _) Hρ)) as [Hid Hid'].
  destruct (HEg _ _ HΓE _ _ (rel_sub_id (ex_intro _ _ HΓE)) _ _ _ _ (proj1 (Ex _ _) Hρ) Hid Hid')
    as [h1 h2 h3 h4 Hh1 _ _ Hh4 Hc].
  (** The outer values, at [ρ] and [ρ'] themselves; the inner ones are at
      the restampings. *)
  rewrite modexp_sub_id in Hh1, Hh4.
  exists h1, h4; repeat split; try assumption.
  pairwise.
Qed.

Corollary rel_modexp_evals_at : forall Γ Γ' H H' R,
    Γ ⊨ᵐ H ≈ H' -> EF Γ ≈ Γ' ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' -> rel_modexp_evals H ρ H' ρ'.
Proof.
  intros * HH HR ρ ρ' Hρ; destruct (rel_modexp_at _ _ _ _ _ HH HR _ _ Hρ) as (h & h' & ? & ? & ?).
  exists h h'; assumption.
Qed.

(** The values of a valid literal over related tails. *)
Lemma unit_chain_at : forall {Γ U U' R},
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> rel_modexp_evals (me_lit U) ρ (me_lit U') ρ'.
Proof. intros * HU HΓ ρ ρ' Hρ; exact (rel_modexp_evals_at _ _ _ _ _ HU HΓ _ _ Hρ). Qed.

(** The context PER of a slot, at units scoped by the tail. *)
Lemma per_ctx_env_of_mod : forall {Γ U U' R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
    EF Γ ▹ₘ U ≈ Γ ▹ₘ U' ∈ per_ctx_env ↘ per_ctx_env_mod_rel R (List.length Γ) U U'.
Proof.
  intros * HΓ HU HsU HsU'.
  eapply per_ctx_env_cons_mod;
    [ exact HΓ | eapply per_env_PER; exact HΓ | exact (gunit_scoped_free_bound _ _ HsU)
    | exact (gunit_scoped_free_bound _ _ HsU') | | reflexivity ].
  intros; eapply unit_chain_at; eassumption.
Qed.

(** The values of a valid literal moved along a substitution, against those
    of the literal over the substituted tails. *)
Lemma unit_sub_chain : forall {Γ' Γ σ σ' U U' R'},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    forall ρ ρ' ρσ ρ'σ', R' ρ ρ' -> ⟦ σ : Γ ⟧s ρ ↘ ρσ -> ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
      rel_modexp_evals (me_lit U[σ]ᵘ) ρ (me_lit U) ρσ /\ rel_modexp_evals (me_lit U) ρσ (me_lit U') ρ'σ' /\
      rel_modexp_evals (me_lit U') ρ'σ' (me_lit U'[σ']ᵘ) ρ'.
Proof.
  intros * HΓ' Hσ [R HΓ HU] * Hρ Hev Hev'.
  destruct (HU _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [h1 h2 h3 h4 H1 H2 H3 H4 (C12 & C23 & C34)].
  cbn [modexp_sub] in H1, H4.
  split; [| split ]; econstructor; eassumption.
Qed.

(** A valid literal is scoped by its context: its judgment is. *)
Lemma valid_unit_lit_scoped : forall Θm Ξm Γ U, valid_unit Θm Ξm Γ (me_lit U) -> gunit_scoped (List.length Γ) U.
Proof.
  intros * H; inversion H; subst;
    try solve [ exfalso; exact (me_apps_qname_not_lit _ _ _ ltac:(eassumption)) ];
    match goal with Hw : _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _ |- _ => exact (proj1 (proj2 (wf_modexp_eq_scoped _ _ _ _ _ Hw))) end.
Qed.

(** The scoping of a unit moved along a substitution. *)
Lemma gunit_scoped_rel_sub : forall {Γ' Γ σ σ' U},
    Γ' ⊨ˢ σ ≈ σ' : Γ -> gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ') U[σ]ᵘ.
Proof.
  intros * [? _ ? _ _ Hσs] HsU.
  exact (gunit_scoped_sub _ _ _ _ HsU (fun x Hx => proj1 (Hσs x Hx))).
Qed.

Lemma per_ctx_env_of_mod_sub : forall {Γ' Γ σ σ' U R'},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    gunit_scoped (List.length Γ) U ->
    EF Γ' ▹ₘ U[σ]ᵘ ≈ Γ' ▹ₘ U[σ]ᵘ ∈ per_ctx_env ↘ per_ctx_env_mod_rel R' (List.length Γ') U[σ]ᵘ U[σ]ᵘ.
Proof.
  intros * HΓ' Hσ HU HsU.
  pose proof (gunit_scoped_free_bound _ _ (gunit_scoped_rel_sub Hσ HsU)) as Hb.
  eapply per_ctx_env_cons_mod; [ exact HΓ' | eapply per_env_PER; exact HΓ' | exact Hb | exact Hb | | reflexivity ].
  intros ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσ) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [RΓ [HΓ0 Hs]]]].
  assert (E : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (ρσ & ρ'σ & Hev & Hev' & _).
  destruct (unit_sub_chain HΓ' Hσσ HU _ _ _ _ Hρ Hev Hev') as (C1 & C2 & C3).
  eapply rel_modexp_evals_trans; [ exact C1 | eapply rel_modexp_evals_trans; [ exact C2 | exact C3 ] ].
Qed.

(** [q τ] at an environment of an extension: the head is kept, retagged
    at the target's entry over the tail ([eval_sub_q]), and the tail is
    related to the value of [τ] at the environment's tail. *)
Lemma rel_sub_q_entry : forall {Γ'' Δ τ τ' e Re RΔ},
    EF (e :: Γ'') ≈ (e :: Γ'') ∈ per_ctx_env ↘ Re ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ ->
    Γ'' ⊨ˢ τ ≈ τ' : Δ ->
    forall x u, Re x x -> ⟦ τ : Δ ⟧s x↯ ↘ u ->
      forall e', exists t, ⟦ q τ : e' :: Δ ⟧s x ↘ retag_entry (centry_tag e' Δ t) (centry_slot_unit e') (env_entry x 0) :: t
                    /\ RΔ t u.
Proof.
  intros * He HΔ [R1 H1 R2 H2 Hσ _] x u Hx Hu e'.
  pose proof (rel_wk_shift H1 He) as Hsh.
  destruct (Hσ _ _ He _ Hsh (fun y Hy => ltac:(cbn; lia)) _ _ Hx) as [t v v' t' Ht Hv Hv' Ht' Hc].
  rewrite eval_wk_shift in Hv, Hv'.
  assert (E : R2 <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Htu : RΔ t u).
  { apply E; destruct Hc as [Hc _].
    exact (per_ctx_env_resp_agree H2 _ _ _ _ (reflexivity _) (functional_eval_sub _ _ _ _ _ Hv Hu) Hc). }
  exists t; split; [| exact Htu ].
  apply eval_sub_q; exact Ht.
Qed.

(** A slot is never a proposition. *)
Lemma head_not_propositional_mod : forall U Δ ρ, ~ head_propositional gc_deps gc_stack (ce_mod U) Δ ρ.
Proof. intros * [T HT]; discriminate HT. Qed.

(** A head tied to the value of [U[σ]] over a tail is tied to the value of
    [U] over any environment related to [σ] at the tail. *)
Lemma tie_mod_sub : forall {Γ' Γ σ U R' R},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ' ⊨ˢ σ ≈ σ : Γ -> Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    forall m ρ ρσ t, R' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ -> R ρσ t ->
      tie_mod m (me_lit U[σ]ᵘ) ρ -> tie_mod m (me_lit U) t.
Proof.
  intros * HΓ' HΓ Hσ HU * Hρ Hev Ht Hm.
  destruct (unit_sub_chain HΓ' Hσ HU _ _ _ _ Hρ Hev Hev) as (C1 & _).
  eapply tie_mod_move; [ eapply tie_mod_move; [ exact Hm | exact C1 ] |].
  exact (unit_chain_at HU HΓ _ _ Ht).
Qed.

(** The tails of [q σ] at a Kripke stage over an extension [e :: Γ'] whose
    heads' modules are tied to the value of [U[σ]] over their tails: the
    four values of [σ[↑]] there, related in [Γ]'s PER, and the heads'
    modules tied to the value of [U] over each.  A slot and a definition
    with a module part both are such extensions; for example [q σ] from
    [Γ' ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]] to [Γ ▸ₘ A ≔ M ‖ U] keeps the source's head
    [de_dm v t h U1], whose module [h] the source PER ties to [U[σ]]. *)
Lemma rel_sub_q_tails_tied : forall {Γ' Γ σ σ' U e Rs R},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF (e :: Γ') ≈ (e :: Γ') ∈ per_ctx_env ↘ Rs ->
    (forall ρ ρ', Rs ρ ρ' -> tie_mod (env_mod ρ 0) (me_lit U[σ]ᵘ) ρ↯ /\ tie_mod (env_mod ρ' 0) (me_lit U[σ]ᵘ) ρ'↯) ->
    forall Γ'' R'' (HΓ'' : EF Γ'' ≈ Γ'' ∈ per_ctx_env ↘ R'') ψ,
      rel_wk ψ R'' Rs -> (forall x, x < List.length (e :: Γ') -> ψ x < List.length Γ'') ->
      forall ρ ρ', R'' ρ ρ' ->
      exists x1 y1 y4 x4,
        ⟦ sb_wk (sb_wk σ ↑) ψ : Γ ⟧s ρ ↘ x1 /\ ⟦ sb_wk σ ↑ : Γ ⟧s ⟪ψ⟫ ρ ↘ y1 /\
        ⟦ sb_wk σ' ↑ : Γ ⟧s ⟪ψ⟫ ρ' ↘ y4 /\ ⟦ sb_wk (sb_wk σ' ↑) ψ : Γ ⟧s ρ' ↘ x4 /\
        rel_chain R ([x1; y1; y4; x4]) /\
        (forall t, In t (x1 :: y1 :: nil) -> tie_mod (env_mod ρ (ψ 0)) (me_lit U) t) /\
        (forall t, In t (y4 :: x4 :: nil) -> tie_mod (env_mod ρ' (ψ 0)) (me_lit U) t).
Proof.
  intros * Hσj HU HΓ HRs Hties * HΓ'' ψ Hψ Hψb ρ ρ' Hρ.
  pose proof Hσj as [R' HΓ' R0 HΓ0 Hσ Hσs].
  assert (E0 : R0 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (rel_wk_shift HΓ' HRs) as Hshift.
  assert (Hshiftb : forall x, x < List.length Γ' -> ↑ x < List.length (e :: Γ')) by (intros x Hx; cbn; lia).
  pose proof (rel_sub_under_ctx_wk_rel Hσj HRs HΓ' Hshift Hshiftb) as Hσwkj.
  pose proof Hσwkj as [Rs' HRs' R2 HΓ2 Hσwk _].
  assert (E1 : Rs' <~> Rs) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R2 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  pose proof (rel_wk_app _ _ _ Hψ _ _ Hρ) as Hψρ.
  destruct (Hties _ _ Hψρ) as [Tρ Tρ'].
  pose proof (rel_wk_app _ _ _ Hshift _ _ Hψρ) as Htail; rewrite !eval_wk_shift in Htail.
  destruct (Hσwk _ _ HΓ'' _ (proj2 (rel_wk_morphism ψ _ _ (reflexivity R'') _ _ E1) Hψ) Hψb _ _ Hρ)
    as [x1 y1 y4 x4 Hx1 Hy1 Hy4 Hx4 Htails].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (E2 a b) H)) in Htails.
  destruct (Hσ _ _ HRs _ Hshift Hshiftb _ _ Hψρ) as [z1 y2 y3 z4 Hz1 Hy2 Hy3 Hz4 Hbtails].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (E0 a b) H)) in Hbtails.
  rewrite ?eval_wk_shift in *.
  assert (Hy12 : R y1 y2).
  { assert (Hz : R z1 y2) by pairwise.
    exact (per_ctx_env_resp_agree HΓ _ _ _ _ (functional_eval_sub _ _ _ _ _ Hz1 Hy1) (reflexivity _) Hz). }
  assert (Hy43 : R y4 y3).
  { assert (Hz : R z4 y3) by pairwise.
    exact (per_ctx_env_resp_agree HΓ _ _ _ _ (functional_eval_sub _ _ _ _ _ Hz4 Hy4) (reflexivity _) Hz). }
  assert (Htl : R' (⟪ψ⟫ ρ)↯ (⟪ψ⟫ ρ)↯) by (etransitivity; [ exact Htail | symmetry; exact Htail ]).
  assert (Htr : R' (⟪ψ⟫ ρ')↯ (⟪ψ⟫ ρ')↯) by (etransitivity; [ symmetry; exact Htail | exact Htail ]).
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [R3 [HΓ3 Hs]]]].
  assert (E3 : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E3 _ _) Htr)) as (w & _ & Hw & _ & _).
  assert (Hw3 : R w y3) by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  rewrite (eval_wk_app_mod ψ) in Tρ, Tρ'.
  assert (Hm : forall t, R y2 t -> tie_mod (env_mod ρ (ψ 0)) (me_lit U) t)
    by (intros t Ht; exact (tie_mod_sub HΓ' HΓ Hσσ HU _ _ _ _ Htl Hy2 Ht Tρ)).
  assert (Hm' : forall t, R w t -> tie_mod (env_mod ρ' (ψ 0)) (me_lit U) t)
    by (intros t Ht; exact (tie_mod_sub HΓ' HΓ Hσσ HU _ _ _ _ Htr Hw Ht Tρ')).
  exists x1, y1, y4, x4; do 5 (split; [ assumption |]); split.
  - intros t Ht; apply Hm; symmetry; etransitivity; [| exact Hy12 ]; eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ];
      destruct Ht as [<- | [<- | []]]; solve_in.
  - intros t Ht; apply Hm'; symmetry; etransitivity; [| symmetry; exact Hw3 ]; etransitivity; [| exact Hy43 ].
    eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ].
    destruct Ht as [<- | [<- | []]]; solve_in.
Qed.

(** [q σ] into a slot.  The four tails come from [σ] at the Kripke stage, as
    for an assumption; the head is the same module value on each side, tied
    to the value of [U[σ]] over the stage's tails, which the validity of [U]
    relates to the value of [U] over the tails of [q σ]. *)
Lemma rel_sub_under_ctx_q_mod : forall {Γ' Γ σ σ' U},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    gunit_scoped (List.length Γ) U ->
    Γ' ▹ₘ U[σ]ᵘ ⊨ˢ q σ ≈ q σ' : Γ ▹ₘ U.
Proof.
  intros * Hσj HU HsU.
  pose proof Hσj as [R' HΓ' R HΓ Hσ Hσs].
  pose proof (per_ctx_env_of_mod_sub HΓ' Hσj HU HsU) as HΓ'U.
  pose proof (per_ctx_env_of_mod HΓ HU HsU HsU) as HΓU.
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  refine (mk_rel_sub_under_ctx _ _ _ _ _ HΓ'U _ HΓU _ _);
    [| intros x Hx; split; eapply sb_q_bound; first [ exact Hx | intros y Hy; exact (proj1 (Hσs y Hy))
                                                   | intros y Hy; exact (proj2 (Hσs y Hy)) ] ].
  intros Γ'' R'' HΓ'' ψ Hψ Hψb ρ ρ' Hρ.
  destruct (rel_sub_q_tails_tied Hσj HU HΓ HΓ'U
              (fun ρ0 ρ0' H0 => conj (per_ctx_env_mod_rel_left_unit _ _ _ _ _ _ H0) (per_ctx_env_mod_rel_right_unit _ _ _ _ _ _ H0))
              _ _ HΓ'' _ Hψ Hψb _ _ Hρ)
    as (x1 & y1 & y4 & x4 & Hx1 & Hy1 & Hy4 & Hx4 & Htails & Hm & Hm').
  destruct (Hψ _ _ Hρ) as [_ _ _ _ _ _ _ [Ul Hkl] [Ur Hkr]].
  (** The heads are retagged at the slot ([eval_sub_q]): module entries
      storing [U], scoped by [Γ], so they are heads of the slot's context
      PER. *)
  rewrite (eval_wk_app_entry ψ), (eval_wk_app_mod ψ) in Hkl, Hkr.
  apply (mk_rel_sub (retag_entry (centry_tag (ce_mod U) Γ x1) (centry_slot_unit (ce_mod U)) (env_entry ρ (ψ 0)) :: x1)
                    (retag_entry (centry_tag (ce_mod U) Γ y1) (centry_slot_unit (ce_mod U)) (env_entry ρ (ψ 0)) :: y1)
                    (retag_entry (centry_tag (ce_mod U) Γ y4) (centry_slot_unit (ce_mod U)) (env_entry ρ' (ψ 0)) :: y4)
                    (retag_entry (centry_tag (ce_mod U) Γ x4) (centry_slot_unit (ce_mod U)) (env_entry ρ' (ψ 0)) :: x4));
    [ exact (eval_sub_wk_q (ce_mod U) _ _ _ _ _ Hx1)
    | rewrite <- (eval_wk_app_entry ψ); exact (eval_sub_q (ce_mod U) _ _ _ _ Hy1)
    | rewrite <- (eval_wk_app_entry ψ); exact (eval_sub_q (ce_mod U) _ _ _ _ Hy4)
    | exact (eval_sub_wk_q (ce_mod U) _ _ _ _ _ Hx4) | ].
  pose proof (gunit_scoped_free_bound _ _ HsU) as Hb.
  rewrite Hkl, Hkr; cbn [retag_entry centry_slot_unit centry_unit].
  cbn [rel_chain]; cbn [drop_env tl].
  repeat split.
  all: unfold env_mod in Hm, Hm' |- *; cbn [env_entry hd] in Hm, Hm' |- *.
  all: rewrite ?Hkl, ?Hkr in Hm, Hm'.
  all: try solve [ apply mod_entry_readable | cbn [entry_unit_bound]; exact Hb | eexists; reflexivity ].
  all: try solve [ eapply (rel_chain_pairwise R); [ exact Htails | solve_in | solve_in ]
          | apply Hm; solve_in | apply Hm'; solve_in ].
Qed.

(** ** Module Expressions: Symmetry and Transitivity *)

Lemma rel_modexp_under_ctx_sym : forall {Γ H H'},
    Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H' ≈ H.
Proof.
  intros * [R HΓ HH]; refine (mk_rel_modexp_under_ctx _ _ _ R HΓ _).
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP : PER R') by (eapply per_env_PER; exact HΓ').
  destruct (HH _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ _ _ _ (symmetry Hρ) Hev' Hev) as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  assert (PER per_dmod) by typeclasses eauto.
  now apply rel_chain_4_sym.
Qed.

End Fixed_GCtx.

Lemma sem_me_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H ).
Proof. intros * HH; sem_intro; first [ assumption | exact (rel_modexp_under_ctx_sym HH) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma rel_modexp_under_ctx_trans : forall {Γ H1 H2 H3},
    Γ ⊨ᵐ H1 ≈ H2 -> Γ ⊨ᵐ H2 ≈ H3 -> Γ ⊨ᵐ H1 ≈ H3.
Proof.
  intros * [R HΓ H12] [R2 HΓ2 H23].
  refine (mk_rel_modexp_under_ctx _ _ _ R HΓ _).
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρ' : R' ρ' ρ') by (etransitivity; [ symmetry |]; eassumption).
  destruct (H12 _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [v1 v2 v3 v4 ? ? ? ? Hc1].
  destruct (H23 _ _ HΓ' _ _ (rel_sub_under_ctx_refl_right Hσ) _ _ _ _ Hρ' Hev' Hev')
    as [w1 w2 w3 w4 ? ? ? ? Hc2].
  repeat match goal with
         | H : eval_modexp _ _ ?E ?r ?a, H' : eval_modexp _ _ ?E ?r ?b |- _ =>
             pose proof (functional_eval_modexp _ _ _ _ H H'); subst; clear H'
         end.
  econstructor; try eassumption.
  assert (PER per_dmod) by typeclasses eauto.
  match type of Hc1 with rel_chain _ (_ :: _ :: ?c :: _) => merge_rel_chain Hc1 Hc2 c end.
Qed.

End Fixed_GCtx.

Lemma sem_me_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H'' ).
Proof. intros * H1 H2; sem_intro; first [ assumption | exact (rel_modexp_under_ctx_trans H1 H2) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary rel_modexp_refl_left : forall {Γ H H'}, Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H ≈ H.
Proof. intros * HH; eapply rel_modexp_under_ctx_trans; [ exact HH | apply rel_modexp_under_ctx_sym, HH ]. Qed.

Corollary rel_modexp_refl_right : forall {Γ H H'}, Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H' ≈ H'.
Proof. intros * HH; eapply rel_modexp_under_ctx_trans; [ apply rel_modexp_under_ctx_sym, HH | exact HH ]. Qed.

(** ** Extensions *)

(** Two definition entries with related types and bodies, over related
    contexts: the left type of a sort, related to the right one as types
    ([rel_type_of_mutual_subtyp] gives that from a telescope equation). *)
Lemma per_ctx_env_extend_def_cross : forall {Δ Δ' A A' M M' S} {R} {i : nat},
    type_sort S ->
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ R ->
    Δ ⊨ A : S ->
    Δ ⊨ᵗ A ≈ A' at i ->
    Δ ⊨ M ≈ M' : A ->
    exists R', EF Δ ▸ A ≔ M ≈ Δ' ▸ A' ≔ M' ∈ per_ctx_env ↘ R'.
Proof.
  intros * HS HR HA0 Hi HM.
  assert (HA : Δ ⊨ A ≈ A : S) by exact HA0.
  pose proof (rel_type_inversion_simple Hi) as [RΔ [HΔ HAs]].
  assert (E : R <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  (** The kind of the entry: [ak_relevant] at a universe, [ak_level] at
      [LevelSort], [ak_propositional] at [Prop]. *)
  assert (Hr : exists r, (forall ρ ρ', RΔ ρ ρ' -> rel_typ_kind A ρ r) /\
                         (forall ρ ρ', RΔ ρ ρ' -> def_bodies_at r M ρ M' ρ' (per_head A A' ρ ρ'))).
  { assert (Hrel : forall k r, evaluated_kind r -> (forall ρ ρ', RΔ ρ ρ' -> rel_typ_kind A ρ r) ->
                             Δ ⊨ᵗ A ≈ A at k ->
                             forall ρ ρ', RΔ ρ ρ' -> def_bodies_at r M ρ M' ρ' (per_head A A' ρ ρ')).
    { intros k r Hr HArel HAk.
      pose proof (rel_type_inversion_simple_at HΔ HAk) as HAl.
      pose proof (rel_exp_under_ctx_simple_at_of_evaluated HΔ
                    (fun ρ ρ' Hρ => rel_typ_evaluated_of_kind (HArel _ _ Hρ) Hr) HM) as HMs.
      intros ρ ρ' Hρ; rewrite (def_bodies_at_evaluated _ _ _ _ _ _ Hr).
      destruct (HAs _ _ Hρ) as [a [a' [Ha [Ha' [R1 HR1]]]]].
      destruct (HAl _ _ Hρ) as [a0 [b [Ha0 [Hb [R2 HR2]]]]].
      destruct (HMs _ _ Hρ) as [m [m' [Hm [Hm' Hmm']]]].
      functional_eval_rewrite_clear.
      econstructor; try eassumption.
      apply (per_head_iff Ha Ha' HR1).
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR2 HR1).
      apply (per_head_iff Ha Hb HR2); exact Hmm'. }
    destruct HS as [j | |].
    2:{ exists ak_propositional; split; [| intros; exact I ].
        intros ρ ρ' Hρ.
        destruct (rel_exp_of_prop_inversion_simple_at HΔ (rel_exp_under_ctx_refl_left HA) _ _ Hρ)
          as (a & a' & Ha & Ha' & [Hl _ _]).
        exists a; split; assumption. }
    - exists ak_relevant; split; [ exact (rel_exp_of_typ_relevant_at HΔ (rel_exp_under_ctx_refl_left HA)) |].
      exact (Hrel _ _ evaluated_kind_relevant (rel_exp_of_typ_relevant_at HΔ (rel_exp_under_ctx_refl_left HA))
                  (rel_type_of_typ (rel_exp_under_ctx_refl_left HA))).
    - exists ak_level; split; [ exact (rel_exp_of_level_sort_kind_at HΔ (rel_exp_under_ctx_refl_left HA)) |].
      exact (Hrel _ _ evaluated_kind_level (rel_exp_of_level_sort_kind_at HΔ (rel_exp_under_ctx_refl_left HA))
                  (rel_type_of_level_sort 0 (rel_exp_under_ctx_refl_left HA))). }
  destruct Hr as [r [Hsort Hbodies]].
  eexists.
  eapply (@per_ctx_env_cons_def _ Δ Δ' i A A' M M' R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ')
            (per_ctx_env_def_rel R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ') A A' r M M') HR r);
    [ eapply per_env_PER; exact HR | | | | reflexivity ].
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ; exact (Hsort _ _ (proj1 (E _ _) Hρ)).
  - intros ρ ρ' Hρ; exact (Hbodies _ _ (proj1 (E _ _) Hρ)).
Qed.

(** Two related extensions by definitions with module parts: the term
    parts as definitions, the units as slots. *)
Lemma per_ctx_env_extend_dm_cross : forall {Δ Δ' A A' M M' U U'} {i : nat} {R},
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ R ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    Δ ⊨ᵐ me_lit U ≈ me_lit U' ->
    gunit_scoped (List.length Δ) U -> gunit_scoped (List.length Δ') U' ->
    exists R', EF Δ ▸ₘ A ≔ M ‖ U ≈ Δ' ▸ₘ A' ≔ M' ‖ U' ∈ per_ctx_env ↘ R'.
Proof.
  intros * HR HA HM HU HsU HsU'.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [RΔ [HΔ HAs]].
  assert (E : R <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ (rel_exp_under_ctx_refl_left HA)) as HAl.
  pose proof (rel_exp_under_ctx_simple_at_rel HΔ (rel_exp_under_ctx_refl_left HA) HM) as HMs.
  eexists.
  eapply per_ctx_env_cons_dm
    with (head_rel := fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ')
         (env_rel := per_ctx_env_dm_rel R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ') (List.length Δ)
                       ak_relevant M M' U U')
         (r := ak_relevant);
    [ exact HR | eapply per_env_PER; exact HR | exact (gunit_scoped_free_bound _ _ HsU) | exact (gunit_scoped_free_bound _ _ HsU')
    | | | | | reflexivity | reflexivity ].
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ; exact (rel_exp_of_typ_relevant_at HΔ (rel_exp_under_ctx_refl_left HA) _ _ (proj1 (E _ _) Hρ)).
  - intros ρ ρ' Hρ; cbn [def_bodies_at].
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    destruct (HAl _ _ (proj1 (E _ _) Hρ)) as [a0 [b [Ha0 [Hb [R2 HR2]]]]].
    destruct (HMs _ _ (proj1 (E _ _) Hρ)) as [m [m' [Hm [Hm' Hmm']]]].
    functional_eval_rewrite_clear.
    econstructor; try eassumption.
    apply (per_head_iff Ha Ha' HR1).
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR2 HR1).
    apply (per_head_iff Ha Hb HR2); exact Hmm'.
  - intros ρ ρ' Hρ; eapply unit_chain_at; [ exact HU | exact HΔ | apply E, Hρ ].
Qed.

End Fixed_GCtx.

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

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Module Lets *)

(** The evaluations of extensions by a slot and by a definition with a
    module part read the definition of an evaluation of a substitution. *)
#[local] Transparent eval_sub.
Lemma eval_sub_wk_extend_mod : forall U Δ σ H φ ρ ρσ h,
    ⟦ sb_wk σ φ : Δ ⟧s ρ ↘ ρσ ->
    ⟦ modexp_wk H φ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
    ⟦ sb_wk (σ ,,ₘ H) φ : ce_mod U :: Δ ⟧s ρ ↘ ρσ ↦ᵐ h ⦂ U.
Proof.
  intros * Hσ HH [| x] Hx.
  - split; [ intros []; discriminate | intros _; exists h; split; [ reflexivity | assumption ] ].
  - cbn [List.length] in Hx.
    split; [ intros Hp; apply (Hσ x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp)
           | intros Hn; apply (Hσ x ltac:(lia)); intros Hp'; exact (Hn (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An evaluated extension by a slot: the tail, and the module. *)
Lemma eval_sub_extend_mod_inv : forall U Δ σ H ρ ρτ,
    ⟦ σ ,,ₘ H : ce_mod U :: Δ ⟧s ρ ↘ ρτ ->
    ⟦ σ : Δ ⟧s ρ ↘ ρτ↯ /\ exists h, env_entry ρτ 0 = de_mod h U /\ ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h.
Proof.
  intros * Hτ; split.
  - intros x Hx; rewrite env_entry_drop, (ctx_entry_tag_drop (ce_mod U));
      change (ctx_entry_unit Δ x) with (ctx_entry_unit (ce_mod U :: Δ) (S x)); split.
    + intros Hp; apply (Hτ (S x) ltac:(cbn; lia)); exact (proj2 (entry_propositional_succ _ _ _ _) Hp).
    + intros Hn; apply (Hτ (S x) ltac:(cbn; lia)); intros Hp; exact (Hn (proj1 (entry_propositional_succ _ _ _ _) Hp)).
  - exact (proj2 (Hτ 0 ltac:(cbn; lia)) (fun Hp => head_not_propositional_mod U _ ρτ↯ (proj1 (entry_propositional_zero_head _ _ _) Hp))).
Qed.

(** A literal's value is the value of its closure. *)
Lemma eval_me_lit_iff : forall Δ D ρ h,
    ⟦ me_lit (gu_mk Δ D) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h <-> ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h.
Proof. intros; split; intros H; [ inversion H; subst; assumption | constructor; exact H ]. Qed.

(** A substitution extended into a slot by the literals of equivalent units. *)
Lemma rel_sub_under_ctx_extend_mod : forall {Γ' Γ σ σ' U U'},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
    Γ' ⊨ˢ σ ,,ₘ me_lit U[σ]ᵘ ≈ σ' ,,ₘ me_lit U'[σ']ᵘ : Γ ▹ₘ U.
Proof.
  intros * Hσj HU HUs HUs'.
  pose proof Hσj as [R' HΓ' R HΓ Hσ Hσs].
  pose proof (rel_modexp_refl_left HU) as HUU.
  pose proof (rel_modexp_refl_right HU) as HU'U'.
  assert (HPd : PER per_dmod) by typeclasses eauto.
  refine (mk_rel_sub_under_ctx _ _ _ _ R' HΓ' _ (per_ctx_env_of_mod HΓ HUU HUs HUs) _ _).
  2:{ intros [| x] Hx; cbn; [ split; eapply gunit_scoped_sub; first [ exact HUs | exact HUs'
                                                                    | intros y Hy; exact (proj1 (Hσs y Hy))
                                                                    | intros y Hy; exact (proj2 (Hσs y Hy)) ]
                              | apply Hσs; cbn in Hx; lia ]. }
  intros Γ'' R'' HΓ'' φ Hφ Hφb ρ ρ' Hρ.
  assert (HP'' : PER R'') by (eapply per_env_PER; exact HΓ'').
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  pose proof (rel_sub_under_ctx_wk_rel Hσj HΓ'' HΓ' Hφ Hφb) as Hσφ.
  destruct (Hσ _ _ HΓ'' _ Hφ Hφb _ _ Hρ) as [x1 x2 x3 x4 Hx1 Hx2 Hx3 Hx4 Hc].
  assert (Hρρ : R'' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R'' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρρ) as Hφρ.
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρ'ρ') as Hφρ'.
  destruct (unit_sub_chain HΓ'' (rel_sub_under_ctx_refl_left Hσφ) HUU _ _ _ _ Hρρ Hx1 Hx1) as (C1 & _).
  destruct (unit_sub_chain HΓ' (rel_sub_under_ctx_refl_left Hσj) HUU _ _ _ _ Hφρ Hx2 Hx2) as (C2 & _).
  destruct (unit_sub_chain HΓ' (rel_sub_under_ctx_refl_right Hσj) HU'U' _ _ _ _ Hφρ' Hx3 Hx3) as (_ & _ & C3).
  destruct (unit_sub_chain HΓ'' (rel_sub_under_ctx_refl_right Hσφ) HU'U' _ _ _ _ Hρ'ρ' Hx4 Hx4) as (_ & _ & C4).
  destruct C1 as [h1 g1 Hh1 Hg1 D1]; destruct C2 as [h2 g2 Hh2 Hg2 D2].
  destruct C3 as [g3 h3 Hg3 Hh3 D3]; destruct C4 as [g4 h4 Hg4 Hh4 D4].
  destruct Hc as (H12 & H23 & H34).
  (* the four heads, tied to both units over each tail *)
  assert (T : forall t h0, R t t -> per_dmod h0 h0 ->
            (exists g, ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ t ↘ g /\ per_dmod h0 g) ->
            tie_mod h0 (me_lit U) t /\ tie_mod h0 (me_lit U') t).
  { intros t h0 Ht Hh0 (g & Hg & Hhg); split; [ exists g; split; assumption |].
    exact (tie_mod_move _ _ _ _ _ (ex_intro _ g (conj Hg Hhg)) (unit_chain_at HU HΓ _ _ Ht)). }
  assert (T' : forall t h0, R t t -> per_dmod h0 h0 ->
            (exists g, ⟦ me_lit U' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ t ↘ g /\ per_dmod h0 g) ->
            tie_mod h0 (me_lit U) t /\ tie_mod h0 (me_lit U') t).
  { intros t h0 Ht Hh0 (g & Hg & Hhg); split; [| exists g; split; assumption ].
    exact (tie_mod_move _ _ _ _ _ (ex_intro _ g (conj Hg Hhg)) (rel_modexp_evals_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Ht))). }
  assert (R11 : R x1 x1) by (etransitivity; [ exact H12 | symmetry; exact H12 ]).
  assert (R22 : R x2 x2) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
  assert (R33 : R x3 x3) by (etransitivity; [ exact H34 | symmetry; exact H34 ]).
  assert (R44 : R x4 x4) by (etransitivity; [ symmetry; exact H34 | exact H34 ]).
  apply (mk_rel_sub (x1 ↦ᵐ h1 ⦂ U) (x2 ↦ᵐ h2 ⦂ U) (x3 ↦ᵐ h3 ⦂ U) (x4 ↦ᵐ h4 ⦂ U)).
  - apply eval_sub_wk_extend_mod; [ exact Hx1 |]; cbn [modexp_wk]; rewrite gunit_wk_sub; exact Hh1.
  - apply eval_sub_extend_mod; [ exact Hx2 | exact Hh2 ].
  - apply eval_sub_extend_mod; [ exact Hx3 | exact Hh3 ].
  - apply eval_sub_wk_extend_mod; [ exact Hx4 |]; cbn [modexp_wk]; rewrite gunit_wk_sub; exact Hh4.
  - cbn [drop_env tl env_mod env_entry hd].
    destruct (T _ _ R11 ltac:(etransitivity; [ exact D1 | symmetry; exact D1 ]) (ex_intro _ g1 (conj Hg1 D1))) as [T1 T1'].
    destruct (T _ _ R22 ltac:(etransitivity; [ exact D2 | symmetry; exact D2 ]) (ex_intro _ g2 (conj Hg2 D2))) as [T2 T2'].
    destruct (T' _ _ R33 ltac:(etransitivity; [ symmetry; exact D3 | exact D3 ]) (ex_intro _ g3 (conj Hg3 (symmetry D3)))) as [T3 T3'].
    destruct (T' _ _ R44 ltac:(etransitivity; [ symmetry; exact D4 | exact D4 ]) (ex_intro _ g4 (conj Hg4 (symmetry D4)))) as [T4 T4'].
    (** The heads store [U], scoped by [Γ]: they read back. *)
    pose proof (gunit_scoped_free_bound _ _ HUs) as Hb.
    repeat split; try assumption; first [ apply mod_entry_readable | exact Hb | eexists; reflexivity ].
Qed.

(** ** Definitions with a Module Part

    The canonical context PER of [Γ ▸ₘ A ≔ M ‖ U] is [per_env_extend_dm]: a
    definition entry's, with the head tied to the closure of [U] as a slot's
    is.  A substitution into it is one into the definition entry and one into
    the slot, read together: the head of the first, the module of the
    second. *)
Lemma per_ctx_env_of_dm : forall {Γ A} {i : nat} {M U R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    gunit_scoped (List.length Γ) U ->
    EF Γ ▸ₘ A ≔ M ‖ U ≈ Γ ▸ₘ A ≔ M ‖ U ∈ per_ctx_env ↘ per_env_extend_dm A M U (List.length Γ) R.
Proof.
  intros * HΓ HA HM HU HsU.
  eapply per_ctx_env_extend_dm; [ exact HΓ | exact (gunit_scoped_free_bound _ _ HsU) | | | | ].
  - exact (rel_exp_of_typ_inversion_simple_at HΓ HA).
  - exact (rel_exp_under_ctx_simple_at_rel HΓ HA HM).
  - exact (rel_exp_of_typ_relevant_at HΓ HA).
  - intros; eapply unit_chain_at; eassumption.
Qed.

(** An evaluation of a substitution extended by a definition with a module
    part, from those of the same substitution extended by its term and by its
    module expression. *)
Lemma eval_sub_dm_combine : forall ed U edm Δ σd σm σdm N H ρ ρd ρm,
    ⟦ σd : ed :: Δ ⟧s ρ ↘ ρd -> ⟦ σm : ce_mod U :: Δ ⟧s ρ ↘ ρm ->
    (forall x, σdm (S x) = σd (S x)) ->
    σd 0 = se_exp N -> σm 0 = se_mod H -> σdm 0 = se_dm N H ->
    ~ head_propositional gc_deps gc_stack ed Δ ρd↯ ->
    ~ head_propositional gc_deps gc_stack edm Δ ρd↯ ->
    ⟦ σdm : edm :: Δ ⟧s ρ ↘ de_dm (ρd 0) (centry_tag edm Δ ρd↯) (env_mod ρm 0) (centry_slot_unit edm) :: ρd↯.
Proof.
  intros * Hed Hem Ht Hd Hm Hdm Hnd Hndm [| x] Hx.
  - split; [ intros Hp; exfalso; apply Hndm; exact (proj1 (entry_propositional_head _ _ _ _) Hp) |].
    intros _; rewrite ctx_entry_tag_head.
    pose proof (proj2 (Hed 0 ltac:(cbn; lia)) (fun Hp => Hnd (proj1 (entry_propositional_zero_head _ _ _) Hp))) as Hed0.
    pose proof (proj2 (Hem 0 ltac:(cbn; lia)) (fun Hp => head_not_propositional_mod U _ _ (proj1 (entry_propositional_zero_head _ _ _) Hp))) as Hem0.
    rewrite Hd in Hed0; rewrite Hm in Hem0; rewrite Hdm.
    destruct Hed0 as (n & En & Hn); destruct Hem0 as (h & Eh & Hh).
    exists n, h; unfold env_var, env_mod; rewrite En, Eh; cbn [env_entry hd]; repeat split; assumption.
  - cbn [List.length] in Hx; rewrite Ht; cbn [env_entry]; rewrite env_entry_drop.
    rewrite ctx_entry_tag_succ, (ctx_entry_tag_drop ed).
    change (ctx_entry_unit (edm :: Δ) (S x)) with (ctx_entry_unit (ed :: Δ) (S x)); split.
    + intros Hp; apply (Hed (S x) ltac:(cbn; lia)).
      apply (proj2 (entry_propositional_succ _ _ _ _)); exact (proj1 (entry_propositional_extend _ _ _ _ _) Hp).
    + intros Hn; apply (Hed (S x) ltac:(cbn; lia)); intros Hp; apply Hn.
      apply (proj2 (entry_propositional_extend _ _ _ _ _)); exact (proj1 (entry_propositional_succ _ _ _ _) Hp).
Qed.

(** Conversely, an evaluation of a substitution extended by a definition
    with a module part gives those of the substitution extended by its term
    and by its module expression, and the environment is the one their
    parts make. *)
Lemma eval_sub_dm_split : forall ed U edm Δ σd σm σdm N H ρ e,
    ⟦ σdm : edm :: Δ ⟧s ρ ↘ e ->
    (forall x, σdm (S x) = σd (S x)) -> (forall x, σm (S x) = σd (S x)) ->
    σd 0 = se_exp N -> σm 0 = se_mod H -> σdm 0 = se_dm N H ->
    ~ head_propositional gc_deps gc_stack edm Δ e↯ ->
    ~ head_propositional gc_deps gc_stack ed Δ e↯ ->
    ⟦ σd : ed :: Δ ⟧s ρ ↘ de_term (e 0) (centry_tag ed Δ e↯) :: e↯ /\
    ⟦ σm : ce_mod U :: Δ ⟧s ρ ↘ de_mod (env_mod e 0) U :: e↯ /\
    env_eq e (de_dm (e 0) (centry_tag edm Δ e↯) (env_mod e 0) (centry_slot_unit edm) :: e↯).
Proof.
  intros * He Ht Htm Hd Hm Hdm Hndm Hnd.
  pose proof (proj2 (He 0 ltac:(cbn; lia)) (fun Hp => Hndm (proj1 (entry_propositional_zero_head _ _ _) Hp))) as H0.
  rewrite Hdm, ctx_entry_tag_head in H0; destruct H0 as (n & h & En & Hn & Hh).
  assert (Ev : e 0 = n) by (unfold env_var; rewrite En; reflexivity).
  assert (Emod : env_mod e 0 = h) by (unfold env_mod; rewrite En; reflexivity).
  (** The tails of the three environments are the same, so are their
      propositional entries after the head. *)
  assert (Hs : forall e1 e2 d d' x,
             entry_propositional gc_deps gc_stack (e1 :: Δ) (d :: e↯) (S x) <->
             entry_propositional gc_deps gc_stack (e2 :: Δ) (d' :: e↯) (S x))
    by (intros; rewrite !entry_propositional_extend; reflexivity).
  assert (Hs' : forall e1 d x,
             entry_propositional gc_deps gc_stack (e1 :: Δ) (d :: e↯) (S x) <->
             entry_propositional gc_deps gc_stack (edm :: Δ) e (S x))
    by (intros; rewrite entry_propositional_extend, entry_propositional_succ; reflexivity).
  rewrite Ev, Emod; split; [| split ].
  - intros [| x] Hx.
    + split; [ intros Hp; exfalso; exact (Hnd (proj1 (entry_propositional_head _ _ _ _) Hp)) |].
      intros _; rewrite Hd, ctx_entry_tag_head; exists n; split; [ reflexivity | exact Hn ].
    + rewrite <- Ht; rewrite env_entry_cons_succ, env_entry_drop.
      rewrite ctx_entry_tag_succ, (ctx_entry_tag_drop edm).
      change (ctx_entry_unit (ed :: Δ) (S x)) with (ctx_entry_unit (edm :: Δ) (S x)); split.
      * intros Hp; apply (He (S x) Hx); exact (proj1 (Hs' _ _ _) Hp).
      * intros Hn'; apply (He (S x) Hx); intros Hp; apply Hn'; exact (proj2 (Hs' ed (de_term n (centry_tag ed Δ e↯)) x) Hp).
  - intros [| x] Hx.
    + split; [ intros [T HT]; discriminate HT |].
      intros _; rewrite Hm; exists h; split; [ reflexivity | exact Hh ].
    + rewrite Htm, <- Ht; rewrite env_entry_cons_succ, env_entry_drop.
      rewrite ctx_entry_tag_succ, (ctx_entry_tag_drop edm).
      change (ctx_entry_unit (ce_mod U :: Δ) (S x)) with (ctx_entry_unit (edm :: Δ) (S x)); split.
      * intros Hp; apply (He (S x) Hx); exact (proj1 (Hs' _ _ _) Hp).
      * intros Hn'; apply (He (S x) Hx); intros Hp; apply Hn'; exact (proj2 (Hs' (ce_mod U) (de_mod h U) x) Hp).
  - intros [| x]; [ exact En | reflexivity ].
Qed.
#[local] Opaque eval_sub.

(** A head tied to a unit over one tail is tied to it over any tail with the
    same entries on the context. *)
Lemma tie_mod_env_eq : forall {Γ U R m t t'},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    R t' t' -> env_agree_upto (List.length Γ) t t' ->
    tie_mod m (me_lit U) t -> tie_mod m (me_lit U) t'.
Proof.
  intros * HΓ HU Ht' Heq Hm.
  assert (Htt : R t t') by (eapply (per_ctx_env_resp_agree HΓ); [ symmetry; exact Heq | reflexivity | exact Ht' ]).
  exact (tie_mod_move _ _ _ _ _ Hm (unit_chain_at HU HΓ _ _ Htt)).
Qed.

(** Two environments related at a definition entry and two related at a
    slot, with the same tails entry by entry, give two related at the
    definition with a module part: the heads of the first, the modules of
    the second.  The assumption context [Γ ▹{κ} A], of any kind, only
    witnesses that the heads read back at [A] ([per_head_dm_readable]). *)
Lemma per_env_extend_dm_combine : forall {Γ κ A M U R RA a b ma mb},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Γ ▹{κ} A ≈ Γ ▹{κ} A ∈ per_ctx_env ↘ RA ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    gunit_scoped (List.length Γ) U ->
    per_env_extend_def A M R a b ->
    per_ctx_env_mod_rel R (List.length Γ) U U ma mb ->
    env_agree_upto (List.length Γ) ma↯ a↯ -> env_agree_upto (List.length Γ) mb↯ b↯ ->
    per_env_extend_dm A M U (List.length Γ) R
      (de_dm (a 0) (centry_tag (ce_dm A M U) Γ a↯) (env_mod ma 0) (centry_slot_unit (ce_dm A M U)) :: a↯)
      (de_dm (b 0) (centry_tag (ce_dm A M U) Γ b↯) (env_mod mb 0) (centry_slot_unit (ce_dm A M U)) :: b↯).
Proof.
  intros * HΓ HΓA HUU HsU Hab Hm Qa Qb.
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  destruct Hab as [[Hab1 Hab2 _ _ _ _] Hta Htb].
  destruct Hm as [_ Ta _ Tb _ _ _ _ _].
  assert (Raa : R a↯ a↯) by (etransitivity; [ exact Hab1 | symmetry; exact Hab1 ]).
  assert (Rbb : R b↯ b↯) by (etransitivity; [ symmetry; exact Hab1 | exact Hab1 ]).
  (** The heads read back at [A] over their tails, their unit scoped by
      [Γ] ([per_head_dm_readable]). *)
  destruct (per_head_dm_readable (h := env_mod ma 0) (h' := env_mod mb 0) (U := U) (List.length Γ) HΓA HΓ Hab1 Hab2
              (gunit_scoped_free_bound _ _ HsU)) as [Rda Rdb].
  econstructor; [ exact Hab1 | exact Hab2 | exact Hta | exact Htb
               | exact (tie_mod_env_eq HΓ HUU Raa Qa Ta) | exact (tie_mod_env_eq HΓ HUU Rbb Qb Tb)
               | exact Rda | exact Rdb | do 2 eexists; reflexivity | do 2 eexists; reflexivity ].
Qed.

(** A substitution extended into a definition with a module part by the
    term and the literal of related parts. *)
Lemma rel_sub_under_ctx_extend_dm : forall {Γ' Γ σ σ' A} {i : nat} {M M' U U'},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
    gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
    Γ' ⊨ˢ σ ,,ᵈ M[σ] ‖ me_lit U[σ]ᵘ ≈ σ' ,,ᵈ M'[σ'] ‖ me_lit U'[σ']ᵘ : Γ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * Hσj HA HM HU HMs HMs' HUs HUs'.
  pose proof (rel_sub_under_ctx_extend_sub_def Hσj HA HM HMs HMs') as [Rd1 HΓ'd Rd HΓd Hd Hds].
  pose proof (rel_sub_under_ctx_extend_mod Hσj HU HUs HUs') as [Rm1 HΓ'm Rm HΓm Hm Hms].
  pose proof Hσj as [R' HΓ' R HΓ _ Hσs].
  pose proof (rel_modexp_refl_left HU) as HUU.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (Ed : Rd <~> per_env_extend_def A M R)
    by (eapply per_ctx_env_right_irrel; [ exact HΓd | exact (per_ctx_env_of_def HΓ HA HMl) ]).
  assert (Em : Rm <~> per_ctx_env_mod_rel R (List.length Γ) U U)
    by (eapply per_ctx_env_right_irrel; [ exact HΓm | exact (per_ctx_env_of_mod HΓ HUU HUs HUs) ]).
  pose proof (per_ctx_env_of_typ (κ := ak_relevant) HΓ (rel_type_of_typ HA)) as HΓA.
  assert (E1 : Rd1 <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : Rm1 <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_sub_under_ctx _ _ _ _ R' HΓ' (per_env_extend_dm A M U (List.length Γ) R) (per_ctx_env_of_dm HΓ HA HMl HUU HUs) _ _).
  2:{ intros [| x] Hx; [| exact (Hds (S x) Hx) ].
      destruct (Hds 0 ltac:(cbn; lia)) as [Sd Sd'], (Hms 0 ltac:(cbn; lia)) as [Sm Sm'].
      cbn in Sd, Sd', Sm, Sm' |- *; split; split; assumption. }
  intros Γ'' R'' HΓ'' φ Hφ Hφb ρ ρ' Hρ.
  destruct (Hd _ _ HΓ'' _ (proj2 (rel_wk_morphism φ _ _ (reflexivity R'') _ _ E1) Hφ) Hφb _ _ Hρ)
    as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Dchain].
  destruct (Hm _ _ HΓ'' _ (proj2 (rel_wk_morphism φ _ _ (reflexivity R'') _ _ E2) Hφ) Hφb _ _ Hρ)
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Cm].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (Ed a b) H)) in Dchain.
  apply (rel_chain_mono _ _ (fun a b H => proj1 (Em a b) H)) in Cm.
  (** The tails of the two evaluations of each side have the same entries. *)
  assert (Q1 : env_agree_upto (List.length Γ) m1↯ d1↯)
    by (eapply functional_eval_sub; [ exact (eval_sub_shift_pre _ _ _ _ _ Hm1) | exact (eval_sub_shift_pre _ _ _ _ _ Hd1) ]).
  assert (Q2 : env_agree_upto (List.length Γ) m2↯ d2↯)
    by (eapply functional_eval_sub; [ exact (eval_sub_shift_pre _ _ _ _ _ Hm2) | exact (eval_sub_shift_pre _ _ _ _ _ Hd2) ]).
  assert (Q3 : env_agree_upto (List.length Γ) m3↯ d3↯)
    by (eapply functional_eval_sub; [ exact (eval_sub_shift_pre _ _ _ _ _ Hm3) | exact (eval_sub_shift_pre _ _ _ _ _ Hd3) ]).
  assert (Q4 : env_agree_upto (List.length Γ) m4↯ d4↯)
    by (eapply functional_eval_sub; [ exact (eval_sub_shift_pre _ _ _ _ _ Hm4) | exact (eval_sub_shift_pre _ _ _ _ _ Hd4) ]).
  (** [A] is a type of a universe: no head is a proof. *)
  assert (Hnp : forall t t', Dom t ≈ t' ∈ R ->
                  ~ head_propositional gc_deps gc_stack (ce_def A M) Γ t /\
                  ~ head_propositional gc_deps gc_stack (ce_dm A M U) Γ t)
    by (intros t t' Ht; split;
        [ exact (proj1 (head_not_propositional_of_typ (e := ce_def A M) HΓ eq_refl HA _ _ Ht))
        | exact (proj1 (head_not_propositional_of_typ (e := ce_dm A M U) HΓ eq_refl HA _ _ Ht)) ]).
  destruct Dchain as (D12 & D23 & D34); destruct Cm as (M12 & M23 & M34).
  assert (T1 : Dom d1↯ ≈ d2↯ ∈ R) by (destruct D12 as [[? _ _ _ _ _] _ _]; assumption).
  assert (T2 : Dom d2↯ ≈ d3↯ ∈ R) by (destruct D23 as [[? _ _ _ _ _] _ _]; assumption).
  assert (T3 : Dom d3↯ ≈ d4↯ ∈ R) by (destruct D34 as [[? _ _ _ _ _] _ _]; assumption).
  assert (T4 : Dom d4↯ ≈ d3↯ ∈ R) by (symmetry; exact T3).
  apply (mk_rel_sub (de_dm (d1 0) (centry_tag (ce_dm A M U) Γ d1↯) (env_mod m1 0) (centry_slot_unit (ce_dm A M U)) :: d1↯)
                    (de_dm (d2 0) (centry_tag (ce_dm A M U) Γ d2↯) (env_mod m2 0) (centry_slot_unit (ce_dm A M U)) :: d2↯)
                    (de_dm (d3 0) (centry_tag (ce_dm A M U) Γ d3↯) (env_mod m3 0) (centry_slot_unit (ce_dm A M U)) :: d3↯)
                    (de_dm (d4 0) (centry_tag (ce_dm A M U) Γ d4↯) (env_mod m4 0) (centry_slot_unit (ce_dm A M U)) :: d4↯)).
  - eapply eval_sub_dm_combine; [ eassumption | eassumption | intros; reflexivity | reflexivity | reflexivity | reflexivity
                                | exact (proj1 (Hnp _ _ T1)) | exact (proj2 (Hnp _ _ T1)) ].
  - eapply eval_sub_dm_combine; [ eassumption | eassumption | intros; reflexivity | reflexivity | reflexivity | reflexivity
                                | exact (proj1 (Hnp _ _ T2)) | exact (proj2 (Hnp _ _ T2)) ].
  - eapply eval_sub_dm_combine; [ eassumption | eassumption | intros; reflexivity | reflexivity | reflexivity | reflexivity
                                | exact (proj1 (Hnp _ _ T3)) | exact (proj2 (Hnp _ _ T3)) ].
  - eapply eval_sub_dm_combine; [ eassumption | eassumption | intros; reflexivity | reflexivity | reflexivity | reflexivity
                                | exact (proj1 (Hnp _ _ T4)) | exact (proj2 (Hnp _ _ T4)) ].
  - apply rel_chain_4; eapply per_env_extend_dm_combine; eassumption.
Qed.

(** Two environments related at a definition entry, their heads
    definitions with a module part whose modules are tied to the value of
    [U] over the tails, are related at the definition with a module part
    once their heads are stored at its unit.  The environments [q σ]
    evaluates to from [Γ' ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]] to [Γ ▸ A ≔ M] are such:
    their heads [de_dm v t h gunit_default] are the source's, retagged at
    the definition; stored at [U] instead they are the values of [q σ] at
    [Γ ▸ₘ A ≔ M ‖ U].  As in [per_env_extend_dm_combine], the assumption
    context [Γ ▹{κ} A] is of any kind. *)
Lemma per_env_extend_dm_of_def : forall {Γ κ A M U R RA a b},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Γ ▹{κ} A ≈ Γ ▹{κ} A ∈ per_ctx_env ↘ RA ->
    gunit_scoped (List.length Γ) U ->
    per_env_extend_def A M R a b ->
    (exists t U0, env_entry a 0 = de_dm (a 0) t (env_mod a 0) U0) ->
    (exists t U0, env_entry b 0 = de_dm (b 0) t (env_mod b 0) U0) ->
    tie_mod (env_mod a 0) (me_lit U) a↯ -> tie_mod (env_mod b 0) (me_lit U) b↯ ->
    per_env_extend_dm A M U (List.length Γ) R
      (retag_entry (centry_tag (ce_dm A M U) Γ a↯) (centry_slot_unit (ce_dm A M U)) (env_entry a 0) :: a↯)
      (retag_entry (centry_tag (ce_dm A M U) Γ b↯) (centry_slot_unit (ce_dm A M U)) (env_entry b 0) :: b↯).
Proof.
  intros * HΓ HΓA HsU Hab (ta & Ua & Ka) (tb & Ub & Kb) Ta Tb.
  destruct Hab as [[Hab1 Hab2 _ _ _ _] Hta Htb].
  (** The heads' values and modules are kept; they read back at [A] over
      their tails, the unit scoped by [Γ] ([per_head_dm_readable]). *)
  destruct (per_head_dm_readable (h := env_mod a 0) (h' := env_mod b 0) (U := U) (List.length Γ) HΓA HΓ Hab1 Hab2
              (gunit_scoped_free_bound _ _ HsU)) as [Rda Rdb].
  rewrite Ka, Kb; cbn [retag_entry centry_slot_unit centry_unit].
  econstructor; cbn [drop_env tl env_mod env_entry hd];
    [ exact Hab1 | exact Hab2 | exact Hta | exact Htb | exact Ta | exact Tb
    | exact Rda | exact Rdb | do 2 eexists; reflexivity | do 2 eexists; reflexivity ].
Qed.

(** The canonical context PER of a definition with a module part, along a
    substitution. *)
Lemma per_ctx_env_of_dm_sub : forall {Γ Δ σ σ' A} {i : nat} {M U R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i -> Δ ⊨ M : A -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    gunit_scoped (List.length Δ) U ->
    EF Γ ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]ᵘ ≈ Γ ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]ᵘ ∈ per_ctx_env
      ↘ per_env_extend_dm A[σ] M[σ] U[σ]ᵘ (List.length Γ) R.
Proof.
  intros * HΓ Hσj HA HM HU HsU.
  eapply per_ctx_env_extend_dm; [ exact HΓ | exact (gunit_scoped_free_bound _ _ (gunit_scoped_rel_sub Hσj HsU))
                                | exact (rel_exp_of_typ_sub_simple HΓ Hσj HA)
                                | exact (rel_exp_under_ctx_sub_simple HΓ Hσj HA HM)
                                | exact (rel_exp_of_typ_sub_relevant HΓ Hσj HA) |].
  intros ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [R3 [HΓ3 Hs]]]].
  assert (E : R <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (ρσ & ρ'σ & Hev & Hev' & _).
  destruct (unit_sub_chain HΓ Hσσ HU _ _ _ _ Hρ Hev Hev') as (C1 & C2 & C3).
  eapply rel_modexp_evals_trans; [ exact C1 | eapply rel_modexp_evals_trans; [ exact C2 | exact C3 ] ].
Qed.

(** [q σ] into a definition with a module part.  The term parts are those
    of [q σ] into the definition entry [Γ ▸ A ≔ M], from the source read as
    one; the modules are the source's, tied to the value of [U] over the
    tails ([rel_sub_q_tails_tied]).  At a source environment
    [de_dm v t h U1 :: ρ0] of [Γ' ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]], [q σ] stores
    [de_dm v T h U] at [Γ ▸ₘ A ≔ M ‖ U], with [T] the type [A] over the
    tail: the head [de_dm v T h gunit_default] it stores at the definition
    entry, at the unit [U] ([per_env_extend_dm_of_def]). *)
Lemma rel_sub_under_ctx_q_dm : forall {Γ' Γ σ σ' A} {i : nat} {M U},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ A : Typeω@i -> Γ ⊨ M : A -> Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    gunit_scoped (List.length Γ) U ->
    Γ' ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]ᵘ ⊨ˢ q σ ≈ q σ' : Γ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * Hσj HA HM HU HsU.
  pose proof Hσj as [R' HΓ' R HΓ _ Hσs].
  pose proof (per_ctx_env_of_dm_sub HΓ' Hσj HA HM HU HsU) as HΓ'dm.
  pose proof (per_ctx_env_of_def HΓ HA HM) as HΓdef.
  pose proof (per_ctx_env_of_typ (κ := ak_relevant) HΓ (rel_type_of_typ HA)) as HΓA.
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  (** The source's environments are those of the definition entry of its
      term part: its type is of a universe, so no head is a proof. *)
  assert (Hqd : Γ' ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]ᵘ ⊨ˢ q σ ≈ q σ' : Γ ▸ A ≔ M).
  { apply (rel_sub_under_ctx_q_def_gen Hσj (rel_type_of_typ HA) (rel_type_evaluated_of_typ HA) HM HΓ'dm).
    - (** The term part's clauses: its type is of a universe, so no head is
          a proof. *)
      intros RΓ0 HΓ0 e e' He.
      assert (PER R') by (eapply per_env_PER; eassumption).
      pose proof He as [Ht _ _ _ _ _ _ _ _ _].
      assert (Ht' : Dom e'↯ ≈ e'↯ ∈ R') by (etransitivity; [ symmetry |]; exact Ht).
      destruct (per_env_extend_dm_clauses He
                  (fun Hp => not_rel_typ_propositional_of_typ_sub HΓ' Hσj HA _ _ Ht Hp)
                  (fun Hp => not_rel_typ_propositional_of_typ_sub HΓ' Hσj HA _ _ Ht' Hp)) as [Ht0 Hh Hl Hr].
      constructor; [ exact (proj1 (per_ctx_env_right_irrel _ _ _ _ _ HΓ' HΓ0 _ _) Ht0) | exact Hh | exact Hl | exact Hr ].
    - (** The term part's tie to [M[σ]] *)
      intros e e' [_ _ Tl _ _ _ _ _ _ _]; exact Tl. }
  pose proof Hqd as [Rd1 HΓd1 Rd HΓd Hd _].
  assert (Ed : Rd <~> per_env_extend_def A M R) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E1 : Rd1 <~> per_env_extend_dm A[σ] M[σ] U[σ]ᵘ (List.length Γ') R') by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_sub_under_ctx _ _ _ _ _ HΓ'dm _ (per_ctx_env_of_dm HΓ HA HM HU HsU) _ _);
    [| intros x Hx; split; eapply sb_q_bound; first [ exact Hx | intros y Hy; exact (proj1 (Hσs y Hy))
                                                   | intros y Hy; exact (proj2 (Hσs y Hy)) ] ].
  intros Γ'' R'' HΓ'' ψ Hψ Hψb ρ ρ' Hρ.
  destruct (rel_sub_q_tails_tied Hσj HU HΓ HΓ'dm
              (fun ρ0 ρ0' H0 => conj (per_env_extend_dm_tie_left _ _ _ _ _ _ _ H0) (per_env_extend_dm_tie_right _ _ _ _ _ _ _ H0))
              _ _ HΓ'' _ Hψ Hψb _ _ Hρ)
    as (x1 & y1 & y4 & x4 & Hx1 & Hy1 & Hy4 & Hx4 & Htails & Hm & Hm').
  destruct (Hd _ _ HΓ'' _ (proj2 (rel_wk_morphism ψ _ _ (reflexivity R'') _ _ E1) Hψ) Hψb _ _ Hρ)
    as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Dchain].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (Ed a b) H)) in Dchain.
  (** The source's heads are definitions with a module part. *)
  destruct (Hψ _ _ Hρ) as [_ _ _ _ _ _ _ _ (tyl & Ul & Kl) (tyr & Ur & Kr)].
  rewrite (eval_wk_app_entry ψ), (eval_wk_app_mod ψ) in Kl, Kr.
  (** The values of [q σ] at the definition entry, from the tails; they
      agree with the ones the restricted judgment relates. *)
  pose proof (eval_sub_wk_q (ce_def A M) _ _ _ _ _ Hx1) as Ha1.
  pose proof (eval_sub_q (ce_def A M) _ _ _ _ Hy1) as Ha2.
  pose proof (eval_sub_q (ce_def A M) _ _ _ _ Hy4) as Ha3.
  pose proof (eval_sub_wk_q (ce_def A M) _ _ _ _ _ Hx4) as Ha4.
  rewrite (eval_wk_app_entry ψ) in Ha2, Ha3.
  pose proof (functional_eval_sub _ _ _ _ _ Hd1 Ha1) as Q1.
  pose proof (functional_eval_sub _ _ _ _ _ Hd2 Ha2) as Q2.
  pose proof (functional_eval_sub _ _ _ _ _ Hd3 Ha3) as Q3.
  pose proof (functional_eval_sub _ _ _ _ _ Hd4 Ha4) as Q4.
  destruct Dchain as (D12 & D23 & D34).
  apply (per_ctx_env_resp_agree HΓdef _ _ _ _ Q1 Q2) in D12.
  apply (per_ctx_env_resp_agree HΓdef _ _ _ _ Q2 Q3) in D23.
  apply (per_ctx_env_resp_agree HΓdef _ _ _ _ Q3 Q4) in D34.
  apply (mk_rel_sub (retag_entry (centry_tag (ce_dm A M U) Γ x1) (centry_slot_unit (ce_dm A M U)) (env_entry ρ (ψ 0)) :: x1)
                    (retag_entry (centry_tag (ce_dm A M U) Γ y1) (centry_slot_unit (ce_dm A M U)) (env_entry ρ (ψ 0)) :: y1)
                    (retag_entry (centry_tag (ce_dm A M U) Γ y4) (centry_slot_unit (ce_dm A M U)) (env_entry ρ' (ψ 0)) :: y4)
                    (retag_entry (centry_tag (ce_dm A M U) Γ x4) (centry_slot_unit (ce_dm A M U)) (env_entry ρ' (ψ 0)) :: x4));
    [ exact (eval_sub_wk_q (ce_dm A M U) _ _ _ _ _ Hx1)
    | rewrite <- (eval_wk_app_entry ψ); exact (eval_sub_q (ce_dm A M U) _ _ _ _ Hy1)
    | rewrite <- (eval_wk_app_entry ψ); exact (eval_sub_q (ce_dm A M U) _ _ _ _ Hy4)
    | exact (eval_sub_wk_q (ce_dm A M U) _ _ _ _ _ Hx4) | ].
  (** Each link: the link at the definition entry, the heads stored at [U]. *)
  assert (Hk : forall e, e = env_entry ρ (ψ 0) \/ e = env_entry ρ' (ψ 0) -> forall t0,
             exists t U0, env_entry (retag_entry t0 (centry_slot_unit (ce_def A M)) e :: nil) 0
                          = de_dm (env_var (retag_entry t0 (centry_slot_unit (ce_def A M)) e :: nil) 0) t
                                  (env_mod (retag_entry t0 (centry_slot_unit (ce_def A M)) e :: nil) 0) U0)
    by (intros e [-> | ->] t0; [ rewrite Kl | rewrite Kr ]; do 2 eexists; reflexivity).
  assert (Hlink : forall a b ea eb,
             (ea = env_entry ρ (ψ 0) \/ ea = env_entry ρ' (ψ 0)) -> (eb = env_entry ρ (ψ 0) \/ eb = env_entry ρ' (ψ 0)) ->
             tie_mod (env_mod (ea :: nil) 0) (me_lit U) a -> tie_mod (env_mod (eb :: nil) 0) (me_lit U) b ->
             per_env_extend_def A M R (retag_entry (centry_tag (ce_def A M) Γ a) (centry_slot_unit (ce_def A M)) ea :: a)
                                      (retag_entry (centry_tag (ce_def A M) Γ b) (centry_slot_unit (ce_def A M)) eb :: b) ->
             per_env_extend_dm A M U (List.length Γ) R
               (retag_entry (centry_tag (ce_dm A M U) Γ a) (centry_slot_unit (ce_dm A M U)) ea :: a)
               (retag_entry (centry_tag (ce_dm A M U) Γ b) (centry_slot_unit (ce_dm A M U)) eb :: b)).
  { intros * Ea Eb Ta Tb Hab.
    pose proof (per_env_extend_dm_of_def (U := U) HΓ HΓA HsU Hab) as Hdm.
    rewrite <- (retag_entry_twice (centry_tag (ce_dm A M U) Γ a) (centry_slot_unit (ce_dm A M U))
                  (centry_tag (ce_def A M) Γ a) (centry_slot_unit (ce_def A M)) ea),
            <- (retag_entry_twice (centry_tag (ce_dm A M U) Γ b) (centry_slot_unit (ce_dm A M U))
                  (centry_tag (ce_def A M) Γ b) (centry_slot_unit (ce_def A M)) eb).
    apply Hdm.
    - destruct (Hk _ Ea (centry_tag (ce_def A M) Γ a)) as (t & U0 & Et); exists t, U0; exact Et.
    - destruct (Hk _ Eb (centry_tag (ce_def A M) Γ b)) as (t & U0 & Et); exists t, U0; exact Et.
    - unfold env_mod in Ta |- *; cbn [env_entry] in Ta |- *; destruct Ea as [-> | ->];
        [ rewrite Kl in Ta |- * | rewrite Kr in Ta |- * ]; exact Ta.
    - unfold env_mod in Tb |- *; cbn [env_entry] in Tb |- *; destruct Eb as [-> | ->];
        [ rewrite Kl in Tb |- * | rewrite Kr in Tb |- * ]; exact Tb. }
  assert (Tm : forall t, In t (x1 :: y1 :: nil) -> tie_mod (env_mod (env_entry ρ (ψ 0) :: nil) 0) (me_lit U) t)
    by (intros t Ht; exact (Hm t Ht)).
  assert (Tm' : forall t, In t (y4 :: x4 :: nil) -> tie_mod (env_mod (env_entry ρ' (ψ 0) :: nil) 0) (me_lit U) t)
    by (intros t Ht; exact (Hm' t Ht)).
  apply rel_chain_4; apply Hlink; first [ left; reflexivity | right; reflexivity | apply Tm; solve_in | apply Tm'; solve_in | assumption ].
Qed.

(** The instance [B[Id,,ₘ⌜U⌝]] against a module [let] whose unit [U'] is
    equivalent to [U] and whose body [B'] is related to [B]: the links come
    from [B] along [σ,,ₘ⌜U[σ]⌝] and [Id,,ₘ⌜U⌝], from [B ≈ B'], and from [B']
    along [q σ'], bridged at the heads, which the slot PER ties to the
    values of the units. *)
Lemma rel_exp_let_mod_gen : forall {Γ U U' B B' C},
    Γ ⊨ᵘ U ≈ U' ->
    Γ ▹ₘ U ⊨ B ≈ B' : C ->
    gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
    Γ ⊨ B[Id ,,ₘ me_lit U] ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U].
Proof.
  intros * [HU _ _] HB HUs HUs'.
  pose proof (rel_modexp_refl_left HU) as HUl.
  pose proof (rel_modexp_refl_right HU) as HUr.
  pose proof HU as [R HΓ _].
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  pose proof (per_ctx_env_of_mod HΓ HUl HUs HUs) as HΓU.
  pose proof (per_ctx_env_of_mod HΓ HUr HUs' HUs') as HΓU'.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  (** [B'] in the context of the right-hand unit. *)
  assert (HB'r : Γ ▹ₘ U' ⊨ B' ≈ B' : C).
  { eapply rel_exp_under_ctx_restrict;
      [ exact HΓU' | exact HΓU | | cbn; lia
      | intros ? ? _ [| x] _; split; intros [T HT E HE a Ea Hp]; econstructor; eassumption | exact HBr ].
    intros ρ ρ' [Ht T1 _ T3 _ Hrl Hrr Hkl Hkr].
    assert (Htt : R ρ↯ ρ↯) by (etransitivity; [ exact Ht | symmetry; exact Ht ]).
    assert (Ht't' : R ρ'↯ ρ'↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]).
    pose proof (tie_mod_move _ _ _ _ _ T1 (rel_modexp_evals_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Htt))) as T1'.
    pose proof (tie_mod_move _ _ _ _ _ T3 (rel_modexp_evals_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Ht't'))) as T3'.
    constructor; assumption. }
  destruct (rel_exp_under_ctx_simple_full_at HΓU HB) as [kX HX].
  destruct (rel_exp_under_ctx_simple_full_at HΓU HBl) as [kY HY].
  destruct (rel_exp_under_ctx_simple_full_at HΓU' HB'r) as [kZ HZ].
  pose proof HBl as [? ? k HBlgen].
  pose proof HB'r as [? ? k3 HB'gen].
  refine (mk_rel_exp_under_ctx _ _ _ _ R HΓ k _).
  intros Γ' R' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρσ : R ρσ ρ'σ') by (eapply rel_sub_under_ctx_at'; eassumption).
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (Hσσ' : R ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  assert (Hσ'σ'' : R ρ'σ' ρ'σ') by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  (** The values of the literals. *)
  destruct (unit_sub_chain HΓ' Hσσ HUl _ _ _ _ Hρρ Hev Hev) as ([u1 u2 Hu1 Hu2 Du12] & _).
  destruct (unit_sub_chain HΓ' Hσ'σ' HUr _ _ _ _ Hρ'ρ' Hev' Hev') as (_ & _ & [v3 v4 Hv3 Hv4 Dv34]).
  destruct (unit_chain_at HU HΓ _ _ Hσ'σ'') as [w2 w3 Hw2 Hw3 Dw].
  (** *** The Instances *)
  pose proof (rel_sub_under_ctx_extend_mod Hσj HUl HUs HUs) as Hτ.
  pose proof (rel_sub_under_ctx_extend_mod (rel_sub_id (ex_intro _ _ HΓ)) HUl HUs HUs) as Hid.
  rewrite gunit_sub_id in Hid.
  destruct (unit_sub_chain HΓ' Hσ'σ' HUl _ _ _ _ Hρ'ρ' Hev' Hev') as ([u4 u3 Hu4 Hu3 Du43] & _).
  pose proof (functional_eval_modexp _ _ _ _ Hw2 Hu3) as ->.
  pose proof (functional_eval_modexp _ _ _ _ Hw3 Hv3) as ->.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend_mod _ _ _ _ _ _ _ Hev Hu1)
              (eval_sub_extend_mod _ _ _ _ _ _ _ Hev' Hu4))
    as [R1 [HI1t HI1e]].
  pose proof HI1t as [c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain].
  (** The heads the substitutions and the [let]s bind read back: they store
      the units of the slots, or the units written, scoped by the
      contexts. *)
  assert (Hrs : forall h, head_readable (List.length Γ) (de_mod h U))
    by (intros h; split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HUs) ]).
  assert (Hrs' : forall h, head_readable (List.length Γ) (de_mod h U'))
    by (intros h; split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HUs') ]).
  pose proof Hσj as [? _ ? _ _ Hσs].
  assert (HU'σ's : gunit_scoped (List.length Γ') U'[σ']ᵘ)
    by (eapply gunit_scoped_sub; [ exact HUs' | intros x Hx; exact (proj2 (Hσs x Hx)) ]).
  assert (HrU' : head_readable (List.length Γ) (de_mod v3 U'))
    by (split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HUs') ]).
  assert (HrU'σ' : head_readable (List.length Γ') (de_mod v4 U'[σ']ᵘ))
    by (split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HU'σ's) ]).
  (** [Id,,ₘ⌜U⌝] evaluates to the extensions of the retagged environments;
      the instance is read at the extensions of [ρσ] and [ρ'σ'] themselves
      ([rel_exp_body_of_retagged]). *)
  assert (Tu2 : tie_mod u2 (me_lit U) ρσ) by (exists u2; split; [ exact Hu2 | etransitivity; [ symmetry; exact Du12 | exact Du12 ] ]).
  assert (Tu2U' : tie_mod u2 (me_lit U') ρσ)
    by (exact (tie_mod_move _ _ _ _ _ Tu2 (unit_chain_at HU HΓ _ _ Hσσ'))).
  assert (Tu3 : tie_mod u3 (me_lit U) ρ'σ') by (exists u3; split; [ exact Hu3 | etransitivity; [ symmetry; exact Du43 | exact Du43 ] ]).
  assert (Tu3U' : tie_mod u3 (me_lit U') ρ'σ')
    by (exact (tie_mod_move _ _ _ _ _ Tu3 (unit_chain_at HU HΓ _ _ Hσ'σ''))).
  assert (HId2 : per_ctx_env_mod_rel R (List.length Γ) U U (ρσ ↦ᵐ u2 ⦂ U) (ρ'σ' ↦ᵐ u3 ⦂ U))
    by (constructor; cbn [drop_env tl env_mod env_entry hd]; first [ assumption | apply Hrs | eexists; reflexivity ]).
  destruct (rel_exp_body_of_retagged HΓU HBlgen _ _ HΓ _ _ Hid ρσ ρ'σ'
              (ρσ ↦ᵐ u2 ⦂ U) (ρ'σ' ↦ᵐ u3 ⦂ U) Hρσ
              (eval_sub_single_mod _ _ _ _ _ Hu2) (eval_sub_single_mod _ _ _ _ _ Hu3) HId2)
    as [R2 [HI2t HI2e]].
  pose proof HI2t as [c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain].
  (** *** The Bridges at the Substituted Environments *)
  assert (Tu1 : tie_mod u1 (me_lit U) ρσ) by (exists u2; split; assumption).
  assert (Tu1U' : tie_mod u1 (me_lit U') ρσ)
    by (exact (tie_mod_move _ _ _ _ _ Tu1 (unit_chain_at HU HΓ _ _ Hσσ'))).
  assert (HY1 : per_ctx_env_mod_rel R (List.length Γ) U U (ρσ ↦ᵐ u1 ⦂ U) (ρσ ↦ᵐ u2 ⦂ U))
    by (constructor; cbn [drop_env tl env_mod env_entry hd]; first [ assumption | apply Hrs | eexists; reflexivity ]).
  assert (Tv3 : tie_mod v3 (me_lit U') ρ'σ') by (exists v3; split; [ exact Hv3 | etransitivity; [ exact Dv34 | symmetry; exact Dv34 ] ]).
  assert (Tv3U : tie_mod v3 (me_lit U) ρ'σ') by (exists u3; split; [ exact Hu3 | symmetry; exact Dw ]).
  assert (HX1 : per_ctx_env_mod_rel R (List.length Γ) U U (ρσ ↦ᵐ u2 ⦂ U) (ρ'σ' ↦ᵐ v3 ⦂ U'))
    by (constructor; cbn [drop_env tl env_mod env_entry hd]; first [ assumption | apply Hrs | eexists; reflexivity ]).
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY HYd]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX HXd]]]]]].
  (** *** The Right Commutation *)
  pose proof (per_ctx_env_of_mod_sub HΓ' Hσ'σ' HUr HUs') as HΓ'U'.
  assert (Tv4 : tie_mod v4 (me_lit U'[σ']ᵘ) ρ') by (exists v4; split; [ exact Hv4 | etransitivity; [ symmetry; exact Dv34 | exact Dv34 ] ]).
  assert (Hpair : per_ctx_env_mod_rel R' (List.length Γ') U'[σ']ᵘ U'[σ']ᵘ (ρ' ↦ᵐ v4 ⦂ U'[σ']ᵘ) (ρ' ↦ᵐ v4 ⦂ U'[σ']ᵘ))
    by (constructor; cbn [drop_env tl env_mod env_entry hd]; first [ assumption | eexists; reflexivity ]).
  destruct (rel_sub_q_entry HΓ'U' HΓ Hσ'σ' _ _ Hpair Hev' (ce_mod U')) as [t [Hqt Htr]].
  pose proof (rel_sub_under_ctx_q_mod Hσ'σ' HUr HUs') as Hq.
  destruct (HB'gen _ _ HΓ'U' _ _ Hq _ _ _ _ Hpair Hqt Hqt) as [R3 [HI3t HI3e]].
  pose proof HI3t as [e1 e2 e3 e4 He1 He2 He3 He4 He1chain].
  assert (Ttv4 : tie_mod v4 (me_lit U') t)
    by (exact (tie_mod_sub HΓ' HΓ Hσ'σ' HUr _ _ _ _ Hρ'ρ' Hev' (symmetry Htr) Tv4)).
  assert (HZ1 : per_ctx_env_mod_rel R (List.length Γ) U' U' (ρ'σ' ↦ᵐ v3 ⦂ U')
                  (retag_entry (centry_tag (ce_mod U') Γ t) (centry_slot_unit (ce_mod U')) (env_entry (ρ' ↦ᵐ v4 ⦂ U'[σ']ᵘ) 0) :: t))
    by (constructor; cbn [drop_env tl env_mod env_entry hd retag_entry centry_slot_unit centry_unit];
        first [ assumption | apply Hrs' | symmetry; exact Htr | eexists; reflexivity ]).
  destruct (HZ _ _ HZ1) as [cz1 [cz2 [RZ [Hcz1 [Hcz2 [HRZ HZd]]]]]].
  assert (cy1 = cA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cy2 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cx1 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz1 = cx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz2 = e2) as -> by (eapply functional_eval_exp; eassumption).
  (** *** Assembling *)
  assert (Hp1 : DF c1 ≈ cA2 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp1' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp14 : DF c1 ≈ c4 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp2 : DF cB2 ≈ c2 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp2' : DF cB2 ≈ cB3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp23 : DF c2 ≈ c3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp3 : DF e1 ≈ e2 ∈ per_univ_elem k3 ↘ R3) by pairwise.
  pose proof (per_univ_elem_kind _ _ _ _ Hp1) as Er1.
  pose proof (per_univ_elem_kind _ _ _ _ HRY) as ErY.
  pose proof (per_univ_elem_kind _ _ _ _ HRX) as ErX.
  pose proof (per_univ_elem_kind _ _ _ _ HRZ) as ErZ.
  assert (E1 : R1 <~> RY) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp1' HRY).
  assert (E2 : R2 <~> RY) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ Hp2' HRY).
  assert (E3 : R2 <~> RX) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp2' HRX).
  assert (E4 : RZ <~> RX) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ HRZ HRX).
  assert (E5 : R3 <~> RZ) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hp3 HRZ).
  assert (F1 : R1 <~> R2) by (rewrite E1, E2; reflexivity).
  assert (FY : RY <~> R2) by (rewrite E2; reflexivity).
  assert (FX : RX <~> R2) by (rewrite E3; reflexivity).
  assert (FZ : RZ <~> R2) by (rewrite E4, E3; reflexivity).
  assert (F3 : R3 <~> R2) by (rewrite E5, FZ; reflexivity).
  apply (fun H => per_univ_elem_resp_iff H F1) in Hp1, Hp14.
  apply (fun H => per_univ_elem_resp_iff H FY) in HRY.
  assert (PER R2) by (eapply per_elem_PER; exact Hp23).
  destruct U' as [Δ' D']; apply eval_me_lit_iff in Hv3; rewrite gunit_sub_mk in Hv4; apply eval_me_lit_iff in Hv4.
  exists R2; split.
  { apply (mk_rel_exp c1 c2 c3 c4); try eassumption.
    - rewrite exp_sub_extend_mod_sub; exact Hc1.
    - rewrite exp_sub_extend_mod_sub; exact Hc4.
    - assert (Hc12 : DF c1 ≈ c2 ∈ per_univ_elem k ↘ R2)
        by (eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hp1 | exact HRY ] | exact Hp2 ]).
      apply rel_chain_4; [ exact Hc12 | exact Hp23 | solve_per ]. }
  (** Whether [C] is a proposition, at the inner instance; the bridges
      carry it to every other value. *)
  destruct (evaluated_kind_or_propositional (domain_kind cB2)) as [ErB | ErB].
  2:{ left; exists c1; split; [ rewrite exp_sub_extend_mod_sub; exact Hc1 | congruence ]. }
  right.
  assert (ErA : evaluated_kind (domain_kind cA2)) by (replace (domain_kind cA2) with (domain_kind cB2) by congruence; exact ErB).
  assert (Er2 : evaluated_kind (domain_kind e2)) by (replace (domain_kind e2) with (domain_kind cB2) by congruence; exact ErB).
  apply (rel_exp_or_prop_evaluated HI1t (ex_intro _ cA2 (conj HcA2 ErA))) in HI1e.
  apply (rel_exp_or_prop_evaluated HI2t (ex_intro _ cB2 (conj HcB2 ErB))) in HI2e.
  apply (rel_exp_or_prop_evaluated HI3t (ex_intro _ e2 (conj He2 Er2))) in HI3e.
  destruct HYd as [HYd | [by1 [by2 [Hby1 [Hby2 Hby]]]]]; [ kind_congruence |].
  destruct HXd as [HXd | [bx1 [bx2 [Hbx1 [Hbx2 Hbx]]]]]; [ kind_congruence |].
  destruct HZd as [HZd | [bz1 [bz2 [Hbz1 [Hbz2 Hbz]]]]]; [ kind_congruence |].
  destruct HI1e as [w1 bA2 bA3 w4x Hw1 HbA2 HbA3 Hw4 Hw1chain].
  destruct HI2e as [w2' bB2 bB3 w3x Hw2' HbB2 HbB3 Hw3' Hw2chain].
  destruct HI3e as [f1 f2 f3 f4 Hf1 Hf2 Hf3 Hf4 Hf1chain].
  assert (by1 = bA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (by2 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bx1 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz1 = bx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz2 = f2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Ht1 : Dom w1 ≈ bA2 ∈ R1) by pairwise.
  assert (Ht2 : Dom w2' ≈ bB2 ∈ R2) by pairwise.
  assert (Ht3 : Dom f2 ≈ f1 ∈ R3) by pairwise.
  apply F1 in Ht1.
  apply FY in Hby.
  apply FX in Hbx.
  apply FZ in Hbz.
  apply F3 in Ht3.
  apply (mk_rel_exp w1 w2' bx2 f1); try eassumption.
  - rewrite exp_sub_extend_mod_sub; exact Hw1.
  - eapply eval_exp_let_mod; [ exact Hv3 | exact Hbx2 ].
  - cbn [exp_sub binding_sub]; rewrite gunit_sub_mk in Hf1 |- *; eapply eval_exp_let_mod; [ exact Hv4 | exact Hf1 ].
  - apply rel_chain_4; solve_per.
Qed.

(** [ζ] for modules. *)
Corollary rel_exp_under_ctx_let_mod_zeta : forall {Γ U B C},
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : C ->
    gunit_scoped (List.length Γ) U ->
    Γ ⊨ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HB HUs.
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_mod_gen HU HB HUs HUs).
Qed.

(** ** Local Definitions with a Module Part *)

(** Related elements of a type read back as definitions with a module part
    stored at the types' values, at any modules and units, as a local
    definition with a module part binds them ([eval_exp_let_dm]). *)
Lemma dm_entry_readable_of_elem : forall {i a a' R v v'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom v ≈ v' ∈ R ->
    forall h h' U U',
      entry_readable (de_dm v (entry_type_value a) h U) /\ entry_readable (de_dm v' (entry_type_value a') h' U').
Proof.
  intros * HR Hv *; split; intros s;
    destruct (per_univ_then_per_top_typ HR s) as [T T' HT HT' _];
    destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _];
    eexists; eapply read_entry_dm; solve [ constructor | eassumption ].
Qed.

(** The instance [B[Id ,,ᵈ M ‖ ⌜U⌝]] against a [let] whose annotation [A'],
    definiens [M'] and unit [U'] are related to [A], [M] and [U], and whose
    body [B'] is related to [B].  The four values are as for a local
    definition ([rel_exp_let_evaluated]): the instances of [B] along
    [σ ,,ᵈ M[σ] ‖ ⌜U[σ]⌝] and along [Id ,,ᵈ M ‖ ⌜U⌝], [B ≈ B'] at the
    substituted pair, and [B'] along [q σ'].  The heads carry the values of
    the units as a local module's do ([rel_exp_let_mod_gen]).  The
    annotation is of a universe, so no head is a proof. *)
Lemma rel_exp_let_dm_gen : forall {Γ A A'} {i : nat} {M M' U U' B B' C},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ᵘ U ≈ U' ->
    exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
    gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
    Γ ▸ₘ A ≔ M ‖ U ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id ,,ᵈ M ‖ me_lit U] ≈ ℓᵈ A' ≔ M' ‖ U' in B' : C[Id ,,ᵈ M ‖ me_lit U].
Proof.
  intros * HA HAA' HM [HU _ _] HMs HMs' HUs HUs' HB.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_under_ctx_refl_right HM) as HMr.
  pose proof (rel_modexp_refl_left HU) as HUl.
  pose proof (rel_modexp_refl_right HU) as HUr.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  pose proof (rel_type_of_typ HA) as HAt.
  pose proof (rel_type_of_typ HAA') as HAA't.
  pose proof (rel_type_inversion HAt) as [R [HΓ _]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  pose proof (rel_type_evaluated_of_typ HA) as HArel.
  pose proof HArel as (r & Hr & HArelk).
  pose proof (HArelk _ HΓ) as HArelΓk.
  pose proof (fun ρ0 ρ0' Hρ0 => rel_typ_evaluated_of_kind (HArelΓk ρ0 ρ0' Hρ0) Hr) as HArelΓ.
  pose proof (per_ctx_env_of_dm HΓ HA HMl HUl HUs) as HΓd.
  pose proof (per_ctx_env_of_dm HΓ HA HMr HUr HUs') as HΓd'.
  pose proof (per_ctx_env_of_typ (κ := ak_relevant) HΓ HAt) as HΓA.
  pose proof (rel_exp_of_typ_inversion_simple_at HΓ HA) as HAs.
  pose proof (rel_type_inversion_simple_at HΓ HAt) as HAat.
  pose proof (rel_type_inversion_simple_at HΓ HAA't) as HAA'at.
  pose proof (not_rel_typ_propositional_of_typ HΓ HA) as Hnp.
  pose proof (gunit_scoped_free_bound _ _ HUs) as HbU.
  pose proof (gunit_scoped_free_bound _ _ HUs') as HbU'.
  (** Environments of a definition with a module part of [A], from their
      parts: the right tie to the definiens follows from the left one. *)
  assert (Hmk : forall N V e e' v v' t t' h h' W W',
             Γ ⊨ N : A -> Dom e ≈ e' ∈ R -> Dom v ≈ v' ∈ per_head A A e e' ->
             def_tie A N (e ↦ᵈ v ⦂ t ‖ h ⦂ W) ->
             tie_mod h (me_lit V) e -> tie_mod h' (me_lit V) e' ->
             head_readable (List.length Γ) (de_dm v t h W) -> head_readable (List.length Γ) (de_dm v' t' h' W') ->
             per_env_extend_dm A N V (List.length Γ) R (e ↦ᵈ v ⦂ t ‖ h ⦂ W) (e' ↦ᵈ v' ⦂ t' ‖ h' ⦂ W')).
  { intros * HN He Hh Tl Ul Ur Rl Rr.
    assert (He' : Dom e' ≈ e' ∈ R) by (etransitivity; [ symmetry; exact He | exact He ]).
    assert (Hcl : per_env_head_clauses A R (e ↦ᵈ v ⦂ t ‖ h ⦂ W) (e' ↦ᵈ v' ⦂ t' ‖ h' ⦂ W'))
      by (constructor; cbn [drop_env tl env_entry hd extend_env_dm];
          [ exact He | exact Hh | intros Hp; exfalso; exact (Hnp _ _ He Hp) | intros Hp; exfalso; exact (Hnp _ _ He' Hp) ]).
    constructor; cbn [drop_env tl env_mod env_entry hd extend_env_dm];
      [ exact He | exact Hh | exact Tl
      | exact (def_tie_resp_clauses HPR HAs (rel_exp_under_ctx_simple_at_rel HΓ HA HN) Hcl Tl)
      | exact Ul | exact Ur | exact Rl | exact Rr | do 2 eexists; reflexivity | do 2 eexists; reflexivity ]. }
  (** The environments of the right-hand definiens and unit are those of
      the left-hand ones. *)
  assert (Hconv : forall e e', per_env_extend_dm A M' U' (List.length Γ) R e e' ->
                     per_env_extend_dm A M U (List.length Γ) R e e').
  { intros e e' He.
    pose proof He as [Ht Hh Tl Tr Ul Ur Hrl Hrr Hkl Hkr].
    assert (Htt : Dom e↯ ≈ e↯ ∈ R) by (etransitivity; [ exact Ht | symmetry; exact Ht ]).
    assert (Ht't' : Dom e'↯ ≈ e'↯ ∈ R) by (etransitivity; [ symmetry; exact Ht | exact Ht ]).
    pose proof (per_env_extend_dm_clauses He (Hnp _ _ Ht) (Hnp _ _ Ht't')) as Hcl.
    pose proof (rel_exp_under_ctx_simple_at_rel HΓ HA (rel_exp_under_ctx_sym HM)) as HM'M.
    constructor; [ exact Ht | exact Hh
                 | exact (def_tie_resp_clauses HPR HAs HM'M (per_env_head_clauses_sym HPR Hcl) Tr)
                 | exact (def_tie_resp_clauses HPR HAs HM'M Hcl Tl)
                 | exact (tie_mod_move _ _ _ _ _ Ul (rel_modexp_evals_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Htt)))
                 | exact (tie_mod_move _ _ _ _ _ Ur (rel_modexp_evals_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Ht't')))
                 | exact Hrl | exact Hrr | exact Hkl | exact Hkr ]. }
  (** [B'] in the context of the right-hand definiens and unit. *)
  assert (HB'r : Γ ▸ₘ A ≔ M' ‖ U' ⊨ B' ≈ B' : C)
    by (eapply rel_exp_under_ctx_restrict;
        [ exact HΓd' | exact HΓd | exact Hconv | cbn; lia
        | intros ? ? _ [| x] _; split; intros [T HT E HE a Ea Hp]; econstructor; eassumption | exact HBr ]).
  destruct (rel_exp_under_ctx_simple_full_at HΓd HB) as [kX HX].
  destruct (rel_exp_under_ctx_simple_full_at HΓd HBl) as [kY HY].
  destruct (rel_exp_under_ctx_simple_full_at HΓd' HB'r) as [kZ HZ].
  pose proof HBl as [? ? k HBlgen].
  pose proof HB'r as [? ? k3 HB'gen].
  refine (mk_rel_exp_under_ctx _ _ _ _ R HΓ k _).
  intros Γ' R' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ R) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hσσ' : Dom ρσ ≈ ρσ ∈ R) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  assert (Hσ'σ'' : Dom ρ'σ' ≈ ρ'σ' ∈ R) by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  assert (Hρρ : Dom ρ ≈ ρ ∈ R') by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ R') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  (** *** The Definientia and the Units *)
  pose proof (HArelΓ _ _ Hρσ) as HArelρσ.
  destruct (head_not_propositional_of_typ (e := ce_dm A M U) HΓ eq_refl HA _ _ Hρσ) as [Hnp2 Hnp3].
  pose proof HM as [? ? j HMgen].
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN [HNtyp HNexp]].
  apply (rel_exp_or_prop_evaluated HNtyp HArelρσ) in HNexp.
  destruct HNtyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  pose proof HMl as [? ? jl HMlgen].
  destruct (HMlgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RNl [HNltyp HNlexp]].
  apply (rel_exp_or_prop_evaluated HNltyp HArelρσ) in HNlexp.
  destruct HNltyp as [a1' a2' a3' a4' Ha1' Ha2' Ha3' Ha4' Halchain].
  destruct HNlexp as [n1' n2' n3m n4m Hn1' Hn2' Hn3m Hn4m Hnlchain].
  assert (a1' = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (a4' = a4) as -> by (eapply functional_eval_exp; eassumption).
  assert (n1' = n1) as -> by (eapply functional_eval_exp; eassumption).
  assert (n2' = n2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Ha22 : DF a2 ≈ a2 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha23 : DF a2 ≈ a3 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha33 : DF a3 ≈ a3 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha44 : DF a4 ≈ a4 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha23l : DF a2 ≈ a3 ∈ per_univ_elem jl ↘ RNl) by pairwise.
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn22 : Dom n2 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn34 : Dom n3 ≈ n4 ∈ RN) by pairwise.
  assert (Hn33 : Dom n3 ≈ n3 ∈ RN) by pairwise.
  assert (Hn44 : Dom n4 ≈ n4 ∈ RN) by pairwise.
  assert (PER RNl) by (eapply per_elem_PER; exact Ha23l).
  destruct (unit_sub_chain HΓ' Hσσ HUl _ _ _ _ Hρρ Hev Hev) as ([u1 u2 Hu1 Hu2 Du12] & _).
  destruct (unit_sub_chain HΓ' Hσ'σ' HUr _ _ _ _ Hρ'ρ' Hev' Hev') as (_ & _ & [v3 v4 Hv3 Hv4 Dv34]).
  destruct (unit_chain_at HU HΓ _ _ Hσ'σ'') as [w2 w3 Hw2 Hw3 Dw].
  destruct (unit_sub_chain HΓ' Hσ'σ' HUl _ _ _ _ Hρ'ρ' Hev' Hev') as ([u4 u3 Hu4 Hu3 Du43] & _).
  pose proof (functional_eval_modexp _ _ _ _ Hw2 Hu3) as ->.
  pose proof (functional_eval_modexp _ _ _ _ Hw3 Hv3) as ->.
  (** *** The Annotation

      [A'] at the two environments the [let] is evaluated at; the heads it
      binds read back at its values. *)
  destruct (HAA'at _ _ Hσ'σ'') as (b3 & b3' & Hb3 & Hb3' & [RA3 HRA3]).
  destruct (rel_type_sub_simple HΓ' Hσ'σ' HAA't _ _ Hρ'ρ') as (b4 & b4' & Hb4 & Hb4' & [RA4 HRA4]).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (b4 = a4) as -> by (eapply functional_eval_exp; eassumption).
  assert (ERA3 : RN <~> RA3) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha33 HRA3).
  assert (ERA4 : RN <~> RA4) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha44 HRA4).
  pose proof Hσj as [? _ ? _ _ Hσs].
  assert (HU'σ's : gunit_scoped (List.length Γ') U'[σ']ᵘ)
    by (eapply gunit_scoped_sub; [ exact HUs' | intros x Hx; exact (proj2 (Hσs x Hx)) ]).
  assert (Hrd3 : head_readable (List.length Γ) (de_dm n3 (entry_type_value b3') v3 U'))
    by (split; [ exact (proj2 (dm_entry_readable_of_elem HRA3 (proj1 (ERA3 _ _) Hn33) v3 v3 U' U')) | exact HbU' ]).
  assert (Hrd4 : head_readable (List.length Γ') (de_dm n4 (entry_type_value b4') v4 U'[σ']ᵘ))
    by (split; [ exact (proj2 (dm_entry_readable_of_elem HRA4 (proj1 (ERA4 _ _) Hn44) v4 v4 U'[σ']ᵘ U'[σ']ᵘ))
               | exact (gunit_scoped_free_bound _ _ HU'σ's) ]).
  (** *** The Instances

      [B] along [σ ,,ᵈ M[σ] ‖ ⌜U[σ]⌝] gives the outer values of the type and
      the first value of the term, and [B] along [Id ,,ᵈ M ‖ ⌜U⌝] at the
      substituted environments the inner values of the type and the second
      value of the term. *)
  pose proof (rel_sub_under_ctx_extend_dm Hσj HA HMl HUl HMs HMs HUs HUs) as Hτ.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend_dm (ce_dm A M U) _ _ _ _ _ _ _ _ Hev Hnp2 Hn1 Hu1)
              (eval_sub_extend_dm (ce_dm A M U) _ _ _ _ _ _ _ _ Hev' Hnp3 Hn4m Hu4))
    as [R1 [HI1t HI1e]].
  pose proof HI1t as [c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain].
  pose proof (rel_sub_under_ctx_extend_dm (rel_sub_id (ex_intro _ _ HΓ)) HA HMl HUl HMs HMs HUs HUs) as Hid.
  rewrite exp_sub_id, gunit_sub_id in Hid.
  destruct (head_not_propositional_of_typ (e := ce_dm A M U) HΓ eq_refl HA _ _ (per_ctx_env_retag HΓ _ _ Hρσ))
    as [Hnp2r Hnp3r].
  assert (Tu2 : tie_mod u2 (me_lit U) ρσ)
    by (exists u2; split; [ exact Hu2 | etransitivity; [ symmetry; exact Du12 | exact Du12 ] ]).
  assert (Tu3 : tie_mod u3 (me_lit U) ρ'σ')
    by (exists u3; split; [ exact Hu3 | etransitivity; [ symmetry; exact Du43 | exact Du43 ] ]).
  assert (Tn2 : forall v t h W, Dom n2 ≈ v ∈ RN -> def_tie A M (ρσ ↦ᵈ v ⦂ t ‖ h ⦂ W))
    by (intros * Hv; exists n2; split; [ exact Hn2 | eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 | exact Hv ] ]).
  assert (Hh23m : Dom n2 ≈ n3m ∈ per_head A A ρσ ρ'σ')
    by (eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23l | pairwise ]).
  destruct (per_head_dm_readable (h := u2) (h' := u3) (U := U) (List.length Γ) HΓA HΓ Hρσ Hh23m HbU) as [Rd2 Rd3].
  pose proof (Hmk M U ρσ ρ'σ' n2 n3m (centry_tag (ce_dm A M U) Γ ρσ) (centry_tag (ce_dm A M U) Γ ρ'σ') u2 u3 U U
                HMl Hρσ Hh23m (Tn2 _ _ _ _ Hn22) Tu2 Tu3 Rd2 Rd3) as HId2.
  destruct (rel_exp_body_of_retagged HΓd HBlgen _ _ HΓ _ _ Hid ρσ ρ'σ'
              (ρσ ↦ᵈ n2 ⦂ centry_tag (ce_dm A M U) Γ ρσ ‖ u2 ⦂ U) (ρ'σ' ↦ᵈ n3m ⦂ centry_tag (ce_dm A M U) Γ ρ'σ' ‖ u3 ⦂ U) Hρσ
              (eval_sub_single_dm (ce_dm A M U) _ _ _ _ _ _ Hnp2r Hn2 Hu2)
              (eval_sub_single_dm (ce_dm A M U) _ _ _ _ _ _ Hnp3r Hn3m Hu3) HId2)
    as [R2 [HI2t HI2e]].
  pose proof HI2t as [c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain].
  (** *** The Bridges at the Substituted Environments

      [B] at the two heads [⟦M[σ]⟧ρ] and [⟦M⟧ρσ], and [B ≈ B'] at the
      substituted pair. *)
  assert (Tu1 : tie_mod u1 (me_lit U) ρσ) by (exists u2; split; assumption).
  assert (Hh12 : Dom n1 ≈ n2 ∈ per_head A A ρσ ρσ)
    by (eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 | exact Hn12 ]).
  destruct (per_head_dm_readable (h := u1) (h' := u2) (U := U) (List.length Γ) HΓA HΓ Hσσ' Hh12 HbU) as [Rd1 Rd2'].
  pose proof (Hmk M U ρσ ρσ n1 n2 (centry_tag (ce_dm A M U) Γ ρσ) (centry_tag (ce_dm A M U) Γ ρσ) u1 u2 U U
                HMl Hσσ' Hh12 (Tn2 _ _ _ _ ltac:(symmetry; exact Hn12)) Tu1 Tu2 Rd1 Rd2') as HY1.
  assert (Tv3U : tie_mod v3 (me_lit U) ρ'σ') by (exists u3; split; [ exact Hu3 | symmetry; exact Dw ]).
  assert (Hh23 : Dom n2 ≈ n3 ∈ per_head A A ρσ ρ'σ')
    by (eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23 | exact Hn23 ]).
  pose proof (Hmk M U ρσ ρ'σ' n2 n3 (centry_tag (ce_dm A M U) Γ ρσ) (entry_type_value b3') u2 v3 U U'
                HMl Hρσ Hh23 (Tn2 _ _ _ _ Hn22) Tu2 Tv3U Rd2 Hrd3) as HX1.
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY HYd]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX HXd]]]]]].
  (** *** The Right Commutation

      [B'] along [q σ'] at [ρ'] extended by the values of [M'[σ']] and
      [⌜U'[σ']⌝], whose inner value is bridged to the [let]'s at [ρ'σ'] by
      [B'] itself. *)
  pose proof (per_ctx_env_of_dm_sub HΓ' Hσ'σ' HA HMr HUr HUs') as HΓ'd.
  pose proof (rel_sub_under_ctx_q_dm Hσ'σ' HA HMr HUr HUs') as Hq.
  assert (Tv4 : tie_mod v4 (me_lit U'[σ']ᵘ) ρ')
    by (exists v4; split; [ exact Hv4 | etransitivity; [ symmetry; exact Dv34 | exact Dv34 ] ]).
  assert (Hh44 : Dom n4 ≈ n4 ∈ per_head A[σ'] A[σ'] ρ' ρ')
    by (eapply per_head_of; [ exact Ha4 | exact Ha4 | exact Ha44 | exact Hn44 ]).
  assert (Hpair : per_env_extend_dm A[σ'] M'[σ'] U'[σ']ᵘ (List.length Γ') R'
                    (ρ' ↦ᵈ n4 ⦂ entry_type_value b4' ‖ v4 ⦂ U'[σ']ᵘ) (ρ' ↦ᵈ n4 ⦂ entry_type_value b4' ‖ v4 ⦂ U'[σ']ᵘ)).
  { assert (T4 : def_tie A[σ'] M'[σ'] (ρ' ↦ᵈ n4 ⦂ entry_type_value b4' ‖ v4 ⦂ U'[σ']ᵘ))
      by (exists n4; split; [ exact Hn4 | exact Hh44 ]).
    constructor; cbn [drop_env tl env_mod env_entry hd extend_env_dm];
      first [ exact Hρ'ρ' | exact Hh44 | exact T4 | exact Tv4 | exact Hrd4 | do 2 eexists; reflexivity ]. }
  destruct (rel_sub_q_entry HΓ'd HΓ Hσ'σ' _ _ Hpair Hev' (ce_dm A M' U')) as [t [Hqt Htr]].
  destruct (HB'gen _ _ HΓ'd _ _ Hq _ _ _ _ Hpair Hqt Hqt) as [R3 [HI3t HI3e]].
  pose proof HI3t as [e1 e2 e3 e4 He1 He2 He3 He4 He1chain].
  assert (Hts' : Dom ρ'σ' ≈ t ∈ R) by (symmetry; exact Htr).
  destruct (HAat _ _ Hts') as [b3x [bs [Hb3x [Hbs [Rs HRs]]]]].
  assert (b3x = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (ERs : RN <~> Rs) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha33 HRs).
  assert (Hh34 : Dom n3 ≈ n4 ∈ per_head A A ρ'σ' t)
    by (eapply per_head_of; [ exact Ha3 | exact Hbs | exact HRs | apply ERs; exact Hn34 ]).
  assert (Tv3 : tie_mod v3 (me_lit U') ρ'σ')
    by (exists v3; split; [ exact Hv3 | etransitivity; [ exact Dv34 | symmetry; exact Dv34 ] ]).
  assert (Ttv4 : tie_mod v4 (me_lit U') t)
    by (exact (tie_mod_sub HΓ' HΓ Hσ'σ' HUr _ _ _ _ Hρ'ρ' Hev' (symmetry Htr) Tv4)).
  assert (Tn3 : def_tie A M' (ρ'σ' ↦ᵈ n3 ⦂ entry_type_value b3' ‖ v3 ⦂ U'))
    by (exists n3; split; [ exact Hn3 | eapply per_head_of; [ exact Ha3 | exact Ha3 | exact Ha33 | exact Hn33 ] ]).
  destruct (per_head_dm_readable (h := v3) (h' := v4) (U := U') (List.length Γ) HΓA HΓ Hts' Hh34 HbU') as [_ Rt].
  pose proof (Hmk M' U' ρ'σ' t n3 n4 (entry_type_value b3') (centry_tag (ce_dm A M' U') Γ t) v3 v4 U' U'
                HMr Hts' Hh34 Tn3 Tv3 Ttv4 Hrd3 Rt) as HZ1.
  destruct (HZ _ _ HZ1) as [cz1 [cz2 [RZ [Hcz1 [Hcz2 [HRZ HZd]]]]]].
  assert (cy1 = cA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cy2 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cx1 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz1 = cx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz2 = e2) as -> by (eapply functional_eval_exp; eassumption).
  (** *** One Element PER *)
  assert (Hp1 : DF c1 ≈ cA2 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp1' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp14 : DF c1 ≈ c4 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp2 : DF cB2 ≈ c2 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp2' : DF cB2 ≈ cB3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp23 : DF c2 ≈ c3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp3 : DF e1 ≈ e2 ∈ per_univ_elem k3 ↘ R3) by pairwise.
  pose proof (per_univ_elem_kind _ _ _ _ Hp1) as Er1.
  pose proof (per_univ_elem_kind _ _ _ _ HRY) as ErY.
  pose proof (per_univ_elem_kind _ _ _ _ HRX) as ErX.
  pose proof (per_univ_elem_kind _ _ _ _ HRZ) as ErZ.
  assert (E1 : R1 <~> RY) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp1' HRY).
  assert (E2 : R2 <~> RY) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ Hp2' HRY).
  assert (E3 : R2 <~> RX) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp2' HRX).
  assert (E4 : RZ <~> RX) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ HRZ HRX).
  assert (E5 : R3 <~> RZ) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hp3 HRZ).
  assert (F1 : R1 <~> R2) by (rewrite E1, E2; reflexivity).
  assert (FY : RY <~> R2) by (rewrite E2; reflexivity).
  assert (FX : RX <~> R2) by (rewrite E3; reflexivity).
  assert (FZ : RZ <~> R2) by (rewrite E4, E3; reflexivity).
  assert (F3 : R3 <~> R2) by (rewrite E5, FZ; reflexivity).
  apply (fun H => per_univ_elem_resp_iff H F1) in Hp1, Hp14.
  apply (fun H => per_univ_elem_resp_iff H FY) in HRY.
  assert (PER R2) by (eapply per_elem_PER; exact Hp23).
  exists R2; split.
  { apply (mk_rel_exp c1 c2 c3 c4); try eassumption.
    - rewrite exp_sub_extend_dm_sub; exact Hc1.
    - rewrite exp_sub_extend_dm_sub; exact Hc4.
    - assert (Hc12 : DF c1 ≈ c2 ∈ per_univ_elem k ↘ R2)
        by (eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hp1 | exact HRY ] | exact Hp2 ]).
      apply rel_chain_4; [ exact Hc12 | exact Hp23 | solve_per ]. }
  (** Whether [C] is a proposition, at the inner instance; the bridges
      carry it to every other value. *)
  destruct (evaluated_kind_or_propositional (domain_kind cB2)) as [ErB | ErB].
  2:{ left; exists c1; split; [ rewrite exp_sub_extend_dm_sub; exact Hc1 | congruence ]. }
  right.
  assert (ErA : evaluated_kind (domain_kind cA2)) by (replace (domain_kind cA2) with (domain_kind cB2) by congruence; exact ErB).
  assert (Er2 : evaluated_kind (domain_kind e2)) by (replace (domain_kind e2) with (domain_kind cB2) by congruence; exact ErB).
  apply (rel_exp_or_prop_evaluated HI1t (ex_intro _ cA2 (conj HcA2 ErA))) in HI1e.
  apply (rel_exp_or_prop_evaluated HI2t (ex_intro _ cB2 (conj HcB2 ErB))) in HI2e.
  apply (rel_exp_or_prop_evaluated HI3t (ex_intro _ e2 (conj He2 Er2))) in HI3e.
  destruct HYd as [HYd | [by1 [by2 [Hby1 [Hby2 Hby]]]]]; [ kind_congruence |].
  destruct HXd as [HXd | [bx1 [bx2 [Hbx1 [Hbx2 Hbx]]]]]; [ kind_congruence |].
  destruct HZd as [HZd | [bz1 [bz2 [Hbz1 [Hbz2 Hbz]]]]]; [ kind_congruence |].
  destruct HI1e as [t1 bA2 bA3 t4 Ht1e HbA2 HbA3 Ht4e Ht1chain].
  destruct HI2e as [t2 bB2 bB3 t3 Ht2e HbB2 HbB3 Ht3e Ht2chain].
  destruct HI3e as [f1 f2 f3 f4 Hf1 Hf2 Hf3 Hf4 Hf1chain].
  assert (by1 = bA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (by2 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bx1 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz1 = bx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz2 = f2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Ht1 : Dom t1 ≈ bA2 ∈ R1) by pairwise.
  assert (Ht2 : Dom t2 ≈ bB2 ∈ R2) by pairwise.
  assert (Ht3 : Dom f2 ≈ f1 ∈ R3) by pairwise.
  apply F1 in Ht1.
  apply FY in Hby.
  apply FX in Hbx.
  apply FZ in Hbz.
  apply F3 in Ht3.
  (** The [let] on the right binds the values of its definiens and of its
      unit's literal, at the value of its annotation. *)
  assert (Hlet3 : ⟦ ℓᵈ A' ≔ M' ‖ U' in B' ⟧ ρ'σ' ↘ bx2)
    by (eapply eval_exp_let_dm; [ exact Hb3' | exact Hn3 | exact Hv3 | exact Hbx2 ]).
  assert (Hlet4 : ⟦ (ℓᵈ A' ≔ M' ‖ U' in B')[σ'] ⟧ ρ' ↘ f1)
    by (cbn [exp_sub binding_sub]; eapply eval_exp_let_dm; [ exact Hb4' | exact Hn4 | exact Hv4 | exact Hf1 ]).
  apply (mk_rel_exp t1 t2 bx2 f1); try eassumption.
  - rewrite exp_sub_extend_dm_sub; exact Ht1e.
  - apply rel_chain_4; solve_per.
Qed.

(** [ζ] for a local definition with a module part. *)
Corollary rel_exp_under_ctx_let_dm_zeta : forall {Γ A} {i : nat} {M U B C},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    Γ ⊨ᵘ U ≈ U ->
    exp_scoped (List.length Γ) M ->
    gunit_scoped (List.length Γ) U ->
    Γ ▸ₘ A ≔ M ‖ U ⊨ B : C ->
    Γ ⊨ ℓᵈ A ≔ M ‖ U in B ≈ B[Id ,,ᵈ M ‖ me_lit U] : C[Id ,,ᵈ M ‖ me_lit U].
Proof.
  intros * HA HM HU HMs HUs HB.
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_dm_gen HA HA HM HU HMs HMs HUs HUs HB).
Qed.

(** Congruence: both sides are related to the instance
    [B[Id ,,ᵈ M ‖ ⌜U⌝]]. *)
Corollary rel_exp_under_ctx_let_dm_cong : forall {Γ A A'} {i : nat} {M M' U U' B B' C},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ᵘ U ≈ U' ->
    exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
    gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
    Γ ▸ₘ A ≔ M ‖ U ⊨ B ≈ B' : C ->
    Γ ⊨ ℓᵈ A ≔ M ‖ U in B ≈ ℓᵈ A' ≔ M' ‖ U' in B' : C[Id ,,ᵈ M ‖ me_lit U].
Proof.
  intros * HA HAA' HM HU HMs HMs' HUs HUs' HB.
  pose proof HU as [HU0 HsU _].
  eapply rel_exp_under_ctx_trans; [| exact (rel_exp_let_dm_gen HA HAA' HM HU HMs HMs' HUs HUs' HB) ].
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_dm_gen HA HA (rel_exp_under_ctx_refl_left HM)
           (mk_rel_unit_under_ctx _ _ _ (rel_modexp_refl_left HU0) HsU HsU) HMs HMs HUs HUs
           (rel_exp_under_ctx_refl_left HB)).
Qed.

Corollary valid_exp_under_ctx_let_dm : forall {Γ A} {i : nat} {M U B C},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    Γ ⊨ᵘ U ≈ U ->
    exp_scoped (List.length Γ) M ->
    gunit_scoped (List.length Γ) U ->
    Γ ▸ₘ A ≔ M ‖ U ⊨ B : C ->
    Γ ⊨ ℓᵈ A ≔ M ‖ U in B : C[Id ,,ᵈ M ‖ me_lit U].
Proof. intros * HA HM HU HMs HUs HB; exact (rel_exp_under_ctx_let_dm_cong HA HA HM HU HMs HMs HUs HUs HB). Qed.

End Fixed_GCtx.

Lemma sem_let_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓᵈ A ≔ M ‖ U in B : C[Id ,,ᵈ M ‖ me_lit U] ).
Proof.
  intros * HA HM HU HB HMs HUs; sem_intro;
    [ assumption | exact (valid_exp_under_ctx_let_dm HA HM HU HMs HUs HB) ].
Qed.

Lemma sem_exp_eq_let_dm_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊨ B ≈ B' : C ->
     exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
     gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓᵈ A ≔ M ‖ U in B ≈ ℓᵈ A' ≔ M' ‖ U' in B' : C[Id ,,ᵈ M ‖ me_lit U] ).
Proof.
  intros * HA HAA' HM HU HB HMs HMs' HUs HUs'; sem_intro;
    [ assumption | exact (rel_exp_under_ctx_let_dm_cong HA HAA' HM HU HMs HMs' HUs HUs' HB) ].
Qed.

Lemma sem_exp_eq_let_dm_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓᵈ A ≔ M ‖ U in B ≈ B[Id ,,ᵈ M ‖ me_lit U] : C[Id ,,ᵈ M ‖ me_lit U] ).
Proof.
  intros * HA HM HU HB HMs HUs; sem_intro;
    [ assumption | exact (rel_exp_under_ctx_let_dm_zeta HA HM HU HMs HUs HB) ].
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

Lemma sem_exp_eq_let_mod_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU _ _ HB HUs; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_mod_zeta HU HB HUs) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Congruence: both sides are related to the instance [B[Id,,ₘ⌜U⌝]]. *)
Corollary rel_exp_under_ctx_let_mod_cong : forall {Γ U U' B B' C},
    Γ ⊨ᵘ U ≈ U' ->
    Γ ▹ₘ U ⊨ B ≈ B' : C ->
    gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
    Γ ⊨ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HB HUs HUs'.
  pose proof HU as [HU0 HsU _].
  eapply rel_exp_under_ctx_trans; [| exact (rel_exp_let_mod_gen HU HB HUs HUs') ].
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_mod_gen (U' := U) (mk_rel_unit_under_ctx _ _ _ (rel_modexp_refl_left HU0) HsU HsU)
           (rel_exp_under_ctx_refl_left HB) HUs HUs).
Qed.

End Fixed_GCtx.

Lemma sem_exp_eq_let_mod_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU HB _ HUs HUs'; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_mod_cong HU HB HUs HUs') ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary valid_exp_under_ctx_let_mod : forall {Γ U B C},
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : C ->
    gunit_scoped (List.length Γ) U ->
    Γ ⊨ ℓₘ U in B : C[Id ,,ₘ me_lit U].
Proof. intros * HU HB HUs; exact (rel_exp_under_ctx_let_mod_cong HU HB HUs HUs). Qed.

End Fixed_GCtx.

Lemma sem_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU _ _ HB HUs; sem_intro; [ assumption | exact (valid_exp_under_ctx_let_mod HU HB HUs) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** ** Environments of Arguments *)

Lemma env_extend_typed_rev : forall ρ vts,
    env_extend_typed ρ vts = List.rev (List.map (fun vt => de_term (fst vt) (snd vt)) vts) ++ ρ.
Proof.
  intros ρ vts; revert ρ; induction vts as [| vt vts IH]; intros; [ reflexivity |].
  unfold env_extend_typed in *; cbn [List.fold_left List.map List.rev].
  rewrite IH, <- List.app_assoc; reflexivity.
Qed.

Lemma skipn_env_extend_typed : forall ρ vts, List.skipn (List.length vts) (env_extend_typed ρ vts) = ρ.
Proof.
  intros; rewrite env_extend_typed_rev.
  rewrite List.skipn_app, List.skipn_all2 by (rewrite List.length_rev, List.length_map; lia).
  rewrite List.length_rev, List.length_map, Nat.sub_diag; reflexivity.
Qed.

Lemma eval_wk_shiftn : forall n ρ, ⟪wk_shiftn n⟫ ρ = List.skipn n ρ.
Proof.
  intros n ρ.
  assert (Hm : wk_mono (wk_shiftn n)) by (intros x y Hxy; cbn; lia).
  assert (Hl : wk_len (wk_shiftn n) (List.length ρ) = List.length (List.skipn n ρ)).
  { apply nat_eq_of_lt_iff; intros x; rewrite wk_len_spec by exact Hm; rewrite List.length_skipn; cbn; lia. }
  apply env_ext; [ rewrite eval_wk_length; exact Hl |].
  intros x Hx; rewrite eval_wk_length, Hl in Hx.
  rewrite eval_wk_var by (rewrite Hl; exact Hx).
  rewrite !env_entry_nth, List.nth_skipn; cbn; f_equal; lia.
Qed.

Lemma eval_wk_shiftn_extend_typed : forall ρ vts, ⟪wk_shiftn (List.length vts)⟫ (env_extend_typed ρ vts) = ρ.
Proof. intros; rewrite eval_wk_shiftn; apply skipn_env_extend_typed. Qed.

(** ** The [n]-fold Shift *)

Lemma wk_mono_shiftn : forall n, wk_mono (wk_shiftn n).
Proof. intros n x y H; cbn; lia. Qed.

#[export] Instance WkMono_shiftn (n : nat) : WkMono (wk_shiftn n) := wk_mono_shiftn n.

Lemma rel_wk_shiftn : forall Ψ Γ RΨ RΓ,
    EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ RΨ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    rel_wk (wk_shiftn (List.length Ψ)) RΨ RΓ.
Proof.
  intros * HΨ HΓ; split; [ intros x y Hxy; cbn; lia |].
  revert RΨ HΨ; induction Ψ as [| e Ψ IH]; intros RΨ HΨ ρ ρ' Hρ; cbn [List.app List.length] in *.
  - rewrite !eval_wk_shiftn; cbn [List.skipn].
    assert (E : RΨ <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption). apply E; exact Hρ.
  - destruct (rel_wk_shift_tail HΨ) as (R' & HR' & Hsh).
    pose proof (Hsh _ _ Hρ) as Ht; rewrite !eval_wk_shift in Ht.
    rewrite !eval_wk_shiftn; cbn [List.skipn].
    destruct ρ as [| d ρ], ρ' as [| d' ρ']; cbn [drop_env List.tl] in Ht;
      (pose proof (IH _ HR' _ _ Ht) as H; rewrite !eval_wk_shiftn in H; try exact H);
      rewrite List.skipn_nil in *; exact H.
Qed.

(** An entry past the prefix [Ψ] is a proposition exactly as the entry of
    [Γ] it is. *)
Lemma entry_propositional_shiftn : forall Ψ Γ ρ x,
    entry_propositional gc_deps gc_stack (Ψ ++ Γ) ρ (List.length Ψ + x) ->
    entry_propositional gc_deps gc_stack Γ (List.skipn (List.length Ψ) ρ) x.
Proof.
  intros * [T HT E HE a Ea Hp]; econstructor; [ | | exact Ea | exact Hp ].
  - unfold ctx_entry_type in *; rewrite List.nth_error_app2 in HT by lia.
    replace (List.length Ψ + x - List.length Ψ) with x in HT by lia; exact HT.
  - intros y Hy.
    rewrite (HE y) by (rewrite !List.length_skipn, List.length_app in *; lia).
    rewrite !env_entry_skipn; f_equal; lia.
Qed.

(** And conversely: an entry of [Γ] past the prefix [Ψ] that is a
    proposition is one of [Ψ ++ Γ]. *)
Lemma entry_propositional_shiftn_intro : forall Ψ Γ ρ x,
    entry_propositional gc_deps gc_stack Γ (List.skipn (List.length Ψ) ρ) x ->
    entry_propositional gc_deps gc_stack (Ψ ++ Γ) ρ (List.length Ψ + x).
Proof.
  intros * [T HT E HE a Ea Hp]; econstructor; [ | | exact Ea | exact Hp ].
  - unfold ctx_entry_type in *; rewrite List.nth_error_app2 by lia.
    replace (List.length Ψ + x - List.length Ψ) with x by lia; exact HT.
  - intros y Hy.
    rewrite (HE y) by (rewrite !List.length_skipn, List.length_app in *; lia).
    rewrite !env_entry_skipn; f_equal; lia.
Qed.

(** Dropping a prefix of a context is a semantic weakening, given the
    context PERs of the context and of its tail. *)
Lemma rel_wk_under_ctx_shiftn_per : forall Ψ Γ R RΓ,
    EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ R -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    Ψ ++ Γ ⊨ʷ (wk_shiftn (List.length Ψ)) : Γ.
Proof.
  intros * HR HΓ.
  eapply rel_wk_under_ctx_intro; [ exact HR | exact HΓ | exact (rel_wk_shiftn _ _ _ _ HR HΓ)
                                 | intros x Hx; cbn [wk_shiftn]; rewrite List.length_app; lia |].
  intros ρ ρ' _ x _; rewrite eval_wk_shiftn; cbn [wk_shiftn]; rewrite PeanoNat.Nat.add_comm; split;
    [ apply entry_propositional_shiftn | apply entry_propositional_shiftn_intro ].
Qed.

Corollary rel_wk_under_ctx_shiftn : forall Ψ Γ, ⊨ Ψ ++ Γ -> Ψ ++ Γ ⊨ʷ (wk_shiftn (List.length Ψ)) : Γ.
Proof.
  intros * H.
  destruct (rel_ctx_wf_per_ctx_env H) as [R HR].
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ H)) as [RΓ HΓ].
  exact (rel_wk_under_ctx_shiftn_per _ _ _ _ HR HΓ).
Qed.

End Fixed_GCtx.
