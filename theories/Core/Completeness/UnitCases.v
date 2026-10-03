(** * Units: the Closures of Related Units are Related

    A unit's closure is related to another's when their parameters, read
    outermost first, and their entries, read in order, are related.  A context
    PER of the units' extended contexts says exactly that: its parameter
    entries relate the parameter types, its definition entries the types and
    bodies, and its slot entries the closures of the nested units.  This file
    walks such a PER to produce the module PER of the closures. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases SubstitutionCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

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

(** The relation of an extension by a slot, with its tail relation fixed. *)
Lemma per_ctx_env_cons_mod_inversion : forall {Γ Γ' U U' RΓ R},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF Γ ▹ₘ U ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', RΓ ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil)) /\
    (R <~> fun ρ ρ' =>
       RΓ ρ↯ ρ'↯ /\
       per_dmod (env_mod ρ 0) (dm_local ρ↯ U nil) /\
       per_dmod (env_mod ρ 0) (dm_local ρ↯ U' nil) /\
       per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U nil) /\
       per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U' nil)).
Proof.
  intros * HΓ H; inversion H; subst.
  match goal with Ht : per_ctx_env ?T Γ Γ' |- _ =>
    assert (HT : T <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption) end.
  split.
  - intros ρ ρ' Hρ; apply H6, HT, Hρ.
  - intros ρ ρ'; split; intros Hρ;
      [ apply H7 in Hρ as (Ht & ?); split; [ apply HT; assumption | assumption ]
      | apply H7; destruct Hρ as (Ht & ?); split; [ apply HT; assumption | assumption ] ].
Qed.

(** ** Walking Parameters

    A telescope of parameters is walked outermost first, so it is given as the
    reversed context.  At the end of the walk, the environments are related
    in the extended context's PER. *)

Lemma walk_params : forall ts ts' Γ Γ' RΓ R D D',
    tele_ass ts -> tele_ass ts' -> List.length ts = List.length ts' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF rev ts ++ Γ ≈ rev ts' ++ Γ' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', R ρ ρ' -> per_mdef ρ D ρ' D') ->
    forall ρ ρ', RΓ ρ ρ' -> per_ltele ts ρ D ts' ρ' D' nil nil.
Proof.
  induction ts as [| e ts IH]; intros [| e' ts'] * Hts Hts' Hl HΓ HR HD ρ ρ' Hρ; cbn in Hl; try discriminate.
  - constructor; apply HD.
    assert (HRR : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    apply HRR, Hρ.
  - inversion Hts as [| ? ? [A ->] Hts0]; inversion Hts' as [| ? ? [A' ->] Hts0']; subst.
    cbn [rev] in HR; rewrite <- !app_assoc in HR; cbn [app] in HR.
    destruct (per_ctx_env_app_tail (rev ts) (rev ts') _ _ _ ltac:(rewrite !length_rev; congruence) HR)
      as [R1 HR1].
    destruct (per_ctx_env_cons_clean_inversion HΓ HR1) as (i & head_rel & Hhead & HE).
    eapply per_ltele_missing with (R := head_rel _ _ Hρ); [ apply Hhead |].
    intros c c' Hc.
    eapply IH; [ eassumption | eassumption | congruence | exact HR1 | exact HR | exact HD |].
    apply HE; exists Hρ; exact Hc.
Qed.

Lemma body_shape_binders : forall Φ Φ', body_shape Φ Φ' -> gm_binders Φ = gm_binders Φ'.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros [| Φ' y' E' | Φ' c'] Hs; cbn in *; try contradiction; auto.
  - destruct Hs as (Hs & _ & _); f_equal; auto.
  - destruct Hs as (Hs & _); auto.
Qed.

(** ** Walking a Body

    Each entry is read in the environment its predecessors make; the
    environments the body makes are related in the extended context's PER. *)

Lemma walk_body : forall Φ Φ' Θ Θ' RΘ R,
    body_shape Φ Φ' ->
    EF Θ ≈ Θ' ∈ per_ctx_env ↘ RΘ ->
    EF body_ctx Φ ++ Θ ≈ body_ctx Φ' ++ Θ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', RΘ ρ ρ' ->
      per_body ρ Φ ρ' Φ' /\
      exists ρ1 ρ1', eval_benv gc_deps gc_stack ρ Φ ρ1 /\ eval_benv gc_deps gc_stack ρ' Φ' ρ1' /\ R ρ1 ρ1'.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros [| Φ' y' E' | Φ' c'] * Hs HΘ HR ρ ρ' Hρ;
    cbn in Hs; try contradiction.
  - assert (HRR : R <~> RΘ) by (eapply per_ctx_env_right_irrel; eassumption).
    split; [ constructor |]; exists ρ, ρ'; repeat split; try constructor; apply HRR, Hρ.
  - destruct Hs as (Hs & <- & HE).
    destruct E as [b pv A [M |] | Uy], E' as [b' pv' A' [M' |] | Uy']; cbn in HE; try contradiction.
    + (* a definition *)
      cbn [body_ctx app] in HR.
      inversion HR; subst.
      match goal with
      | Htyp : forall ρ0 ρ'0 (e : tail_rel ρ0 ρ'0), rel_typ _ A _ A' _ _,
        Helem : forall ρ0 ρ'0 (e : tail_rel ρ0 ρ'0), rel_elem M _ M' _ _,
        HER : R <~> _ |- _ =>
          destruct (IH _ _ _ _ _ Hs HΘ equiv_Γ_Γ' _ _ Hρ) as (Hb & ρ1 & ρ1' & Hb1 & Hb1' & H1);
          assert (H11 : tail_rel ρ1 ρ1) by (etransitivity; [ exact H1 | symmetry; exact H1 ]);
          assert (H1'1' : tail_rel ρ1' ρ1') by (etransitivity; [ symmetry; exact H1 | exact H1 ]);
          split;
          [ eapply per_body_def; [ exact Hb | exact Hb1 | exact Hb1' | apply (Htyp _ _ H1) | apply (Helem _ _ H1) ]
          | destruct (Helem _ _ H1) as [m m' Hm Hm' Hmm'];
            exists (ρ1 ↦ m), (ρ1' ↦ m'); repeat split; [ econstructor; eassumption | econstructor; eassumption |];
            apply HER; exists H1; cbn;
            pose proof (Htyp _ _ H11); pose proof (Htyp _ _ H1'1'); pose proof (Helem _ _ H11);
            pose proof (Helem _ _ H1'1'); pose proof (Htyp _ _ H1);
            solve_def_heads ]
      end.
    + (* a module *)
      cbn [body_ctx app] in HR.
      inversion HR; subst.
      match goal with
      | HU : forall ρ0 ρ'0, tail_rel ρ0 ρ'0 -> per_dmod _ _, HER : R <~> _ |- _ =>
          destruct (IH _ _ _ _ _ Hs HΘ equiv_Γ_Γ' _ _ Hρ) as (Hb & ρ1 & ρ1' & Hb1 & Hb1' & H1);
          assert (H11 : tail_rel ρ1 ρ1) by (etransitivity; [ exact H1 | symmetry; exact H1 ]);
          assert (H1'1' : tail_rel ρ1' ρ1') by (etransitivity; [ symmetry; exact H1 | exact H1 ]);
          split;
          [ eapply per_body_mod; [ exact Hb | exact Hb1 | exact Hb1' | apply HU, H1 ]
          | exists (ρ1 ↦ᵐ dm_local ρ1 Uy nil), (ρ1' ↦ᵐ dm_local ρ1' Uy' nil);
            repeat split; [ econstructor; eassumption | econstructor; eassumption |];
            destruct (mod_closure_move _ _ _ _ _ _ H11 HU) as (M1 & M2 & _);
            destruct (mod_closure_move _ _ _ _ _ _ H1'1' HU) as (_ & _ & M3 & M4);
            apply HER; repeat split; cbn; assumption ]
      end.
  - destruct Hs as (Hs & Hc).
    destruct (IH _ _ _ _ _ Hs HΘ HR _ _ Hρ) as (Hb & ρ1 & ρ1' & Hb1 & Hb1' & H1).
    split; [ constructor; exact Hb | exists ρ1, ρ1'; repeat split; try (constructor; assumption); exact H1 ].
Qed.

(** ** Related Closures *)

Lemma rel_closure_body : forall Γ Γ' Δ Δ' Φ Φ' RΓ R,
    tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    body_shape Φ Φ' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF body_ctx Φ ++ Δ ++ Γ ≈ body_ctx Φ' ++ Δ' ++ Γ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', RΓ ρ ρ' -> per_dmod (dm_local ρ (gu_body Δ Φ) nil) (dm_local ρ' (gu_body Δ' Φ') nil).
Proof.
  intros * HΔ HΔ' Hl Hs HΓ HR ρ ρ' Hρ.
  destruct (per_ctx_env_app_tail (body_ctx Φ) (body_ctx Φ') _ _ _ ltac:(rewrite !length_body_ctx; apply body_shape_binders; exact Hs) HR)
    as [RΔ HRΔ].
  constructor; cbn [gu_params gu_def].
  eapply walk_params; [ apply Forall_rev; exact HΔ | apply Forall_rev; exact HΔ' | rewrite !length_rev; exact Hl
                      | exact HΓ | rewrite !rev_involutive; exact HRΔ | | exact Hρ ].
  intros ρ1 ρ1' Hρ1; constructor.
  exact (proj1 (walk_body _ _ _ _ _ _ Hs HRΔ HR _ _ Hρ1)).
Qed.

Lemma rel_closure_alias : forall Γ Γ' Δ Δ' E E' RΓ R,
    tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF Δ ++ Γ ≈ Δ' ++ Γ' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', R ρ ρ' -> exists h h', eval_modexp gc_deps gc_stack E ρ h /\
                                     eval_modexp gc_deps gc_stack E' ρ' h' /\ per_dmod h h') ->
    forall ρ ρ', RΓ ρ ρ' ->
      per_dmod (dm_local ρ (gu_mk Δ (md_alias E)) nil) (dm_local ρ' (gu_mk Δ' (md_alias E')) nil).
Proof.
  intros * HΔ HΔ' Hl HΓ HR HE ρ ρ' Hρ.
  constructor; cbn [gu_params gu_def].
  eapply walk_params; [ apply Forall_rev; exact HΔ | apply Forall_rev; exact HΔ' | rewrite !length_rev; exact Hl
                      | exact HΓ | rewrite !rev_involutive; exact HR | | exact Hρ ].
  intros ρ1 ρ1' Hρ1; destruct (HE _ _ Hρ1) as (h & h' & ? & ? & ?); econstructor; eassumption.
Qed.

(** ** Slots

    The context PER of a slot, its semantic substitutions, and what the
    validity of a unit says of its closures. *)

Definition env_ext_mod (U U' : gunit) (R : relation env) : relation env :=
  fun ρ ρ' =>
    R ρ↯ ρ'↯ /\
    per_dmod (env_mod ρ 0) (dm_local ρ↯ U nil) /\
    per_dmod (env_mod ρ 0) (dm_local ρ↯ U' nil) /\
    per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U nil) /\
    per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U' nil).

(** The closures of a valid unit, along a substitution. *)
Lemma unit_chain : forall {Γ U U'},
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    exists R (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ R),
    forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
      Γ' ⊨s σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        R' ρ ρ' -> ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_chain per_dmod ([dm_local ρ U[σ]ᵘ nil; dm_local ρσ U nil; dm_local ρ'σ' U' nil; dm_local ρ' U'[σ']ᵘ nil]).
Proof.
  intros * [R [HΓ HU]]; exists R, HΓ; intros * HΓ' * Hσ * Hρ Hev Hev'.
  destruct (HU _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [h1 h2 h3 h4 H1 H2 H3 H4 Hc].
  cbn [modexp_sub] in H1, H4.
  inversion H1; inversion H2; inversion H3; inversion H4; subst; exact Hc.
Qed.

Lemma unit_chain_at : forall {Γ U U' R},
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil).
Proof.
  intros * HU HΓ ρ ρ' Hρ.
  destruct (unit_chain HU) as [R0 [HΓ0 Hc]].
  assert (E : R <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (Hc _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _)) as Hch.
  destruct Hch as (_ & H & _); exact H.
Qed.

Lemma per_ctx_env_of_mod : forall {Γ U U' R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    EF Γ ▹ₘ U ≈ Γ ▹ₘ U' ∈ per_ctx_env ↘ env_ext_mod U U' R.
Proof.
  intros * HΓ HU.
  eapply per_ctx_env_cons_mod; [ exact HΓ | eapply per_env_PER; exact HΓ | | reflexivity ].
  intros; eapply unit_chain_at; eassumption.
Qed.

Lemma per_ctx_env_of_mod_sub : forall {Γ' Γ σ σ' U R'},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨s σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    EF Γ' ▹ₘ U[σ]ᵘ ≈ Γ' ▹ₘ U[σ]ᵘ ∈ per_ctx_env ↘ env_ext_mod U[σ]ᵘ U[σ]ᵘ R'.
Proof.
  intros * HΓ' Hσ HU.
  eapply per_ctx_env_cons_mod; [ exact HΓ' | eapply per_env_PER; exact HΓ' | | reflexivity ].
  intros ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσ) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [RΓ [HΓ0 Hs]]]].
  assert (E : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (ρσ & ρ'σ & Hev & Hev' & _).
  destruct (unit_chain HU) as [R0 [HΓ00 Hc]].
  pose proof (Hc _ _ HΓ' _ _ Hσσ _ _ _ _ Hρ Hev Hev') as Hch.
  assert (PER per_dmod) by typeclasses eauto.
  pairwise.
Qed.

(** [q σ] into a slot.  The four tails come from [σ] at the Kripke stage, as
    for an assumption; the head is the same module value on each side, tied to
    the closures of [U[σ]] over the stage's tails, which the validity of [U]
    relates to the closures of [U] over the tails of [q σ]. *)
Lemma rel_sub_under_ctx_q_mod : forall {Γ' Γ σ σ' U},
    Γ' ⊨s σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    Γ' ▹ₘ U[σ]ᵘ ⊨s q σ ≈ q σ' : Γ ▹ₘ U.
Proof.
  intros * Hσj HU.
  pose proof Hσj as [R' [HΓ' [R [HΓ Hσ]]]].
  pose proof (per_ctx_env_of_mod_sub HΓ' Hσj HU) as HΓ'U.
  pose proof (per_ctx_env_of_mod HΓ HU) as HΓU.
  pose proof (rel_wk_shift HΓ' HΓ'U) as Hshift.
  pose proof (rel_sub_under_ctx_wk Hσj (rel_wk_under_ctx_intro HΓ'U HΓ' Hshift)) as Hσwkj.
  pose proof Hσwkj as [R'U [HΓ'U' [R2 [HΓ2 Hσwk]]]].
  assert (E1 : R'U <~> env_ext_mod U[σ]ᵘ U[σ]ᵘ R') by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R2 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  destruct (unit_chain HU) as [R0 [HΓ0 Hch]].
  exists (env_ext_mod U[σ]ᵘ U[σ]ᵘ R'), HΓ'U, (env_ext_mod U U R), HΓU.
  intros Γ'' R'' HΓ'' ψ Hψ ρ ρ' Hρ.
  destruct (Hψ _ _ Hρ) as (Htail & Tρ & _ & Tρ' & _).
  destruct (Hσwk _ _ HΓ'' _ (proj2 (rel_wk_morphism ψ _ _ (reflexivity R'') _ _ E1) Hψ) _ _ Hρ)
    as [x1 y1 y4 x4 Hx1 Hy1 Hy4 Hx4 Htails].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (E2 a b) H)) in Htails.
  destruct (Hσ _ _ HΓ'U _ Hshift _ _ (Hψ _ _ Hρ)) as [z1 y2 y3 z4 Hz1 Hy2 Hy3 Hz4 Hbtails].
  rewrite ?eval_wk_shift in *.
  assert (Heq1 : env_eq y1 z1) by (eapply functional_eval_sub; eassumption).
  assert (Heq4 : env_eq y4 z4) by (eapply functional_eval_sub; eassumption).
  assert (Hy12 : R y1 y2) by (rewrite Heq1; pairwise).
  assert (Hy43 : R y4 y3) by (rewrite Heq4; pairwise).
  (** The closures of [U[σ]] over the stage's tails, against those of [U]. *)
  assert (Htl : R' (⟪ψ⟫ ρ)↯ (⟪ψ⟫ ρ)↯) by (etransitivity; [ exact Htail | symmetry; exact Htail ]).
  assert (Htr : R' (⟪ψ⟫ ρ')↯ (⟪ψ⟫ ρ')↯) by (etransitivity; [ symmetry; exact Htail | exact Htail ]).
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (Hch _ _ HΓ' _ _ Hσσ _ _ _ _ Htl Hy2 Hy2) as C1.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [R3 [HΓ3 Hs]]]].
  assert (E3 : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E4 : R3 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E3 _ _) Htr)) as (w & _ & Hw & _ & _).
  pose proof (Hch _ _ HΓ' _ _ Hσσ _ _ _ _ Htr Hw Hw) as C2.
  assert (Hw3 : R w y3) by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  assert (Hm : forall t, R t y2 -> per_dmod (env_mod ρ (ψ 0)) (dm_local t U nil)).
  { intros t Ht; rewrite <- (eval_wk_app_mod ψ).
    eapply per_dmod_trans; [ exact Tρ |].
    eapply per_dmod_trans; [ destruct C1 as (C & _); exact C |].
    destruct (mod_closure_move _ _ _ _ _ HPR (symmetry Ht) (unit_chain_at HU HΓ)) as (M & _); exact M. }
  assert (Hm' : forall t, R t w -> per_dmod (env_mod ρ' (ψ 0)) (dm_local t U nil)).
  { intros t Ht; rewrite <- (eval_wk_app_mod ψ).
    eapply per_dmod_trans; [ exact Tρ' |].
    eapply per_dmod_trans; [ destruct C2 as (C & _); exact C |].
    destruct (mod_closure_move _ _ _ _ _ HPR (symmetry Ht) (unit_chain_at HU HΓ)) as (M & _); exact M. }
  assert (Hl : forall t, In t (x1 :: y1 :: nil) -> R t y2)
    by (intros t Ht; etransitivity; [| exact Hy12 ]; eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ];
        destruct Ht as [<- | [<- | []]]; solve_in).
  assert (Hr : forall t, In t (y4 :: x4 :: nil) -> R t w).
  { intros t Ht; etransitivity; [| symmetry; exact Hw3 ]; etransitivity; [| exact Hy43 ].
    eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ].
    destruct Ht as [<- | [<- | []]]; solve_in. }
  apply (mk_rel_sub (env_entry ρ (ψ 0) :: x1) (env_entry ρ (ψ 0) :: y1)
                    (env_entry ρ' (ψ 0) :: y4) (env_entry ρ' (ψ 0) :: x4));
    [ apply eval_sub_wk_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | apply eval_sub_wk_q; eassumption
    | ].
  cbn [rel_chain]; unfold env_ext_mod; cbn [drop_env tl].
  unfold env_mod in Hm, Hm' |- *; cbn [env_entry hd] in Hm, Hm' |- *.
  repeat split.
  all: try solve [ eapply (rel_chain_pairwise R); [ exact Htails | solve_in | solve_in ]
          | apply Hm, Hl; solve_in | apply Hm', Hr; solve_in ].
Qed.

End Fixed_GCtx.
