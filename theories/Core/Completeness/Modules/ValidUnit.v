(** * Valid Units: Properties

    The valid units ([valid_unit]) and module expressions valid in what they
    denote ([valid_modexp]) are defined in [LogicalRelation/Definitions.v]; this file
    proves their properties.  A context has valid slots ([valid_ctx]) exactly
    when it is semantically well formed and each slot holds a unit valid in
    the context before it ([valid_ctx_iff]).  Descriptions are read at
    [Θm ⍮ Ξm], a global context the target one extends. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases PropCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Variables (Θm : gdeps) (Ξm : gstack).

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_modexp := (valid_modexp Θm Ξm).

(** The slots of a context (its modules and the module parts of its
    definitions with one, [centry_unit]) hold valid units, each in the
    context before it. *)
Definition valid_slots (Γ : ctx) : Prop :=
  forall Γ1 e U Γ0, Γ = Γ1 ++ e :: Γ0 -> centry_unit e = Some U -> valid_unit Γ0 (me_lit U).

(** A context with valid slots is a semantically well-formed one whose
    slots hold valid units. *)
Lemma valid_ctx_iff : forall Γ, valid_ctx Θm Ξm Γ <-> ⊨ Γ /\ valid_slots Γ.
Proof.
  induction Γ as [| e Γ IH]; split.
  - intros _; split; [ constructor | intros Γ1 e U Γ0 H; destruct Γ1; discriminate ].
  - intros _; constructor.
  - intros H; inversion H; subst; (split; [ assumption |]);
      intros [| e1 Γ1] e0 U0 Γ0 Heq Hu; cbn in Heq; inversion Heq; subst; cbn in Hu;
      first [ discriminate | injection Hu as <-; assumption
            | eapply (proj2 (proj1 IH ltac:(assumption))); [ reflexivity | exact Hu ] ].
  - intros [H Hok]; destruct e as [κ A | A M | U | A M U]; inversion H; subst.
    + apply valid_ctx_ass; [ apply IH; split; [ assumption |] | assumption ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_ass κ A :: Γ1) e0 U0 Γ0 eq_refl Hu).
    + apply valid_ctx_def; [ apply IH; split; [ assumption |] | assumption ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_def A M :: Γ1) e0 U0 Γ0 eq_refl Hu).
    + apply valid_ctx_mod; [ apply IH; split; [ assumption |] | assumption | exact (Hok nil _ U Γ eq_refl eq_refl) ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_mod U :: Γ1) e0 U0 Γ0 eq_refl Hu).
    + apply valid_ctx_dm; [ apply IH; split; [ assumption |] | assumption | exact (Hok nil _ U Γ eq_refl eq_refl) ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_dm A M U :: Γ1) e0 U0 Γ0 eq_refl Hu).
Qed.

Lemma valid_unit_ctx_wf : forall Γ K, valid_unit Γ K -> ⊨ Γ.
Proof. intros * H; destruct H; assumption. Qed.

Lemma valid_unit_wf : forall Γ K, valid_unit Γ K -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ K ≈ K.
Proof. intros * H; destruct H; assumption. Qed.

Lemma valid_modexp_wf : forall Γ H, valid_modexp Γ H -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * H; destruct H; assumption. Qed.

Lemma valid_modexp_rel : forall Γ H, valid_modexp Γ H -> Γ ⊨ᵐ H ≈ H.
Proof.
  intros * Hs; destruct Hs as [Γ H R Rm K RK _ _ _ HHK _ _ _].
  eapply rel_modexp_under_ctx_trans; [ exact HHK | apply rel_modexp_under_ctx_sym; exact HHK ].
Qed.

(** ** Instances of Valid Terms *)

(** At a type of an evaluated kind, the values of a valid term along a
    substitution and in the environment it evaluates to are related. *)
Lemma valid_inst : forall Δ M A D τ RD, Δ ⊨ M : A -> rel_type_evaluated Δ A ->
    D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ : Δ ⟧s ρ ↘ ρτ ->
    exists m1 m2 a i R, ⟦ M[τ] ⟧ ρ ↘ m1 /\ ⟦ M ⟧ ρτ ↘ m2 /\ ⟦ A ⟧ ρτ ↘ a /\ per_univ_elem i R a a /\ R m1 m2.
Proof.
  intros * [RΔ HΔ i Hgen] HArel Hτ HD ρ ρτ Hρ Hev.
  destruct (Hgen _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [E [HT HMexp]].
  pose proof (rel_sub_under_ctx_at' Hτ HD HΔ _ _ _ _ Hρ Hev Hev) as Hρτ.
  apply (rel_exp_or_prop_evaluated HT (rel_typ_evaluated_at HArel HΔ _ _ Hρτ)) in HMexp.
  destruct HT as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & T23 & _)].
  destruct HMexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 (M12 & _)].
  exists m1, m2, a2, i, E; repeat split; try assumption.
  etransitivity; [ symmetry; exact T12 | exact T12 ].
Qed.

(** At a type of an evaluated kind, the values of a valid term at related
    environments are related. *)
Lemma valid_at : forall Δ M A k RΔ, Δ ⊨ M : A -> Δ ⊨ᵗ A ≈ A at k -> rel_type_evaluated Δ A ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ ->
    forall ρ ρ', RΔ ρ ρ' ->
    exists m m' a i R, ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ ⟦ A ⟧ ρ ↘ a /\ per_univ_elem i R a a /\ R m m'.
Proof.
  intros * HM HA HArel HΔ ρ ρ' Hρ.
  destruct (rel_exp_under_ctx_simple_at_of_evaluated HΔ (rel_typ_evaluated_at HArel HΔ) HM _ _ Hρ) as (m & m' & Em & Em' & Hmm).
  destruct (rel_type_inversion_simple_at HΔ HA _ _ Hρ) as (a & a' & Ea & Ea' & [R HR]).
  exists m, m', a, k, R.
  split; [ exact Em | split; [ exact Em' | split; [ exact Ea | split ] ] ];
    [ etransitivity; [ exact HR | symmetry; exact HR ] | exact (Hmm _ _ _ _ Ea Ea' HR) ].
Qed.

(** A type of a relevant sort (a universe or [LevelSort]) is a type of an
    index, of an evaluated kind. *)
Lemma rel_type_of_evaluated_sort : forall {Γ A Srt}, evaluated_sort Srt -> Γ ⊨ A : Srt ->
    (exists k : nat, Γ ⊨ᵗ A ≈ A at k) /\ rel_type_evaluated Γ A.
Proof.
  intros * [i |] HA.
  - split; [ exists i; exact (rel_type_of_typ HA) | exact (rel_type_evaluated_of_typ HA) ].
  - split; [ exists 0; exact (rel_type_of_level_sort 0 HA) | exact (rel_type_evaluated_of_level_sort HA) ].
Qed.

(** A type of either sort, along a semantic substitution: its value under
    the substitution against its value at the substitution's value. *)
Lemma rel_type_inst : forall Δ A i D τ RD, Δ ⊨ᵗ A ≈ A at i -> D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ : Δ ⟧s ρ ↘ ρτ ->
    exists a1 a2, ⟦ A[τ] ⟧ ρ ↘ a1 /\ ⟦ A ⟧ ρτ ↘ a2 /\ Dom a1 ≈ a2 ∈ per_univ i.
Proof.
  intros * HA Hτ HD ρ ρτ Hρ Hev.
  pose proof (rel_type_inversion HA) as [R0 [HΔ0 HAgen]].
  destruct (HAgen _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & _)].
  exists a1, a2; repeat split; assumption.
Qed.

(** An element PER of a type related to [a] is the element PER [a] has. *)
Lemma per_univ_irrel_rel : forall i R a a' j t k Q t',
    per_univ_elem i R a a' -> Dom a ≈ t ∈ per_univ j -> per_univ_elem k Q t t' -> (R <~> Q).
Proof.
  intros * HR [S HS] HQ.
  destruct (per_univ_elem_sym _ _ _ _ HS) as [HS' _].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HS' HR) as (T & HT & _).
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HT HQ) as E1.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR HT) as E2.
  rewrite E2; exact E1.
Qed.

(** The same, for a type of a universe. *)
Corollary valid_typ_inst : forall Δ A i D τ RD, Δ ⊨ A : Typeω@i -> D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ : Δ ⟧s ρ ↘ ρτ ->
    exists a1 a2, ⟦ A[τ] ⟧ ρ ↘ a1 /\ ⟦ A ⟧ ρτ ↘ a2 /\ Dom a1 ≈ a2 ∈ per_univ i.
Proof. intros * HA; exact (rel_type_inst _ _ _ _ _ _ (rel_type_of_typ HA)). Qed.

Lemma valid_mod_inst : forall Δ H D τ RD, Δ ⊨ᵐ H ≈ H -> D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ : Δ ⟧s ρ ↘ ρτ ->
    exists h1 h2, ⟦ H[τ]ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h1 /\ ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρτ ↘ h2 /\ per_dmod h1 h2.
Proof.
  intros * [R0 HΔ0 HH] Hτ HD ρ ρτ Hρ Hev.
  destruct (HH _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [h1 h2 h3 h4 H1 H2 H3 H4 (C12 & _)].
  exists h1, h2; repeat split; assumption.
Qed.

(** A term over parameters, generalized over them: a function into a type
    of a universe, or a proof of a [∀]; as [valid_exp_under_ctx_ctx_pi_at],
    not into a type of levels. *)
Lemma valid_exp_under_ctx_ctx_fn : forall r Ψ D M X i, r <> ak_level -> all_assumptions Ψ -> ⊨ Ψ ++ D ->
    Ψ ++ D ⊨ X : abs_kind_sort r Typeω@i -> Ψ ++ D ⊨ M : X ->
    D ⊨ ctx_fn Ψ M : ctx_pi_at r Ψ X.
Proof.
  intros [| |] Ψ; [| | intros * Hr; contradiction ].
  - induction Ψ as [| e Ψ IH]; intros * _ HΨ HC HX HM; cbn in *; [ exact HM |].
    inversion HΨ as [| ? ? (κ & B & ->) HΨ']; subst.
    destruct (rel_ctx_wf_ass_type HC) as [k HB].
    pose proof (rel_ctx_wf_ass_kind HC) as HBk.
    apply (IH _ _ _ (max i k)); [ discriminate | exact HΨ' | exact (rel_ctx_wf_tail HC) | |].
    + apply rel_exp_under_ctx_pi_cong; [ apply HB; lia | apply HB; lia | exact HBk | eapply rel_exp_cumu_ge; [| exact HX ]; lia ].
    + apply (rel_exp_under_ctx_fn_cong (i := max i k));
        [ apply HB; lia | apply HB; lia | exact HBk | eapply rel_exp_cumu_ge; [| exact HX ]; lia | exact HM ].
  - intros * Hr HΨ HC HX HM.
    destruct (valid_exp_under_ctx_ctx_pi_at ak_propositional _ _ _ _ Hr HΨ HC HX) as [j Hj].
    exact (rel_exp_under_ctx_proof Hj).
Qed.

(** The expansion of a well formed unit's body is scoped by the context
    of the body, its parameters before the unit's context. *)
Lemma body_xp_scoped_of_wf : forall Γ Δ Φ Φx,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> gmod_scoped (List.length (Δ ++ Γ)) Φx.
Proof.
  intros * Hw Hx.
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wf_scoped))))))) _ _ _ _ _ Hw)
    as ([HΓ Hc] & HU & _).
  cbn [modexp_scoped] in HU; apply gunit_scoped_mk in HU as [HΔ [_ HΦ]].
  assert (HΔΓ : ctx_scoped 0 (Δ ++ Γ)) by (apply ctx_scoped_app_iff; split; assumption).
  eapply (proj1 (proj2 (proj2 (proj2 (mdenote_scoped_all _ _ Hc))))); [ exact Hx | exact (slots_ok_ctx _ HΔΓ) |].
  rewrite length_app; exact HΦ.
Qed.

(** ** A Body Filled in, Against its Environment

    The substitution filling in the entries of a body without opens is
    built from valid parts, and at an environment of the context it
    extends evaluates to one related to the environment the body makes
    there. *)

Lemma fill_gsub : forall Φ D σ, gm_nopens Φ = 0 -> gm_fill Φ = Some σ -> ⊨ body_ctx Φ ++ D ->
    gmod_scoped (List.length D) Φ ->
    gsub D σ (body_ctx Φ ++ D).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hn Hf HC Hs; cbn in Hn, Hf; [| | discriminate ].
  - injection Hf as <-; constructor; exact HC.
  - cbn [gmod_scoped] in Hs; destruct Hs as [Hs HsE].
    (** The entry is scoped by the body before it and [D]. *)
    rewrite <- (length_body_ctx _ Hn), <- List.length_app in HsE.
    destruct E as [b pv ra A [M |] | pv U | ? ? ? ? ? | ? ? ? ? | ? ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HC; cbn [gentry_scoped] in HsE.
    + destruct (rel_ctx_wf_def_inv HC) as [(Srt & HS & HA) HM].
      eapply gsub_def; [ apply IH; [ exact Hn | reflexivity | exact (rel_ctx_wf_tail HC) | exact Hs ]
                       | exact HS | exact HA | exact HM | exact (proj2 HsE) ].
    + eapply gsub_mod; [ apply IH; [ exact Hn | reflexivity | exact (rel_ctx_wf_tail HC) | exact Hs ]
                       | exact (rel_ctx_wf_mod_inv HC) | exact HsE ].
    + destruct (rel_ctx_wf_dm_inv HC) as ([i HA] & HM & HU).
      eapply gsub_dm; [ apply IH; [ exact Hn | reflexivity | exact (rel_ctx_wf_tail HC) | exact Hs ]
                      | exact HA | exact HM | exact HU | exact (proj1 (proj2 HsE)) | exact (proj2 (proj2 HsE)) ].
Qed.

(** Related elements read back as the term parts of definition entries
    with module parts, stored at the closures of their types. *)
Lemma dm_entry_readable_of_elem_closure : forall {i A A' ρ ρ' a a' R v v'},
    ⟦ A ⟧ ρ ↘ a -> ⟦ A' ⟧ ρ' ↘ a' -> DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom v ≈ v' ∈ R ->
    forall h h' U U',
      entry_readable (de_dm v (entry_type_closure A ρ) h U) /\ entry_readable (de_dm v' (entry_type_closure A' ρ') h' U').
Proof.
  intros * Ea Ea' HR Hv *; split; intros s;
    destruct (per_univ_then_per_top_typ HR s) as [T T' HT HT' _];
    destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _];
    eexists; eapply read_entry_dm; solve [ eapply eval_entry_type_closure; eassumption | eassumption ].
Qed.

Lemma fill_rel : forall Φ D σ, gm_nopens Φ = 0 -> gm_fill Φ = Some σ -> ⊨ body_ctx Φ ++ D -> body_sorts_valid Φ D ->
    gmod_scoped (List.length D) Φ ->
    forall R RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> EF body_ctx Φ ++ D ≈ body_ctx Φ ++ D ∈ per_ctx_env ↘ R ->
    forall ρ, RD ρ ρ -> exists ρσ ρ1, ⟦ σ : body_ctx Φ ++ D ⟧s ρ ↘ ρσ /\ ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ R ρσ ρ1.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hn Hf HC Hsv Hs R RD HD HR ρ Hρ; cbn in Hn, Hf; [| | discriminate ].
  - (** The identity evaluates to the retagged environment. *)
    injection Hf as <-.
    assert (E : R <~> RD) by (eapply per_ctx_env_right_irrel; eassumption).
    exists (ctx_retag D ρ), ρ; split; [ exact (proj1 (eval_sub_id_rel HD Hρ)) | split; [ constructor |] ].
    apply E; exact (per_ctx_env_retag_left HD _ _ Hρ).
  - cbn [gmod_scoped] in Hs; destruct Hs as [Hs HsE].
    rewrite <- (length_body_ctx _ Hn), <- List.length_app in HsE.
    destruct E as [b pv ra A [M |] | pv U | ? ? ? ? ? | pv A M [Δy Dy] | ? ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HC, HR; cbn [body_sorts_valid entry_tm entry_kind] in Hsv;
      cbn [gentry_scoped] in HsE.
    + (* a definition: its filled-in body at the environment, against its value in the body's *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      destruct (rel_ctx_wf_def_inv HC) as [_ HM].
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (IH _ _ Hn eq_refl HC0 (proj1 Hsv) Hs _ _ HD HR0 _ Hρ) as (ρσ0 & ρ10 & Hσ0 & Hb0 & H0).
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0 Hs)) as Hτ.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      (** The tag [ra] is the sort of [A] ([body_sorts_valid]). *)
      destruct (proj2 Hsv _ _ eq_refl) as [i0 HA].
      destruct (evaluated_kind_or_propositional ra) as [Hra | ->].
      2:{ (* a proof: kept on both sides, neither body evaluated *)
        cbn [abs_kind_sort] in HA.
        pose proof (per_ctx_env_of_def_prop (M := M) HR0 HA) as HR'.
        assert (EQ : R <~> per_env_extend A A R0) by (eapply per_ctx_env_right_irrel; eassumption).
        destruct (rel_exp_of_prop_inversion_simple_at HR0 HA _ _ H0) as (a & a' & Ha & Ha' & Haa').
        pose proof Haa' as [Hl Hr _].
        (** The kept proofs read back: [M[σ0]] is scoped by [D], [M] by the
            body's context. *)
        pose proof Hτ as [_ _ _ _ _ Hτs].
        assert (HMσ : exp_scoped (List.length D) M[σ0])
          by (eapply exp_scoped_sub; [ exact (proj2 HsE) | intros x Hx; exact (proj1 (Hτs x Hx)) ]).
        destruct (per_ctx_env_kept_proof_readable _ _ _ M[σ0] HD (exp_scoped_free_bound _ _ HMσ) _ _ Hρ) as [Rp1 _].
        destruct (per_ctx_env_kept_proof_readable _ _ _ M HR0 (exp_scoped_free_bound _ _ (proj2 HsE)) _ _ H0) as [_ Rp2].
        assert (Ha'a' : per_prop a' a') by (etransitivity; [ symmetry; exact Haa' | exact Haa' ]).
        pose proof (entry_readable_of_elem_closure Ha' Ha' (per_univ_elem_of_prop 0 _ _ Ha'a') (conj Rp2 Rp2)) as [Rc _].
        pose proof (per_head_proof (S' := A) (ρ' := ρ10) Ha Hl Rp1 Rp2) as Hhd.
        (** The substitution's head is stored at [A] over its tail. *)
        destruct (per_head_closure_readable (per_ctx_env_of_typ (κ := ak_propositional) HR0 (rel_type_of_prop 0 HA)) HR0 H0 Hhd) as [Rl _].
        exists (ρσ0 ↦ ⋆ᵈ⟨M[σ0], ρ⟩ ⦂ centry_tag (ce_def A M) (body_ctx Φ ++ D) ρσ0),
          (ρ10 ↦ ⋆ᵈ⟨M, ρ10⟩ ⦂ entry_type_closure A ρ10); split.
        { apply eval_sub_extend_proof; [ exact Hσ0 |].
          econstructor; [ reflexivity | intros y' _; reflexivity | exact Ha | exact Hl ]. }
        split; [ eapply eval_body_env_def_proof; exact Hb0 |].
        apply EQ; apply per_env_extend_intro'; [ exact H0 | exact Hhd | exact Rl | exact Rc ]. }
      assert (HSrt : evaluated_sort (abs_kind_sort ra Typeω@i0)) by (destruct Hra; constructor).
      destruct (rel_type_of_evaluated_sort HSrt HA) as [[k HAt] HArel].
      destruct (valid_inst _ _ _ _ _ _ HM HArel Hτ HD _ _ Hρ Hσ0) as (m1 & m2 & a2 & j & Ra & Hm1 & Hm2 & Ha2 & HRa & Hm12).
      destruct (valid_at _ _ _ _ _ HM HAt HArel HR0 _ _ H0) as (m2' & m3 & a2' & j' & Ra' & Hm2' & Hm3 & Ha2' & HRa' & Hm23).
      functional_eval_rewrite_clear.
      pose proof (rel_type_inversion_simple_at HR0 HAt _ _ H0) as Htyp.
      destruct Htyp as (x & x' & Hx & Hx' & [Rx Hxx]).
      functional_eval_rewrite_clear.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa Hxx) as E1.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa' Hxx) as E2.
      assert (HPx : PER Rx) by (eapply per_elem_PER; exact Hxx).
      apply E1 in Hm12; apply E2 in Hm23.
      assert (Hm13 : Rx m1 m3) by (etransitivity; eassumption).
      pose proof (entry_readable_of_elem_closure Ha2 Hx' Hxx Hm13) as [_ Rm3].
      pose proof HArel as (rA0 & HrA0 & HAk).
      pose proof (per_ctx_env_of_def_evaluated HrA0 HR0 HAt (HAk _ HR0) HM) as HR'.
      assert (EQ : R <~> per_env_extend_def A M R0) by (eapply per_ctx_env_right_irrel; eassumption).
      assert (Hhd : per_head A A ρσ0 ρ10 m1 m3) by (eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | exact Hm13 ]).
      (** The substitution's head is stored at [A] over its tail. *)
      destruct (per_head_closure_readable (per_ctx_env_of_typ (κ := ak_relevant) HR0 HAt) HR0 H0 Hhd) as [Rm1 _].
      exists (ρσ0 ↦ m1 ⦂ centry_tag (ce_def A M) (body_ctx Φ ++ D) ρσ0), (ρ10 ↦ m3 ⦂ entry_type_closure A ρ10); split;
        [ apply eval_sub_extend;
          [ exact Hσ0 | exact (proj1 (head_not_propositional_of_evaluated (e := ce_def A M) HR0 eq_refl HAt HArel _ _ H0))
          | exact Hm1 ] |].
      split; [ eapply eval_body_env_def; [ exact Hra | exact Hb0 | exact Hm3 ] |].
      apply EQ.
      eapply per_env_extend_def_intro;
        [ exact HP0 | | | exact H0 | exact Hhd | exact Rm1 | exact Rm3 | exact Hm2 | ].
      * exact (rel_type_inversion_simple_at HR0 HAt).
      * exact (rel_exp_under_ctx_simple_at_of_evaluated HR0 (rel_typ_evaluated_at HArel HR0) HM).
      * eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | symmetry; exact Hm12 ].
    + (* a submodule: the closure of its filled-in unit, against its closure in the body's *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      pose proof (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HC)) as HU.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (IH _ _ Hn eq_refl HC0 (proj1 Hsv) Hs _ _ HD HR0 _ Hρ) as (ρσ0 & ρ10 & Hσ0 & Hb0 & H0).
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0 Hs)) as Hτ.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      pose proof (per_ctx_env_of_mod HR0 HU HsE HsE) as HR'.
      assert (EQ : R <~> per_ctx_env_mod_rel R0 (List.length (body_ctx Φ ++ D)) U U)
        by (eapply per_ctx_env_right_irrel; eassumption).
      destruct (unit_sub_chain HD Hτ HU _ _ _ _ Hρ Hσ0 Hσ0) as ([g1 g2 Hg1 Hg2 G12] & _).
      destruct (unit_chain_at HU HR0 _ _ H0) as [k2 k3 Hk2 Hk3 K23].
      pose proof (functional_eval_modexp _ _ _ _ Hg2 Hk2) as <-.
      assert (K33 : per_dmod k3 k3) by (etransitivity; [ symmetry; exact K23 | exact K23 ]).
      (** Both heads store the unit written, scoped by the body's context. *)
      assert (HrU : forall h, head_readable (List.length (body_ctx Φ ++ D)) (de_mod h U))
        by (intros h; split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HsE) ]).
      destruct U as [Δy Dy].
      exists (ρσ0 ↦ᵐ g1 ⦂ gu_mk Δy Dy), (ρ10 ↦ᵐ k3 ⦂ gu_mk Δy Dy).
      split; [ apply eval_sub_extend_mod; [ exact Hσ0 | exact Hg1 ] |].
      split; [ econstructor; [ exact Hb0 | apply eval_me_lit_iff; exact Hk3 ] |].
      apply EQ.
      constructor; cbn [drop_env tl env_mod env_entry hd extend_env_mod];
        first [ exact H0 | apply HrU | eexists; reflexivity
              | exists g2; split; [ exact Hg2 | exact G12 ] | exists k3; split; [ exact Hk3 | exact K33 ] ].
    + (* a definition with a module part: its term as a definition's, its
         unit as a submodule's *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      destruct (rel_ctx_wf_dm_inv HC) as ([i HA] & HM & HUv).
      pose proof (rel_unit_under_ctx_lit _ _ _ HUv) as HU.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (IH _ _ Hn eq_refl HC0 (proj1 Hsv) Hs _ _ HD HR0 _ Hρ) as (ρσ0 & ρ10 & Hσ0 & Hb0 & H0).
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0 Hs)) as Hτ.
      pose proof (rel_type_of_typ HA) as HAt; pose proof (rel_type_evaluated_of_typ HA) as HArel.
      destruct (valid_inst _ _ _ _ _ _ HM HArel Hτ HD _ _ Hρ Hσ0) as (m1 & m2 & a2 & j & Ra & Hm1 & Hm2 & Ha2 & HRa & Hm12).
      destruct (valid_at _ _ _ _ _ HM HAt HArel HR0 _ _ H0) as (m2' & m3 & a2' & j' & Ra' & Hm2' & Hm3 & Ha2' & HRa' & Hm23).
      functional_eval_rewrite_clear.
      pose proof (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ H0) as Htyp.
      destruct Htyp as (x & x' & Hx & Hx' & [Rx Hxx]).
      functional_eval_rewrite_clear.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa Hxx) as E1.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa' Hxx) as E2.
      assert (HPx : PER Rx) by (eapply per_elem_PER; exact Hxx).
      apply E1 in Hm12; apply E2 in Hm23.
      assert (Hm13 : Rx m1 m3) by (etransitivity; eassumption).
      pose proof (entry_readable_of_elem_closure Ha2 Hx' Hxx Hm13) as [_ Rm3].
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      assert (Hhd : per_head A A ρσ0 ρ10 m1 m3) by (eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | exact Hm13 ]).
      (** The substitution's head is stored at [A] over its tail. *)
      pose proof (per_ctx_env_of_typ (κ := ak_relevant) HR0 HAt) as HRA.
      destruct (per_head_closure_readable HRA HR0 H0 Hhd) as [Rm1 _].
      assert (Hdef : per_env_extend_def A M R0 (ρσ0 ↦ m1 ⦂ centry_tag (ce_ass ak_relevant A) (body_ctx Φ ++ D) ρσ0)
                       (ρ10 ↦ m3 ⦂ entry_type_closure A ρ10)).
      { eapply per_env_extend_def_intro;
          [ exact HP0 | | | exact H0 | exact Hhd | exact Rm1 | exact Rm3 | exact Hm2 | ].
        - exact (rel_type_inversion_simple_at HR0 HAt).
        - exact (rel_exp_under_ctx_simple_at_of_evaluated HR0 (rel_typ_evaluated_at HArel HR0) HM).
        - eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | symmetry; exact Hm12 ]. }
      destruct (unit_sub_chain HD Hτ HU _ _ _ _ Hρ Hσ0 Hσ0) as ([g1 g2 Hg1 Hg2 G12] & _).
      destruct (unit_chain_at HU HR0 _ _ H0) as [k2 k3 Hk2 Hk3 K23].
      pose proof (functional_eval_modexp _ _ _ _ Hg2 Hk2) as <-.
      assert (EQ : R <~> per_env_extend_dm A M (gu_mk Δy Dy) R0)
        by (eapply per_ctx_env_right_irrel; [ exact HR | exact (per_ctx_env_of_dm HR0 HA HM HU) ]).
      pose proof (dm_entry_readable_of_elem_closure Ha2 Hx' Hxx Hm13 g1 k3 (gu_mk Δy Dy) (gu_mk Δy Dy)) as [_ Rdm3].
      destruct (per_head_dm_readable (h := g1) (h' := k3) (U := gu_mk Δy Dy) HRA HR0 H0 Hhd) as [Rdm1 _].
      exists (ρσ0 ↦ᵈ m1 ⦂ centry_tag (ce_dm A M (gu_mk Δy Dy)) (body_ctx Φ ++ D) ρσ0 ‖ g1 ⦂ gu_mk Δy Dy),
        (ρ10 ↦ᵈ m3 ⦂ entry_type_closure A ρ10 ‖ k3 ⦂ gu_mk Δy Dy).
      split; [ apply eval_sub_extend_dm;
               [ exact Hσ0 | exact (proj1 (head_not_propositional_of_typ (e := ce_dm A M (gu_mk Δy Dy)) HR0 eq_refl HA _ _ H0))
               | exact Hm1 | exact Hg1 ] |].
      split; [ econstructor; [ exact Hb0 | exact Hm3 | apply eval_me_lit_iff; exact Hk3 ] |].
      apply EQ.
      assert (K33 : per_dmod k3 k3) by (etransitivity; [ symmetry; exact K23 | exact K23 ]).
      destruct Hdef as [[Hd1 Hd2 _ _ _ _] Hd3 Hd4].
      constructor; [ exact Hd1 | exact Hd2 | exact Hd3 | exact Hd4 | | | exact Rdm1 | split; [ exact Rdm3 | cbn; lia ]
                   | do 2 eexists; reflexivity | do 2 eexists; reflexivity ];
        unfold env_mod; cbn [drop_env tl env_entry hd];
        solve [ exists g2; split; [ exact Hg2 | exact G12 ] | exists k3; split; [ exact Hk3 | exact K33 ] ].
Qed.

(** Dropping the first [S n] entries is dropping the first [n] of the tail. *)
Lemma skipn_succ_drop : forall n (ρ : env), List.skipn (S n) ρ = List.skipn n ρ↯.
Proof. intros n [| e ρ]; cbn; [ destruct n; reflexivity | reflexivity ]. Qed.

(** The other way round from [fill_rel]: an environment the context PER of
    a body without opens relates to itself is related to the value of the
    substitution filling in the body at its tail.  So a type over the body's
    context is read, at any environment of it, as the type filled in is at
    the tail ([body_sorts_valid_of_fill]). *)
Lemma fill_rel_back : forall Φ D σ, gm_nopens Φ = 0 -> gm_fill Φ = Some σ -> ⊨ body_ctx Φ ++ D ->
    gmod_scoped (List.length D) Φ ->
    forall R RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> EF body_ctx Φ ++ D ≈ body_ctx Φ ++ D ∈ per_ctx_env ↘ R ->
    forall ρ1, R ρ1 ρ1 -> RD (List.skipn (List.length (body_ctx Φ)) ρ1) (List.skipn (List.length (body_ctx Φ)) ρ1) /\
      exists ρσ, ⟦ σ : body_ctx Φ ++ D ⟧s List.skipn (List.length (body_ctx Φ)) ρ1 ↘ ρσ /\ R ρ1 ρσ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hn Hf HC Hs R RD HD HR ρ1 Hρ1; cbn in Hn, Hf; [| | discriminate ].
  - (** The identity evaluates to the retagged environment. *)
    injection Hf as <-; cbn [body_ctx List.length List.skipn app] in *.
    assert (E : R <~> RD) by (eapply per_ctx_env_right_irrel; eassumption).
    split; [ apply E, Hρ1 |].
    exists (ctx_retag D ρ1); split; [ exact (proj1 (eval_sub_id_rel HD (proj1 (E _ _) Hρ1))) |].
    exact (per_ctx_env_retag_right HR _ _ Hρ1).
  - cbn [gmod_scoped] in Hs; destruct Hs as [Hs HsE].
    rewrite <- (length_body_ctx _ Hn), <- List.length_app in HsE.
    destruct E as [b pv ra A [M |] | pv U | ? ? ? ? ? | pv A M [Δy Dy] | ? ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app List.length] in HC, HR |- *; rewrite skipn_succ_drop; cbn [gentry_scoped] in HsE.
    + (* a definition *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      destruct (rel_ctx_wf_def_inv HC) as [(Srt & HS & HA) HM].
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0 Hs)) as Hτ.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      assert (HSr : evaluated_sort Srt \/ Srt = Propₘ)
        by (destruct HS; [ left; constructor | right; reflexivity | left; constructor ]).
      destruct HSr as [HSr | ->].
      2:{ (* at a proposition: a kept proof *)
        pose proof (per_ctx_env_of_def_prop (M := M) HR0 HA) as HR'.
        assert (EQ : R <~> per_env_extend A A R0) by (eapply per_ctx_env_right_irrel; eassumption).
        pose proof (proj1 (EQ _ _) Hρ1) as [Ht Hh Hl _ Hrl _].
        destruct (IH _ _ Hn eq_refl HC0 Hs _ _ HD HR0 _ Ht) as (Htail & ρσ0 & Hσ0 & H0).
        split; [ exact Htail |].
        destruct (rel_exp_of_prop_inversion_simple_at HR0 HA _ _ H0) as (a & a' & Ea & Ea' & Hp).
        pose proof Hp as [Hpl Hpr _].
        assert (Haa : per_prop a a) by (etransitivity; [ exact Hp | symmetry; exact Hp ]).
        (** The head is a readable proof; so is the substitution's kept one,
            [M[σ0]] being scoped by [D]. *)
        pose proof (Hh _ _ _ _ Ea Ea (per_univ_elem_of_prop 0 _ _ Haa)) as [Rp1 _].
        pose proof Hτ as [_ _ _ _ _ Hτs].
        assert (HMσ : exp_scoped (List.length D) M[σ0])
          by (eapply exp_scoped_sub; [ exact (proj2 HsE) | intros x Hx; exact (proj1 (Hτs x Hx)) ]).
        destruct (per_ctx_env_kept_proof_readable _ _ _ M[σ0] HD (exp_scoped_free_bound _ _ HMσ) _ _ Htail) as [Rp2 _].
        pose proof (per_head_proof (S' := A) (ρ' := ρσ0) Ea Hpl Rp1 Rp2) as Hph.
        (** The substitution's head is stored at [A] over its tail. *)
        destruct (per_head_closure_readable (per_ctx_env_of_typ (κ := ak_propositional) HR0 (rel_type_of_prop 0 HA)) HR0 H0 Hph) as [_ Rr].
        exists (ρσ0 ↦ ⋆ᵈ⟨M[σ0], List.skipn (List.length (body_ctx Φ)) ρ1↯⟩ ⦂ centry_tag (ce_def A M) (body_ctx Φ ++ D) ρσ0); split.
        { apply eval_sub_extend_proof; [ exact Hσ0 |].
          econstructor; [ reflexivity | intros y' _; reflexivity | exact Ea' | exact Hpr ]. }
        apply EQ.
        apply (mk_per_ctx_env_cons_rel _ _ _ _ ρ1
                 (ρσ0 ↦ ⋆ᵈ⟨M[σ0], List.skipn (List.length (body_ctx Φ)) ρ1↯⟩ ⦂ centry_tag (ce_def A M) (body_ctx Φ ++ D) ρσ0) H0);
          [ exact Hph | exact Hl | intros _; eexists; reflexivity | exact Hrl | split; [ exact Rr | cbn; lia ] ]. }
      (* at a relevant type: the value of the body filled in *)
      destruct (rel_type_of_evaluated_sort HSr HA) as [[i HAt] HArel].
      pose proof HArel as (rA0 & HrA0 & HAk).
      pose proof (per_ctx_env_of_def_evaluated HrA0 HR0 HAt (HAk _ HR0) HM) as HR'.
      assert (EQ : R <~> per_env_extend_def A M R0) by (eapply per_ctx_env_right_irrel; eassumption).
      pose proof (proj1 (EQ _ _) Hρ1) as [[Ht Hh _ _ Hrl _] Htl _].
      destruct (IH _ _ Hn eq_refl HC0 Hs _ _ HD HR0 _ Ht) as (Htail & ρσ0 & Hσ0 & H0).
      split; [ exact Htail |].
      destruct (valid_inst _ _ _ _ _ _ HM HArel Hτ HD _ _ Htail Hσ0) as (m1 & m2 & a2 & j & Ra & Hm1 & Hm2 & Ha2 & HRa & Hm12).
      destruct (rel_type_inversion_simple_at HR0 HAt _ _ H0) as (a & a' & Ea & Ea' & [RX HRX]).
      destruct (rel_exp_under_ctx_simple_at_of_evaluated HR0 (rel_typ_evaluated_at HArel HR0) HM _ _ H0) as (z & z' & Ez & Ez' & Hzz).
      destruct Htl as (ma & Ema & Hma).
      functional_eval_rewrite_clear.
      assert (HPX : PER RX) by (eapply per_elem_PER; exact HRX).
      assert (HRXa : per_univ_elem i RX a a) by (etransitivity; [ exact HRX | symmetry; exact HRX ]).
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa (proj1 (per_univ_elem_sym _ _ _ _ HRX))) as E1.
      (* the head, against the body's value filled in *)
      assert (Hhd : RX (ρ1 0) m1).
      { pose proof (Hma _ _ _ _ Ea Ea HRXa) as H1.
        pose proof (Hzz _ _ _ _ Ea Ha2 HRX) as H2.
        pose proof (proj1 (E1 _ _) Hm12) as H3.
        etransitivity; [ symmetry; exact H1 |]; etransitivity; [ exact H2 | symmetry; exact H3 ]. }
      assert (Hnp : forall r r', R0 r r' -> ~ rel_typ_propositional A r).
      { intros r r' Hr (c & Ec & Hc); destruct (rel_typ_evaluated_at HArel HR0 _ _ Hr) as (c' & Ec' & Hc').
        pose proof (functional_eval_exp _ _ _ _ Ec Ec') as <-; rewrite Hc in Hc'; inversion Hc'. }
      assert (Hph : per_head A A ρ1↯ ρσ0 (ρ1 0) m1) by (eapply per_head_of; [ exact Ea | exact Ha2 | exact HRX | exact Hhd ]).
      (** The substitution's head is stored at [A] over its tail. *)
      destruct (per_head_closure_readable (per_ctx_env_of_typ (κ := ak_relevant) HR0 HAt) HR0 H0 Hph) as [_ Rr].
      assert (Hext : per_env_extend A A R0 ρ1 (ρσ0 ↦ m1 ⦂ centry_tag (ce_def A M) (body_ctx Φ ++ D) ρσ0)).
      { apply (mk_per_ctx_env_cons_rel _ _ _ _ ρ1 (ρσ0 ↦ m1 ⦂ centry_tag (ce_def A M) (body_ctx Φ ++ D) ρσ0) H0);
          [ exact Hph
          | intros Hp; exfalso; exact (Hnp _ _ Ht Hp)
          | intros Hp; exfalso; exact (Hnp _ _ ltac:(etransitivity; [ symmetry; exact H0 | exact H0 ]) Hp)
          | exact Hrl | split; [ exact Rr | cbn; lia ] ]. }
      exists (ρσ0 ↦ m1 ⦂ centry_tag (ce_def A M) (body_ctx Φ ++ D) ρσ0); split;
        [ apply eval_sub_extend;
          [ exact Hσ0 | exact (proj2 (head_not_propositional_of_evaluated (e := ce_def A M) HR0 eq_refl HAt HArel _ _ H0))
          | exact Hm1 ] |].
      apply EQ; constructor; [ exact Hext | exists ma; split; assumption |].
      eapply (def_tie_resp HP0 (rel_type_inversion_simple_at HR0 HAt) (rel_exp_under_ctx_simple_at_of_evaluated HR0 (rel_typ_evaluated_at HArel HR0) HM) Hext).
      exists ma; split; assumption.
    + (* a submodule: the closure of its unit filled in *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      pose proof (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HC)) as HU.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0 Hs)) as Hτ.
      pose proof (per_ctx_env_of_mod HR0 HU HsE HsE) as HR'.
      assert (EQ : R <~> per_ctx_env_mod_rel R0 (List.length (body_ctx Φ ++ D)) U U)
        by (eapply per_ctx_env_right_irrel; eassumption).
      pose proof (proj1 (EQ _ _) Hρ1) as [Ht Hll Hll' _ _ Hrl _].
      destruct (IH _ _ Hn eq_refl HC0 Hs _ _ HD HR0 _ Ht) as (Htail & ρσ0 & Hσ0 & H0).
      split; [ exact Htail |].
      destruct (unit_sub_chain HD Hτ HU _ _ _ _ Htail Hσ0 Hσ0) as ([g1 g2 Hg1 Hg2 G12] & _).
      exists (ρσ0 ↦ᵐ g1 ⦂ U); split; [ apply eval_sub_extend_mod; [ exact Hσ0 | exact Hg1 ] |].
      apply EQ; constructor; cbn [drop_env tl env_mod env_entry hd extend_env_mod];
        first [ exact H0 | exact Hll | exact Hll' | exact Hrl | exact per_ctx_env_mod_rel_left_kind | eexists; reflexivity
              | split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HsE) ]
              | exists g2; split; [ exact Hg2 | exact G12 ] ].
    + (* a definition with a module part: both *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      destruct (rel_ctx_wf_dm_inv HC) as ([i HA] & HM & HUv).
      pose proof (rel_unit_under_ctx_lit _ _ _ HUv) as HU.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0 Hs)) as Hτ.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      assert (EQ : R <~> per_env_extend_dm A M (gu_mk Δy Dy) R0)
        by (eapply per_ctx_env_right_irrel; [ exact HR | exact (per_ctx_env_of_dm HR0 HA HM HU) ]).
      pose proof (proj1 (EQ _ _) Hρ1) as [Ht Hh Htl _ Hml _ Hrl _].
      destruct (IH _ _ Hn eq_refl HC0 Hs _ _ HD HR0 _ Ht) as (Htail & ρσ0 & Hσ0 & H0).
      split; [ exact Htail |].
      destruct (valid_inst _ _ _ _ _ _ HM (rel_type_evaluated_of_typ HA) Hτ HD _ _ Htail Hσ0)
        as (m1 & m2 & a2 & j & Ra & Hm1 & Hm2 & Ha2 & HRa & Hm12).
      destruct (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ H0) as (a & a' & Ea & Ea' & [RX HRX]).
      destruct (rel_exp_under_ctx_simple_at_rel HR0 HA HM _ _ H0) as (z & z' & Ez & Ez' & Hzz).
      destruct Htl as (ma & Ema & Hma).
      functional_eval_rewrite_clear.
      assert (HPX : PER RX) by (eapply per_elem_PER; exact HRX).
      assert (HRXa : per_univ_elem i RX a a) by (etransitivity; [ exact HRX | symmetry; exact HRX ]).
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa (proj1 (per_univ_elem_sym _ _ _ _ HRX))) as E1.
      assert (Hhd : RX (ρ1 0) m1).
      { pose proof (Hma _ _ _ _ Ea Ea HRXa) as H1.
        pose proof (Hzz _ _ _ _ Ea Ha2 HRX) as H2.
        pose proof (proj1 (E1 _ _) Hm12) as H3.
        etransitivity; [ symmetry; exact H1 |]; etransitivity; [ exact H2 | symmetry; exact H3 ]. }
      destruct (unit_sub_chain HD Hτ HU _ _ _ _ Htail Hσ0 Hσ0) as ([g1 g2 Hg1 Hg2 G12] & _).
      assert (Hph : per_head A A ρ1↯ ρσ0 (ρ1 0) m1) by (eapply per_head_of; [ exact Ea | exact Ha2 | exact HRX | exact Hhd ]).
      (** The substitution's head is stored at [A] over its tail, at the
          unit written. *)
      destruct (per_head_dm_readable (h := env_mod ρ1 0) (h' := g1) (U := gu_mk Δy Dy)
                  (per_ctx_env_of_typ (κ := ak_relevant) HR0 (rel_type_of_typ HA)) HR0 H0 Hph) as [_ Rr].
      assert (Hext : per_env_extend A A R0 ρ1
                       (ρσ0 ↦ᵈ m1 ⦂ centry_tag (ce_dm A M (gu_mk Δy Dy)) (body_ctx Φ ++ D) ρσ0 ‖ g1 ⦂ gu_mk Δy Dy)).
      { apply (mk_per_ctx_env_cons_rel _ _ _ _ ρ1
                 (ρσ0 ↦ᵈ m1 ⦂ centry_tag (ce_dm A M (gu_mk Δy Dy)) (body_ctx Φ ++ D) ρσ0 ‖ g1 ⦂ gu_mk Δy Dy) H0);
          [ exact Hph
          | intros Hp; exfalso; exact (not_rel_typ_propositional_of_typ HR0 HA _ _ Ht Hp)
          | intros Hp; exfalso; exact (not_rel_typ_propositional_of_typ HR0 HA _ _ ltac:(etransitivity; [ symmetry; exact H0 | exact H0 ]) Hp)
          | exact Hrl | exact Rr ]. }
      exists (ρσ0 ↦ᵈ m1 ⦂ centry_tag (ce_dm A M (gu_mk Δy Dy)) (body_ctx Φ ++ D) ρσ0 ‖ g1 ⦂ gu_mk Δy Dy); split;
        [ apply eval_sub_extend_dm;
          [ exact Hσ0 | exact (proj2 (head_not_propositional_of_typ (e := ce_dm A M (gu_mk Δy Dy)) HR0 eq_refl HA _ _ H0))
          | exact Hm1 | exact Hg1 ] |].
      apply EQ; constructor; [ exact H0 | exact Hph
                             | exists ma; split; assumption | | exact Hml | | exact Hrl | exact Rr
                             | exact per_env_extend_dm_left_kind | do 2 eexists; reflexivity ].
      * eapply (def_tie_resp HP0 (rel_exp_of_typ_inversion_simple_at HR0 HA) (rel_exp_under_ctx_simple_at_rel HR0 HA HM) Hext).
        exists ma; split; assumption.
      * unfold env_mod; cbn [drop_env tl env_entry hd]; exists g2; split; [ exact Hg2 | exact G12 ].
Qed.

(** A body without opens that can be filled in evaluates at every
    environment of its context, to one of the context it makes. *)
Lemma body_env_exists : forall Φ D, gm_nopens Φ = 0 -> gm_fill Φ <> None -> ⊨ body_ctx Φ ++ D -> body_sorts_valid Φ D ->
    gmod_scoped (List.length D) Φ ->
    forall R RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> EF body_ctx Φ ++ D ≈ body_ctx Φ ++ D ∈ per_ctx_env ↘ R ->
    forall ρ, RD ρ ρ -> exists ρ1, ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ R ρ1 ρ1.
Proof.
  intros * Hn Hf HC Hsv Hs R RD HD HR ρ Hρ.
  destruct (gm_fill Φ) as [σ |] eqn:Ef; [| congruence ].
  destruct (fill_rel _ _ _ Hn Ef HC Hsv Hs _ _ HD HR _ Hρ) as (ρσ & ρ1 & _ & Hb & H1).
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  exists ρ1; split; [ exact Hb | etransitivity; [ symmetry; exact H1 | exact H1 ] ].
Qed.

(** An environment of a context extended by parameters, extending a given
    one of the context by arguments, each at the value of its type. *)
Lemma params_env : forall Δ Γ RΓ R, all_assumptions Δ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R ->
    forall ρ, RΓ ρ ρ ->
    exists vts, List.length vts = List.length Δ /\ R (env_extend_typed ρ vts) (env_extend_typed ρ vts).
Proof.
  induction Δ as [| e Δ IH] using rev_ind; intros * HΔ HΓ HR ρ Hρ; cbn [List.app] in *.
  - exists nil; split; [ reflexivity |].
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption); apply E, Hρ.
  - destruct (all_assumptions_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? (κ & A & ->) _]; subst.
    rewrite <- app_assoc in HR; cbn [List.app] in HR.
    destruct (per_ctx_env_app_tail Δ Δ _ _ _ eq_refl HR) as [R1 HR1].
    destruct (per_ctx_env_cons_clean_inversion HΓ HR1) as (i & head_rel & Hhead & HAn & HE).
    destruct (Hhead _ _ Hρ) as [a a' Ha Ha' HRa].
    pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
    destruct (HAn _ _ Hρ) as (a0 & Ea0 & Hna); pose proof (functional_eval_exp _ _ _ _ Ea0 Ha) as ->.
    (** The reflected variable, a neutral proof at a proposition. *)
    pose proof (var_per_elem 0 HRa Hna) as Hv.
    pose proof (entry_readable_of_elem HRa Hv) as [Rv _].
    assert (Hρc : R1 (ρ ↦ ⇑! a 0 ⦂ entry_type_value a) (ρ ↦ ⇑! a 0 ⦂ entry_type_value a)).
    { apply HE.
      apply (mk_per_ctx_env_cons_rel _ _ _ _ (ρ ↦ ⇑! a 0 ⦂ entry_type_value a) (ρ ↦ ⇑! a 0 ⦂ entry_type_value a) Hρ);
        [ exact Hv | intros _; eexists; reflexivity | intros _; eexists; reflexivity
        | split; [ exact Rv | cbn; lia ] | split; [ exact Rv | cbn; lia ] ]. }
    destruct (IH _ _ _ HΔ0 HR1 HR _ Hρc) as (vts & Hl & Hvts).
    exists ((⇑! a 0, entry_type_value a) :: vts); split; [ rewrite length_app; cbn; lia | exact Hvts ].
Qed.

(** ** Kinds of Valid Module Values *)

Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

Lemma kinds_shape_sym : forall ρ ρ', kinds_shape gc_deps gc_stack ρ ρ' -> kinds_shape gc_deps gc_stack ρ' ρ.
Proof. intros * [K S]; split; [ intros x; apply kinds_equiv_sym, K | intros x; symmetry; apply S ]. Qed.

Lemma kinds_shape_trans : forall ρ1 ρ2 ρ3, kinds_shape gc_deps gc_stack ρ1 ρ2 -> kinds_shape gc_deps gc_stack ρ2 ρ3 ->
    kinds_shape gc_deps gc_stack ρ1 ρ3.
Proof.
  intros * [K1 S1] [K2 S2]; split; [ intros x; eapply kinds_equiv_trans; [ apply K1 | apply K2 ] | intros x; rewrite S1; apply S2 ].
Qed.

(** A module value related to itself is a module. *)
Lemma per_dmod_nil_kind_all :
  (forall h h', per_dmod h h' -> dmod_member_kind gc_deps gc_stack h nil member_kind_mod) /\
  (forall ts ρ ρ' args args', per_tele_args ts ρ ρ' args args' -> True) /\
  (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> True).
Proof.
  apply per_dmod_mut_ind_all; intros; try exact I.
  - apply dmod_member_kind_global_here_mod; unfold gc_loc in *; destruct (gc_frame _ _) eqn:Hfr;
      [ right; eauto | left; destruct (gc_body_module _ _ _ _ _ ltac:(eassumption)); eauto ].
  - apply dmod_member_kind_local, gunit_member_kind_self.
  - match goal with Hu : per_univ_elem _ _ _ _, E1 : forall c c', _ -> exists hc, eval_appm _ _ h c hc,
                    E2 : forall c c', _ -> exists hc', eval_appm _ _ h' c' hc',
                    IH : forall c c' hc hc', _ -> eval_appm _ _ h c hc -> eval_appm _ _ h' c' hc' -> dmod_member_kind _ _ hc _ _ |- _ =>
      destruct (per_univ_elem_inhabited _ _ _ _ Hu) as (c0 & c0' & Hv);
      destruct (E1 _ _ Hv) as (hc & Hc); destruct (E2 _ _ Hv) as (hc' & Hc');
      apply (kind_eval_appm _ _ _ _ _ Hc); exact (IH _ _ _ _ Hv Hc Hc') end.
Qed.

Corollary per_dmod_nil_kind : forall h h', per_dmod h h' -> dmod_member_kind gc_deps gc_stack h nil member_kind_mod.
Proof. exact (proj1 per_dmod_nil_kind_all). Qed.

(** A valid module expression is a module, at every environment of its
    context. *)
Lemma valid_nil_kind : forall Γ E RΓ, Γ ⊨ᵐ E ≈ E -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ, RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ E nil member_kind_mod.
Proof.
  intros * HE HΓ ρ Hρ.
  destruct (rel_modexp_at _ _ _ _ _ HE HΓ _ _ Hρ) as (h & h' & Hh & _ & Hr).
  apply (kind_eval_modexp _ _ _ _ _ Hh), (per_dmod_nil_kind _ _ Hr).
Qed.

(** ** Bodies Read by Kinds

    Kinds read a body as its expansion ([gunit_expand]), which is the
    expansion typing reads ([body_xp_expand]). *)

(** The kind of what a description describes: a term, a module, or a
    member with a term part and a module part. *)
Definition mdesc_member_kind (R : mdesc) : member_kind :=
  match R with
  | mdesc_term r _ _ => member_kind_term r
  | mdesc_dm _ _ _ _ => member_kind_dm
  | _ => member_kind_mod
  end.

Lemma mdesc_member_kind_up : forall Θ' R, mdesc_member_kind (mdesc_up Θ' R) = mdesc_member_kind R.
Proof. intros Θ' R; induction R; cbn; auto. Qed.

Lemma mdesc_member_kind_sub : forall R σ, mdesc_member_kind (mdesc_sub R σ) = mdesc_member_kind R.
Proof. intros R σ; revert σ; induction R; intros; cbn; auto. Qed.

Lemma mdesc_member_kind_named : forall Θ' Ns M R, mdesc_member_kind (mdesc_named Θ' Ns M R) = mdesc_member_kind R.
Proof.
  intros; apply (mdesc_named_cases (fun R' => mdesc_member_kind R' = mdesc_member_kind R)); [ reflexivity |].
  destruct R as [? ? [] | | |]; reflexivity.
Qed.

Lemma entry_member_kind_read : forall T E, entry_member_kind (ge_read T E) = entry_member_kind E.
Proof. intros T [| ? [? [[|] ?|?]] | | |]; reflexivity. Qed.

Lemma mdesc_member_kind_edenote : forall Γ o E R, edenote Θm Ξm Γ o E R -> mdesc_member_kind R = entry_member_kind E.
Proof.
  intros * He; inversion He; subst; try reflexivity.
  all: match goal with Hu : udenote _ _ _ _ _ ?R0 |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm; destruct R0 end;
    cbn in *; first [ contradiction | reflexivity ].
Qed.

(** A description with a term part and a module part has no outside
    parameter left: an entry's ([edenote]) is one. *)
Definition mdesc_dm_closed (R : mdesc) : Prop :=
  match R with
  | mdesc_dm Θd _ _ _ => Θd = nil
  | _ => True
  end.

Lemma edenote_dm_closed : forall Γ o E R, edenote Θm Ξm Γ o E R -> mdesc_dm_closed R.
Proof.
  intros * He; inversion He; subst; cbn; try reflexivity; try exact I.
  match goal with Hu : udenote _ _ _ _ _ ?R0 |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm; destruct R0 end;
    cbn in *; first [ contradiction | exact I ].
Qed.

(** Not a description with a term part and a module part: one stays so at
    arguments, with its kind. *)
Definition mdesc_not_dm (R : mdesc) : Prop :=
  match R with
  | mdesc_dm _ _ _ _ => False
  | _ => True
  end.

Lemma mdesc_member_kind_at : forall R N R', mdesc_not_dm R -> mdesc_at R N = Some R' -> mdesc_not_dm R' /\ mdesc_member_kind R' = mdesc_member_kind R.
Proof.
  intros R N; destruct R as [| | | Θd A M Rm]; intros R' Hn E1; cbn in E1, Hn; [| | | contradiction ].
  all: repeat match type of E1 with
         | match ?s with _ => _ end = _ => destruct s; try discriminate
         end;
       injection E1 as <-; split; first [ exact I | reflexivity ].
Qed.

Lemma mdesc_member_kind_ats : forall Ns R R', mdesc_not_dm R -> mdesc_ats R Ns = Some R' -> mdesc_member_kind R' = mdesc_member_kind R.
Proof.
  induction Ns as [| N Ns IH]; intros * Hn Ha; cbn in Ha; [ injection Ha as <-; reflexivity |].
  destruct (mdesc_at R N) as [R1 |] eqn:E1; [| discriminate ].
  destruct (mdesc_member_kind_at _ _ _ Hn E1) as [Hn1 E].
  rewrite (IH _ _ Hn1 Ha); exact E.
Qed.

Lemma mdesc_member_kind_ats_read : forall Ns R R', mdesc_dm_closed R -> mdesc_ats_read R Ns = Some R' -> mdesc_member_kind R' = mdesc_member_kind R.
Proof.
  intros Ns [| | | Θd A M Rm] R' Hc Ha; cbn in Hc.
  4: { subst Θd; cbn in Ha; mdesc_dm_read_shape Ha; reflexivity. }
  all: apply (mdesc_member_kind_ats Ns); [ exact I | exact Ha ].
Qed.

Lemma mdesc_member_kind_read : forall rd R R', mdesc_dm_closed R -> mdesc_read rd R = Some R' -> mdesc_member_kind R' = mdesc_member_kind R.
Proof.
  intros [Δ Φ' | Θ' Ns M] * Hc Hr; cbn in Hr.
  - destruct (gm_fill Φ'); cbn in Hr; [ injection Hr as <- | discriminate ]; rewrite mdesc_member_kind_up, mdesc_member_kind_sub; reflexivity.
  - destruct (mdesc_ats_read R Ns) as [R1 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
    rewrite mdesc_member_kind_up, mdesc_member_kind_named; exact (mdesc_member_kind_ats_read _ _ _ Hc Ha).
Qed.

(** What a member of a module expression denotes has the kind its value
    gives the name: an entry of the module part, or a unit or open frame
    the member names, of any kind. *)
Record kinds_ok (Γ : ctx) (H : modexp) : Prop := mk_kinds_ok
  { (** An entry of the module part has its entry's kind *)
    kinds_ok_entry : forall R Rm x Γy E rd, mdenote Θm Ξm Γ H R -> mdesc_mod R = Some Rm -> mdesc_entry Rm x = Some (Γy, E, rd) ->
      forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) (entry_member_kind E)
    (** A unit the member names is a module *)
  ; kinds_ok_unit : forall x, (exists TΦ, gc_unit Θm Ξm (me_mem H x) = Some TΦ) ->
      forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_mod
    (** The open frame of an inductive or a record type's module the member
        names is a member with a term part and a module part *)
  ; kinds_ok_frame : forall x, (exists p r, mod_qname (me_mem H x) = Some p /\ gs_find_ind Ξm p = Some r) \/
      (exists p Rr, mod_qname (me_mem H x) = Some p /\ gs_find_record Ξm p = Some Rr) ->
      forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm }.

Lemma kinds_ok_mem : forall Γ H x R, kinds_ok Γ H -> mdenote Θm Ξm Γ (me_mem H x) R ->
    forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) (mdesc_member_kind R).
Proof.
  intros * [Ke Ku Kf] Hm RΓ ρ HΓ Hρ.
  inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hr
                  | ? ? ? Rr ? ? Hq Hk]; subst.
  - exact (Ku _ (ex_intro _ _ Hu) _ _ HΓ Hρ).
  - exact (Kf _ (or_introl (ex_intro _ _ (ex_intro _ _ (conj Hq Hk)))) _ _ HΓ Hρ).
  - rewrite (mdesc_member_kind_read _ _ _ (edenote_dm_closed _ _ _ _ Hed) Hr), (mdesc_member_kind_edenote _ _ _ _ Hed);
      exact (Ke _ _ _ _ _ _ Hm0 Hmd He _ _ HΓ Hρ).
  - exact (Kf _ (or_intror (ex_intro _ _ (ex_intro _ _ (conj Hq Hk)))) _ _ HΓ Hρ).
Qed.

(** The definitions of a body before generated entries are of their
    tagged sorts when the whole body's are. *)
Lemma body_sorts_valid_of_gens_append : forall gs Φ k D, body_sorts_valid (gens_append Φ k gs) D -> body_sorts_valid Φ D.
Proof.
  induction gs as [| g gs IH]; intros * Hv; cbn [gens_append] in Hv; [ exact Hv |].
  destruct (generated_item_entry g) as [d E]; exact (proj1 (IH _ _ _ Hv)).
Qed.

(** A body prefixed by some of an open's generated entries has its sorts
    valid when the whole does. *)
Lemma body_sorts_valid_gens_firstn : forall Φ D gs0 gs1, body_sorts_valid (gens_append Φ 0 (gs0 ++ gs1)) D ->
    body_sorts_valid (gens_append Φ 0 gs0) D.
Proof.
  intros * Hsv; rewrite gens_append_app in Hsv; exact (body_sorts_valid_of_gens_append _ _ _ _ Hsv).
Qed.

(** The entries an open generates are of their tagged sorts over any base
    that makes the same context. *)
Lemma body_sorts_valid_gens_rebase : forall gs Φ Φ' k D D',
    body_ctx Φ ++ D = body_ctx Φ' ++ D' ->
    body_sorts_valid (gens_append Φ k gs) D -> body_sorts_valid Φ' D' -> body_sorts_valid (gens_append Φ' k gs) D'.
Proof.
  induction gs as [| g gs IH]; intros * Hc Hv Hv'; cbn [gens_append] in Hv |- *; [ exact Hv' |].
  destruct (generated_item_entry g) as [d E].
  assert (Hce : forall X, exists e, body_ctx (gm_ext X d (gentry_wk E (wk_shiftn k))) = e :: body_ctx X)
    by (intros X; destruct (gentry_wk E (wk_shiftn k)) as [? ? ? ? [] | | | |]; eexists; reflexivity).
  apply (IH (gm_ext Φ d (gentry_wk E (wk_shiftn k))) _ _ D); [ | exact Hv |].
  - destruct (Hce Φ) as [e He]; destruct (Hce Φ') as [e' He'].
    rewrite He, He'; cbn [List.app].
    replace e' with e by (destruct (gentry_wk E (wk_shiftn k)) as [? ? ? ? [] | | | |]; cbn in He, He'; congruence).
    rewrite Hc; reflexivity.
  - pose proof (body_sorts_valid_of_gens_append _ _ _ _ Hv) as [_ Hh].
    split; [ exact Hv' |]; intros A M HE; rewrite <- Hc; exact (Hh A M HE).
Qed.

(** ** Valid Global Modules

    What the filed modules and open frames of [Θm ⍮ Ξm] are worth at the
    target ([valid_filed_mods], in [LogicalRelation/Definitions.v]). *)

Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
Hypothesis Hgf : valid_filed_mods Θm Ξm.
Hypothesis Hsb : gc_sub Θm Ξm gc_deps gc_stack.

Lemma modexp_member_kind_apps : forall Ns H ρ ch k, modexp_member_kind gc_deps gc_stack ρ (me_apps H Ns) ch k <-> modexp_member_kind gc_deps gc_stack ρ H ch k.
Proof.
  induction Ns as [| N Ns IH]; intros; cbn [me_apps]; [ reflexivity |].
  rewrite IH; apply modexp_member_kind_app_iff.
Qed.

(** An open frame a member names is a module, unless it is the module of
    a member with a term part. *)
Lemma frame_kind : forall H x p TΦ, mod_qname (me_mem H x) = Some p -> gc_frame Ξm p = Some TΦ ->
    ~ dm_path gc_deps gc_stack p ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_mod.
Proof.
  intros * Hq Hf Hdm ρ.
  cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hf.
  assert (Ht : exists U T0, gs_find_tele Ξm (qname_in mq x) = Some (U, nil, T0)).
  { unfold gc_frame in Hf; destruct (gs_find_tele Ξm (qname_in mq x)) as [[[U [| ? ?]] T0] |];
      try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
  destruct Ht as (U & T0 & Ht).
  destruct (frame_parent _ _ Hgm _ _ _ _ Ht) as (T1 & Φ1 & Hf1 & _).
  assert (Hgl0 : gc_loc Θm Ξm mq = Some (T1, Φ1)) by (unfold gc_loc; rewrite Hf1; reflexivity).
  assert (Hgl : gc_loc Θm Ξm (qname_in mq x) = Some TΦ) by (unfold gc_loc; rewrite Hf; reflexivity).
  destruct (Hgf _ _ _ Hgl0) as [_ Hp _ _ _ _ Hsub _ _ _ _ _].
  rewrite (mod_qname_inv _ _ Hq0).
  apply (kind_eval_modexp _ _ _ _ _ (Hp ρ)), (Hsub x TΦ); [ exact Hgl | exact Hdm ].
Qed.

(** A unit a member names is an open frame, so a module. *)
Lemma gunit_kind : forall H x TΦ, gc_unit Θm Ξm (me_mem H x) = Some TΦ ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_mod.
Proof.
  intros * Hu ρ; destruct TΦ as [T' Φ'].
  destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hf | (_ & Hc & _)]).
  - apply (frame_kind _ _ _ _ Hq Hf).
    exact (frame_not_dm_sub _ _ _ _ _ _ _ Hsb Hf (gc_unit_not_ind _ _ _ _ _ _ Hq Hu) (gc_unit_not_record _ _ _ _ _ _ Hq Hu)).
  - exfalso; cbn in Hq; destruct (mod_qname H) as [mq |]; [| discriminate ]; injection Hq as <-.
    cbn in Hc; destruct (q_chain mq); discriminate.
Qed.

(** An open frame a member names that is the module of a member with a
    term part is that member: one with a term part and a module part. *)
Lemma frame_dm_kind : forall H x p TΦ, mod_qname (me_mem H x) = Some p -> gc_frame Ξm p = Some TΦ ->
    dm_path gc_deps gc_stack p ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * Hq Hf Hdm ρ.
  cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hf, Hdm.
  assert (Ht : exists U T0, gs_find_tele Ξm (qname_in mq x) = Some (U, nil, T0)).
  { unfold gc_frame in Hf; destruct (gs_find_tele Ξm (qname_in mq x)) as [[[U [| ? ?]] T0] |];
      try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
  destruct Ht as (U & T0 & Ht).
  destruct (frame_parent _ _ Hgm _ _ _ _ Ht) as (T1 & Φ1 & Hf1 & _).
  assert (Hgl0 : gc_loc Θm Ξm mq = Some (T1, Φ1)) by (unfold gc_loc; rewrite Hf1; reflexivity).
  destruct TΦ as [T Φ].
  assert (Hgl : gc_loc Θm Ξm (qname_in mq x) = Some (T, Φ)) by (unfold gc_loc; rewrite Hf; reflexivity).
  destruct (gc_loc_grow _ _ _ _ Hgw Hsb _ _ _ Hgl) as (Φ2 & Hgl2 & _).
  destruct (Hgf _ _ _ Hgl0) as [_ Hp _ _ _ _ _ _ _ _ _ _].
  rewrite (mod_qname_inv _ _ Hq0).
  apply (kind_eval_modexp _ _ _ _ _ (Hp ρ)).
  eapply dmod_member_kind_global_here_dm; [ exact Hdm | exact Hgl2 ].
Qed.

(** The open frame of a member's module a member names is that member. *)
Lemma ind_frame_kind : forall H x p r, mod_qname (me_mem H x) = Some p -> gs_find_ind Ξm p = Some r ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * Hq Hk ρ; destruct r as [[pq k] D].
  destruct (frame_ind_loc _ _ Hgm _ _ _ _ Hk) as (? & ? & T & Φ & ? & _ & Hf & _ & _).
  apply (frame_dm_kind _ _ _ _ Hq Hf).
  left; eexists; exact (gc_sub_frame_ind_field _ _ _ _ Hsb _ _ Hk).
Qed.

(** So is the open frame of a record type's module. *)
Lemma record_frame_kind : forall H x p Rr, mod_qname (me_mem H x) = Some p -> gs_find_record Ξm p = Some Rr ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * Hq Hk ρ.
  destruct (frame_record_loc _ _ Hgm _ _ Hk) as (? & ? & T & Φ & _ & Hf & _).
  apply (frame_dm_kind _ _ _ _ Hq Hf).
  right; left; eexists; exact (gc_sub_frame_record_field _ _ _ _ Hsb _ _ Hk).
Qed.

Lemma frame_member_kind : forall H x,
    (exists p r, mod_qname (me_mem H x) = Some p /\ gs_find_ind Ξm p = Some r) \/
    (exists p Rr, mod_qname (me_mem H x) = Some p /\ gs_find_record Ξm p = Some Rr) ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * [(p & r & Hq & Hk) | (p & Rr & Hq & Hk)] ρ;
    [ exact (ind_frame_kind _ _ _ _ Hq Hk ρ) | exact (record_frame_kind _ _ _ _ Hq Hk ρ) ].
Qed.

Lemma mdesc_entry_up_inv : forall Δ R y Γy E rd, mdesc_entry (mdesc_up Δ R) y = Some (Γy, E, rd) ->
    exists Γy' rd', mdesc_entry R y = Some (Γy', E, rd').
Proof.
  intros * He; destruct R; cbn in He |- *; try discriminate.
  - destruct (gm_prefix_upto _ y) as [[| ? ? [[|] ? ? ? [] | | | |] | ] |]; try discriminate;
      injection He as <- <- <-; eauto.
  - destruct (gm_prefix_upto _ y) as [[| ? ? E0 | ] |]; try discriminate; injection He as <- <- <-; eauto.
Qed.

Lemma mdesc_entry_open_inv : forall Δ Φ Φx y Γy E rd, mdesc_entry (mdesc_open Δ Φ Φx) y = Some (Γy, E, rd) ->
    exists Φ' E0, gm_prefix_upto Φx y = Some (gm_ext Φ' y E0) /\ entry_member_kind E = entry_member_kind E0 /\
      Γy = body_ctx Φ' ++ Δ /\ rd = reader_open Δ Φ'.
Proof.
  intros * He; cbn in He.
  destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  exists Φ', E0; split; [ reflexivity |].
  destruct E0 as [[|] ? ? ? [] | | | |]; try discriminate; injection He as <- <- <-; repeat split.
Qed.

Lemma mdesc_entry_closed_inv : forall Θ p T Φ Ns y Γy E rd, mdesc_entry (mdesc_closed Θ p T Φ Ns) y = Some (Γy, E, rd) ->
    exists Φ0 E0, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) /\ E = ge_read T E0.
Proof.
  intros * He; cbn in He.
  destruct (gm_prefix_upto Φ y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  injection He as _ <- _; eauto.
Qed.

(** A prefix of a body is a tail of its context. *)
Lemma prefix_body_ctx : forall Φ y Φp, gm_nopens Φ = 0 -> gm_prefix_upto Φ y = Some Φp ->
    exists X, body_ctx Φ = X ++ body_ctx Φp.
Proof.
  induction Φ as [| Φ IH z E | Φ IH H its]; intros * Hn Hp; cbn in Hn, Hp; try discriminate.
  destruct (String.eqb y z); [ injection Hp as <-; exists nil; reflexivity |].
  destruct (IH _ _ Hn Hp) as (X & HX).
  destruct E as [? ? ? ? [] | | | |]; cbn [body_ctx]; rewrite HX; eexists (_ :: X); reflexivity.
Qed.

Lemma prefix_shape : forall Φ x Φ' E, body_shape Φ Φ -> gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    body_shape Φ' Φ' /\ entry_shape E E.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH H its]; intros * Hs Hp; cbn in Hs, Hp; try discriminate.
  - destruct (String.eqb x z); [ injection Hp as <- _ <-; split; [ exact (proj1 Hs) | exact (proj2 (proj2 Hs)) ] |].
    exact (IH _ _ _ (proj1 Hs) Hp).
  - destruct (existsb _ _); [ discriminate | exact (IH _ _ _ (proj1 Hs) Hp) ].
Qed.

Lemma prefix_nopens : forall Φ x Φ', gm_nopens Φ = 0 -> gm_prefix_upto Φ x = Some Φ' -> gm_nopens Φ' = 0.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH H its]; intros * Hn Hp; cbn in Hn, Hp; try discriminate.
  destruct (String.eqb x z); [ injection Hp as <-; exact Hn | exact (IH _ _ Hn Hp) ].
Qed.

(** The definitions of a body up to an entry are of their tagged sorts
    when the whole body's are. *)
Lemma body_sorts_valid_prefix : forall Φ x Φ' D, gm_prefix_upto Φ x = Some Φ' -> body_sorts_valid Φ D -> body_sorts_valid Φ' D.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH H its]; intros * Hp Hv; cbn in Hp, Hv; try discriminate.
  - destruct (String.eqb x z); [ injection Hp as <-; exact Hv | exact (IH _ _ _ Hp (proj1 Hv)) ].
  - destruct (existsb _ _); [ discriminate | exact (IH _ _ _ Hp Hv) ].
Qed.

(** ** The Kinds of Valid Units *)

Lemma valid_unit_kinds_all :
  (forall Γ K, valid_unit Γ K -> kinds_ok Γ K) /\ (forall Γ H, valid_modexp Γ H -> kinds_ok Γ H).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs;
      split; [| intros x [TΦ Hu] RΓ ρ _ _; exact (gunit_kind _ _ _ Hu ρ)
              | intros x Hx RΓ ρ _ _; exact (frame_member_kind _ _ Hx ρ) ].
    intros R Rm x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ Hm1), Hmod1 in Hmod; injection Hmod as <-.
    destruct (mdesc_entry_closed_inv _ _ _ _ _ _ _ _ _ He) as (Φ0 & E0 & Hp & ->).
    destruct (Hgf _ _ _ Hgl) as [_ Hpe _ _ _ Hk _ _ _ _ _ _].
    apply modexp_member_kind_apps, (kind_eval_modexp _ _ _ _ _ (Hpe ρ)); rewrite entry_member_kind_read; exact (Hk _ _ _ Hp).
  - (* a body *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΔr HΓ HC Hsv Hslots IHslots Hs Hsx HK Hopv Hops IHops.
    split; [| intros x (TΦ & Hu); cbn in Hu; unfold gc_unit in Hu; cbn in Hu; discriminate
            | intros x [(p & r & Hq & _) | (p & r & Hq & _)]; cbn in Hq; discriminate ].
    intros R Rm x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    inversion Hm; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    match goal with Hx' : body_xp _ _ _ Φ ?Φx1 |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgm)))) _ _ _ Hx _ Hx') as <- end.
    cbn in Hmod; injection Hmod as <-.
    destruct (mdesc_entry_open_inv _ _ _ _ _ _ _ He) as (Φ' & E0 & Hp & Hek & _ & _).
    rewrite Hek.
    (* an environment of the parameters, and the kinds of the closure there *)
    destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HC)) as [RΔ HRΔ].
    destruct (params_env _ _ _ _ HΔ HRΓ HRΔ _ Hρ) as (args & Hl & Hρa).
    pose proof (kinds_shape_args_pad gc_deps gc_stack ρ _ _ Hl) as Hsa.
    pose proof (body_xp_scoped_of_wf _ _ _ _ Hw Hx) as Hsc.
    (* kinds read the expansion, the body typing reads *)
    apply modexp_member_kind_lit; cbn [gunit_expand]; rewrite <- (body_xp_expand _ _ _ _ _ Hx).
    apply gunit_member_kind_pad.
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    pose proof (gm_noopen_prefix_upto _ _ _ (body_xp_result_noopen _ _ _ _ _ Hx) Hp) as Hno'; cbn [gm_noopen] in Hno'.
    destruct (prefix_shape _ _ _ _ Hsx Hp) as [Hsh' HshE].
    pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn [gm_nopens] in Hn'.
    destruct E0 as [b pv ra A0 oM | pm U | | pv A0 M0 U | ]; cbn in HshE; try contradiction; cbn [entry_member_kind].
    1: eapply gunit_member_kind_def; exact Hp.
    2: (* a definition with a module part: [dm_of] its unit's kind, a
            module's, at an environment of its context *)
      destruct (kinds_env_total gc_deps gc_stack _ (kinds_pads 0 (kinds_pads (List.length Δ) ρ)) Hno') as (σ1 & Hσ1);
      change member_kind_dm with (dm_of member_kind_mod);
      eapply gunit_member_kind_dm_here; [ exact Hp | exact Hσ1 |];
      destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX);
      rewrite HX, <- app_assoc in HC; pose proof (rel_ctx_wf_app_r _ _ HC) as HC1; cbn [body_ctx app] in HC1;
      pose proof (rel_ctx_wf_tail HC1) as HC0;
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0];
      destruct (body_env_exists _ _ Hn' (proj1 (body_shape_fill _ _ Hn' Hsh')) HC0
                 (proj1 (body_sorts_valid_prefix _ _ _ _ Hp Hsv))
                 (proj1 (gm_prefix_upto_scoped _ _ _ _ Hp Hsc)) _ _ HRΔ HR0 _ Hρa) as (ρ1 & Hb1 & Hρ1);
      destruct (kind_eval_body_env _ _ _ _ _ Hb1 _ Hsa) as (σ' & Hk1 & Hs1);
      pose proof (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack))) _ _ _ Hσ1 _ Hk1) as <-;
      apply (gunit_member_kind_id _ _ _ _ (proj1 (kinds_shape_sym _ _ Hs1))), modexp_member_kind_lit_iff;
      exact (valid_nil_kind _ _ _ (rel_unit_under_ctx_lit _ _ _ (proj2 (proj2 (rel_ctx_wf_dm_inv HC1)))) HR0 _ Hρ1).
    + (* a submodule: a module, at an environment of its context *)
      destruct (kinds_env_total gc_deps gc_stack _ (kinds_pads 0 (kinds_pads (List.length Δ) ρ)) Hno') as (σ1 & Hσ1).
      eapply gunit_member_kind_mod; [ exact Hp | exact Hσ1 |].
      destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX).
      rewrite HX, <- app_assoc in HC; pose proof (rel_ctx_wf_app_r _ _ HC) as HC1; cbn [body_ctx app] in HC1.
      pose proof (rel_ctx_wf_tail HC1) as HC0.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (body_env_exists _ _ Hn' (proj1 (body_shape_fill _ _ Hn' Hsh')) HC0
                 (proj1 (body_sorts_valid_prefix _ _ _ _ Hp Hsv))
                 (proj1 (gm_prefix_upto_scoped _ _ _ _ Hp Hsc)) _ _ HRΔ HR0 _ Hρa) as (ρ1 & Hb1 & Hρ1).
      destruct (kind_eval_body_env _ _ _ _ _ Hb1 _ Hsa) as (σ' & Hk1 & Hs1).
      pose proof (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack))) _ _ _ Hσ1 _ Hk1) as <-.
      apply (gunit_member_kind_id _ _ _ _ (proj1 (kinds_shape_sym _ _ Hs1))), modexp_member_kind_lit_iff.
      exact (valid_nil_kind _ _ _ (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HC1)) HR0 _ Hρ1).
  - (* an alias *)
    intros Γ Δ E Hw HΔ HΔr HΓ HΔΓ HK HE Hsmt IHE.
    split; [| intros x (TΦ & Hu); cbn in Hu; unfold gc_unit in Hu; cbn in Hu; discriminate
            | intros x [(p & r & Hq & _) | (p & r & Hq & _)]; cbn in Hq; discriminate ].
    intros R Rm x Γy E' rd Hm Hmod He RΓ ρ HRΓ Hρ.
    inversion Hm; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? E0 RE Rem HmE HmodE]; subst end.
    rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ (mdesc_mod_is_mod _ _ HmodE))) in Hmod; injection Hmod as <-.
    destruct (mdesc_entry_up_inv _ _ _ _ _ _ He) as (Γy' & rd' & He').
    destruct (rel_ctx_wf_per_ctx_env HΔΓ) as [RΔ HRΔ].
    destruct (params_env _ _ _ _ HΔ HRΓ HRΔ _ Hρ) as (args & Hl & Hρa).
    pose proof (kinds_shape_args_pad gc_deps gc_stack ρ _ _ Hl) as Hsa.
    apply modexp_member_kind_lit, gunit_member_kind_alias, (modexp_member_kind_id _ _ _ _ (proj1 Hsa)).
    exact (kinds_ok_entry _ _ IHE _ _ _ _ _ _ HmE HmodE He' _ _ HRΔ Hρa).
  - (* a module expression equal to a valid unit: as the unit *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK.
    split; [| intros x [TΦ Hu] RΓ ρ _ _; exact (gunit_kind _ _ _ Hu ρ)
            | intros x Hx RΓ ρ _ _; exact (frame_member_kind _ _ Hx ρ) ].
    intros R' Rm' x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ HmH), HmodH in Hmod; injection Hmod as <-.
    pose proof (kinds_ok_entry _ _ IHK _ _ _ _ _ _ HmK HmodK He _ _ HRΓ Hρ) as Hk.
    destruct (rel_modexp_at _ _ _ _ _ HHK HRΓ _ _ Hρ) as (h & h' & Hh & Hh' & Hr).
    apply (kind_eval_modexp _ _ _ _ _ Hh), (per_dmod_kinds_equiv _ _ Hr), (kind_eval_modexp _ _ _ _ _ Hh'); exact Hk.
Qed.

Corollary valid_unit_kinds : forall Γ K, valid_unit Γ K -> kinds_ok Γ K.
Proof. exact (proj1 valid_unit_kinds_all). Qed.

Corollary valid_modexp_kinds : forall Γ H, valid_modexp Γ H -> kinds_ok Γ H.
Proof. exact (proj2 valid_unit_kinds_all). Qed.

End Fixed_GCtx.
