(** * Π-Types in the Gluing Model

    A [Π] out of a domain of the kind [κd] into a codomain of the kind
    [κc] ([pi_kinds]).  Into an evaluated kind it is glued by the [Π]
    clause ([glu_pi_typ_point]); into propositions it is the universal
    proposition, glued by its readback ([glu_all_typ_point]).  As a term of
    its sort it is a type of a large universe, of a small one (whose
    readback is built from its parts'), a proposition, or a type of levels.

    A λ or an application into an evaluated kind is glued at the [Π]'s
    element predicate; into propositions it is a proof, kept
    ([glu_rel_exp_proof]).  The type of an application is an instantiated
    codomain, whose value is related to the codomain's at the argument's
    value ([per_univ_of_instance_at]).

    The gluing quantifies over Kripke weakenings, so a codomain obligation
    has the form [OT[(ι φ),,M]]; [exp_sub_q_extend_wk] relates it to the
    [q]-form, and [sb_wk σ φ] is a substitution followed by a Kripke
    weakening.  The sorts' gluings and inversions come first: they are what
    the sorts of the domain and of the codomain give ([UniverseCases]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UniverseCases.
From Mctt.Core.Completeness Require LevelCases FunctionCases.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  Instances
  UniverseCases.
Import Domain_Notations Wk_Notations.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A type of the sort of a kind next to a small universe [Type⟨L⟩], at the realiser of the
    level's value, with the readback at the sort. *)
Lemma glu_rel_exp_kind_sort_small_inversion : forall {Γ Sb A κ L} {n : nat},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ L : Level@n ->
    Γ ⊩ A : abs_kind_sort κ Type⟨L⟩ ->
    forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      forall l, ⟦ L ⟧ ρ ↘ l ->
      Δ ⊢ A[σ] : abs_kind_sort κ Type⟨L[σ]⟩ /\
        exists a, ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_univ (us (domain_level_real l)) /\
             (forall P El, DG a ∈ glu_univ_elem (us (domain_level_real l)) ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
             (forall Δ' φ W, Δ' ⊢ᵏ φ : Δ -> Rtyp a in length Δ' ↘ W ->
                        glu_nf_eq Δ' A[σ][φ]ʷ W (abs_kind_sort κ Type⟨L[σ]⟩)[φ]ʷ).
Proof.
  intros * HSb HL HA Δ σ ρ Hσ l Hl.
  destruct κ; cbn [abs_kind_sort] in *.
  - destruct (glu_rel_exp_of_suniv_tm_inversion HSb HL HA _ _ _ Hσ) as (l0 & Hl0 & _ & _ & HAσ & a & Ha & Hpa & HaP & Hrd).
    functional_eval_rewrite_clear.
    split; [ exact HAσ | exists a; split; [ exact Ha | split; [ exact Hpa | split; [ exact HaP | exact Hrd ] ] ] ].
  - destruct (glu_rel_exp_prop_inversion HSb HA _ _ _ Hσ) as (a & Ha & Hpa & HaP).
    destruct (glu_prop_typ_at_index (u := us (domain_level_real l)) Hpa HaP) as [Hpi HPi].
    destruct HaP as [HAσ HR].
    split; [ exact HAσ | exists a; split; [ exact Ha | split; [ exact Hpi | split; [ exact HPi | exact HR ] ] ] ].
  - destruct (glu_rel_exp_level_sort_inversion HSb HA _ _ _ Hσ) as (a & Pa & Ela & Ha & _ & HAσ & Hga & HaP).
    destruct (glu_least_typ_at_index (u := us (domain_level_real l)) Hga HaP) as [Hpi HPi].
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_level 0 Hga HaP HAσ) as [Hk Hna].
    destruct (realize_glu_typ_top _ _ _ _ Hga Hna _ _ HaP) as [_ _ Hrd].
    rewrite Hk in Hrd.
    split; [ exact HAσ | exists a; split; [ exact Ha | split; [ exact Hpi | split; [ exact HPi | exact Hrd ] ] ] ].
Qed.

(** [wf_pi] at a large universe, the codomain's sort unweakened. *)
Lemma wf_pi_large : forall {Γ κd κc A B} {n : nat},
    ⊢ Γ ->
    Γ ⊢ A : abs_kind_sort κd Typeω@n ->
    Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@n ->
    pi_kinds κd κc ->
    Γ ⊢ a_pi κd κc A B : abs_kind_sort κc Typeω@n.
Proof.
  intros * HΓ HA HB Hk.
  eapply wf_pi with (U := Typeω@n); [ constructor; assumption | exact HA | | exact Hk ].
  rewrite abs_kind_sort_wk; exact HB.
Qed.

Lemma glu_pi_typ_point : forall {u : universe_index} {κd κc Γ A B SbΓ SbB Δ σ ρ a P El},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    EG Γ ▹{κd} A ∈ glu_ctx_env ↘ SbB ->
    Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
    pi_kinds κd κc ->
    evaluated_kind κc ->
    Δ ⊢ A[σ] : abs_kind_sort κd Typeω@(large_level u) ->
    Δ ▹{κd} A[σ] ⊢ B[q σ] : abs_kind_sort κc Typeω@(large_level u) ->
    ⟦ A ⟧ ρ ↘ a ->
    (forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    (forall Δ' σ' c, Δ' ⊢ˢ σ' ® ρ ↦ c ⦂ entry_type_value a ∈ SbB ->
       exists b, ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\
         forall P El, DG b ∈ glu_univ_elem u ↘ P ↘ El -> Δ' ⊢ B[σ'] ® P) ->
    DG d_pi κd κc a ρ B ∈ glu_univ_elem u ↘ P ↘ El ->
    Δ ⊢ (a_pi κd κc A B)[σ] ® P.
Proof.
  intros * HΓ HΓA Hσ Hk Hev HAσ HBσ Ha HaP HB Hglu.
  destruct (glu_ctx_env_cons_clean_inversion HΓ HΓA) as (j & HAj & HAg & ESb).
  invert_glu_univ_elem Hglu.
  match goal with H4 : ?tr <∙> pi_glu_typ_pred _ _ _ _ _ _ _ |- ?tr _ _ => apply H4 end.
  assert (⊢ Δ) by (gen_presups; eassumption).
  econstructor; [ | exact HAσ | exact HBσ | |].
  - apply wf_exp_eq_refl; cbn [exp_sub]; apply wf_pi_large; assumption.
  - intros Δ' φ Hφ.
    match goal with Hg : glu_univ_elem _ _ _ a |- _ =>
      exact (glu_univ_elem_typ_monotone _ _ _ _ Hg _ _ _ _ (HaP _ _ Hg) Hφ) end.
  - intros Δ' φ M m Hφ HM equiv_m.
    pose proof (glu_ctx_env_sub_monotone _ _ HΓ _ _ _ _ _ Hσ Hφ) as Hσ'.
    destruct (HAg _ _ _ Hσ') as [a' P' El' Ea' Hg' HP'].
    functional_eval_rewrite_clear.
    assert (HM' : Δ' ⊢ M : A[sb_wk σ φ] ® m ∈ El').
    { rewrite <- exp_wk_sub.
      match goal with Hg : glu_univ_elem u _ _ a, Hp : per_univ_elem u _ a a |- _ =>
        assert (Hpa : Dom a ≈ a ∈ per_univ u) by (eexists; exact Hp);
        eapply (glu_univ_elem_exp_conv_universe_index Hpa Hg Hg' HM) end.
      rewrite exp_wk_sub; exact HP'. }
    assert (Hc : Δ' ⊢ˢ (sb_wk σ φ),,M ® ρ ↦ m ⦂ entry_type_value a ∈ SbB)
      by (apply ESb; eapply cons_glu_sub_pred_helper; [ exact HΓ | exact Hσ' | exact HAj | exact Ha | exact Hg' | exact HM' ]).
    destruct (HB _ _ _ Hc) as (b & Hb & HbP).
    rewrite exp_sub_q_extend_wk.
    match goal with H1 : forall c (equiv_c : _ c c) b, _ -> glu_univ_elem _ _ _ b |- _ =>
      exact (HbP _ _ (H1 _ equiv_m _ Hb)) end.
Qed.

Lemma glu_nf_eq_pi : forall {Γ U κd κc A B WA WB},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U ->
    Γ ⊢ A : abs_kind_sort κd U ->
    pi_kinds κd κc ->
    glu_nf_eq Γ A WA (abs_kind_sort κd U) ->
    glu_nf_eq (Γ ▹{κd} A) B WB (abs_kind_sort κc U)[↑]ʷ ->
    glu_nf_eq Γ (a_pi κd κc A B) (nf_pi κd κc WA WB) (abs_kind_sort κc U).
Proof.
  intros * HU HA Hk HA' HB'.
  unfold glu_nf_eq in *; cbn; eapply wf_exp_eq_pi_cong; eassumption.
Qed.

(** A glued substitution extended by a term glued at its type, at any
    index, glues into the extended context, at whatever index its gluing
    is ([glu_ctx_env_cons_clean_inversion]). *)
Lemma glu_cons_sub_at : forall {u : universe_index} {κd Γ A SbΓ SbB Δ σ ρ a P El M m},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    EG Γ ▹{κd} A ∈ glu_ctx_env ↘ SbB ->
    Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem u ↘ P ↘ El ->
    Δ ⊢ M : A[σ] ® m ∈ El ->
    Δ ⊢ˢ σ,,M ® ρ ↦ m ⦂ entry_type_value a ∈ SbB.
Proof.
  intros * HΓ HΓA Hσ Ha Hg HM.
  destruct (glu_ctx_env_cons_clean_inversion HΓ HΓA) as (j & HAj & HAg & ESb).
  destruct (HAg _ _ _ Hσ) as [a' P' El' Ea' Hg' HP'].
  functional_eval_rewrite_clear.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [R HR].
  pose proof (glu_univ_elem_exp_conv_universe_index (ex_intro _ R HR) Hg Hg' HM HP') as HM'.
  apply ESb; eapply cons_glu_sub_pred_helper; [ exact HΓ | exact Hσ | exact HAj | exact Ha | exact Hg' | exact HM' ].
Qed.

(** The same after a Kripke weakening. *)
Lemma glu_cons_sub_of_elem : forall {u : universe_index} {κd Γ A SbΓ SbB Δ σ ρ a P El Δ' φ M m},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    EG Γ ▹{κd} A ∈ glu_ctx_env ↘ SbB ->
    Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem u ↘ P ↘ El ->
    Δ' ⊢ᵏ φ : Δ ->
    Δ' ⊢ M : A[σ][φ]ʷ ® m ∈ El ->
    Δ' ⊢ˢ (sb_wk σ φ),,M ® ρ ↦ m ⦂ entry_type_value a ∈ SbB.
Proof.
  intros * HΓ HΓA Hσ Ha Hg Hφ HM.
  rewrite exp_wk_sub in HM.
  exact (glu_cons_sub_at HΓ HΓA (glu_ctx_env_sub_monotone _ _ HΓ _ _ _ _ _ Hσ Hφ) Ha Hg HM).
Qed.

Lemma glu_all_typ_point : forall {u : universe_index} {κd Γ A B SbΓ SbB Δ σ ρ a},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    EG Γ ▹{κd} A ∈ glu_ctx_env ↘ SbB ->
    Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
    Δ ⊢ A[σ] : abs_kind_sort κd Typeω@(large_level u) ->
    Δ ▹{κd} A[σ] ⊢ B[q σ] : Propₘ ->
    ⟦ A ⟧ ρ ↘ a ->
    Dom a ≈ a ∈ per_univ u ->
    (forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    (forall Δ' σ' c, Δ' ⊢ˢ σ' ® ρ ↦ c ⦂ entry_type_value a ∈ SbB ->
       exists b, ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\ Δ' ⊢ B[σ'] ® prop_glu_typ_pred b) ->
    Δ ⊢ (a_pi κd ak_propositional A B)[σ] ® prop_glu_typ_pred (d_pi κd ak_propositional a ρ B).
Proof.
  intros * HΓ HΓA Hσ HAσ HBσ Ha Hpa HaP HB.
  assert (⊢ Δ) by (gen_presups; eassumption).
  assert (HΠ : Δ ⊢ (a_pi κd ak_propositional A B)[σ] : Propₘ).
  { cbn [exp_sub].
    apply (wf_pi_large (κc := ak_propositional) (n := large_level u)); [ assumption | exact HAσ | exact HBσ | constructor ]. }
  split; [ exact HΠ |].
  intros Δ' φ W Hφ HW.
  inversion HW; subst.
  destruct Hpa as [Ra HRa].
  assert (exists Pa Ela, DG a ∈ glu_univ_elem u ↘ Pa ↘ Ela) as (Pa & Ela & Hga) by mauto 3.
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ κd _ Hga (HaP _ _ Hga) HAσ) as [Hka Hna].
  assert (HPa : Δ' ⊢ A[σ][φ]ʷ ® Pa) by exact (glu_univ_elem_typ_monotone _ _ _ _ Hga _ _ _ _ (HaP _ _ Hga) Hφ).
  destruct (realize_glu_typ_top _ _ _ _ Hga Hna _ _ HPa) as [HAφ _ HArd].
  rewrite Hka in HAφ, HArd.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  assert (HArd' : glu_nf_eq Δ' A[σ][φ]ʷ A0 (abs_kind_sort κd Typeω@(large_level u))).
  { pose proof (HArd Δ' wk_id A0 ltac:(mauto 3) ltac:(eassumption)) as Hr; rewrite exp_wk_id in Hr; exact Hr. }
  pose proof (var0_glu_elem Hga Hna HPa) as Hv.
  rewrite Hka in Hv.
  assert (⊢ Δ' ▹{κd} A[σ][φ]ʷ) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
  assert (Hk : Δ' ▹{κd} A[σ][φ]ʷ ⊢ᵏ φ ⊙ ↑ : Δ) by mauto 3.
  rewrite exp_wk_wk in Hv.
  pose proof (glu_cons_sub_of_elem HΓ HΓA Hσ Ha Hga Hk Hv) as Hc.
  destruct (HB _ _ _ Hc) as (b' & Hb' & HbP).
  functional_eval_rewrite_clear.
  destruct HbP as [_ HbR].
  pose proof (HbR _ wk_id B' ltac:(mauto 3) ltac:(eassumption)) as HBW; rewrite exp_wk_id in HBW.
  pose proof (kripke_q_var_eq _ _ _ _ _ _ _ _ HBσ HAσ (sort_kind_abs_kind_sort _ _) Hφ) as Hq.
  rewrite exp_sub_q_extend_wk in Hq.
  cbn [exp_sub exp_wk].
  eapply (glu_nf_eq_pi (U := Typeω@(large_level u)) (κc := ak_propositional)); [ constructor; assumption | exact HAφ | constructor | exact HArd' |].
  eapply glu_nf_eq_exp_eq; [ apply wf_exp_eq_sym; exact Hq | exact HBW ].
Qed.

(** A codomain of the sort of a kind next to a large universe, moved
    along [q σ]. *)
Lemma sub_preserves_codomain : forall {Γ Δ σ κd κc A B} {n : nat},
    Δ ⊢ˢ σ : Γ ->
    Γ ⊢ A : abs_kind_sort κd Typeω@n ->
    Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@n ->
    Δ ⊢ A[σ] : abs_kind_sort κd Typeω@n /\ Δ ▹{κd} A[σ] ⊢ B[q σ] : abs_kind_sort κc Typeω@n.
Proof.
  intros * Hσ HA HB.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ) as HAσ; rewrite abs_kind_sort_sub in HAσ; cbn [exp_sub] in HAσ.
  pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hσ HA (sort_kind_abs_kind_sort _ _) HAσ) as Hq.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB Hq) as HBq; rewrite abs_kind_sort_sub in HBq; cbn [exp_sub] in HBq.
  split; assumption.
Qed.

(** [Π] at a large universe: a type of the universe, the universal
    proposition, or a [Π] between types of levels. *)
Lemma glu_rel_exp_pi_large : forall {Γ κd κc A B} {i : nat},
    Γ ⊩ A : abs_kind_sort κd Typeω@i ->
    Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    Γ ⊩ a_pi κd κc A B : abs_kind_sort κc Typeω@i.
Proof.
  intros * HA HB Hk.
  destruct (presup_ctx_glu_rel_exp HA) as [SbΓ HSbΓ].
  destruct (presup_ctx_glu_rel_exp HB) as [SbB HSbB].
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  pose proof (glu_rel_exp_to_wf_exp HB) as HBt.
  pose proof (glu_ctx_env_wf_ctx HSbΓ) as HΓ.
  assert (HΠt : Γ ⊢ a_pi κd κc A B : abs_kind_sort κc Typeω@i) by (apply wf_pi_large; assumption).
  pose proof (completeness_fundamental_exp _ _ _ HΠt) as HΠc.
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [R HR].
  pose proof (glu_rel_exp_kind_sort_large_inversion HSbΓ HA) as HAg.
  destruct Hk as [κd | κd |]; cbn [abs_kind_sort] in *.
  - (** A type of the universe *)
    eapply glu_rel_exp_of_typ; [ exact HSbΓ |].
    intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
    pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
    destruct (sub_preserves_codomain (κc := ak_relevant) Hσt HAt HBt) as [HAσ HBσ].
    assert (⊢ Δ) by (gen_presups; assumption).
    destruct (HAg _ _ _ Hσ) as [_ (a & Ha & _ & HaP)].
    split; [ cbn [exp_sub]; apply (wf_pi_large (κc := ak_relevant)); [ assumption | exact HAσ | exact HBσ | constructor ] |].
    exists (d_pi κd ak_relevant a ρ B); split; [ constructor; exact Ha |].
    destruct (rel_exp_of_typ_inversion_simple_at HR HΠc _ _ Hρ) as (p & p' & Ep & Ep' & Hp).
    inversion Ep; inversion Ep'; subst; functional_eval_rewrite_clear.
    split; [ exact Hp |].
    intros P El Hg.
    eapply (glu_pi_typ_point (u := ul i)); [ exact HSbΓ | exact HSbB | exact Hσ | constructor | constructor
                                           | exact HAσ | exact HBσ | exact Ha | exact HaP | | exact Hg ].
    intros Δ' σ' c Hc.
    destruct (glu_rel_exp_of_univ_inversion (u := ul i) HSbB HB _ _ _ Hc) as [_ (b & Hb & _ & HbP & _)].
    exists b; split; [ exact Hb | exact HbP ].
  - (** The universal proposition *)
    eapply glu_rel_exp_of_prop; [ exact HSbΓ |].
    intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
    pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
    destruct (sub_preserves_codomain (κc := ak_propositional) (n := i) Hσt HAt HBt) as [HAσ HBσ].
    destruct (HAg _ _ _ Hσ) as [_ (a & Ha & Hpa & HaP)].
    exists (d_pi κd ak_propositional a ρ B); split; [ constructor; exact Ha |].
    destruct (rel_exp_of_prop_inversion_simple_at HR HΠc _ _ Hρ) as (p & p' & Ep & Ep' & Hp).
    inversion Ep; inversion Ep'; subst; functional_eval_rewrite_clear.
    split; [ exact Hp |].
    eapply (glu_all_typ_point (u := ul i)); [ exact HSbΓ | exact HSbB | exact Hσ | exact HAσ | exact HBσ | exact Ha | exact Hpa | exact HaP |].
    intros Δ' σ' c Hc.
    destruct (glu_rel_exp_prop_inversion HSbB HB _ _ _ Hc) as (b & Hb & _ & HbP).
    exists b; split; [ exact Hb | exact HbP ].
  - (** A [Π] between types of levels *)
    eapply glu_rel_exp_of_level_sort; [ exact HSbΓ |].
    intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
    pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
    destruct (sub_preserves_codomain (κd := ak_level) (κc := ak_level) (n := 0) Hσt HAt HBt) as [HAσ HBσ].
    assert (⊢ Δ) by (gen_presups; assumption).
    destruct (glu_rel_exp_level_sort_inversion HSbΓ HA _ _ _ Hσ) as (a & Pa & Ela & Ha & _ & _ & Hga & HaP).
    destruct (rel_exp_of_level_sort_inversion_simple_at HR HΠc _ _ Hρ) as (p & p' & Ep & Ep' & Hp).
    inversion Ep; inversion Ep'; subst; functional_eval_rewrite_clear.
    destruct Hp as (Hcp & _ & Hpp).
    destruct (per_univ_glu_univ_elem _ _ Hpp) as (P & El & Hg).
    exists (d_pi ak_level ak_level a ρ B), P, El.
    split; [ exact Ep | split; [ exact Hcp | split; [ cbn [exp_sub]; apply (wf_pi_large (κc := ak_level) (n := 0)); [ assumption | exact HAσ | exact HBσ | constructor ] | split; [ exact Hg |] ] ] ].
    eapply (glu_pi_typ_point (u := us (0, 0))); [ exact HSbΓ | exact HSbB | exact Hσ | constructor | constructor
                                                | exact HAσ | exact HBσ | exact Ha | | | exact Hg ].
    + exact (proj2 (glu_least_typ_at_index (u := us (0, 0)) Hga HaP)).
    + intros Δ' σ' c Hc.
      destruct (glu_rel_exp_level_sort_inversion HSbB HB _ _ _ Hc) as (b & Pb & Elb & Hb & _ & _ & Hgb & HbP).
      exists b; split; [ exact Hb | exact (proj2 (glu_least_typ_at_index (u := us (0, 0)) Hgb HbP)) ].
Qed.

(** A type of the sort of a kind next to a small universe is one next to
    every large universe. *)
Lemma lift_kind_sort_small : forall {Δ A κ L} {n j : nat},
    Δ ⊢ L : Level@n ->
    Δ ⊢ A : abs_kind_sort κ Type⟨L⟩ ->
    Δ ⊢ A : abs_kind_sort κ Typeω@j.
Proof. intros * HL HA; destruct κ; cbn in *; [ eapply wf_exp_suniv_large; eassumption | exact HA | exact HA ]. Qed.

(** [wf_pi] at a small universe, into it. *)
Lemma wf_pi_small : forall {Γ κd A B L} {n : nat},
    Γ ⊢ L : Level@n ->
    Γ ⊢ A : abs_kind_sort κd Type⟨L⟩ ->
    Γ ▹{κd} A ⊢ B : Type⟨L[↑]ʷ⟩ ->
    Γ ⊢ a_pi κd ak_relevant A B : Type⟨L⟩.
Proof.
  intros * HL HA HB.
  change Type⟨L⟩ with (abs_kind_sort ak_relevant Type⟨L⟩).
  eapply wf_pi; [ econstructor; exact HL | exact HA | exact HB | constructor ].
Qed.

(** [Π] into a small universe: its realiser is the level's at every
    glued substitution, the codomain's the weakened level's at the extended
    one, which is the same ([Completeness.FunctionCases.suniv_real_shift]). *)
Lemma glu_rel_exp_pi_small_relevant : forall {Γ κd A B L} {n : nat},
    Γ ⊩ L : Level@n ->
    Γ ⊩ A : abs_kind_sort κd Type⟨L⟩ ->
    Γ ▹{κd} A ⊩ B : Type⟨L[↑]ʷ⟩ ->
    Γ ⊩ a_pi κd ak_relevant A B : Type⟨L⟩.
Proof.
  intros * HL HA HB.
  destruct (presup_ctx_glu_rel_exp HA) as [SbΓ HSbΓ].
  destruct (presup_ctx_glu_rel_exp HB) as [SbB HSbB].
  pose proof (glu_rel_exp_to_wf_exp HL) as HLt.
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  pose proof (glu_rel_exp_to_wf_exp HB) as HBt.
  pose proof (glu_ctx_env_wf_ctx HSbΓ) as HΓ.
  pose proof (lift_kind_sort_small (j := 0) HLt HAt) as HAl.
  assert (⊢ Γ ▹{κd} A) by (econstructor; [ exact HAl | apply sort_kind_abs_kind_sort ]).
  pose proof (wk_preserves_exp _ _ _ _ _ _ _ HLt (wf_wk_shift _ _ _ _ ltac:(eassumption))) as HLA; cbn [exp_wk] in HLA.
  pose proof (wf_pi_small HLt HAt HBt) as HΠt.
  pose proof (completeness_fundamental_exp _ _ _ HΠt) as HΠc.
  destruct (LevelCases.rel_exp_of_suniv_tm_inversion_simple HΠc) as [R [HR HΠs]].
  destruct (glu_ctx_env_per_ctx_env HSbB) as [RB HRB].
  pose proof (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HAl)) as HAc.
  pose proof (completeness_fundamental_exp _ _ _ HLt) as HLc.
  eapply glu_rel_exp_of_suniv_tm; [ exact HSbΓ | exact HL |].
  intros Δ σ ρ Hσ l Hl.
  pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
  pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
  assert (⊢ Δ) by (gen_presups; assumption).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HLt Hσt) as HLσ; cbn [exp_sub] in HLσ.
  destruct (glu_rel_exp_kind_sort_small_inversion HSbΓ HL HA _ _ _ Hσ l Hl) as [HAσ (a & Ha & Hpa & HaP & HaR)].
  pose proof (lift_kind_sort_small (j := 0) HLσ HAσ) as HAσl.
  pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hσt HAl (sort_kind_abs_kind_sort _ _) HAσl) as Hq.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HBt Hq) as HBq; cbn [exp_sub] in HBq; rewrite exp_wk_shift_sub_q in HBq.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HLA Hq) as HLq; cbn [exp_sub] in HLq; rewrite exp_wk_shift_sub_q in HLq.
  pose proof (wf_exp_suniv_large (i := 0) HLq HBq) as HBql.
  (** The codomain at the extended substitutions, at the level's realiser *)
  assert (HBg : forall Δ' σ' c, Δ' ⊢ˢ σ' ® ρ ↦ c ⦂ entry_type_value a ∈ SbB ->
             exists b, ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\
               (forall P El, DG b ∈ glu_univ_elem (us (domain_level_real l)) ↘ P ↘ El -> Δ' ⊢ B[σ'] ® P) /\
               (forall Δ'' φ W, Δ'' ⊢ᵏ φ : Δ' -> Rtyp b in length Δ'' ↘ W ->
                           glu_nf_eq Δ'' B[σ'][φ]ʷ W Type⟨L[↑]ʷ[σ']⟩[φ]ʷ)).
  { intros Δ' σ' c Hc.
    destruct (glu_rel_exp_of_suniv_tm_inversion' HSbB HB _ _ _ Hc) as (l' & Hl' & _ & _ & b & Hb & _ & HbP & HbR).
    pose proof (glu_ctx_env_per_env HSbB HRB Hc) as Hρc.
    rewrite (FunctionCases.suniv_real_shift HAc HLc HRB _ _ _ _ _ _ _ _ Hρc Hl' Hl) in HbP.
    exists b; split; [ exact Hb | split; [ exact HbP | exact HbR ] ]. }
  split; [ cbn [exp_sub]; eapply wf_pi_small; [ exact HLσ | exact HAσ | exact HBq ] |].
  exists (d_pi κd ak_relevant a ρ B); split; [ constructor; exact Ha |].
  destruct (HΠs _ _ Hρ) as (p & p' & t & Ep & Ep' & Ht & Hp).
  inversion Ep; inversion Ep'; subst; functional_eval_rewrite_clear.
  split; [ exact (per_universe_elements_rel _ _ _ Hp) | split ].
  - intros P El Hg.
    eapply (glu_pi_typ_point (u := us (domain_level_real l))); [ exact HSbΓ | exact HSbB | exact Hσ | constructor | constructor
                                                             | exact HAσl | exact HBql | exact Ha | exact HaP | | exact Hg ].
    intros Δ' σ' c Hc; destruct (HBg _ _ _ Hc) as (b & Hb & HbP & _); exists b; split; assumption.
  - (** The readback: the domain's at the small universe, and the
        codomain's at the glued variable, which [kripke_q_var_eq] relates
        to [B[q σ]] under the weakening. *)
    intros Δ' φ W Hφ HW.
    inversion HW; subst.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    pose proof (HaR _ _ _ Hφ ltac:(eassumption)) as HArd; rewrite abs_kind_sort_wk in HArd; cbn [exp_wk] in HArd.
    destruct Hpa as [Ra HRa].
    assert (exists Pa Ela, DG a ∈ glu_univ_elem (us (domain_level_real l)) ↘ Pa ↘ Ela) as (Pa & Ela & Hga) by mauto 3.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ κd _ Hga (HaP _ _ Hga) HAσl) as [Hka Hna].
    assert (HPa : Δ' ⊢ A[σ][φ]ʷ ® Pa) by exact (glu_univ_elem_typ_monotone _ _ _ _ Hga _ _ _ _ (HaP _ _ Hga) Hφ).
    pose proof (kripke_preserves_exp _ _ _ _ _ HAσl Hφ) as HAφl; rewrite abs_kind_sort_wk in HAφl; cbn [exp_wk] in HAφl.
    pose proof (kripke_preserves_exp _ _ _ _ _ HAσ Hφ) as HAφ; rewrite abs_kind_sort_wk in HAφ; cbn [exp_wk] in HAφ.
    pose proof (kripke_preserves_exp _ _ _ _ _ HLσ Hφ) as HLφ; cbn [exp_wk] in HLφ.
    pose proof (var0_glu_elem Hga Hna HPa) as Hv.
    rewrite Hka in Hv.
    assert (⊢ Δ' ▹{κd} A[σ][φ]ʷ) by (econstructor; [ exact HAφl | apply sort_kind_abs_kind_sort ]).
    assert (Hk' : Δ' ▹{κd} A[σ][φ]ʷ ⊢ᵏ φ ⊙ ↑ : Δ) by mauto 3.
    rewrite exp_wk_wk in Hv.
    pose proof (glu_cons_sub_of_elem HSbΓ HSbB Hσ Ha Hga Hk' Hv) as Hc.
    destruct (HBg _ _ _ Hc) as (b' & Hb' & _ & HbR).
    functional_eval_rewrite_clear.
    pose proof (HbR _ wk_id _ ltac:(mauto 3) ltac:(eassumption)) as HBW; rewrite !exp_wk_id in HBW.
    rewrite exp_sub_shift_extend, <- exp_wk_sub, <- exp_wk_wk in HBW.
    pose proof (kripke_q_var_eq _ _ _ _ _ _ _ _ HBq HAσl (sort_kind_abs_kind_sort _ _) Hφ) as Hqv.
    rewrite exp_sub_q_extend_wk in Hqv; cbn [exp_wk] in Hqv; rewrite exp_wk_shift_wk_q in Hqv.
    cbn [exp_sub exp_wk].
    eapply (glu_nf_eq_pi (U := Type⟨L[σ][φ]ʷ⟩) (κc := ak_relevant)); [ econstructor; exact HLφ | exact HAφ | constructor | exact HArd |].
    eapply glu_nf_eq_exp_eq; [ apply wf_exp_eq_sym; exact Hqv | exact HBW ].
Qed.

(** A glued type of the sort of a kind next to a small universe glues next
    to every large one ([glu_rel_exp_subtyp]). *)
Lemma glu_rel_exp_kind_sort_small_large : forall {Γ A κ L} {n j : nat},
    Γ ⊩ L : Level@n ->
    Γ ⊩ A : abs_kind_sort κ Type⟨L⟩ ->
    Γ ⊩ A : abs_kind_sort κ Typeω@j.
Proof.
  intros * HL HA; destruct κ; cbn in *; [| exact HA | exact HA ].
  pose proof (presup_ctx_glu_rel_exp HA) as HΓ.
  eapply glu_rel_exp_subtyp; [ exact HA | apply glu_rel_exp_typ; exact HΓ | constructor |].
  eapply wf_subtyp_small_large; [ destruct HΓ as [? HΓ]; exact (glu_ctx_env_wf_ctx HΓ) | exact (glu_rel_exp_to_wf_exp HL) ].
Qed.

(** [Π] at a small universe: into the universe, or the universal
    proposition and a [Π] between types of levels, which do not depend on
    the universe. *)
Lemma glu_rel_exp_pi_small : forall {Γ κd κc A B L} {n : nat},
    Γ ⊩ L : Level@n ->
    Γ ⊩ A : abs_kind_sort κd Type⟨L⟩ ->
    Γ ▹{κd} A ⊩ B : (abs_kind_sort κc Type⟨L⟩)[↑]ʷ ->
    pi_kinds κd κc ->
    Γ ⊩ a_pi κd κc A B : abs_kind_sort κc Type⟨L⟩.
Proof.
  intros * HL HA HB Hk.
  destruct Hk as [κd | κd |]; cbn [abs_kind_sort exp_wk] in *.
  - exact (glu_rel_exp_pi_small_relevant HL HA HB).
  - exact (glu_rel_exp_pi_large (i := 0) (κc := ak_propositional) (glu_rel_exp_kind_sort_small_large (j := 0) HL HA) HB (pi_kinds_prop _)).
  - exact (glu_rel_exp_pi_large (i := 0) (κd := ak_level) (κc := ak_level) HA HB pi_kinds_level).
Qed.

(** β at a substitution followed by a Kripke weakening: an instance of
    [wf_exp_eq_pi_beta] at [sb_wk σ φ], once [exp_wk_sub] has merged the
    two steps and [exp_sub_q_extend] has put both bodies into [q]-form. *)
Lemma exp_eq_fn_sub_wk_beta : forall {Γ Δ Δ' σ φ κd κc A B M N} {i : nat},
    Δ ⊢ˢ σ : Γ ->
    Γ ⊢ A : abs_kind_sort κd Typeω@i ->
    Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    Γ ▹{κd} A ⊢ M : B ->
    Δ' ⊢ᵏ φ : Δ ->
    Δ' ⊢ N : A[sb_wk σ φ] ->
    Δ' ⊢ (λ A M)[σ][φ]ʷ $ N ≈ M[(sb_wk σ φ),,N] : B[(sb_wk σ φ),,N].
Proof.
  intros * Hσ HA HB Hk HM Hφ HN.
  saturate_kripke_escape.
  assert (Hτ : Δ' ⊢ˢ sb_wk σ φ : Γ) by (rewrite sb_wk_compose; mauto 3).
  destruct (sub_preserves_codomain Hτ HA HB) as [HAτ HBτ].
  pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hτ HA (sort_kind_abs_kind_sort _ _) HAτ) as Hq.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM Hq) as HMτ.
  rewrite exp_wk_sub; cbn [exp_sub].
  rewrite <- (exp_sub_q_extend M), <- (exp_sub_q_extend B).
  eapply wf_exp_eq_pi_beta; [ exact HAτ | apply sort_kind_abs_kind_sort | exact HBτ | exact Hk | exact HMτ | exact HN ].
Qed.

(** A λ into a type of an evaluated kind: a function glued at its [Π],
    applied to a glued argument glued as its body at the extended
    substitution, up to β. *)
Lemma glu_rel_exp_fn_evaluated : forall {Γ κd κc A B M} {i : nat},
    Γ ⊩ A : abs_kind_sort κd Typeω@i ->
    Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    evaluated_kind κc ->
    Γ ▹{κd} A ⊩ M : B ->
    Γ ⊩ λ A M : a_pi κd κc A B.
Proof.
  intros * HA HB Hk Hev HM.
  destruct (presup_ctx_glu_rel_exp HA) as [SbΓ HSbΓ].
  destruct (presup_ctx_glu_rel_exp HB) as [SbB HSbB].
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  pose proof (glu_rel_exp_to_wf_exp HB) as HBt.
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  pose proof (glu_ctx_env_wf_ctx HSbΓ) as HΓ.
  assert (HΠt : Γ ⊢ a_pi κd κc A B : abs_kind_sort κc Typeω@i) by (apply wf_pi_large; assumption).
  assert (Hλt : Γ ⊢ λ A M : a_pi κd κc A B)
    by (eapply wf_fn; [ exact HAt | apply sort_kind_abs_kind_sort | exact HBt | exact Hk | exact HMt ]).
  pose proof (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HΠt)) as HΠc.
  pose proof (completeness_fundamental_exp _ _ _ Hλt) as Hλc.
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [R HR].
  destruct (rel_exp_under_ctx_simple_full_at HR Hλc) as [jλ Hλs].
  pose proof (glu_rel_exp_kind_sort_large_inversion HSbΓ HA) as HAg.
  pose proof (glu_rel_exp_kind_sort_large_inversion HSbB HB) as HBg.
  destruct (glu_rel_exp_clean_inversion1 HSbB HM) as [kM HMk].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HSbΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ) as Hσt.
  pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
  assert (⊢ Δ) by (gen_presups; assumption).
  destruct (sub_preserves_codomain Hσt HAt HBt) as [HAσ HBσ].
  destruct (HAg _ _ _ Hσ) as [_ (a & Ha & _ & HaP)].
  destruct (rel_type_inversion_simple_at HR HΠc _ _ Hρ) as (p & p' & Ep & Ep' & Hp).
  inversion Ep; inversion Ep'; subst; functional_eval_rewrite_clear.
  destruct (per_univ_glu_univ_elem _ _ Hp) as (P & El & Hg).
  pose proof Hg as Hg0.
  econstructor; [ exact Ep | destruct Hev; cbn; apply eval_exp_fn; exact Ha | exact Hg |].
  (** The value of the λ, related to itself at the [Π]'s element PER *)
  destruct (Hλs _ _ Hρ) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & [Hkp | (m1 & m2 & Hm1 & Hm2 & Hmm)]);
    functional_eval_rewrite_clear; [ destruct Hev; cbn in Hkp; discriminate |].
  inversion Hm1; subst; functional_eval_rewrite_clear.
  invert_glu_univ_elem Hg.
  match goal with HE : ?el <∙> pi_glu_exp_pred _ _ _ _ _ _ _ _ |- ?el _ _ _ _ => apply HE end.
  econstructor; [ exact (sub_preserves_exp _ _ _ _ _ _ _ Hλt Hσt) | | | exact HAσ | exact HBσ | |].
  - match goal with Hp2 : per_univ_elem _ ?er (d_pi _ _ _ _ _) (d_pi _ _ _ _ _) |- ?er _ _ =>
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp2 HR1); exact Hmm end.
  - apply wf_exp_eq_refl; cbn [exp_sub]; apply wf_pi_large; assumption.
  - intros Δ' φ Hφ.
    match goal with Hga : glu_univ_elem _ _ _ a |- _ =>
      exact (glu_univ_elem_typ_monotone _ _ _ _ Hga _ _ _ _ (HaP _ _ Hga) Hφ) end.
  - intros Δ' φ N n Hφ HN equiv_n.
    match goal with Hga : glu_univ_elem _ _ _ a |- _ =>
      pose proof (glu_cons_sub_of_elem HSbΓ HSbB Hσ Ha Hga Hφ HN) as Hc;
      pose proof (glu_univ_elem_trm_escape _ _ _ _ Hga _ _ _ _ HN) as HNt end.
    rewrite exp_wk_sub in HNt.
    destruct (HMk _ _ _ Hc) as [b mb Pb Elb Eb Hmb Hgb HMb].
    destruct (HBg _ _ _ Hc) as [HBc (b' & Eb' & _ & HbP)].
    functional_eval_rewrite_clear.
    match goal with H1 : forall c (equiv_c : _ c c) b, _ -> glu_univ_elem _ _ _ b |- _ =>
      pose proof (H1 _ equiv_n _ Eb) as Hgb' end.
    pose proof (HbP _ _ Hgb') as HBcP.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ κc i Hgb' HBcP HBc) as [Hkb _].
    rewrite Hkb in Hmb.
    exists mb; split; [ apply eval_app_fn; destruct Hev; exact Hmb |].
    rewrite exp_sub_q_extend_wk.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
    pose proof (glu_univ_elem_exp_conv_universe_index (ex_intro _ Rb HRb) Hgb Hgb' HMb HBcP) as HM'.
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hgb' | exact HM' |].
    apply wf_exp_eq_sym; eapply exp_eq_fn_sub_wk_beta; eassumption.
Qed.

(** A λ ([wf_fn]): a function into a type of an evaluated kind, or a
    proof of a [∀], kept. *)
Lemma glu_rel_exp_fn : forall {Γ κd κc A Srt B M} {i : nat},
    Γ ⊩ A : Srt ->
    sort_kind Srt κd ->
    Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    Γ ▹{κd} A ⊩ M : B ->
    Γ ⊩ λ A M : a_pi κd κc A B.
Proof.
  intros * HA HS HB Hk HM.
  destruct (sort_kind_abs_kind_sort_inv HS) as [j ->].
  pose proof (glu_rel_exp_kind_sort_lift (k := max j i) (PeanoNat.Nat.le_max_l j i) HA) as HA'.
  pose proof (glu_rel_exp_kind_sort_lift (k := max j i) (PeanoNat.Nat.le_max_r j i) HB) as HB'.
  destruct (evaluated_kind_or_propositional κc) as [Hev | ->].
  - exact (glu_rel_exp_fn_evaluated HA' HB' Hk Hev HM).
  - apply glu_rel_exp_proof; [ exact (glu_rel_exp_pi_large (κc := ak_propositional) HA' HB' Hk) |].
    eapply wf_fn; [ exact (glu_rel_exp_to_wf_exp HA') | apply sort_kind_abs_kind_sort
                  | exact (glu_rel_exp_to_wf_exp HB') | exact Hk | exact (glu_rel_exp_to_wf_exp HM) ].
Qed.

(** The value of an instantiated type at one environment, as the gluing
    model reads it: [⟦B[Id,,N]⟧ρ] is related to [B]'s value at [ρ]
    extended by [N]'s value at its kind, at the tag the gluing model
    stores, [entry_type_value a].  [Id ,, N] extends the retagged
    environment at the closure tag ([eval_sub_extend],
    [eval_sub_extend_proof]); the two extensions of [ρ], at the two tags,
    are related in the context PER of [Γ ▹{κ} A], where [B]'s values
    are. *)
Lemma per_univ_of_instance_at : forall {Γ κ κc A B N R RA} {i j : nat} {ρ a n},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Γ ▹{κ} A ≈ Γ ▹{κ} A ∈ per_ctx_env ↘ RA ->
    Γ ⊨ A : abs_kind_sort κ Typeω@j ->
    Γ ▹{κ} A ⊨ B : abs_kind_sort κc Typeω@i ->
    Γ ⊨ N : A ->
    exp_scoped (List.length Γ) N ->
    Dom ρ ≈ ρ ∈ R ->
    ⟦ A ⟧ ρ ↘ a ->
    glu_term_value N ρ (domain_kind a) n ->
    Dom ρ ↦ n ⦂ entry_type_value a ≈ ρ ↦ n ⦂ entry_type_value a ∈ RA ->
    exists c b, ⟦ B[Id,,N] ⟧ ρ ↘ c /\ ⟦ B ⟧ ρ ↦ n ⦂ entry_type_value a ↘ b /\ Dom c ≈ b ∈ per_univ i.
Proof.
  intros * HΓ HΓA HA HB HN HNs Hρ Ha Hn Hρn.
  pose proof (rel_type_of_abs_kind_sort HA) as HAt.
  pose proof (rel_type_of_abs_kind_sort HB) as HBt.
  pose proof (rel_sub_under_ctx_extend_sub (κ := κ) (rel_sub_id (ex_intro _ _ HΓ)) HN
                (rel_type_not_level_sort_of_sort (type_sort_abs_kind _ _ (type_sort_universe _)) HA) HNs HNs) as HidN.
  rewrite exp_sub_id in HidN.
  pose proof (rel_type_inversion HBt) as [RA' [HΓA' HBgen]].
  destruct (eval_sub_id_rel HΓ Hρ) as [Hid _].
  pose proof (per_ctx_env_of_typ (κ := κ) HΓ HAt) as HΓA0.
  assert (EA : RA' <~> per_env_extend A A R) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (EA2 : RA <~> per_env_extend A A R) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (rel_type_inversion_simple_at HΓ HAt) as HAs.
  pose proof (per_ctx_env_retag HΓ _ _ Hρ) as Hρr.
  pose proof (per_ctx_env_retag_left HΓ _ _ Hρ) as Hρl.
  destruct (HAs _ _ Hρl) as (ar & a0 & Ear & Ea0 & [Rar Har]).
  functional_eval_rewrite_clear.
  pose proof (per_univ_elem_kind _ _ _ _ Har) as Hkar.
  pose proof (proj1 (EA2 _ _) Hρn) as Hρn'.
  destruct Hρn' as [_ Hhead _ Hright _ Hrr].
  change (Dom n ≈ n ∈ per_head A A ρ ρ) in Hhead.
  (** [Id ,, N] at [ρ] *)
  assert (Hev1 : ⟦ Id,,N : Γ ▹{κ} A ⟧s ρ ↘ ctx_retag Γ ρ ↦ n ⦂ centry_tag (ce_ass κ A) Γ (ctx_retag Γ ρ)).
  { destruct (evaluated_kind_or_propositional (domain_kind a)) as [Hev | Hp].
    - assert (Hnp : ~ head_propositional gc_deps gc_stack (ce_ass κ A) Γ (ctx_retag Γ ρ)).
      { intros Hhp; apply (head_propositional_iff (e := ce_ass κ A) HΓ eq_refl HAs Hρr Ear) in Hhp.
        rewrite Hkar in Hhp; destruct Hev; discriminate. }
      destruct (domain_kind a); [| inversion Hev |]; cbn in Hn; exact (eval_sub_extend _ _ _ _ _ _ _ Hid Hnp Hn).
    - assert (Hhp : head_propositional gc_deps gc_stack (ce_ass κ A) Γ (ctx_retag Γ ρ))
        by (apply (head_propositional_iff (e := ce_ass κ A) HΓ eq_refl HAs Hρr Ear); rewrite Hkar; exact Hp).
      rewrite Hp in Hn; cbn in Hn; subst n.
      exact (eval_sub_extend_proof _ _ _ _ _ N Hid Hhp). }
  pose proof (per_env_extend_intro_tagged HΓA0 HΓ Hρ Hhead) as Hext0.
  pose proof (proj2 (EA _ _) Hext0) as Hext.
  destruct (rel_type_body_of_retagged HΓA' HBgen _ _ HΓ _ _ HidN ρ ρ
                (ρ ↦ n ⦂ centry_tag (ce_ass κ A) Γ ρ) (ρ ↦ n ⦂ centry_tag (ce_ass κ A) Γ ρ) Hρ Hev1 Hev1 Hext)
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Hchain].
  destruct Hchain as [Ht12 _].
  (** The two tags *)
  destruct Hext0 as [_ _ Hleft _ Hlr _].
  assert (Hcross : Dom ρ ↦ n ⦂ centry_tag (ce_ass κ A) Γ ρ ≈ ρ ↦ n ⦂ entry_type_value a ∈ RA).
  { apply EA2; apply per_env_extend_intro; [ exact Hρ | exact Hhead | exact Hleft | exact Hright | exact Hlr | exact Hrr ]. }
  destruct (rel_type_inversion_simple_at HΓA HBt _ _ Hcross) as (b1 & b2 & Eb1 & Eb2 & Hb12).
  functional_eval_rewrite_clear.
  exists t1, b2; split; [ exact Ht1 | split; [ exact Eb2 |] ].
  etransitivity; eassumption.
Qed.

(** An element of a [Π] takes arguments of its domain's kind. *)
Lemma per_univ_elem_pi_arg_kind : forall {i κd κc a ρ B a' ρ' B' R f f'},
    evaluated_kind κc ->
    DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem i ↘ R ->
    Dom f ≈ f' ∈ R ->
    arg_kind gc_deps gc_stack f = domain_kind a.
Proof.
  intros * Hev HR Hf.
  invert_per_univ_elem HR.
  match goal with HE : _ <~> pi_elements _ _ _ _ |- _ => apply HE in Hf end.
  exact (pi_elements_left _ _ _ _ _ _ Hf).
Qed.

(** An application at a [Π] into a type of an evaluated kind: the
    function's gluing applies it to the glued argument, at the codomain's
    value at the argument's.  That value is related to the value of the
    instantiated type ([per_univ_of_instance_at]), and the application is
    moved to the instantiated type's gluing, its witness
    ([glu_univ_elem_exp_conv]). *)
Lemma glu_rel_exp_app_evaluated : forall {Γ κd κc A B M N} {i : nat},
    Γ ⊩ A : abs_kind_sort κd Typeω@i ->
    Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    evaluated_kind κc ->
    Γ ⊩ M : a_pi κd κc A B ->
    Γ ⊩ N : A ->
    Γ ⊩ B[Id,,N] : abs_kind_sort κc Typeω@i ->
    Γ ⊩ M $ N : B[Id,,N].
Proof.
  intros * HA HB Hk Hev HM HN HW.
  destruct (glu_rel_exp_sort_typ HW (sort_kind_abs_kind_sort κc i)) as (SbW & kW & HSbW & _ & HWg).
  destruct (presup_ctx_glu_rel_exp HA) as [SbΓ HSbΓ].
  destruct (presup_ctx_glu_rel_exp HB) as [SbB HSbB].
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  pose proof (glu_rel_exp_to_wf_exp HB) as HBt.
  pose proof (glu_rel_exp_to_wf_exp HN) as HNt.
  pose proof (glu_rel_exp_pi_large HA HB Hk) as HΠ.
  pose proof (glu_rel_exp_kind_sort_large_inversion HSbΓ HA) as HAg.
  pose proof (glu_rel_exp_kind_sort_large_inversion HSbΓ HΠ) as HΠg.
  pose proof (glu_rel_exp_kind_sort_large_inversion HSbB HB) as HBg.
  assert (HMg : forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ SbΓ -> glu_rel_exp_with_sub i Δ M (a_pi κd κc A B) σ ρ).
  { apply (glu_rel_exp_at_typ_index HSbΓ); [| exact HM ].
    intros Δ σ ρ Hσ; apply glu_rel_typ_with_sub_of_point; exact (proj2 (HΠg _ _ _ Hσ)). }
  assert (HNg : forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ SbΓ -> glu_rel_exp_with_sub i Δ N A σ ρ).
  { apply (glu_rel_exp_at_typ_index HSbΓ); [| exact HN ].
    intros Δ σ ρ Hσ; apply glu_rel_typ_with_sub_of_point; exact (proj2 (HAg _ _ _ Hσ)). }
  assert (HNs : exp_scoped (List.length Γ) N) by exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HNt))).
  pose proof (completeness_fundamental_exp _ _ _ HAt) as HAc.
  pose proof (completeness_fundamental_exp _ _ _ HBt) as HBc.
  pose proof (completeness_fundamental_exp _ _ _ HNt) as HNc.
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [R HR].
  destruct (glu_ctx_env_per_ctx_env HSbB) as [RB HRB].
  assert (EW : SbΓ <∙> SbW) by (eapply functional_glu_ctx_env; eassumption).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := kW); [ exact HSbΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_per_env HSbΓ HR Hσ) as Hρ.
  destruct (HNg _ _ _ Hσ) as [a n Pa Ela Ea Hn Hga HNσ].
  destruct (HAg _ _ _ Hσ) as [HAσ (a0 & Ea0 & _ & HaP)].
  assert (a0 = a) by (eapply functional_eval_exp; eassumption); subst a0; clear Ea0.
  pose proof (glu_cons_sub_at HSbΓ HSbB Hσ Ea Hga HNσ) as Hc.
  pose proof (glu_ctx_env_per_env HSbB HRB Hc) as Hρn.
  destruct (per_univ_of_instance_at HR HRB HAc HBc HNc HNs Hρ Ea Hn Hρn) as (c & b & Ec & Eb & Hcb).
  (** The witness: the instantiated type glued at its value *)
  destruct (HWg _ _ _ (proj1 (EW _ _ _) Hσ)) as [c' Pc Elc Ec' Hgc HWσ].
  assert (c' = c) by (eapply functional_eval_exp; eassumption); subst c'; clear Ec'.
  destruct (HBg _ _ _ Hc) as [HBc' (b' & Eb' & _ & HbP)].
  destruct (HMg _ _ _ Hσ) as [p m Pp Elp Ep Hm Hgp HMσ].
  inversion Ep; subst; functional_eval_rewrite_clear.
  assert (HmE : ⟦ M ⟧ ρ ↘ m) by (destruct Hev; exact Hm).
  invert_glu_univ_elem Hgp.
  match goal with HE : ?el <∙> pi_glu_exp_pred _ _ _ _ _ _ _ _, HMσ' : ?el _ _ _ _ |- _ => apply HE in HMσ' end.
  inversion_clear HMσ as [? ? ? ? IT OT HMσt Hmm HΠeq HIT HOT HIP Happ].
  match goal with Hg2 : glu_univ_elem _ IP IEl a |- _ => rename Hg2 into Hga2 end.
  match goal with Hp2 : per_univ_elem _ in_rel a a |- _ => rename Hp2 into Hin end.
  match goal with Hp2 : per_univ_elem _ elem_rel (d_pi _ _ _ _ _) _ |- _ => rename Hp2 into Hel end.
  destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga Hga2) as [_ EEl].
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ κd i Hga2 (HaP _ _ Hga2) HAσ) as [_ Hna].
  assert (⊢ Δ) by (gen_presups; assumption).
  assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
  pose proof (HIP _ _ Hid) as HITP; rewrite exp_wk_id in HITP.
  pose proof (glu_univ_elem_typ_unique_upto_exp_eq' Hga2 Hna HITP (HaP _ _ Hga2)) as HITeq.
  assert (HNσ' : Δ ⊢ N[σ] : IT[wk_id]ʷ ® n ∈ IEl).
  { rewrite exp_wk_id; apply EEl in HNσ.
    eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hga2 | exact HNσ | apply wf_exp_eq_sym; exact HITeq ]. }
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hga2 _ _ _ _ _ HNσ' Hin) as equiv_n.
  destruct (Happ _ _ _ _ Hid HNσ' equiv_n) as (mn & Hmn & HMN).
  match goal with H1 : forall c (equiv_c : _ c c) b, _ -> glu_univ_elem _ _ _ b |- _ =>
    pose proof (H1 _ equiv_n _ Eb) as Hgb end.
  pose proof (HbP _ _ Hgb) as HBcP.
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ κc i Hgb HBcP HBc') as [Hkb Hnb].
  destruct Hcb as [Rc HRc].
  pose proof (per_univ_elem_kind _ _ _ _ HRc) as Hkc.
  pose proof (per_univ_elem_pi_arg_kind Hev Hel Hmm) as Harg.
  assert (HappE : ⟦ M $ N ⟧ ρ ↘ mn).
  { destruct (evaluated_kind_or_propositional (domain_kind a)) as [Hea | Hpa].
    - eapply eval_exp_app; [ exact HmE | rewrite Harg; exact Hea | | exact Hmn ].
      destruct (domain_kind a); [| inversion Hea |]; exact Hn.
    - rewrite Hpa in Hn; cbn in Hn; subst n.
      eapply eval_exp_app_proof; [ exact HmE | rewrite Harg; exact Hpa | exact Hmn ]. }
  econstructor; [ exact Ec | rewrite Hkc, Hkb; destruct Hev; exact HappE | exact Hgc |].
  (** The application at the codomain's value, moved to the witness *)
  assert (HMNb : Δ ⊢ (M $ N)[σ] : B[Id,,N][σ] ® mn ∈ OEl n equiv_n).
  { rewrite exp_sub_extend_sub; cbn [exp_sub].
    rewrite exp_wk_id in HMN.
    pose proof (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HMN) as HOTP.
    pose proof (glu_univ_elem_typ_unique_upto_exp_eq' Hgb Hnb HOTP HBcP) as HOTeq.
    exact (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgb _ _ _ _ _ HMN HOTeq). }
  assert (Hbc : Dom b ≈ c ∈ per_univ i) by (eexists; symmetry; exact HRc).
  exact (glu_univ_elem_exp_conv Hbc Hgb Hgc HMNb HWσ).
Qed.

(** An application ([wf_app]): of a function into a type of an evaluated
    kind, or of a proof of a [∀], a proof of the instance.  The instance
    of the codomain is glued, its witness. *)
Lemma glu_rel_exp_app : forall {Γ κd κc A Srt B M N} {i : nat},
    Γ ⊩ A : Srt ->
    sort_kind Srt κd ->
    Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    Γ ⊩ M : a_pi κd κc A B ->
    Γ ⊩ N : A ->
    Γ ⊩ B[Id,,N] : abs_kind_sort κc Typeω@i ->
    Γ ⊩ M $ N : B[Id,,N].
Proof.
  intros * HA HS HB Hk HM HN HW.
  destruct (sort_kind_abs_kind_sort_inv HS) as [j ->].
  pose proof (glu_rel_exp_kind_sort_lift (k := max j i) (PeanoNat.Nat.le_max_l j i) HA) as HA'.
  pose proof (glu_rel_exp_kind_sort_lift (k := max j i) (PeanoNat.Nat.le_max_r j i) HB) as HB'.
  destruct (evaluated_kind_or_propositional κc) as [Hev | ->].
  - pose proof (glu_rel_exp_kind_sort_lift (k := max j i) (PeanoNat.Nat.le_max_r j i) HW) as HW'.
    exact (glu_rel_exp_app_evaluated HA' HB' Hk Hev HM HN HW').
  - apply glu_rel_exp_proof; [ exact HW |].
    eapply wf_app; [ exact (glu_rel_exp_to_wf_exp HA') | apply sort_kind_abs_kind_sort
                   | exact (glu_rel_exp_to_wf_exp HB') | exact Hk | exact (glu_rel_exp_to_wf_exp HM)
                   | exact (glu_rel_exp_to_wf_exp HN) ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_fn glu_rel_exp_app : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

(** [Π] at a universe ([wf_pi]): at a large universe, or at a small one. *)
Lemma glu_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A : abs_kind_sort κd U ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : (abs_kind_sort κc U)[↑]ʷ ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_pi κd κc A B : abs_kind_sort κc U ).
Proof.
  glu_inst_intro.
  match goal with HU : (exists i, ?U = Typeω@i) \/ _ |- _ => destruct HU as [[? ->] | (L & n & -> & HL)] end.
  - rewrite abs_kind_sort_wk in *; cbn [exp_wk] in *.
    rewrite abs_kind_sort_sub; cbn [exp_sub].
    assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A))
      by (eapply glu_rel_sub_inst_q; [ exact Hτ | eassumption | apply sort_kind_abs_kind_sort ]).
    eapply glu_rel_exp_pi_large; glu_inst_premise.
  - (** The domain, at a large universe, for the lifted instance *)
    match goal with HA : glu_rel_exp_under_sub Γ A _ |- _ => rename HA into HAs end.
    assert (HAl : @glu_rel_exp_under_sub (gc_mk Θ2 Ξ2) Γ A (abs_kind_sort κd Typeω@n)).
    { eapply glu_rel_exp_under_sub_conv_typ; [| exact HAs ].
      intros Γ0 τ0 Hτ0 HA0; rewrite !abs_kind_sort_sub in *; cbn [exp_sub] in *.
      eapply glu_rel_exp_kind_sort_small_large; [ glu_inst | exact HA0 ]. }
    assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A))
      by (eapply glu_rel_sub_inst_q; [ exact Hτ | exact HAl | apply sort_kind_abs_kind_sort ]).
    rewrite abs_kind_sort_sub; cbn [exp_sub].
    eapply glu_rel_exp_pi_small; glu_inst_premise.
Qed.

Lemma glu_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊩ λ A M : a_pi κd κc A B ).
Proof.
  glu_inst_intro.
  assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A)) by (eapply glu_rel_sub_inst_q; eassumption).
  eapply (glu_rel_exp_fn (A := A[τ]) (Srt := Srt)); glu_inst_premise.
Qed.

Lemma glu_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : a_pi κd κc A B ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M $ N : B[Id,,N] ).
Proof.
  glu_inst_intro.
  assert (Hq : glu_rel_sub_inst (Γ' ▹{κd} A[τ]) (q τ) (Γ ▹{κd} A)) by (eapply glu_rel_sub_inst_q; eassumption).
  (** The codomain's instance at the argument, the witness *)
  assert (Hext : glu_rel_sub_inst Γ' (τ,,N[τ]) (Γ ▹{κd} A)).
  { eapply glu_rel_sub_inst_extend; [ exact Hτ | eapply glu_rel_exp_under_sub_wf; eassumption | eassumption
                                    | eapply glu_rel_exp_under_sub_inst_renaming; eassumption ]. }
  rewrite <- exp_sub_extend_comm.
  eapply (glu_rel_exp_app (A := A[τ]) (Srt := Srt) (B := B[q τ])); try glu_inst_premise.
  rewrite exp_sub_q_extend; glu_inst.
Qed.

(** The equations glue their context, which their domain's premise
    does. *)
Lemma glu_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : abs_kind_sort κd U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
