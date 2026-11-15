(** * The Rules of Subtyping

    The rules of [⊆] in the PER model, with the subsumption rules of terms
    and equations and the symmetry and transitivity of equations.  The
    lemmas they rest on are in [LogicalRelation/Subtyping.v] and
    [LogicalRelation/Levels.v]. *)

From Stdlib Require Import Lia List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Contexts Universes Functions Levels Subtyping.
From Mctt.Core.Semantic Require Import Levels Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Generalizable All Variables.

(** ** Subtyping of Small Universes

    The premise [maxl M M' ≈ M'] is, in the model, the canonical order on the
    two levels at every length ([per_sublvl_of_max]), which is what
    [per_subtyp_suniv] asks.  A small universe below a large one needs only
    that its level is a level. *)
Lemma sem_subtyp_suniv :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M M' ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ ⊆ Type⟨M'⟩ ).
Proof.
  intros * HΓc HM HM' Hmax; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HM') as [env_relΓ' [HΓ' HM'gen]].
  pose proof (rel_exp_of_level_inversion Hmax) as [env_relΓ'' [HΓ'' Hmaxgen]].
  eexists_subtyp_with 0.
  intros Γ' env_rel' HΓ0 σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HM'gen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  destruct (Hmaxgen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [j1 j2 j3 j4 Hj1 Hj2 Hj3 Hj4 Hjchain].
  inversion Hj2; subst.
  functional_eval_rewrite_clear.
  assert (Dom m1 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (Dom m2 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (Dom n4 ≈ n3 ∈ per_lvl) by lvl_pw.
  assert (Dom n2 ≈ n3 ∈ per_lvl) by lvl_pw.
  assert (Dom domain_level_max m2 n2 ≈ n3 ∈ per_lvl) by lvl_pw.
  functional_eval_rewrite_clear.
  exists 𝕌@m1 𝕌@m2 𝕌@n4 𝕌@n3; try (apply eval_exp_univ; eassumption).
  - eexists; apply per_univ_elem_core_suniv';
      [ eassumption | exact I | reflexivity ].
  - eexists; apply per_univ_elem_core_suniv';
      [ eassumption | exact I | reflexivity ].
  - apply per_subtyp_suniv; [| exact I ].
    apply (per_sublvl_of_max m2 n2 n3); assumption.
Qed.

Lemma sem_subtyp_small_large :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ ⊆ Typeω@i ).
Proof.
  intros * HΓc HM; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_subtyp_with (S i).
  intros Γ' env_rel' HΓ0 σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Dom m1 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (Dom m2 ≈ m2 ∈ per_lvl) by lvl_pw.
  exists 𝕌@m1 𝕌@m2 𝕌ω@i 𝕌ω@i; try (apply eval_exp_univ; eassumption); try apply eval_exp_typ.
  - eexists; apply per_univ_elem_core_suniv';
      [ eassumption | exact I | reflexivity ].
  - eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ].
  - apply per_subtyp_small_large; [ assumption | solve_universe_index ].
Qed.

Lemma sem_subtyp_refl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M' : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ⊆ M' ).
Proof.
  intros * _ HS HM; sem_intro; [ assumption |].
  destruct (rel_type_of_sort_ge HS HM) as [k Hk].
  exact (rel_subtyp_under_ctx_refl (Hk k (le_n k))).
Qed.

Lemma sem_subtyp_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ⊆ M' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' ⊆ M'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ⊆ M'' ).
Proof. intros * H1 H2; sem_intro; [ assumption | exact (rel_subtyp_under_ctx_trans H1 H2) ]. Qed.

(** ** [Sub-Univ]

    [Typeω@i[σ]] is [Typeω@i], so all four values in both columns are equal and the
    two commutation obligations are reflexivity.  Only the middle has content, and
    it is [per_subtyp_univ].  The ambient level must be strictly above [j], hence
    [S j]. *)
Lemma sem_subtyp_univ :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     i < j ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Typeω@i ⊆ Typeω@j ).
Proof.
  intros * HΓsem Hij; sem_intro; [ assumption |].
  assert (Hij' : i <= j) by lia; clear Hij; rename Hij' into Hij.
  pose proof (rel_ctx_wf_per_ctx_env HΓsem) as [env_relΓ HΓ].
  eexists_subtyp_with (S j).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists 𝕌ω@i 𝕌ω@i 𝕌ω@j 𝕌ω@j; try apply eval_exp_typ.
  - eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ].
  - eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ].
  - apply per_subtyp_univ; solve [ lia | solve_universe_index ].
Qed.

(** ** Types of Levels

    A type of levels is below every type of levels of a larger sort: in the
    model their elements are the same, the level values. *)
Lemma sem_subtyp_level :
  `( m <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Level@m ⊆ Level@n ).
Proof.
  intros * Hmn HΓsem; sem_intro; [ assumption |].
  pose proof (rel_ctx_wf_per_ctx_env HΓsem) as [env_relΓ HΓ].
  eexists_subtyp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (Levelᵈ@m) (Levelᵈ@m) (Levelᵈ@n) (Levelᵈ@n); try apply eval_exp_level.
  - eexists; per_univ_elem_econstructor; reflexivity.
  - eexists; per_univ_elem_econstructor; reflexivity.
  - apply per_subtyp_level; assumption.
Qed.

(** ** [Sub-Pi]

    [per_subtyp_pi] needs the two Π-values self-related, a domain PER relating
    them, and a codomain subtyping at every argument pair of that PER.  The first
    three come from [rel_typ_of_pi] at the three type equalities among the
    premises (the two self-equalities give the Π-values, the heterogeneous one the
    domain PER).  The fourth is the codomain premise, whose extended context PER is
    [per_env_extend A' A' env_relΓ] because both codomains are checked in
    [Γ ▹ A'] (see [System/Definitions.v]).

    The one step with content moves the quantified argument pair from the domain
    PER into that extended context PER: the two PERs share their right value
    [⟦A'⟧ρ'σ'], so [per_univ_elem_left_irrel] identifies them.

    Levels and kinds: all four types are at the sorts of their kinds over
    the one index [i] ([abs_kind_sort]), so all are types at [i]
    ([rel_type_of_abs_kind_sort]) with no lifting; the codomain subtyping
    comes at whatever level [rel_subtyp_under_ctx_simple] reports, and
    everything is raised to [max i i0].  The kinds of the domains and
    codomains are read off their sorts ([rel_exp_of_abs_kind_sort_at]), and
    the codomain kind is evaluated, as [per_subtyp_pi] requires. *)
Lemma sem_subtyp_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : abs_kind_sort κd Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A' : abs_kind_sort κd Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : abs_kind_sort κd Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : abs_kind_sort κc Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ⊨ B' : abs_kind_sort κc Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ⊨ B ⊆ B' ->
     pi_kinds κd κc ->
     evaluated_kind κc ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_pi κd κc A B ⊆ a_pi κd κc A' B' ).
Proof.
  intros * HAself0 HA'self0 HAA'0 HB0 HB'0 Hsub Hk Hev0; sem_intro; [ assumption |].
  pose proof (rel_type_of_abs_kind_sort HAself0) as HAself.
  pose proof (rel_type_of_abs_kind_sort HA'self0) as HA'self.
  pose proof (rel_type_of_abs_kind_sort HAA'0) as HAA'.
  pose proof (rel_type_of_abs_kind_sort HB0) as HB.
  pose proof (rel_type_of_abs_kind_sort HB'0) as HB'.
  assert (HAk : rel_type_kind Γ A κd)
    by (intros R HR ρ ρ' Hρ; exact (rel_exp_of_abs_kind_sort_at HR HAself0 _ _ Hρ)).
  assert (HA'k : rel_type_kind Γ A' κd)
    by (intros R HR ρ ρ' Hρ; exact (rel_exp_of_abs_kind_sort_at HR HA'self0 _ _ Hρ)).
  assert (HBk : rel_type_kind (Γ ▹{κd} A) B κc)
    by (intros R HR ρ ρ' Hρ; exact (rel_exp_of_abs_kind_sort_at HR HB0 _ _ Hρ)).
  assert (HB'k : rel_type_kind (Γ ▹{κd} A') B' κc)
    by (intros R HR ρ ρ' Hρ; exact (rel_exp_of_abs_kind_sort_at HR HB'0 _ _ Hρ)).
  clear HAself0 HA'self0 HAA'0 HB0 HB'0.
  pose proof (rel_type_inversion HAA') as [env_relΓ [HΓ HAA'gen]].
  pose proof (rel_subtyp_under_ctx_simple Hsub) as [env_relΓA' [HΓA' [i0 Hsubgen]]].
  pose proof (per_ctx_env_of_typ (κ := κd) HΓ HA'self) as HΓA'can.
  assert (HiffA' : env_relΓA' <~> per_env_extend A' A' env_relΓ)
    by (eapply per_ctx_env_right_irrel; [ exact HΓA' | exact HΓA'can ]).
  eexists_subtyp_with (max i i0).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσ HΓ' HΓ); eassumption).
  (** The two Π-values, each from its own self-equality. *)
  destruct (rel_typ_of_pi_evaluated HAself HAself HAk HB HBk Hk Hev0 _ _ HΓ' _ _ _ _ _ _ Hσ Hρ Hev Hev')
    as [in1 [p1 [p2 [p3 [p4 [Hp1 [Hp2 [Hp3 [Hp4 [_ [_ Htyp1]]]]]]]]]]].
  destruct (rel_typ_of_pi_evaluated HA'self HA'self HA'k HB' HB'k Hk Hev0 _ _ HΓ' _ _ _ _ _ _ Hσ Hρ Hev Hev')
    as [in2 [q1 [q2 [q3 [q4 [Hq1 [Hq2 [Hq3 [Hq4 [_ [Hmid2 Htyp2]]]]]]]]]]].
  pose proof Htyp1 as [P1 P2 P3 P4 HP1 HP2 HP3 HP4 HPchain].
  pose proof Htyp2 as [Q1 Q2 Q3 Q4 HQ1 HQ2 HQ3 HQ4 HQchain].
  assert (P2 = d_pi κd κc p2 ρσ B) as ->
    by (eapply functional_eval_exp; [ exact HP2 | apply eval_exp_pi; exact Hp2 ]).
  assert (Q3 = d_pi κd κc q3 ρ'σ' B') as ->
    by (eapply functional_eval_exp; [ exact HQ3 | apply eval_exp_pi; exact Hq3 ]).
  (** The domain PER, from the heterogeneous equality's middle link. *)
  destruct (HAA'gen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  assert (d2 = p2) as -> by (eapply functional_eval_exp; [ exact Hd2 | exact Hp2 ]).
  assert (d3 = q3) as -> by (eapply functional_eval_exp; [ exact Hd3 | exact Hq3 ]).
  assert (Hmid : Dom p2 ≈ q3 ∈ per_univ i) by pairwise.
  destruct Hmid as [in_rel Hin_rel].
  (** The two element PERs are named rather than left to [eexists]: [pairwise]
      matches its [rel_chain] hypothesis syntactically, so a metavariable in the
      relation position of the goal finds nothing. *)
  exists P1 (d_pi κd κc p2 ρσ B) Q4 (d_pi κd κc q3 ρ'σ' B'); try eassumption.
  - exists (per_pi p2 p3 in1 B ρσ B ρ'σ').
    eapply per_univ_elem_cumu_max_left; pairwise.
  - (** [Q4 ≈ Q3], i.e. the second chain's last link read backwards. *)
    exists (per_pi q2 q3 in2 B' ρσ B' ρ'σ').
    eapply per_univ_elem_cumu_max_left; pairwise.
  - eapply per_subtyp_pi with (in_rel := in_rel)
                              (elem_rel := per_pi p2 p3 in1 B ρσ B ρ'σ')
                              (elem_rel' := per_pi q2 q3 in2 B' ρσ B' ρ'σ').
    + exact Hev0.
    + eapply per_univ_elem_cumu_max_left; exact Hin_rel.
    + intros c c' b b' Hc Hb Hb'.
      (** [in_rel] and [in2] share the value [q3] on the right. *)
      assert (Hii : in_rel <~> in2)
        by (eapply per_univ_elem_left_irrel; [ exact Hin_rel | exact Hmid2 ]).
      pose proof (entry_readable_of_elem Hin_rel Hc) as [Rc Rc'].
      rewrite Hii in Hc.
      assert (Hext : Dom ρσ ↦ c ⦂ entry_type_value p2 ≈ ρ'σ' ↦ c' ⦂ entry_type_value q3 ∈ env_relΓA')
        by (rewrite HiffA'; apply per_env_extend_intro';
            [ exact Hρσ | eapply per_head_of; [ exact Hq2 | exact Hq3 | exact Hmid2 | exact Hc ] | exact Rc | exact Rc' ]).
      destruct (Hsubgen _ _ Hext) as [b0 [b0' [Hb0 [Hb0' Hsubb]]]].
      assert (b0 = b) as -> by (eapply functional_eval_exp; [ exact Hb0 | exact Hb ]).
      assert (b0' = b') as -> by (eapply functional_eval_exp; [ exact Hb0' | exact Hb' ]).
      apply per_subtyp_cumu_right; exact Hsubb.
    + eapply per_univ_elem_cumu_max_left; pairwise.
    + eapply per_univ_elem_cumu_max_left; pairwise.
Qed.

Lemma sem_exp_eq_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A' : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A' ).
Proof.
  intros * HM HA' HS Hsub; sem_intro; [ assumption |].
  destruct (rel_type_of_sort_ge HS HA') as [k Hk].
  exact (rel_exp_under_ctx_subtyp HM (Hk k (le_n k)) Hsub).
Qed.

Lemma sem_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A' : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A' ).
Proof. intros * HM HA' HS Hsub; eapply sem_exp_eq_subtyp; [ exact HM | exact HA' | exact HS | exact Hsub ]. Qed.

Lemma sem_exp_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' ≈ M : A ).
Proof. intros * HM; sem_intro; [ assumption | exact (rel_exp_under_ctx_sym HM) ]. Qed.

Lemma sem_exp_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' ≈ M'' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M'' : A ).
Proof. intros * H1 H2; sem_intro; [ assumption | exact (rel_exp_under_ctx_trans H1 H2) ]. Qed.
