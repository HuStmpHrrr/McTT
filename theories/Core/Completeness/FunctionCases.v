(** * Fundamental Theorem: Π-Types

    Substitution pushes through [Π], [λ] and application by computation of
    [exp_sub]: [(Π A B)[σ]] is [Π (A[σ]) (B[q σ])].  So only the congruence, β and
    η rules are validated here.

    The file is organised around [rel_typ_of_pi]: the type judgment of a Π, in the
    form needed at each stage of [subtyp_under_ctx].  In all five rules the type is
    a Π built from a domain judgment and a judgment in the extended context, so the
    element PER is always the canonical [per_pi].  The remaining work of each rule
    concerns its own four values:

    - [rel_exp_pi_cong] has nothing more to do: the type judgment is the goal,
      read at [per_univ i] instead of at the element PER.
    - [rel_exp_fn_cong] applies [rel_exp_under_ctx_q], whose three obligations
      are the three links of [per_pi] once [eval_app_fn] has stripped the λ.
    - [rel_exp_app_cong], [rel_exp_pi_beta] and [rel_exp_fn_eta] read the
      canonical [per_pi] off a Π-typed judgment with [per_pi_iff], and differ in
      what they do with the resulting [rel_mod_app].

    Cumulativity is needed for the level: [per_univ_elem_pi_canonical] requires the
    domain and codomain of a Π-value to be related at one level, while the syntax
    types [A] and [B] at unrelated ones.  So every rule whose codomain level comes
    from a presupposition lifts both to their maximum with [rel_exp_cumu_ge]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import
  ContextCases LevelCases LogicalRelation SubstitutionCases UniverseCases VariableCases.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

(** ** The Type Judgment of a Π

    A stage of [subtyp_under_ctx], that is, a related pair of environments and a
    related pair of substitutions out of it, determines four Π-values and the
    canonical element PER they carry.  Both are forced: [(Π A B)[σ]] is
    [Π (A[σ]) (B[q σ])] definitionally, so [eval_exp_pi] applies to the
    substituted head directly, and the [per_pi] is the one
    [per_univ_elem_pi_chain] produces.

    As in [rel_typ_of_instance], the domain's four values are reported with both
    pairs a caller may need: the outer pair, at which [per_env_extend_sub_intro]
    and every irrelevance step along [q σ] are stated, and the inner pair, at which
    [per_pi_iff] must be applied, since the middle link of the type chain is
    [Π a2 ρσ B ≈ Π a3 ρ'σ' B']. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma rel_typ_of_pi_univ : forall {Γ A A' u B B'},
    Γ ⊨ A ≈ A' : ulvl_tm u ->
    Γ ▹ A ⊨ B ≈ B' : ulvl_tm u ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        exists in_rel a1 a2 a3 a4,
          ⟦ A[σ] ⟧ ρ ↘ a1 /\
          ⟦ A ⟧ ρσ ↘ a2 /\
          ⟦ A' ⟧ ρ'σ' ↘ a3 /\
          ⟦ A'[σ'] ⟧ ρ' ↘ a4 /\
          DF a1 ≈ a4 ∈ per_univ_elem u ↘ in_rel /\
          DF a2 ≈ a3 ∈ per_univ_elem u ↘ in_rel /\
          rel_exp (Π A B) σ ρ ρσ (Π A' B') σ' ρ' ρ'σ'
            (per_univ_elem u (per_pi in_rel B ρσ B' ρ'σ')).
Proof.
  intros * HA HB * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_exp_univ_cumu (uidx_le_ulvl u) (rel_exp_under_ctx_refl_left HA)) as HAself.
  pose proof (rel_exp_of_univ_inversion HA) as [env_relΓ [HΓ HAgen]].
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  (** The domain PER, named by weak functionality: the outer pair the caller is
    owed and the inner pair it needs are links of the same chain, with no
    refinement step in between. *)
  functionalize_per_univ_chain Hachain in_rel.
  exists in_rel, a1, a2, a3, a4.
  do 4 (split; [ eassumption |]).
  do 2 (split; [ pairwise |]).
  apply (mk_rel_exp Πᵈ a1 ρ B[q σ] Πᵈ a2 ρσ B
                    Πᵈ a3 ρ'σ' B' Πᵈ a4 ρ' B'[q σ']);
    [ apply eval_exp_pi; exact Ha1 | apply eval_exp_pi; exact Ha2
    | apply eval_exp_pi; exact Ha3 | apply eval_exp_pi; exact Ha4 |].
  (** The three codomain obligations are, in order, the three [q]-obligations of
      [B] at an argument pair drawn from the domain PER. *)
  eapply per_univ_elem_pi_chain; [ exact Hachain | | |];
    intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc) as Hpair;
    destruct (rel_exp_of_univ_under_ctx_q HΓ' Hσj HAself HB _ _ _ _ _ _ Hpair Hev Hev')
      as [O1 [O2 O3]];
    eassumption.
Qed.

Lemma rel_typ_of_pi : forall {Γ A A'} {i : nat} {B B'},
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ▹ A ⊨ B ≈ B' : Typeω@i ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        exists in_rel a1 a2 a3 a4,
          ⟦ A[σ] ⟧ ρ ↘ a1 /\
          ⟦ A ⟧ ρσ ↘ a2 /\
          ⟦ A' ⟧ ρ'σ' ↘ a3 /\
          ⟦ A'[σ'] ⟧ ρ' ↘ a4 /\
          DF a1 ≈ a4 ∈ per_univ_elem i ↘ in_rel /\
          DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel /\
          rel_typ i (Π A B) σ ρ ρσ (Π A' B') σ' ρ' ρ'σ'
            (per_pi in_rel B ρσ B' ρ'σ').
Proof.
  intros * HA HB * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAself.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ HAgen]].
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  (** The domain PER, named by weak functionality: the outer pair the caller is
    owed and the inner pair it needs are links of the same chain, with no
    refinement step in between. *)
  functionalize_per_univ_chain Hachain in_rel.
  exists in_rel, a1, a2, a3, a4.
  do 4 (split; [ eassumption |]).
  do 2 (split; [ pairwise |]).
  apply (mk_rel_exp Πᵈ a1 ρ B[q σ] Πᵈ a2 ρσ B
                    Πᵈ a3 ρ'σ' B' Πᵈ a4 ρ' B'[q σ']);
    [ apply eval_exp_pi; exact Ha1 | apply eval_exp_pi; exact Ha2
    | apply eval_exp_pi; exact Ha3 | apply eval_exp_pi; exact Ha4 |].
  (** The three codomain obligations are, in order, the three [q]-obligations of
      [B] at an argument pair drawn from the domain PER. *)
  eapply per_univ_elem_pi_chain; [ exact Hachain | | |];
    intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc) as Hpair;
    destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HAself HB _ _ _ _ _ _ Hpair Hev Hev')
      as [O1 [O2 O3]];
    eassumption.
Qed.

(** ** The Small [Π] at a Level Term

    The codomain is at the weakened level [L[↑]ʷ], whose value at an extended
    environment has the realiser of [L]'s at the tail: the two are related
    levels, through [L]'s judgment along [Wk]
    ([rel_exp_under_ctx_shift_at]). *)
Lemma suniv_real_shift : forall {Δ A L} {i : nat} {env_relΔA},
    Δ ⊨ A ≈ A : Typeω@i ->
    Δ ⊨ L : Level ->
    EF Δ ▹ A ≈ Δ ▹ A ∈ per_ctx_env ↘ env_relΔA ->
    forall e x e' x' t1 t2,
      Dom e ↦ x ≈ e' ↦ x' ∈ env_relΔA ->
      ⟦ L[↑]ʷ ⟧ e ↦ x ↘ t1 ->
      ⟦ L ⟧ e' ↘ t2 ->
      dlvl_real t1 = dlvl_real t2.
Proof.
  intros * HA HL HΔA * Hee Ht1 Ht2.
  pose proof (rel_exp_of_level_inversion HL) as [env_relΔ [HΔ _]].
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA'.
  handle_per_ctx_env_irrel.
  destruct (rel_exp_under_ctx_shift_at HΔ HA HL _ _ _ _ Hee)
    as (j & R & b1 & b2 & b3 & b4 & w1 & w2 & w3 & w4 & Hb1 & Hb2 & Hb3 & Hb4 & HR1 & HR2 & Hw1 & Hw2 & Hw3 & Hw4 & Hwc).
  cbn [exp_wk] in Hb1, Hb4.
  simplify_evals.
  match goal with H : per_univ_elem _ _ Levelᵈ Levelᵈ |- _ => invert_per_univ_elem H end.
  apply_relation_equivalence.
  assert (Hw : per_lvl t1 t2) by pairwise.
  exact (per_lvl_real _ _ Hw).
Qed.

(** [rel_exp_of_univ_under_ctx_q] for a codomain in the small universe at
    the weakened level: the five instantiations have the realisers of [L[↑]ʷ]
    at extended environments related to [ρσ ↦ c], which are [L]'s at
    [ρσ] ([suniv_real_shift]), so all five chains are in one small universe. *)
Lemma rel_exp_of_suniv_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B' L env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    Δ ⊨ L : Level ->
    Δ ▹ A ⊨ B ≈ B' : Type⟨L[↑]ʷ⟩ ->
    forall ρ ρ' ρσ ρ'σ' c c' t,
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      ⟦ L ⟧ ρσ ↘ t ->
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ (us (dlvl_real t))) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ (us (dlvl_real t))) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ (us (dlvl_real t))).
Proof.
  intros * HΓ Hσj HA HL HB * Hpair Hev Hev' Ht.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_suniv_tm_inversion HB) as [env_relΔA [HΔA HBgen]].
  pose proof (rel_exp_of_suniv_tm_inversion_simple (rel_exp_under_ctx_refl_left HB))
    as [env_relΔA2 [HΔA2 HBl]].
  pose proof (rel_exp_of_suniv_tm_inversion_simple (rel_exp_under_ctx_refl_right HB))
    as [env_relΔA3 [HΔA3 HBr]].
  handle_per_ctx_env_irrel.
  destruct (rel_sub_under_ctx_q_at HΓ HΔA3 Hσj HA _ _ _ _ _ _ Hpair Hev Hev')
    as [s [s' [Hq [Hq' Hchain]]]].
  destruct (HBgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq')
    as [t0 [Ht0 [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain]]].
  assert (P1 : Dom s ↦ c ≈ ρσ ↦ c' ∈ env_relΔA) by pairwise.
  assert (P2 : Dom ρσ ↦ c ≈ s ↦ c ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ≈ ρ'σ' ↦ c' ∈ env_relΔA) by pairwise.
  assert (P4 : Dom ρ'σ' ↦ c ≈ s' ↦ c' ∈ env_relΔA) by pairwise.
  destruct (HBl _ _ P1) as [x1 [x2 [t1 [Hx1 [Hx2 [Ht1 Hx]]]]]].
  destruct (HBl _ _ P2) as [y1 [y2 [t2 [Hy1 [Hy2 [Ht2 Hy]]]]]].
  destruct (HBr _ _ P3) as [z1 [z2 [t3 [Hz1 [Hz2 [Ht3 Hz]]]]]].
  destruct (HBr _ _ P4) as [u1 [u2 [t4 [Hu1 [Hu2 [Ht4 Hu]]]]]].
  (** All five realisers are [L]'s at [ρσ]. *)
  assert (R0 : dlvl_real t0 = dlvl_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s c ρσ c); [ pairwise | exact Ht0 | exact Ht ]).
  assert (R1 : dlvl_real t1 = dlvl_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s c ρσ c); [ pairwise | exact Ht1 | exact Ht ]).
  assert (R2 : dlvl_real t2 = dlvl_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 ρσ c ρσ c); [ pairwise | exact Ht2 | exact Ht ]).
  assert (R3 : dlvl_real t3 = dlvl_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s' c' ρσ c); [ pairwise | exact Ht3 | exact Ht ]).
  assert (R4 : dlvl_real t4 = dlvl_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 ρ'σ' c ρσ c); [ pairwise | exact Ht4 | exact Ht ]).
  rewrite R0 in Hbchain; rewrite R1 in Hx; rewrite R2 in Hy; rewrite R3 in Hz; rewrite R4 in Hu.
  assert (x1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (y2 = b2) by (eapply functional_eval_exp; eassumption).
  assert (z1 = b3) by (eapply functional_eval_exp; eassumption).
  assert (u2 = b3) by (eapply functional_eval_exp; eassumption).
  subst.
  apply rel_chain_of_pair in Hx, Hy, Hz, Hu.
  set (j := us (dlvl_real t)) in *.
  assert (M1 : rel_chain (per_univ j) ([b1; b2; b3; b4; x2]))
    by (merge_rel_chain Hbchain Hx b2).
  assert (M2 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2]))
    by (merge_rel_chain M1 Hy b2).
  assert (M3 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M2 Hz b3).
  assert (M4 : rel_chain (per_univ j) ([u1; y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M3 Hu b3).
  repeat split.
  - exists b1, x2; repeat split; try eassumption.
    pairwise.
  - exists y1, z2; repeat split; try eassumption.
    pairwise.
  - exists u1, b4; repeat split; try eassumption.
    pairwise.
Qed.

(** The small [Π] at a level term: at each pair of environments it is the
    small [Π] at the realiser of the level's value, whose codomain obligations
    [rel_exp_of_suniv_under_ctx_q] discharges. *)
Lemma rel_exp_pi_cong_small_tm : forall {Γ L A A' B B'},
    Γ ⊨ L : Level ->
    Γ ⊨ A ≈ A' : Type⟨L⟩ ->
    Γ ▹ A ⊨ B ≈ B' : Type⟨L[↑]ʷ⟩ ->
    Γ ⊨ Π A B ≈ Π A' B' : Type⟨L⟩.
Proof.
  intros * HL HA HB.
  pose proof (rel_exp_suniv_tm_large (i := 0) (rel_exp_under_ctx_refl_left HA)) as HAself.
  pose proof (rel_exp_of_suniv_tm_inversion HA) as [env_relΓ [HΓ HAgen]].
  apply rel_exp_of_suniv_tm; [ exact HL |].
  eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev' t Ht.
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [t' [Ht' [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain]]].
  assert (t' = t) as -> by (eapply functional_eval_exp; eassumption).
  functionalize_per_univ_chain Hachain in_rel.
  apply (mk_rel_exp Πᵈ a1 ρ B[q σ] Πᵈ a2 ρσ B
                    Πᵈ a3 ρ'σ' B' Πᵈ a4 ρ' B'[q σ']);
    [ apply eval_exp_pi; exact Ha1 | apply eval_exp_pi; exact Ha2
    | apply eval_exp_pi; exact Ha3 | apply eval_exp_pi; exact Ha4 |].
  eapply rel_chain_mono; [ intros ? ? HR; eexists; exact HR |].
  eapply per_univ_elem_pi_chain; [ exact Hachain | | |];
    intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc) as Hpair;
    destruct (rel_exp_of_suniv_under_ctx_q HΓ' Hσj HAself HL HB _ _ _ _ _ _ t Hpair Hev Hev' Ht)
      as [O1 [O2 O3]];
    eassumption.
Qed.

Hint Resolve rel_exp_pi_cong_small_tm : mctt.

(** ** Π-Congruence *)

Lemma rel_exp_pi_cong : forall {Γ A A'} {i : nat} {B B'},
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ▹ A ⊨ B ≈ B' : Typeω@i ->
    Γ ⊨ Π A B ≈ Π A' B' : Typeω@i.
Proof.
  intros * HA HB.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HA HB _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  (** Forgetting the element PER is all that separates a type judgment from a
      judgment in the universe. *)
  eapply rel_typ_implies_rel_exp; eassumption.
Qed.

Hint Resolve rel_exp_pi_cong : mctt.

(** ** λ-Congruence

    A λ evaluates to a closure with no premise ([eval_exp_fn]), so all four values
    of the goal are known up front.  Each link of the chain applies two closures,
    which [eval_app_fn] turns into evaluating the two bodies in the two extended
    environments.  These are the three obligations of [rel_exp_under_ctx_q], and
    they land in the [per_head] that [per_pi] asks for. *)
Lemma rel_exp_fn_cong : forall {Γ A A'} {i : nat} {B M M'},
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ▹ A ⊨ M ≈ M' : B ->
    Γ ⊨ λ A M ≈ λ A' M' : Π A B.
Proof.
  intros * HA HM.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAself.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (presup_rel_exp_under_ctx HM) as [j HB].
  pose proof (rel_exp_cumu_ge (Nat.le_max_l i j) HAself) as HAk.
  pose proof (rel_exp_cumu_ge (Nat.le_max_r i j) HB) as HBk.
  eexists_rel_exp_with (Nat.max i j).
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HAk HBk _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  exists (per_pi in_rel B ρσ B ρ'σ').
  split; [ exact Htyp |].
  apply (mk_rel_exp λᵈ ρ M[q σ] λᵈ ρσ M
                    λᵈ ρ'σ' M' λᵈ ρ' M'[q σ']);
    [ apply eval_exp_fn | apply eval_exp_fn | apply eval_exp_fn | apply eval_exp_fn |].
  apply rel_chain_4; hnf; intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc)
      as Hpair;
    destruct (rel_exp_under_ctx_q HΓ' Hσj HAself HM _ _ _ _ _ _ Hpair Hev Hev')
      as [[m1 [m2 [Hm1 [Hm2 Hm]]]]
            [[n1 [n2 [Hn1 [Hn2 Hn]]]] [p1 [p2 [Hp1 [Hp2 Hp]]]]]].
  - econstructor; [ apply eval_app_fn; exact Hm1 | apply eval_app_fn; exact Hm2 | exact Hm ].
  - econstructor; [ apply eval_app_fn; exact Hn1 | apply eval_app_fn; exact Hn2 | exact Hn ].
  - econstructor; [ apply eval_app_fn; exact Hp1 | apply eval_app_fn; exact Hp2 | exact Hp ].
Qed.

Hint Resolve rel_exp_fn_cong : mctt.

(** ** Application Congruence

    The type of this rule is an instantiated codomain rather than a Π.  Everything
    the type [B[Id,,N]] costs (two instantiations of the codomain judgment, a
    bridge between them, two merges) is done once in [rel_typ_of_instance], which
    also serves β and the ℕ-eliminator.  What is left here is the term side.

    The element PER is the head PER of [B] at the arguments the type names,
    [⟦N⟧ρσ] and [⟦N⟧ρ'σ'].  Each link of [M]'s chain arrives in the head PER of its
    own pair of arguments, and [per_head_of_args] moves it. *)
Lemma rel_exp_app_cong : forall {Γ A} {i : nat} {B M M' N N'},
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ M ≈ M' : Π A B ->
    Γ ⊨ N ≈ N' : A ->
    Γ ⊨ M $ N ≈ M' $ N' : B[Id ,, N].
Proof.
  intros * HA HB HM HN.
  (** The type mentions [N] on both sides, so the type judgment is built from the
    reflexive-left form of [HN]; [HN] itself is used only for the term chain. *)
  pose proof (rel_exp_under_ctx_refl_left HN) as HNl.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  destruct HM as [? [? [k HMgen]]].
  destruct HN as [? [? [l HNgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** *** The Type

    Nothing here is specific to this rule: the type judgment, the argument's four
    values, and the codomain at an arbitrary related pair of arguments all come
    from [rel_typ_of_instance]. *)
  destruct (rel_typ_of_instance HA HB HNl _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l' [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ p2) (ρ'σ' ↦ p3)).
  split; [ exact Htyp |].
  (** *** The Argument

    The other instantiation of [N]'s judgment, for [N ≈ N'], identified with the
    reflexive one.  Both agree on the values of [A], so [retype_rel_chain] puts
    both chains in one PER, and they merge. *)
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN2 [HNtyp HNexp]].
  destruct HNtyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  assert (b2 = a2) as -> by (eapply functional_eval_exp; [ exact Hb2 | exact Ha2 ]).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; [ exact Hb3 | exact Ha3 ]).
  retype_rel_chain Hbchain Hmid Hnchain.
  assert (Hp1n1 : p1 = n1) by (eapply functional_eval_exp; [ exact Hp1 | exact Hn1 ]).
  assert (Hp2n2 : p2 = n2) by (eapply functional_eval_exp; [ exact Hp2 | exact Hn2 ]).
  subst p1 p2.
  assert (Hnall : rel_chain RN ([n1; n2; n3; n4; p3; p4]))
    by (merge_rel_chain Hnchain Hpchain n1).
  (** *** The Function

    The middle link of its type chain is a Π of the values of [A] and the
    syntactic [B], which identifies its element PER with the canonical [per_pi].
    Each link of its term chain is then a function of an argument pair. *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RM [HMtyp HMexp]].
  destruct HMtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (c2 = Πᵈ a2 ρσ B) as ->
    by (eapply functional_eval_exp; [ exact Hc2 | apply eval_exp_pi; exact Ha2 ]).
  assert (c3 = Πᵈ a3 ρ'σ' B) as ->
    by (eapply functional_eval_exp; [ exact Hc3 | apply eval_exp_pi; exact Ha3 ]).
  assert (HRMmid : DF Πᵈ a2 ρσ B ≈ Πᵈ a3 ρ'σ' B ∈ per_univ_elem k ↘ RM) by pairwise.
  rewrite (per_pi_iff Hmid HRMmid) in Hmchain.
  (** *** The Term Chain

    Three applications, at the three consecutive argument pairs.  The middle value
    of each link is the first value of the next, so the three [rel_mod_app]s form
    one chain. *)
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn34 : Dom n3 ≈ n4 ∈ RN) by pairwise.
  assert (Hn2p3 : Dom n2 ≈ p3 ∈ RN) by pairwise.
  assert (Hn22 : Dom n2 ≈ n2 ∈ RN) by pairwise.
  assert (Hn24 : Dom n2 ≈ n4 ∈ RN) by pairwise.
  assert (Hpi1 : per_pi RN B ρσ B ρ'σ' m1 m2)
    by (eapply rel_chain_4_commut_left; first [ eassumption | solve_chain_PER ]).
  assert (Hpi2 : per_pi RN B ρσ B ρ'σ' m2 m3)
    by (eapply rel_chain_4_related; first [ eassumption | solve_chain_PER ]).
  assert (Hpi3 : per_pi RN B ρσ B ρ'σ' m3 m4)
    by (eapply rel_chain_4_commut_right; first [ eassumption | solve_chain_PER ]).
  destruct (Hpi1 _ _ Hn12) as [r1 r2 Hr1 Hr2 Hr].
  destruct (Hpi2 _ _ Hn23) as [s1 s2 Hs1 Hs2 Hs].
  destruct (Hpi3 _ _ Hn34) as [u1 u2 Hu1 Hu2 Hu].
  assert (Hs1e : s1 = r2) by (eapply functional_eval_app; [ exact Hs1 | exact Hr2 ]).
  assert (Hu1e : u1 = s2) by (eapply functional_eval_app; [ exact Hu1 | exact Hs2 ]).
  subst s1 u1.
  apply (mk_rel_exp r1 r2 s2 u2);
    [ eapply eval_exp_app; [ exact Hm1 | exact Hn1 | exact Hr1 ]
    | eapply eval_exp_app; [ exact Hm2 | exact Hn2 | exact Hr2 ]
    | eapply eval_exp_app; [ exact Hm3 | exact Hn3 | exact Hs2 ]
    | eapply eval_exp_app; [ exact Hm4 | exact Hn4 | exact Hu2 ]
    |].
  apply rel_chain_4;
    [ apply (per_head_of_args Hcod n1 n2 n2 p3 Hn12 Hn2p3 Hn22); exact Hr
    | apply (per_head_of_args Hcod n2 n3 n2 p3 Hn23 Hn2p3 Hn23); exact Hs
    | apply (per_head_of_args Hcod n3 n4 n2 p3 Hn34 Hn2p3 Hn24); exact Hu ].
Qed.

Hint Resolve rel_exp_app_cong : mctt.

(** ** β

    The type is [B[Id,,N]] again, so [rel_typ_of_instance] settles it, and what it
    also reports ([N]'s four values, their PER, and the codomain at an arbitrary
    related pair) is what the term side needs.  No type judgment is instantiated
    here.

    The four values of the term are [⟦M[q σ]⟧(ρ ↦ n1)], [⟦M⟧(ρσ ↦ n2)],
    [⟦M[Id,,N]⟧ρ'σ'] and [⟦M[Id,,N][σ']⟧ρ'].  The first holds because
    [((λ A M) N)[σ]] is [(λ A[σ] M[q σ]) (N[σ])] and applying a closure evaluates
    its body in the extended environment ([eval_app_fn]).  So the redex adds no
    evaluation of its own: the first link is the first obligation of
    [rel_exp_under_ctx_q] at the argument pair [n1 ≈ n2].

    The other two values need the same two instantiations of [M]'s judgment that
    the type needed of [B]'s (along [σ ,, N[σ]] for the outer one, along [Id ,, N]
    at the substituted environments for the inner one) and the same bridge, which
    here is [M] at the crossing pair of arguments.  Three merges then select the
    goal's four values, all in the canonical head PER. *)
Lemma rel_exp_pi_beta : forall {Γ A} {i : nat} {B M N},
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ▹ A ⊨ M ≈ M : B ->
    Γ ⊨ N ≈ N : A ->
    Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id ,, N].
Proof.
  intros * HA HB HM HN.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN) as HidN.
  rewrite exp_sub_id in HidN.
  pose proof HM as [? [? [k HMgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance HA HB HN _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [j [RN [a1 [a2 [a3 [a4 [n1 [n2 [n3 [n4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hn1 [Hn2 [Hn3 [Hn4 [Hnchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3)).
  split; [ exact Htyp |].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** The argument pairs the links are read at. *)
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn13 : Dom n1 ≈ n3 ∈ RN) by pairwise.
  assert (Hn14 : Dom n1 ≈ n4 ∈ RN) by pairwise.
  assert (Hn22 : Dom n2 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn24 : Dom n2 ≈ n4 ∈ RN) by pairwise.
  (** *** The Redex

      [rel_exp_under_ctx_q] at the argument pair [n1 ≈ n2]. *)
  pose proof (per_env_extend_sub_intro HΓ' Hσj HA _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hn12)
    as Hpair.
  destruct (rel_exp_under_ctx_q HΓ' Hσj HA HM _ _ _ _ _ _ Hpair Hev Hev')
    as [[v1 [v2 [Hv1 [Hv2 Hv]]]] _].
  assert (Hlink1 : Dom v1 ≈ v2 ∈ per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
    by (apply (per_head_of_args Hcod n1 n2 n2 n3 Hn12 Hn23 Hn22); exact Hv).
  apply rel_chain_of_pair in Hlink1.
  (** *** The Outer Instantiation

      Along [σ ,, N[σ] ≈ σ' ,, N[σ']], whose right-hand outer value is the goal's
      fourth once [exp_sub_extend_sub] has rewritten it. *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN) _ _ _ _ Hρ
                  (eval_sub_extend _ _ _ _ _ Hev Hn1)
                  (eval_sub_extend _ _ _ _ _ Hev' Hn4))
    as [RA [HAtyp HAexp]].
  destruct HAtyp as [cA1 cA2 cA3 cA4 HcA1 HcA2 HcA3 HcA4 HcAchain].
  destruct HAexp as [h1 h2 h3 h4 Hh1 Hh2 Hh3 Hh4 Hhchain].
  rewrite <- exp_sub_extend_sub in Hh4.
  destruct (per_head_anchor Hcod n1 n4 n2 n3 Hn14 Hn23 Hn24)
    as [e1 [e2 [He1 [He2 HanchorA]]]].
  assert (e1 = cA2) as -> by (eapply functional_eval_exp; [ exact He1 | exact HcA2 ]).
  assert (e2 = cA3) as -> by (eapply functional_eval_exp; [ exact He2 | exact HcA3 ]).
  retype_rel_chain HcAchain HanchorA Hhchain.
  (** *** The Inner Instantiation

      Along [Id ,, N ≈ Id ,, N] at the substituted environments: its second value
      is the goal's second and its right-hand outer value the goal's third. *)
  destruct (HMgen _ _ HΓ _ _ HidN _ _ _ _ Hρσ
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn2)
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn3))
    as [RB [HBtyp HBexp]].
  destruct HBtyp as [cB1 cB2 cB3 cB4 HcB1 HcB2 HcB3 HcB4 HcBchain].
  destruct HBexp as [g1 g2 g3 g4 Hg1 Hg2 Hg3 Hg4 Hgchain].
  destruct (per_head_anchor Hcod n2 n3 n2 n3 Hn23 Hn23 Hn23)
    as [f1 [f2 [Hf1 [Hf2 HanchorB]]]].
  assert (f1 = cB2) as -> by (eapply functional_eval_exp; [ exact Hf1 | exact HcB2 ]).
  assert (f2 = cB3) as -> by (eapply functional_eval_exp; [ exact Hf2 | exact HcB3 ]).
  retype_rel_chain HcBchain HanchorB Hgchain.
  (** The goal's second value is produced by this instantiation and by the redex
      alike. *)
  assert (v2 = g2) as -> by (eapply functional_eval_exp; [ exact Hv2 | exact Hg2 ]).
  (** *** The Bridge

      [M] at the pair of arguments that crosses from the one instantiation to the
      other. *)
  destruct (rel_exp_under_ctx_extend_simple HΓ HA HM _ _
              (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hn13)))
    as [b1 [b2 [Hb1 [Hb2 Hb]]]].
  assert (b1 = h2) as -> by (eapply functional_eval_exp; [ exact Hb1 | exact Hh2 ]).
  assert (b2 = g3) as -> by (eapply functional_eval_exp; [ exact Hb2 | exact Hg3 ]).
  assert (Hbridge : Dom h2 ≈ g3 ∈ per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
    by (apply (per_head_of_args Hcod n1 n3 n2 n3 Hn13 Hn23 Hn23); exact Hb).
  apply rel_chain_of_pair in Hbridge.
  (** *** The Four Values *)
  assert (Hmerge1 : rel_chain (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
                      ([h4; g3]))
    by (merge_rel_chain Hhchain Hbridge h2).
  assert (Hmerge2 : rel_chain (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
                      ([g2; g4; h4]))
    by (merge_rel_chain Hmerge1 Hgchain g3).
  apply (mk_rel_exp v1 g2 g4 h4);
    [ eapply eval_exp_app;
      [ apply eval_exp_fn | exact Hn1 | apply eval_app_fn; exact Hv1 ]
    | eapply eval_exp_app;
      [ apply eval_exp_fn | exact Hn2 | apply eval_app_fn; exact Hg2 ]
    | exact Hg4
    | exact Hh4
    |].
  merge_rel_chain Hlink1 Hmerge2 g2.
Qed.

Hint Resolve rel_exp_pi_beta : mctt.

(** ** η

    The only rule whose statement mentions a weakening rather than a substitution.
    [M[↑]ʷ] is a term in its own right, and [⟦M[↑]ʷ⟧(ρ ↦ c)] is not [⟦M⟧ρ]: in the
    λ case they are the different closures [λ (ρ ↦ c) (N[wk_q ↑]ʷ)] and [λ ρ N].
    So the weakening is crossed semantically, by instantiating [M]'s judgment along
    [Wk] with [rel_exp_under_ctx_shift_at].

    The type is [rel_typ_of_pi] unchanged.  The four values of the term are
    [⟦M[σ]⟧ρ], [⟦M⟧ρσ], [λ ρ'σ' (M[↑]ʷ #0)] and [λ ρ' ((M[↑]ʷ #0)[q σ'])], the last
    two by [eval_exp_fn].  Of the three links:

    - the first is [M]'s own left commutation;
    - the second is η proper: [M] and the closure of its weakened body agree on
      every argument.  This is [rel_exp_under_ctx_shift_at] at the substituted
      environments, read at the argument pair; applying the closure evaluates
      [M[↑]ʷ #0] in [ρ'σ' ↦ c'], by [eval_app_fn] and then [eval_exp_app];
    - the third is the right commutation of the closure, the third obligation of
      [rel_exp_under_ctx_q] for the weakened judgment
      [Γ ▹ A ⊨ M[↑]ʷ ≈ M[↑]ʷ : (Π A B)[↑]ʷ].  Its right value is
      [⟦M[↑]ʷ[q σ']⟧(ρ' ↦ c')], the closure body's, and the outer pair of the
      same weakening instance identifies its [per_head] of [(Π A B)[↑]ʷ] with
      [per_pi].

    So both nontrivial links come from one application of
    [rel_exp_under_ctx_shift_at]: the second from its chain, the third from its
    type PER. *)
Lemma rel_exp_fn_eta : forall {Γ A} {i : nat} {B M},
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ M ≈ M : Π A B ->
    Γ ⊨ M ≈ λ A M[↑]ʷ $ #0 : Π A B.
Proof.
  intros * HA HB HM.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  pose proof (rel_exp_under_ctx_shift HΓA HM) as HMwk.
  pose proof HM as [? [? [k HMgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HA HB _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  exists (per_pi in_rel B ρσ B ρ'σ').
  split; [ exact Htyp |].
  (** [pairwise] needs [per_pi in_rel B ρσ B ρ'σ'] to be a PER.  It is one
    because it is an element PER: the middle link of the type chain just
    obtained. *)
  destruct Htyp as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  assert (Hanchor : DF d2 ≈ d3 ∈ per_univ_elem i ↘ (per_pi in_rel B ρσ B ρ'σ'))
    by pairwise.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** [M]'s own chain, brought to the canonical [per_pi]. *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RM [HMtyp HMexp]].
  destruct HMtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (c2 = Πᵈ a2 ρσ B) as ->
    by (eapply functional_eval_exp; [ exact Hc2 | apply eval_exp_pi; exact Ha2 ]).
  assert (c3 = Πᵈ a3 ρ'σ' B) as ->
    by (eapply functional_eval_exp; [ exact Hc3 | apply eval_exp_pi; exact Ha3 ]).
  assert (HRMmid : DF Πᵈ a2 ρσ B ≈ Πᵈ a3 ρ'σ' B ∈ per_univ_elem k ↘ RM) by pairwise.
  rewrite (per_pi_iff Hmid HRMmid) in Hmchain.
  apply (mk_rel_exp m1 m2 λᵈ ρ'σ' (M[↑]ʷ $ #0) λᵈ ρ' (M[↑]ʷ $ #0)[q σ']);
    [ exact Hm1 | exact Hm2 | apply eval_exp_fn | apply eval_exp_fn |].
  (** The first link is [M]'s; the other two are read at an argument pair, both
    from the same instance of [M]'s judgment along [Wk] at the substituted
    environments extended by that pair. *)
  apply rel_chain_4;
    [ pairwise | |];
    hnf; intros c c' Hc;
    pose proof (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hc)) as Hpair;
    destruct (rel_exp_under_ctx_shift_at HΓ HA HM _ _ _ _ Hpair)
      as [j [R [b1 [b2 [b3 [b4 [w1 [w2 [w3 [w4 [Hb1 [Hb2 [Hb3 [Hb4 [Hbouter
         [Hbmid [Hw1 [Hw2 [Hw3 [Hw4 Hwchain]]]]]]]]]]]]]]]]]]]];
    assert (b2 = Πᵈ a2 ρσ B) as ->
      by (eapply functional_eval_exp; [ exact Hb2 | apply eval_exp_pi; exact Ha2 ]);
    assert (b3 = Πᵈ a3 ρ'σ' B) as ->
      by (eapply functional_eval_exp; [ exact Hb3 | apply eval_exp_pi; exact Ha3 ]);
    assert (HRpi : R <~> per_pi in_rel B ρσ B ρ'σ')
      by (eapply per_pi_iff; [ exact Hmid | exact Hbmid ]).
  - (** η itself: the instance's inner value on the left is [⟦M⟧ρσ], the goal's
      second, and its outer value on the right is [⟦M[↑]ʷ⟧(ρ'σ' ↦ c')], the head
      the closure applies. *)
    assert (w2 = m2) as ->
      by (eapply functional_eval_exp; [ exact Hw2 | exact Hm2 ]).
    rewrite HRpi in Hwchain.
    assert (Hlink : Dom m2 ≈ w4 ∈ per_pi in_rel B ρσ B ρ'σ') by pairwise.
    destruct (Hlink _ _ Hc) as [r r' Hr Hr' Hrr'].
    econstructor;
      [ exact Hr
      | apply eval_app_fn; eapply eval_exp_app;
        [ exact Hw4 | apply eval_exp_var | exact Hr' ]
      | exact Hrr' ].
  - (** The closure's right commutation, from the weakened judgment along [q σ'].
      The outer type pair of the weakening instance identifies the [per_head] of
      [(Π A B)[↑]ʷ] it lands in with [per_pi]. *)
    pose proof (per_env_extend_sub_intro HΓ' Hσj HA _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc)
      as Hpair'.
    destruct (rel_exp_under_ctx_q HΓ' Hσj HA HMwk _ _ _ _ _ _ Hpair' Hev Hev')
      as [_ [_ [u [v [Hu [Hv Huv]]]]]].
    assert (HuvR : Dom u ≈ v ∈ R)
      by (eapply Huv; [ exact Hb1 | exact Hb4 | exact Hbouter ]).
    apply HRpi in HuvR.
    destruct (HuvR _ _ Hc) as [r r' Hr Hr' Hrr'].
    (** [(M[↑]ʷ #0)[q σ']] is [(M[↑]ʷ[q σ']) #0], since [(#0)[q σ']] is [#0] by
      [sb_q_zero], so the head is the value [rel_exp_under_ctx_q] reports. *)
    econstructor;
      [ apply eval_app_fn; eapply eval_exp_app;
        [ exact Hu | apply eval_exp_var | exact Hr ]
      | apply eval_app_fn; eapply eval_exp_app;
        [ exact Hv | apply eval_exp_var | exact Hr' ]
      | exact Hrr' ].
Qed.

Hint Resolve rel_exp_fn_eta : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve rel_exp_pi_cong : mctt.
#[export]
Hint Resolve rel_exp_fn_cong : mctt.
#[export]
Hint Resolve rel_exp_app_cong : mctt.
#[export]
Hint Resolve rel_exp_pi_beta : mctt.
#[export]
Hint Resolve rel_exp_fn_eta : mctt.
