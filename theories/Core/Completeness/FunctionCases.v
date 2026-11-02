(** * Fundamental Theorem: Π-Types and Universal Propositions

    Substitution pushes through [Π], [λ] and application by computation of
    [exp_sub]: [(a_pi r A B)[σ]] is [a_pi r (A[σ]) (B[q σ])].  So only the
    congruence, β and η rules are validated here.

    A [Π] carries a relevance tag.  At [relevant] it is a type of functions
    in a universe: its domain is a type of that universe or a proposition
    (a function of a proof), and its codomain is a type of the universe.  At
    [propositional] it is the impredicative [∀]: its domain is a type of
    either sort and its codomain a family of propositions, and it is itself
    a proposition.

    The relevant case is organised around [rel_typ_of_pi]: the type judgment
    of a Π, at the canonical element PER [per_pi].  The rules whose type is a
    Π read their four values off it; application and β, whose type is the
    instantiated codomain, read it off [rel_typ_of_instance] at a relevant
    domain and off [rel_typ_of_instance_prop] at a propositional one, whose
    argument is the proof [⋆ᵈ].

    The propositional case is proof irrelevance: the [∀] is a proposition
    ([rel_exp_under_ctx_all]), so every term of it, and every application of
    one, is a proof, related to every other ([rel_exp_under_ctx_proof]).

    Cumulativity is needed for the level: [per_univ_elem_pi_chain] requires
    the domain and codomain of a Π-value to be related at one index, while
    the syntax types [A] and [B] at unrelated ones.  So the domain's
    judgment is lifted to the codomain's index ([rel_type_of_sort_ge]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import ContextCases LevelCases LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases VariableCases PropCases LetCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Domains of Either Sort

    A type of either sort is a type of every index from some index on: a
    type of a universe by cumulativity, a proposition at every index. *)
Lemma rel_type_of_sort_ge : forall {Γ A A' Srt},
    type_sort Srt ->
    Γ ⊨ A ≈ A' : Srt ->
    exists i, forall j, i <= j -> Γ ⊨ᵗ A ≈ A' at j.
Proof.
  intros * [i |] H.
  - exists i; intros j Hj; exact (rel_type_of_typ (rel_exp_cumu_ge Hj H)).
  - exists 0; intros j _; exact (rel_type_of_prop j H).
Qed.

(** The codomain of a Π along a lifted substitution is a relevant type, at
    the left environment: its four values are relevant types of a
    universe. *)
Lemma rel_typ_sort_of_univ_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B' u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ▹ A ⊨ B ≈ B' : universe_index_term u ->
    forall ρ ρ' ρσ ρ'σ' c c',
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      rel_typ_sort B[q σ] (ρ ↦ c) relevant.
Proof.
  intros * HΓ Hσj HA HB * Hpair Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_univ_inversion HB) as [env_relΔA [HΔA HBgen]].
  destruct (rel_sub_under_ctx_q_at HΓ HΔA Hσj HA _ _ _ _ _ _ Hpair Hev Hev')
    as [s [s' [Hq [Hq' _]]]].
  destruct (HBgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq')
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 [[_ Hr _] _]].
  exists b1; split; assumption.
Qed.

(** ** The Type Judgment of a Π

    A stage of a semantic judgment, that is, a related pair of environments
    and a related pair of substitutions out of it, determines four Π-values
    and the canonical element PER they carry.  Both are forced: [(Π A B)[σ]]
    is [Π (A[σ]) (B[q σ])] definitionally, so [eval_exp_pi] applies to the
    substituted head directly, and the [per_pi] is the one
    [per_univ_elem_pi_chain] produces.

    The domain is of either sort, at the codomain's index, and its four
    values are reported with both pairs a caller may need: the outer pair,
    at which [per_env_extend_sub_intro] and every irrelevance step along
    [q σ] are stated, and the inner pair, at which [per_pi_iff] must be
    applied, since the middle link of the type chain is
    [Π a2 ρσ B ≈ Π a3 ρ'σ' B']. *)
Lemma rel_typ_of_pi : forall {Γ A A'} {i : nat} {B B'},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ᵗ A ≈ A' at i ->
    Γ ▹ A ⊨ B ≈ B' : Typeω@i ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        exists in_rel a1 a2 a3 a4,
          ⟦ A[σ] ⟧ ρ ↘ a1 /\
          ⟦ A ⟧ ρσ ↘ a2 /\
          ⟦ A' ⟧ ρ'σ' ↘ a3 /\
          ⟦ A'[σ'] ⟧ ρ' ↘ a4 /\
          DF a1 ≈ a4 ∈ per_univ_elem i ↘ in_rel /\
          DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel /\
          Definitions.rel_typ i (Π A B) σ ρ ρσ (Π A' B') σ' ρ' ρ'σ'
            (per_pi a2 a3 in_rel B ρσ B' ρ'σ').
Proof.
  intros * HAself HA HB * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ HAgen]].
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
      [B] at an argument pair drawn from the domain PER, and the codomain is
      relevant. *)
  eapply per_univ_elem_pi_chain; [ exact Hachain | | | |];
    intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc) as Hpair;
    [ destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HAself HB _ _ _ _ _ _ Hpair Hev Hev')
        as [O1 [O2 O3]]; eassumption .. |].
  exact (rel_typ_sort_of_univ_under_ctx_q (u := ul i) HΓ' Hσj HAself HB _ _ _ _ _ _ Hpair Hev Hev').
Qed.

(** A chain of Π-values in [per_univ i] is one of relevant types of the
    universe at [i]. *)
Lemma rel_chain_pi_relevant : forall {i R a1 a2 a3 a4 ρ1 ρ2 ρ3 ρ4 B1 B2 B3 B4},
    rel_chain (per_univ_elem i R) ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2; Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]) ->
    rel_chain (per_relevant_nonlevel (per_univ i)) ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2; Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]).
Proof.
  intros * (H12 & H23 & H34).
  apply rel_chain_4; (constructor; [ eexists; eassumption | reflexivity | reflexivity ]).
Qed.

(** ** Π-Congruence in a Large Universe *)

Lemma rel_exp_under_ctx_pi_cong : forall {Γ A A'} {i : nat} {B B'},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ᵗ A ≈ A' at i ->
    Γ ▹ A ⊨ B ≈ B' : Typeω@i ->
    Γ ⊨ Π A B ≈ Π A' B' : Typeω@i.
Proof.
  intros * HAself HA HB.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ _]].
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HAself HA HB _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  destruct Htyp as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  inversion Hd1; inversion Hd2; inversion Hd3; inversion Hd4; subst.
  apply (mk_rel_exp _ _ _ _ Hd1 Hd2 Hd3 Hd4).
  exact (rel_chain_pi_relevant Hdchain).
Qed.

Hint Resolve rel_exp_under_ctx_pi_cong : mctt.

(** ** The Small [Π] at a Level Term

    The codomain is at the weakened level [L[↑]ʷ], whose value at an extended
    environment has the realiser of [L]'s at the tail: the two are related
    levels, through [L]'s judgment along [Wk]
    ([rel_exp_under_ctx_shift_at]). *)
Lemma suniv_real_shift : forall {Δ A L} {i n : nat} {env_relΔA},
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ⊨ L : Level@n ->
    EF Δ ▹ A ≈ Δ ▹ A ∈ per_ctx_env ↘ env_relΔA ->
    forall e x e' x' t1 t2,
      Dom e ↦ x ≈ e' ↦ x' ∈ env_relΔA ->
      ⟦ L[↑]ʷ ⟧ e ↦ x ↘ t1 ->
      ⟦ L ⟧ e' ↘ t2 ->
      domain_level_real t1 = domain_level_real t2.
Proof.
  intros * HA HL HΔA * Hee Ht1 Ht2.
  pose proof (rel_exp_of_level_inversion HL) as [env_relΔ [HΔ _]].
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA'.
  handle_per_ctx_env_irrel.
  assert (Hlr : forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔ -> rel_typ_sort Level@n ρ relevant)
    by (intros; eexists; split; [ apply eval_exp_level | reflexivity ]).
  destruct (rel_exp_under_ctx_shift_at HΔ HA HL Hlr _ _ _ _ Hee)
    as (j & R & b1 & b2 & b3 & b4 & w1 & w2 & w3 & w4 & Hb1 & Hb2 & Hb3 & Hb4 & HR1 & HR2 & Hw1 & Hw2 & Hw3 & Hw4 & Hwc).
  cbn [exp_wk] in Hb1, Hb4.
  simplify_evals.
  match goal with H : per_univ_elem _ _ (Levelᵈ@_) (Levelᵈ@_) |- _ => invert_per_univ_elem H end.
  apply_relation_equivalence.
  assert (Hw : per_lvl t1 t2) by lvl_pw.
  exact (per_lvl_real _ _ Hw).
Qed.

(** [rel_exp_of_univ_under_ctx_q] for a codomain in the small universe at
    the weakened level: the five instantiations have the realisers of [L[↑]ʷ]
    at extended environments related to [ρσ ↦ c], which are [L]'s at
    [ρσ] ([suniv_real_shift]), so all five chains are in one small universe.
    The left value is a relevant type. *)
Lemma rel_exp_of_suniv_under_ctx_q : forall {Γ Δ σ σ' A} {i n : nat} {B B' L env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ⊨ L : Level@n ->
    Δ ▹ A ⊨ B ≈ B' : Type⟨L[↑]ʷ⟩ ->
    forall ρ ρ' ρσ ρ'σ' c c' t,
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      ⟦ L ⟧ ρσ ↘ t ->
      rel_typ_sort B[q σ] (ρ ↦ c) relevant /\
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ (us (domain_level_real t))) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ (us (domain_level_real t))) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ (us (domain_level_real t))).
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
  assert (Hrel : rel_typ_sort B[q σ] (ρ ↦ c) relevant)
    by (exists b1; split; [ exact Hb1 | destruct Hbchain as [[_ Hr _] _]; exact Hr ]).
  eapply rel_chain_mono in Hbchain; [| intros ? ? Hx; exact (per_relevant_nonlevel_univ_rel Hx) ].
  assert (P1 : Dom s ↦ c ≈ ρσ ↦ c' ∈ env_relΔA) by pairwise.
  assert (P2 : Dom ρσ ↦ c ≈ s ↦ c ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ≈ ρ'σ' ↦ c' ∈ env_relΔA) by pairwise.
  assert (P4 : Dom ρ'σ' ↦ c ≈ s' ↦ c' ∈ env_relΔA) by pairwise.
  destruct (HBl _ _ P1) as [x1 [x2 [t1 [Hx1 [Hx2 [Ht1 Hx]]]]]].
  destruct (HBl _ _ P2) as [y1 [y2 [t2 [Hy1 [Hy2 [Ht2 Hy]]]]]].
  destruct (HBr _ _ P3) as [z1 [z2 [t3 [Hz1 [Hz2 [Ht3 Hz]]]]]].
  destruct (HBr _ _ P4) as [u1 [u2 [t4 [Hu1 [Hu2 [Ht4 Hu]]]]]].
  (** All five realisers are [L]'s at [ρσ]. *)
  assert (R0 : domain_level_real t0 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s c ρσ c); [ pairwise | exact Ht0 | exact Ht ]).
  assert (R1 : domain_level_real t1 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s c ρσ c); [ pairwise | exact Ht1 | exact Ht ]).
  assert (R2 : domain_level_real t2 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 ρσ c ρσ c); [ pairwise | exact Ht2 | exact Ht ]).
  assert (R3 : domain_level_real t3 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s' c' ρσ c); [ pairwise | exact Ht3 | exact Ht ]).
  assert (R4 : domain_level_real t4 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 ρ'σ' c ρσ c); [ pairwise | exact Ht4 | exact Ht ]).
  rewrite R0 in Hbchain; rewrite R1 in Hx; rewrite R2 in Hy; rewrite R3 in Hz; rewrite R4 in Hu.
  assert (x1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (y2 = b2) by (eapply functional_eval_exp; eassumption).
  assert (z1 = b3) by (eapply functional_eval_exp; eassumption).
  assert (u2 = b3) by (eapply functional_eval_exp; eassumption).
  subst.
  apply rel_chain_of_pair in Hx, Hy, Hz, Hu.
  set (j := us (domain_level_real t)) in *.
  assert (M1 : rel_chain (per_univ j) ([b1; b2; b3; b4; x2]))
    by (merge_rel_chain Hbchain Hx b2).
  assert (M2 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2]))
    by (merge_rel_chain M1 Hy b2).
  assert (M3 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M2 Hz b3).
  assert (M4 : rel_chain (per_univ j) ([u1; y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M3 Hu b3).
  split; [ exact Hrel |].
  repeat split.
  - exists b1, x2; repeat split; try eassumption.
    pairwise.
  - exists y1, z2; repeat split; try eassumption.
    pairwise.
  - exists u1, b4; repeat split; try eassumption.
    pairwise.
Qed.

(** The four values of a domain of the small [Π] at a level, at the
    realiser of the level's inner value: a type of the small universe there,
    or a proposition. *)
Lemma rel_domain_suniv_at : forall {Γ L A A' Srt},
    pi_domain_sort Type⟨L⟩ Srt ->
    Γ ⊨ A ≈ A' : Srt ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ' t,
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        ⟦ L ⟧ ρσ ↘ t ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ (us (domain_level_real t))).
Proof.
  intros * [] HA.
  - pose proof (rel_exp_of_suniv_tm_inversion HA) as [env_relΓ [HΓ HAgen]].
    eexists; eexists; [ eassumption |].
    intros * HΓ' * Hσj * Hρ Hev Hev' Ht.
    destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [t' [Ht' [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hc]]].
    assert (t' = t) as -> by (eapply functional_eval_exp; eassumption).
    econstructor; try eassumption.
    eapply rel_chain_mono; [| exact Hc ]; intros ? ? Hx; exact (per_relevant_nonlevel_univ_rel Hx).
  - pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ [HΓ HAgen]].
    eexists; eexists; [ eassumption |].
    intros * HΓ' * Hσj * Hρ Hev Hev' Ht.
    destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hc].
    econstructor; try eassumption.
    eapply rel_chain_mono; [| exact Hc ]; intros ? ? Hp; eexists; exact (per_univ_elem_of_prop _ _ _ Hp).
Qed.

(** A domain of the small [Π] at a level is a type of index [0]. *)
Lemma rel_type_of_domain_suniv : forall {Γ L A A' Srt},
    pi_domain_sort Type⟨L⟩ Srt ->
    Γ ⊨ A ≈ A' : Srt ->
    Γ ⊨ᵗ A ≈ A' at 0.
Proof.
  intros * [] HA; [ exact (rel_type_of_typ (rel_exp_suniv_tm_large (i := 0) HA)) | exact (rel_type_of_prop 0 HA) ].
Qed.

(** The small [Π] at a level term: at each pair of environments it is the
    small [Π] at the realiser of the level's value, whose codomain
    obligations [rel_exp_of_suniv_under_ctx_q] discharges. *)
Lemma rel_exp_under_ctx_pi_cong_small : forall {Γ L A A' B B' Srt} {n : nat},
    pi_domain_sort Type⟨L⟩ Srt ->
    Γ ⊨ L : Level@n ->
    Γ ⊨ A : Srt ->
    Γ ⊨ A ≈ A' : Srt ->
    Γ ▹ A ⊨ B ≈ B' : Type⟨L[↑]ʷ⟩ ->
    Γ ⊨ Π A B ≈ Π A' B' : Type⟨L⟩.
Proof.
  intros * HS HL HA0 HA HB.
  pose proof (rel_type_of_domain_suniv HS HA0) as HAself.
  pose proof (rel_domain_suniv_at HS HA) as [env_relΓ [HΓ HAgen]].
  apply (rel_exp_of_suniv_tm (n := n)); [ exact HL |].
  eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev' t Ht.
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ _ Hρ Hev Hev' Ht)
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  functionalize_per_univ_chain Hachain in_rel.
  apply (mk_rel_exp Πᵈ a1 ρ B[q σ] Πᵈ a2 ρσ B
                    Πᵈ a3 ρ'σ' B' Πᵈ a4 ρ' B'[q σ']);
    [ apply eval_exp_pi; exact Ha1 | apply eval_exp_pi; exact Ha2
    | apply eval_exp_pi; exact Ha3 | apply eval_exp_pi; exact Ha4 |].
  apply (rel_chain_pi_relevant (i := us (domain_level_real t)) (R := per_pi a2 a3 in_rel B ρσ B' ρ'σ')).
  eapply per_univ_elem_pi_chain; [ exact Hachain | | | |];
    intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc) as Hpair;
    destruct (rel_exp_of_suniv_under_ctx_q HΓ' Hσj HAself HL HB _ _ _ _ _ _ t Hpair Hev Hev' Ht)
      as [Or [O1 [O2 O3]]];
    eassumption.
Qed.

Hint Resolve rel_exp_under_ctx_pi_cong_small : mctt.

(** ** The Universal Proposition

    A [∀] is a proposition by its head, and two [∀]s read back equally
    when their domains do and their bodies do under the fresh variable of
    the domain, which is related to itself at the domain's element PER
    (realisability).  The bodies are propositions, related at [per_prop]
    at every related pair of arguments. *)
Lemma per_prop_all : forall {k R a a' ρ ρ' B B'},
    DF a ≈ a' ∈ per_univ_elem k ↘ R ->
    (forall c c', Dom c ≈ c' ∈ R ->
        exists b b', ⟦ B ⟧ ρ ↦ c ↘ b /\ ⟦ B' ⟧ ρ' ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_prop) ->
    Dom ∀ₚᵈ a ρ B ≈ ∀ₚᵈ a' ρ' B' ∈ per_prop.
Proof.
  intros * Ha HB.
  constructor; [ reflexivity | reflexivity |].
  intros s.
  destruct (per_univ_then_per_top_typ Ha s) as [A [HA HA']].
  pose proof (per_bot_then_per_elem Ha (var_per_bot (n := s))) as Hvar.
  destruct (HB _ _ Hvar) as [b [b' [Hb [Hb' [_ _ Hbb]]]]].
  destruct (Hbb (S s)) as [P [HP HP']].
  exists (∀ₚⁿ A P); split; eapply read_typ_all; eassumption.
Qed.

Lemma rel_exp_under_ctx_all : forall {Γ A A'} {i : nat} {B B'},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ᵗ A ≈ A' at i ->
    Γ ▹ A ⊨ B ≈ B' : Propₘ ->
    Γ ⊨ ∀ₚ A B ≈ ∀ₚ A' B' : Propₘ.
Proof.
  intros * HAself HA HB.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ HAgen]].
  apply rel_exp_of_prop; eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  functionalize_per_univ_chain Hachain in_rel.
  assert (Ha14 : DF a1 ≈ a4 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  (** The bodies at every related pair of arguments, along the three links. *)
  assert (Hq : forall c c', Dom c ≈ c' ∈ in_rel ->
             (exists b b', ⟦ B[q σ] ⟧ ρ ↦ c ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_prop) /\
             (exists b b', ⟦ B ⟧ ρσ ↦ c ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_prop) /\
             (exists b b', ⟦ B' ⟧ ρ'σ' ↦ c ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_prop)).
  { intros c c' Hc.
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1 Ha14 Hc) as Hpair.
    exact (rel_exp_of_prop_under_ctx_q HΓ' Hσj HAself HB _ _ _ _ _ _ Hpair Hev Hev'). }
  destruct Hachain as (H12 & H23 & H34).
  apply (mk_rel_exp ∀ₚᵈ a1 ρ B[q σ] ∀ₚᵈ a2 ρσ B ∀ₚᵈ a3 ρ'σ' B' ∀ₚᵈ a4 ρ' B'[q σ']);
    [ apply eval_exp_pi; exact Ha1 | apply eval_exp_pi; exact Ha2
    | apply eval_exp_pi; exact Ha3 | apply eval_exp_pi; exact Ha4 |].
  apply rel_chain_4.
  - eapply per_prop_all; [ exact H12 |]; intros c c' Hc; exact (proj1 (Hq _ _ Hc)).
  - eapply per_prop_all; [ exact H23 |]; intros c c' Hc; exact (proj1 (proj2 (Hq _ _ Hc))).
  - eapply per_prop_all; [ exact H34 |]; intros c c' Hc; exact (proj2 (proj2 (Hq _ _ Hc))).
Qed.

Hint Resolve rel_exp_under_ctx_all : mctt.

End Fixed_GCtx.

(** A [Π] of the sort [r] in a universe [U]: at [relevant] a type of [U],
    large or small at a level term, over a domain of [U] or a proposition;
    at [propositional] the [∀], a proposition. *)
Lemma sem_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     pi_domain_sort U Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B ≈ B' : (relevance_sort r U)[↑]ʷ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_pi r A B ≈ a_pi r A' B' : relevance_sort r U ).
Proof.
  intros * HU HA0 HS HA HB; sem_intro; [ assumption |].
  destruct r; cbn [relevance_sort exp_wk] in *.
  - destruct HU as [[? ->] | (? & ? & -> & ?)]; cbn [exp_wk] in *.
    + destruct HS.
      * eapply rel_exp_under_ctx_pi_cong; [ apply rel_type_of_typ; exact HA0 | apply rel_type_of_typ; exact HA | exact HB ].
      * eapply rel_exp_under_ctx_pi_cong; [ apply rel_type_of_prop; exact HA0 | apply rel_type_of_prop; exact HA | exact HB ].
    + eapply rel_exp_under_ctx_pi_cong_small; eassumption.
  - destruct HU as [[? ->] | (? & ? & -> & ?)].
    + assert (HSrt : type_sort Srt) by (destruct HS; [ apply type_sort_universe | apply type_sort_prop ]).
      destruct (rel_type_of_sort_ge HSrt HA0) as [k0 Hk0].
      destruct (rel_type_of_sort_ge HSrt HA) as [k1 Hk1].
      eapply rel_exp_under_ctx_all; [ apply (Hk0 (Nat.max k0 k1)); lia | apply (Hk1 (Nat.max k0 k1)); lia | exact HB ].
    + eapply rel_exp_under_ctx_all;
        [ exact (rel_type_of_domain_suniv HS HA0) | exact (rel_type_of_domain_suniv HS HA) | exact HB ].
Qed.

Lemma sem_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     pi_domain_sort U Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : (relevance_sort r U)[↑]ʷ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_pi r A B : relevance_sort r U ).
Proof. intros * HU HA HS HB; eapply sem_exp_eq_pi_cong; eassumption. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** λ-Congruence

    A λ evaluates to a closure over its domain's value with no other premise
    ([eval_exp_fn]), so all four values of the goal are known up front.
    Each link of the chain applies two closures, which take arguments of
    their domains' sorts, and [eval_app_fn] turns the application into
    evaluating the two bodies in the two extended environments.  These are
    the three obligations of [rel_exp_under_ctx_q], and they land in the
    [per_head] that [per_pi] asks for. *)
Lemma rel_exp_under_ctx_fn_cong : forall {Γ A A'} {i : nat} {B M M'},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ᵗ A ≈ A' at i ->
    Γ ▹ A ⊨ B : Typeω@i ->
    Γ ▹ A ⊨ M ≈ M' : B ->
    Γ ⊨ λ A M ≈ λ A' M' : Π A B.
Proof.
  intros * HAself HA HB HM.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ HAgen]].
  assert (HBrel : forall ρ ρ' R, EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R -> rel_typ_sort B ρ relevant)
    by (intros * HR Hρ; exact (rel_exp_of_typ_relevant_at HR HB _ _ Hρ)).
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HAself HAself HB _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  exists (per_pi a2 a3 in_rel B ρσ B ρ'σ').
  split; [ exact Htyp |]; right.
  (** The right closures keep the values of [A']; all four domains are of
      one sort. *)
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbc].
  functional_eval_rewrite_clear.
  destruct Hbc as ([R12 H12] & [R23 H23] & [R34 H34]).
  pose proof (per_univ_elem_relevance _ _ _ _ H12) as E12.
  pose proof (per_univ_elem_relevance _ _ _ _ H23) as E23.
  pose proof (per_univ_elem_relevance _ _ _ _ H34) as E34.
  pose proof (per_univ_elem_relevance _ _ _ _ Hmid) as E23'.
  apply (mk_rel_exp λᵈ a1 ρ M[q σ] λᵈ a2 ρσ M λᵈ b3 ρ'σ' M' λᵈ b4 ρ' M'[q σ']);
    [ apply eval_exp_fn; exact Ha1 | apply eval_exp_fn; exact Ha2 | apply eval_exp_fn; exact Hb3 | apply eval_exp_fn; exact Hb4 |].
  apply rel_chain_4; (constructor; [ cbn; congruence | cbn; congruence |]); intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc)
      as Hpair;
    destruct (rel_exp_under_ctx_q HΓ' Hσj HAself HM HBrel _ _ _ _ _ _ Hpair Hev Hev')
      as [[m1 [m2 [Hm1 [Hm2 Hm]]]]
            [[n1 [n2 [Hn1 [Hn2 Hn]]]] [p1 [p2 [Hp1 [Hp2 Hp]]]]]].
  - econstructor; [ apply eval_app_fn; exact Hm1 | apply eval_app_fn; exact Hm2 | exact Hm ].
  - econstructor; [ apply eval_app_fn; exact Hn1 | apply eval_app_fn; exact Hn2 | exact Hn ].
  - econstructor; [ apply eval_app_fn; exact Hp1 | apply eval_app_fn; exact Hp2 | exact Hp ].
Qed.

Hint Resolve rel_exp_under_ctx_fn_cong : mctt.

(** The domain and the codomain of a [Π] the rules of λ and of
    application name, at one index: the domain's from its sort, lifted, and
    the codomain's index, lifted, at a relevant [Π]; at a [∀] the [∀]
    itself, a proposition. *)
Lemma rel_pi_parts : forall {Γ A A' Srt B} {i : nat},
    type_sort Srt ->
    Γ ⊨ A : Srt ->
    Γ ⊨ A ≈ A' : Srt ->
    Γ ▹ A ⊨ B : Typeω@i ->
    exists k, Γ ⊨ᵗ A ≈ A at k /\ Γ ⊨ᵗ A ≈ A' at k /\ Γ ▹ A ⊨ B : Typeω@k.
Proof.
  intros * HS HA0 HA HB.
  destruct (rel_type_of_sort_ge HS HA0) as [k0 Hk0].
  destruct (rel_type_of_sort_ge HS HA) as [k1 Hk1].
  exists (Nat.max i (Nat.max k0 k1)); split; [| split ].
  - apply Hk0; lia.
  - apply Hk1; lia.
  - eapply rel_exp_cumu_ge; [| exact HB ]; lia.
Qed.

Lemma rel_all_of_parts : forall {Γ A A' Srt B B'},
    type_sort Srt ->
    Γ ⊨ A : Srt ->
    Γ ⊨ A ≈ A' : Srt ->
    Γ ▹ A ⊨ B ≈ B' : Propₘ ->
    Γ ⊨ ∀ₚ A B ≈ ∀ₚ A' B' : Propₘ.
Proof.
  intros * HS HA0 HA HB.
  destruct (rel_type_of_sort_ge HS HA0) as [k0 Hk0].
  destruct (rel_type_of_sort_ge HS HA) as [k1 Hk1].
  eapply rel_exp_under_ctx_all; [ apply (Hk0 (Nat.max k0 k1)); lia | apply (Hk1 (Nat.max k0 k1)); lia | exact HB ].
Qed.

End Fixed_GCtx.

(** A λ over a domain of either sort: a function into a type of a
    universe, or a proof of a [∀]. *)
Lemma sem_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ M ≈ M' : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ λ A M ≈ λ A' M' : a_pi r A B ).
Proof.
  intros * HA0 HS HA HB HM; sem_intro; [ assumption |].
  destruct r; cbn [relevance_sort] in *.
  - destruct (rel_pi_parts HS HA0 HA HB) as [k [Hl [Hr Hk]]].
    exact (rel_exp_under_ctx_fn_cong Hl Hr Hk HM).
  - exact (rel_exp_under_ctx_proof (rel_all_of_parts HS HA0 HA0 HB)).
Qed.

Lemma sem_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ λ A M : a_pi r A B ).
Proof. intros * HA HS HB HM; eapply sem_exp_eq_fn_cong; eassumption. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Application Congruence

    The type of this rule is an instantiated codomain rather than a Π.  At
    a relevant domain, everything the type [B[Id,,N]] costs is done once in
    [rel_typ_of_instance], which also serves β; what is left here is the
    term side.  The element PER is the head PER of [B] at the arguments the
    type names, [⟦N⟧ρσ] and [⟦N⟧ρ'σ'].  Each link of [M]'s chain arrives in
    the head PER of its own pair of arguments, and [per_head_of_args] moves
    it. *)
Lemma rel_exp_under_ctx_app_cong : forall {Γ A} {i : nat} {B M M' N N'},
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
  destruct HM as [? ? k HMgen].
  destruct HN as [? ? l HNgen].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance HA HB HNl _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l' [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ p2) (ρ'σ' ↦ p3)).
  split; [ exact Htyp |]; right.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** The domain is relevant. *)
  destruct (rel_exp_of_typ_relevant_at HΓ HA _ _ Hρσ) as (a2' & Ha2' & Er2).
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  (** *** The Argument

    The other instantiation of [N]'s judgment, for [N ≈ N'], identified with the
    reflexive one.  Both agree on the values of [A], so [retype_rel_chain] puts
    both chains in one PER, and they merge. *)
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN2 [HNtyp HNexp]].
  apply (rel_exp_or_prop_relevant HNtyp (ex_intro _ a2 (conj Ha2 Er2))) in HNexp.
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
  assert (HΠr : rel_typ_sort (Π A B) ρσ relevant)
    by (exists (Πᵈ a2 ρσ B); split; [ apply eval_exp_pi; exact Ha2 | reflexivity ]).
  apply (rel_exp_or_prop_relevant HMtyp HΠr) in HMexp.
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
  destruct Hmchain as (Hpi1 & Hpi2 & Hpi3).
  pose proof (per_univ_elem_relevance _ _ _ _ Hmid) as Er23.
  destruct (pi_elements_app _ _ _ _ _ _ Hpi1 _ _ Hn12) as [r1 r2 Hr1 Hr2 Hr].
  destruct (pi_elements_app _ _ _ _ _ _ Hpi2 _ _ Hn23) as [s1 s2 Hs1 Hs2 Hs].
  destruct (pi_elements_app _ _ _ _ _ _ Hpi3 _ _ Hn34) as [u1 u2 Hu1 Hu2 Hu].
  assert (Hs1e : s1 = r2) by (eapply functional_eval_app; [ exact Hs1 | exact Hr2 ]).
  assert (Hu1e : u1 = s2) by (eapply functional_eval_app; [ exact Hu1 | exact Hs2 ]).
  subst s1 u1.
  (** The functions take relevant arguments. *)
  assert (Ef1 : arg_relevance gc_deps gc_stack m1 = relevant) by (rewrite (pi_elements_left _ _ _ _ _ _ Hpi1); exact Er2).
  assert (Ef2 : arg_relevance gc_deps gc_stack m2 = relevant) by (rewrite (pi_elements_right _ _ _ _ _ _ Hpi1); congruence).
  assert (Ef3 : arg_relevance gc_deps gc_stack m3 = relevant) by (rewrite (pi_elements_right _ _ _ _ _ _ Hpi2); congruence).
  assert (Ef4 : arg_relevance gc_deps gc_stack m4 = relevant) by (rewrite (pi_elements_right _ _ _ _ _ _ Hpi3); congruence).
  apply (mk_rel_exp r1 r2 s2 u2);
    [ eapply eval_exp_app; [ exact Hm1 | exact Ef1 | exact Hn1 | exact Hr1 ]
    | eapply eval_exp_app; [ exact Hm2 | exact Ef2 | exact Hn2 | exact Hr2 ]
    | eapply eval_exp_app; [ exact Hm3 | exact Ef3 | exact Hn3 | exact Hs2 ]
    | eapply eval_exp_app; [ exact Hm4 | exact Ef4 | exact Hn4 | exact Hu2 ]
    |].
  apply rel_chain_4;
    [ apply (per_head_of_args Hcod n1 n2 n2 p3 Hn12 Hn2p3 Hn22); exact Hr
    | apply (per_head_of_args Hcod n2 n3 n2 p3 Hn23 Hn2p3 Hn23); exact Hs
    | apply (per_head_of_args Hcod n3 n4 n2 p3 Hn34 Hn2p3 Hn24); exact Hu ].
Qed.

Hint Resolve rel_exp_under_ctx_app_cong : mctt.

(** A head whose type's value in the tail is a proposition is a
    proposition. *)
Lemma head_propositional_of_value : forall {Γ A ρ a},
    ⟦ A ⟧ ρ ↘ a ->
    domain_relevance a = propositional ->
    head_propositional gc_deps gc_stack (ce_ass A) Γ ρ.
Proof. intros * Ha Hr; econstructor; [ reflexivity | intros y _; reflexivity | exact Ha | exact Hr ]. Qed.

(** ** The Type Judgment of an Instantiation at a Proposition

    [rel_typ_of_instance] for a domain that is a proposition: the argument
    is a proof, so every instantiating environment holds [⋆ᵈ] at the head
    ([eval_sub_extend_proof]), and the codomain is read at [⋆ᵈ].  The two
    instantiations of the codomain, along [σ ,, N[σ]] and along [Id ,, N]
    at the substituted environments, then share their inner values, and no
    bridge is needed. *)
Lemma rel_typ_of_instance_prop : forall {Γ A} {i : nat} {B N},
    Γ ⊨ A : Propₘ ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ N ≈ N : A ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        exists a1 a2 a3 a4,
          ⟦ A[σ] ⟧ ρ ↘ a1 /\
          ⟦ A ⟧ ρσ ↘ a2 /\
          ⟦ A ⟧ ρ'σ' ↘ a3 /\
          ⟦ A[σ'] ⟧ ρ' ↘ a4 /\
          rel_chain per_prop ([a1; a2; a3; a4]) /\
          (exists b b', ⟦ B ⟧ ρσ ↦ ⋆ᵈ ↘ b /\ ⟦ B ⟧ ρ'σ' ↦ ⋆ᵈ ↘ b' /\ Dom b ≈ b' ∈ per_univ i) /\
          Definitions.rel_typ i B[Id,,N] σ ρ ρσ B[Id,,N] σ' ρ' ρ'σ'
            (per_head B B (ρσ ↦ ⋆ᵈ) (ρ'σ' ↦ ⋆ᵈ)).
Proof.
  intros * HA HB HN * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ [HΓ HAgen]].
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓA [HΓA HBgen]].
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN) as HidN.
  rewrite exp_sub_id in HidN.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  pose proof Hachain as (_ & [Hr2 Hr3 _] & _).
  pose proof (head_propositional_of_value (Γ := Γ) Ha2 Hr2) as Hp2.
  pose proof (head_propositional_of_value (Γ := Γ) Ha3 Hr3) as Hp3.
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  (** The two instantiations, their outer values rewritten into the goal's
      spelling. *)
  destruct (HBgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN) _ _ _ _ Hρ
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev Hp2)
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev' Hp3))
    as [t1 tA2 tA3 t4 Ht1 HtA2 HtA3 Ht4 HtAchain].
  apply rel_chain_relevant_univ in HtAchain.
  rewrite <- exp_sub_extend_sub in Ht1, Ht4.
  destruct (HBgen _ _ HΓ _ _ HidN _ _ _ _ Hρσ
                  (eval_sub_extend_proof _ _ _ _ _ _ Hid2 Hp2)
                  (eval_sub_extend_proof _ _ _ _ _ _ Hid3 Hp3))
    as [t2 tB2 tB3 t3 Ht2 HtB2 HtB3 Ht3 HtBchain].
  apply rel_chain_relevant_univ in HtBchain.
  assert (tB2 = tA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (tB3 = tA3) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hall : rel_chain (per_univ i) ([t1; tA2; tA3; t4; t2; t3]))
    by (merge_rel_chain HtAchain HtBchain tA2).
  assert (Hmid : Dom tA2 ≈ tA3 ∈ per_univ i) by pairwise.
  pose proof (per_univ_elem_at_head HtA2 HtA3 Hmid) as Hanchor.
  assert (HallR : rel_chain (per_univ_elem i (per_head B B (ρσ ↦ ⋆ᵈ) (ρ'σ' ↦ ⋆ᵈ)))
                    ([t1; tA2; tA3; t4; t2; t3]))
    by (eapply per_univ_chain_at_in; [ exact Hall | | | exact Hanchor ]; solve_in).
  exists a1, a2, a3, a4.
  do 5 (split; [ assumption |]).
  split; [ exists tA2, tA3; repeat split; assumption |].
  apply (mk_rel_exp t1 t2 t3 t4); try eassumption.
  apply rel_chain_4; pairwise.
Qed.

(** Application of a function of a proof: the argument is not evaluated,
    and every link applies the two functions to [⋆ᵈ]. *)
Lemma rel_exp_under_ctx_app_cong_prop : forall {Γ A} {i : nat} {B M M' N N'},
    Γ ⊨ A : Propₘ ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ M ≈ M' : Π A B ->
    Γ ⊨ N ≈ N' : A ->
    Γ ⊨ M $ N ≈ M' $ N' : B[Id ,, N].
Proof.
  intros * HA HB HM HN.
  pose proof (rel_exp_under_ctx_refl_left HN) as HNl.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ [HΓ _]].
  destruct HM as [? ? k HMgen].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance_prop HA HB HNl _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Hachain [_ Htyp]]]]]]]]]].
  exists (per_head B B (ρσ ↦ ⋆ᵈ) (ρ'σ' ↦ ⋆ᵈ)).
  split; [ exact Htyp |]; right.
  pose proof Hachain as (_ & H23 & _).
  pose proof (per_univ_elem_of_prop k _ _ H23) as Hmid.
  destruct H23 as [Er2 Er3 _].
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RM [HMtyp HMexp]].
  assert (HΠr : rel_typ_sort (Π A B) ρσ relevant)
    by (exists (Πᵈ a2 ρσ B); split; [ apply eval_exp_pi; exact Ha2 | reflexivity ]).
  apply (rel_exp_or_prop_relevant HMtyp HΠr) in HMexp.
  destruct HMtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (c2 = Πᵈ a2 ρσ B) as ->
    by (eapply functional_eval_exp; [ exact Hc2 | apply eval_exp_pi; exact Ha2 ]).
  assert (c3 = Πᵈ a3 ρ'σ' B) as ->
    by (eapply functional_eval_exp; [ exact Hc3 | apply eval_exp_pi; exact Ha3 ]).
  assert (HRMmid : DF Πᵈ a2 ρσ B ≈ Πᵈ a3 ρ'σ' B ∈ per_univ_elem k ↘ RM) by pairwise.
  rewrite (per_pi_iff Hmid HRMmid) in Hmchain.
  destruct Hmchain as (Hpi1 & Hpi2 & Hpi3).
  assert (Hstar : Dom ⋆ᵈ ≈ ⋆ᵈ ∈ per_proof) by (split; reflexivity).
  destruct (pi_elements_app _ _ _ _ _ _ Hpi1 _ _ Hstar) as [r1 r2 Hr1 Hr2 Hr].
  destruct (pi_elements_app _ _ _ _ _ _ Hpi2 _ _ Hstar) as [s1 s2 Hs1 Hs2 Hs].
  destruct (pi_elements_app _ _ _ _ _ _ Hpi3 _ _ Hstar) as [u1 u2 Hu1 Hu2 Hu].
  assert (Hs1e : s1 = r2) by (eapply functional_eval_app; [ exact Hs1 | exact Hr2 ]).
  assert (Hu1e : u1 = s2) by (eapply functional_eval_app; [ exact Hu1 | exact Hs2 ]).
  subst s1 u1.
  (** The functions take proofs. *)
  assert (Ef1 : arg_relevance gc_deps gc_stack m1 = propositional) by (rewrite (pi_elements_left _ _ _ _ _ _ Hpi1); exact Er2).
  assert (Ef2 : arg_relevance gc_deps gc_stack m2 = propositional) by (rewrite (pi_elements_right _ _ _ _ _ _ Hpi1); exact Er3).
  assert (Ef3 : arg_relevance gc_deps gc_stack m3 = propositional) by (rewrite (pi_elements_right _ _ _ _ _ _ Hpi2); exact Er3).
  assert (Ef4 : arg_relevance gc_deps gc_stack m4 = propositional) by (rewrite (pi_elements_right _ _ _ _ _ _ Hpi3); exact Er3).
  apply (mk_rel_exp r1 r2 s2 u2);
    [ eapply eval_exp_app_proof; [ exact Hm1 | exact Ef1 | exact Hr1 ]
    | eapply eval_exp_app_proof; [ exact Hm2 | exact Ef2 | exact Hr2 ]
    | eapply eval_exp_app_proof; [ exact Hm3 | exact Ef3 | exact Hs2 ]
    | eapply eval_exp_app_proof; [ exact Hm4 | exact Ef4 | exact Hu2 ]
    |].
  apply rel_chain_4; assumption.
Qed.

(** The codomain of a [∀] at an argument is a proposition: its instance
    along [Id ,, N], which is built from valid parts. *)
Lemma rel_exp_under_ctx_instance : forall {Γ A Srt B B' C N},
    ⊨ Γ ->
    type_sort Srt ->
    Γ ⊨ A : Srt ->
    Γ ▹ A ⊨ B ≈ B' : C ->
    Γ ⊨ N : A ->
    Γ ⊨ B[Id,,N] ≈ B'[Id,,N] : C[Id,,N].
Proof.
  intros * HΓ HS HA HB HN.
  eapply rel_exp_under_ctx_gsub; [| exact HB ].
  eapply gsub_ass; [ apply gsub_id; exact HΓ | exact HS | exact HA | rewrite exp_sub_id; exact HN ].
Qed.

End Fixed_GCtx.

(** Application of a function or of a proof of a [∀]. *)
Lemma sem_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : a_pi r A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N ≈ M' $ N' : B[Id,,N] ).
Proof.
  intros * HA HS HB HM HN; sem_intro; [ assumption |].
  destruct r; cbn [relevance_sort] in *.
  - destruct HS as [k |].
    + eapply (rel_exp_under_ctx_app_cong (i := Nat.max k i));
        [ eapply rel_exp_cumu_ge; [| exact HA ]; lia | eapply rel_exp_cumu_ge; [| exact HB ]; lia
        | exact HM | exact HN ].
    + exact (rel_exp_under_ctx_app_cong_prop HA HB HM HN).
  - apply rel_exp_under_ctx_proof.
    match goal with HΓ : ⊨ Γ |- _ =>
      exact (rel_exp_under_ctx_instance HΓ HS HA HB (rel_exp_under_ctx_refl_left HN)) end.
Qed.

Lemma sem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : a_pi r A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N : B[Id,,N] ).
Proof.
  intros * HA HS HB HM HN; eapply sem_exp_eq_app_cong; [ exact HA | exact HS | exact HB | exact HM | exact HN ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

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
Lemma rel_exp_under_ctx_pi_beta : forall {Γ A B M N} {i : nat},
    Γ ⊨ A : Typeω@i ->
    Γ ▹ A ⊨ B : Typeω@i ->
    Γ ▹ A ⊨ M : B ->
    Γ ⊨ N : A ->
    Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N].
Proof.
  intros * HA HB HM HN.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (rel_type_of_typ HA) as HAt.
  pose proof (per_ctx_env_of_typ HΓ HAt) as HΓA.
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN) as HidN.
  rewrite exp_sub_id in HidN.
  assert (HBrel : forall ρ ρ' R, EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R -> rel_typ_sort B ρ relevant)
    by (intros * HR Hρ; exact (rel_exp_of_typ_relevant_at HR HB _ _ Hρ)).
  pose proof HM as [? ? k HMgen].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance HA HB HN _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [j [RN [a1 [a2 [a3 [a4 [n1 [n2 [n3 [n4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hn1 [Hn2 [Hn3 [Hn4 [Hnchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3)).
  split; [ exact Htyp |]; right.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  pose proof (head_not_propositional_of_typ (e := ce_ass A) HΓ eq_refl HA _ _ Hρσ) as [Hnp2 Hnp3].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  (** The argument pairs the links are read at. *)
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn13 : Dom n1 ≈ n3 ∈ RN) by pairwise.
  assert (Hn14 : Dom n1 ≈ n4 ∈ RN) by pairwise.
  assert (Hn22 : Dom n2 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn24 : Dom n2 ≈ n4 ∈ RN) by pairwise.
  (** *** The Redex

      [rel_exp_under_ctx_q] at the argument pair [n1 ≈ n2]. *)
  pose proof (per_env_extend_sub_intro HΓ' Hσj HAt _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hn12) as Hpair.
  destruct (rel_exp_under_ctx_q HΓ' Hσj HAt HM HBrel _ _ _ _ _ _ Hpair Hev Hev')
    as [[v1 [v2 [Hv1 [Hv2 Hv]]]] _].
  clear Hpair.
  assert (Hlink1 : Dom v1 ≈ v2 ∈ per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
    by (apply (per_head_of_args Hcod n1 n2 n2 n3 Hn12 Hn23 Hn22); exact Hv).
  apply rel_chain_of_pair in Hlink1.
  (** *** The Outer Instantiation

      Along [σ ,, N[σ] ≈ σ' ,, N[σ']], whose right-hand outer value is the goal's
      fourth once [exp_sub_extend_sub] has rewritten it. *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN) _ _ _ _ Hρ
                  (eval_sub_extend _ _ _ _ _ _ _ Hev Hnp2 Hn1)
                  (eval_sub_extend _ _ _ _ _ _ _ Hev' Hnp3 Hn4))
    as [RA [HAtyp HAexp]].
  apply (rel_exp_or_prop_relevant HAtyp
           (HBrel _ _ _ HΓA (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hn14)))) in HAexp.
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
                  (eval_sub_extend _ _ _ _ _ _ _ Hid2 Hnp2 Hn2)
                  (eval_sub_extend _ _ _ _ _ _ _ Hid3 Hnp3 Hn3))
    as [RB [HBtyp HBexp]].
  apply (rel_exp_or_prop_relevant HBtyp
           (HBrel _ _ _ HΓA (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hn23)))) in HBexp.
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
      other; the codomain there is relevant. *)
  destruct (rel_exp_under_ctx_extend_simple HΓ HAt HM _ _
              (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hn13)))
    as [Hp | [b1 [b2 [Hb1 [Hb2 Hb]]]]].
  { exfalso; destruct (HBrel _ _ _ HΓA (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hn13))) as (x & Ex & Hx).
    destruct Hp as (y & Ey & Hy); functional_eval_rewrite_clear; congruence. }
  assert (b1 = h2) as -> by (eapply functional_eval_exp; [ exact Hb1 | exact Hh2 ]).
  assert (b2 = g3) as -> by (eapply functional_eval_exp; [ exact Hb2 | exact Hg3 ]).
  assert (Hbridge : Dom h2 ≈ g3 ∈ per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
    by (apply (per_head_of_args Hcod n1 n3 n2 n3 Hn13 Hn23 Hn23); exact Hb).
  apply rel_chain_of_pair in Hbridge.
  (** *** The Four Values *)
  assert (Hmerge1 : rel_chain (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3)) ([h4; g3]))
    by (merge_rel_chain Hhchain Hbridge h2).
  assert (Hmerge2 : rel_chain (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3)) ([g2; g4; h4]))
    by (merge_rel_chain Hmerge1 Hgchain g3).
  (** The redex takes a relevant argument on both sides. *)
  destruct (rel_exp_of_typ_relevant_at HΓ HA _ _ Hρσ) as (a2' & Ha2' & Er2).
  destruct (rel_exp_of_typ_sub_relevant HΓ' Hσj HA _ _ Hρ) as (a1' & Ha1' & Er1).
  functional_eval_rewrite_clear.
  apply (mk_rel_exp v1 g2 g4 h4);
    [ eapply eval_exp_app; [ apply eval_exp_fn; exact Ha1 | exact Er1 | exact Hn1 | apply eval_app_fn; exact Hv1 ]
    | eapply eval_exp_app; [ apply eval_exp_fn; exact Ha2 | exact Er2 | exact Hn2 | apply eval_app_fn; exact Hg2 ]
    | exact Hg4
    | exact Hh4
    |].
  merge_rel_chain Hlink1 Hmerge2 g2.
Qed.

(** β for a function of a proof: the argument is [⋆ᵈ] in every
    environment, so the redex's values, [M]'s along [q σ] at [⋆ᵈ], and the
    two instantiations' share their inner values, and no bridge is
    needed. *)
Lemma rel_exp_under_ctx_pi_beta_prop : forall {Γ A B M N} {i : nat},
    Γ ⊨ A : Propₘ ->
    Γ ▹ A ⊨ B : Typeω@i ->
    Γ ▹ A ⊨ M : B ->
    Γ ⊨ N : A ->
    Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N].
Proof.
  intros * HA HB HM HN.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (rel_type_of_prop i HA) as HAt.
  pose proof (per_ctx_env_of_typ HΓ HAt) as HΓA.
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN) as HidN.
  rewrite exp_sub_id in HidN.
  assert (HBrel : forall ρ ρ' R, EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R -> rel_typ_sort B ρ relevant)
    by (intros * HR Hρ; exact (rel_exp_of_typ_relevant_at HR HB _ _ Hρ)).
  pose proof HM as [? ? k HMgen].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance_prop HA HB HN _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Hachain [_ Htyp]]]]]]]]]].
  exists (per_head B B (ρσ ↦ ⋆ᵈ) (ρ'σ' ↦ ⋆ᵈ)).
  split; [ exact Htyp |]; right.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  pose proof Hachain as ([Hr1 _ _] & [Hr2 Hr3 _] & _).
  assert (Ha14 : DF a1 ≈ a4 ∈ per_univ_elem i ↘ per_proof) by (apply per_univ_elem_of_prop; pairwise).
  pose proof (head_propositional_of_value (Γ := Γ) Ha2 Hr2) as Hp2.
  pose proof (head_propositional_of_value (Γ := Γ) Ha3 Hr3) as Hp3.
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  assert (Hstar : Dom ⋆ᵈ ≈ ⋆ᵈ ∈ per_proof) by (split; reflexivity).
  assert (Hext : Dom ρσ ↦ ⋆ᵈ ≈ ρ'σ' ↦ ⋆ᵈ ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro'; [ exact Hρσ | eapply per_head_proof; eassumption ]).
  (** *** The Redex *)
  pose proof (per_env_extend_sub_intro HΓ' Hσj HAt _ _ _ _ _ _ _ _ Hρ Ha1 Ha14 Hstar) as Hpair.
  destruct (rel_exp_under_ctx_q HΓ' Hσj HAt HM HBrel _ _ _ _ _ _ Hpair Hev Hev')
    as [[v1 [v2 [Hv1 [Hv2 Hlink1]]]] _].
  apply rel_chain_of_pair in Hlink1.
  (** *** The Outer Instantiation *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN) _ _ _ _ Hρ
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev Hp2)
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev' Hp3))
    as [RA [HAtyp HAexp]].
  apply (rel_exp_or_prop_relevant HAtyp (HBrel _ _ _ HΓA Hext)) in HAexp.
  destruct HAtyp as [cA1 cA2 cA3 cA4 HcA1 HcA2 HcA3 HcA4 HcAchain].
  destruct HAexp as [h1 h2 h3 h4 Hh1 Hh2 Hh3 Hh4 Hhchain].
  rewrite <- exp_sub_extend_sub in Hh4.
  assert (HcA23 : Dom cA2 ≈ cA3 ∈ per_univ k) by (eexists; pairwise).
  pose proof (per_univ_elem_at_head HcA2 HcA3 HcA23) as HanchorA.
  retype_rel_chain HcAchain HanchorA Hhchain.
  (** *** The Inner Instantiation *)
  destruct (HMgen _ _ HΓ _ _ HidN _ _ _ _ Hρσ
                  (eval_sub_extend_proof _ _ _ _ _ _ Hid2 Hp2)
                  (eval_sub_extend_proof _ _ _ _ _ _ Hid3 Hp3))
    as [RB [HBtyp HBexp]].
  apply (rel_exp_or_prop_relevant HBtyp (HBrel _ _ _ HΓA Hext)) in HBexp.
  destruct HBtyp as [cB1 cB2 cB3 cB4 HcB1 HcB2 HcB3 HcB4 HcBchain].
  destruct HBexp as [g1 g2 g3 g4 Hg1 Hg2 Hg3 Hg4 Hgchain].
  assert (HcB23 : Dom cB2 ≈ cB3 ∈ per_univ k) by (eexists; pairwise).
  pose proof (per_univ_elem_at_head HcB2 HcB3 HcB23) as HanchorB.
  retype_rel_chain HcBchain HanchorB Hgchain.
  assert (v2 = g2) as -> by (eapply functional_eval_exp; [ exact Hv2 | exact Hg2 ]).
  assert (h3 = g3) as -> by (eapply functional_eval_exp; [ exact Hh3 | exact Hg3 ]).
  assert (Hmerge : rel_chain (per_head B B (ρσ ↦ ⋆ᵈ) (ρ'σ' ↦ ⋆ᵈ)) ([g1; g2; g3; g4; h4]))
    by (merge_rel_chain Hgchain Hhchain g3).
  apply (mk_rel_exp v1 g2 g4 h4);
    [ eapply eval_exp_app_proof; [ apply eval_exp_fn; exact Ha1 | exact Hr1 | apply eval_app_fn; exact Hv1 ]
    | eapply eval_exp_app_proof; [ apply eval_exp_fn; exact Ha2 | exact Hr2 | apply eval_app_fn; exact Hg2 ]
    | exact Hg4
    | exact Hh4
    |].
  apply rel_chain_4; [ pairwise | pairwise | pairwise ].
Qed.

End Fixed_GCtx.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** η

    The only rule whose statement mentions a weakening rather than a substitution.
    [M[↑]ʷ] is a term in its own right, and [⟦M[↑]ʷ⟧(ρ ↦ c)] is not [⟦M⟧ρ]: in the
    λ case they are the different closures [λ (ρ ↦ c) (N[wk_q ↑]ʷ)] and [λ ρ N].
    So the weakening is crossed semantically, by instantiating [M]'s judgment along
    [Wk] with [rel_exp_under_ctx_shift_at].

    The type is [rel_typ_of_pi] unchanged.  The four values of the term are
    [⟦M[σ]⟧ρ], [⟦M⟧ρσ], [λ a3 ρ'σ' (M[↑]ʷ #0)] and [λ a4 ρ' ((M[↑]ʷ #0)[q σ'])], the
    last two by [eval_exp_fn].  Of the three links:

    - the first is [M]'s own left commutation;
    - the second is η proper: [M] and the closure of its weakened body agree on
      every argument.  This is [rel_exp_under_ctx_shift_at] at the substituted
      environments, read at the argument pair; applying the closure evaluates
      [M[↑]ʷ #0] in [ρ'σ' ↦ c'], by [eval_app_fn] and then the application of
      the function to its argument, [c'] itself at a relevant domain and the
      proof [⋆ᵈ], which [c'] is, at a proposition;
    - the third is the right commutation of the closure, the third obligation of
      [rel_exp_under_ctx_q] for the weakened judgment
      [Γ ▹ A ⊨ M[↑]ʷ ≈ M[↑]ʷ : (Π A B)[↑]ʷ].  Its right value is
      [⟦M[↑]ʷ[q σ']⟧(ρ' ↦ c')], the closure body's, and the outer pair of the
      same weakening instance identifies its [per_head] of [(Π A B)[↑]ʷ] with
      [per_pi]. *)
Lemma rel_exp_under_ctx_fn_eta : forall {Γ A B M} {i : nat},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ▹ A ⊨ B : Typeω@i ->
    Γ ⊨ M : Π A B ->
    Γ ⊨ M ≈ λ A M[↑]ʷ $ #0 : Π A B.
Proof.
  intros * HA HB HM.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  pose proof (rel_exp_under_ctx_shift HΓA HM) as HMwk.
  (** A type that is a Π is relevant, by its head, wherever it has a value. *)
  assert (HΠ : forall Δ R T M0, EF Δ ≈ Δ ∈ per_ctx_env ↘ R -> Δ ⊨ M0 : T ->
                 (forall ρ a, ⟦ T ⟧ ρ ↘ a -> domain_relevance a = relevant) ->
                 forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> rel_typ_sort T ρ relevant).
  { intros * HR HT Hhead ρ0 ρ0' Hρ0.
    destruct (rel_exp_under_ctx_simple_full_at HR HT) as [k Hk].
    destruct (Hk _ _ Hρ0) as (a & _ & _ & Ha & _).
    exists a; split; [ exact Ha | eapply Hhead; exact Ha ]. }
  assert (Hpihead : forall T ρ a, (exists A0 B0, T = Π A0 B0) -> ⟦ T ⟧ ρ ↘ a -> domain_relevance a = relevant)
    by (intros * (? & ? & ->) Ha; inversion Ha; reflexivity).
  pose proof (HΠ _ _ _ _ HΓ HM (fun ρ a => Hpihead _ ρ a (ex_intro _ _ (ex_intro _ _ eq_refl)))) as HΠrel.
  assert (HΠwkrel : forall ρ ρ' R, EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R ->
                      rel_typ_sort (Π A B)[↑]ʷ ρ relevant)
    by (intros * HR Hρ0; exact (HΠ _ _ _ _ HR HMwk (fun ρ a => Hpihead _ ρ a (ex_intro _ _ (ex_intro _ _ eq_refl))) _ _ Hρ0)).
  pose proof HM as [? ? k HMgen].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HA HA HB _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  exists (per_pi a2 a3 in_rel B ρσ B ρ'σ').
  split; [ exact Htyp |]; right.
  (** [pairwise] needs [per_pi] to be a PER: it is the element PER of the
      middle link of the type chain just obtained. *)
  destruct Htyp as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  assert (Hanchor : DF d2 ≈ d3 ∈ per_univ_elem i ↘ (per_pi a2 a3 in_rel B ρσ B ρ'σ'))
    by pairwise.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** [M]'s own chain, brought to the canonical [per_pi]. *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RM [HMtyp HMexp]].
  apply (rel_exp_or_prop_relevant HMtyp (HΠrel _ _ Hρσ)) in HMexp.
  destruct HMtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (c2 = Πᵈ a2 ρσ B) as ->
    by (eapply functional_eval_exp; [ exact Hc2 | apply eval_exp_pi; exact Ha2 ]).
  assert (c3 = Πᵈ a3 ρ'σ' B) as ->
    by (eapply functional_eval_exp; [ exact Hc3 | apply eval_exp_pi; exact Ha3 ]).
  assert (HRMmid : DF Πᵈ a2 ρσ B ≈ Πᵈ a3 ρ'σ' B ∈ per_univ_elem k ↘ RM) by pairwise.
  rewrite (per_pi_iff Hmid HRMmid) in Hmchain.
  pose proof (per_univ_elem_relevance _ _ _ _ Hmid) as Er23.
  (** The application in the closure's body: to the argument itself at a
      relevant domain, to the proof, which the argument is, at a
      proposition. *)
  assert (Happ : forall T w c' r ρ0 a0, ⟦ T ⟧ ρ0 ↦ c' ↘ w -> $| w & c' |↘ r ->
                   arg_relevance gc_deps gc_stack w = domain_relevance a0 ->
                   (domain_relevance a0 = propositional -> c' = ⋆ᵈ) ->
                   ⟦ T $ #0 ⟧ ρ0 ↦ c' ↘ r).
  { intros * Hw Hr Ew Hp.
    destruct (domain_relevance a0) eqn:Ea0.
    - eapply eval_exp_app; [ exact Hw | exact Ew | apply eval_exp_var_eq; reflexivity | exact Hr ].
    - rewrite (Hp eq_refl) in Hr; eapply eval_exp_app_proof; [ exact Hw | exact Ew | exact Hr ]. }
  assert (Harg : forall c c', Dom c ≈ c' ∈ in_rel -> domain_relevance a2 = propositional -> c = ⋆ᵈ /\ c' = ⋆ᵈ)
    by (intros c c' Hc Hp; apply (per_univ_elem_propositional _ _ _ _ Hmid Hp) in Hc; exact Hc).
  (** The four domains are of one sort. *)
  pose proof (rel_type_inversion HA) as [env_relΓ0 [HΓ0 HAgen]].
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [e1 e2 e3 e4 He1 He2 He3 He4 Hechain].
  functional_eval_rewrite_clear.
  destruct Hechain as ([R1 HR1] & _ & [R3 HR3]).
  pose proof (per_univ_elem_relevance _ _ _ _ HR1) as Er12.
  pose proof (per_univ_elem_relevance _ _ _ _ HR3) as Er34.
  pose proof Hmchain as (Hpi1 & Hpi2 & Hpi3).
  apply (mk_rel_exp m1 m2 λᵈ a3 ρ'σ' (M[↑]ʷ $ #0) λᵈ a4 ρ' (M[↑]ʷ $ #0)[q σ']);
    [ exact Hm1 | exact Hm2 | apply eval_exp_fn; exact Ha3 | apply eval_exp_fn; exact Ha4 |].
  apply rel_chain_4; [ exact Hpi1 | |].
  - (** η itself: the instance's inner value on the left is [⟦M⟧ρσ], the goal's
      second, and its outer value on the right is [⟦M[↑]ʷ⟧(ρ'σ' ↦ c')], the head
      the closure applies. *)
    constructor; [ rewrite (pi_elements_right _ _ _ _ _ _ Hpi1); congruence | reflexivity |].
    intros c c' Hc.
    pose proof (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hc)) as Hpair.
    destruct (rel_exp_under_ctx_shift_at HΓ HA HM HΠrel _ _ _ _ Hpair)
      as [j [R [b1 [b2 [b3 [b4 [w1 [w2 [w3 [w4 [Hb1 [Hb2 [Hb3 [Hb4 [Hbouter
         [Hbmid [Hw1 [Hw2 [Hw3 [Hw4 Hwchain]]]]]]]]]]]]]]]]]]]].
    assert (b2 = Πᵈ a2 ρσ B) as -> by (eapply functional_eval_exp; [ exact Hb2 | apply eval_exp_pi; exact Ha2 ]).
    assert (b3 = Πᵈ a3 ρ'σ' B) as -> by (eapply functional_eval_exp; [ exact Hb3 | apply eval_exp_pi; exact Ha3 ]).
    assert (HRpi : R <~> per_pi a2 a3 in_rel B ρσ B ρ'σ') by (eapply per_pi_iff; [ exact Hmid | exact Hbmid ]).
    assert (w2 = m2) as -> by (eapply functional_eval_exp; [ exact Hw2 | exact Hm2 ]).
    rewrite HRpi in Hwchain.
    assert (Hlink : Dom m2 ≈ w4 ∈ per_pi a2 a3 in_rel B ρσ B ρ'σ') by pairwise.
    destruct (pi_elements_app _ _ _ _ _ _ Hlink _ _ Hc) as [r r' Hr Hr' Hrr'].
    econstructor; [ exact Hr | apply eval_app_fn | exact Hrr' ].
    eapply Happ; [ exact Hw4 | exact Hr' | exact (pi_elements_right _ _ _ _ _ _ Hlink) |].
    intros Hp; rewrite <- Er23 in Hp; exact (proj2 (Harg _ _ Hc Hp)).
  - (** The closure's right commutation, from the weakened judgment along [q σ'].
      The outer type pair of the weakening instance identifies the [per_head] of
      [(Π A B)[↑]ʷ] it lands in with [per_pi]. *)
    constructor; [ cbn; congruence | cbn; congruence |].
    intros c c' Hc.
    pose proof (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hc)) as Hpair.
    destruct (rel_exp_under_ctx_shift_at HΓ HA HM HΠrel _ _ _ _ Hpair)
      as [j [R [b1 [b2 [b3 [b4 [w1 [w2 [w3 [w4 [Hb1 [Hb2 [Hb3 [Hb4 [Hbouter
         [Hbmid [Hw1 [Hw2 [Hw3 [Hw4 Hwchain]]]]]]]]]]]]]]]]]]]].
    assert (b2 = Πᵈ a2 ρσ B) as -> by (eapply functional_eval_exp; [ exact Hb2 | apply eval_exp_pi; exact Ha2 ]).
    assert (b3 = Πᵈ a3 ρ'σ' B) as -> by (eapply functional_eval_exp; [ exact Hb3 | apply eval_exp_pi; exact Ha3 ]).
    assert (HRpi : R <~> per_pi a2 a3 in_rel B ρσ B ρ'σ') by (eapply per_pi_iff; [ exact Hmid | exact Hbmid ]).
    pose proof (per_env_extend_sub_intro HΓ' Hσj HA _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc) as Hpair'.
    destruct (rel_exp_under_ctx_q HΓ' Hσj HA HMwk HΠwkrel _ _ _ _ _ _ Hpair' Hev Hev')
      as [_ [_ [u [v [Hu [Hv Huv]]]]]].
    assert (HuvR : Dom u ≈ v ∈ R) by (eapply Huv; [ exact Hb1 | exact Hb4 | exact Hbouter ]).
    apply HRpi in HuvR.
    destruct (pi_elements_app _ _ _ _ _ _ HuvR _ _ Hc) as [r r' Hr Hr' Hrr'].
    (** [(M[↑]ʷ #0)[q σ']] is [(M[↑]ʷ[q σ']) #0], since [(#0)[q σ']] is [#0], so
      the head is the value [rel_exp_under_ctx_q] reports. *)
    econstructor; [ apply eval_app_fn | apply eval_app_fn | exact Hrr' ].
    + eapply Happ; [ exact Hu | exact Hr | exact (pi_elements_left _ _ _ _ _ _ HuvR) |].
      intros Hp; exact (proj1 (Harg _ _ Hc Hp)).
    + eapply Happ; [ exact Hv | exact Hr' | exact (pi_elements_right _ _ _ _ _ _ HuvR) |].
      intros Hp; rewrite <- Er23 in Hp; exact (proj2 (Harg _ _ Hc Hp)).
Qed.

End Fixed_GCtx.

(** β for a function or for a proof of a [∀]. *)
Lemma sem_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] ).
Proof.
  intros * HA HS HB HM HN; sem_intro; [ assumption |].
  destruct r; cbn [relevance_sort] in *.
  - destruct HS as [k |].
    + eapply (rel_exp_under_ctx_pi_beta (i := Nat.max k i));
        [ eapply rel_exp_cumu_ge; [| exact HA ]; lia | eapply rel_exp_cumu_ge; [| exact HB ]; lia
        | exact HM | exact HN ].
    + exact (rel_exp_under_ctx_pi_beta_prop HA HB HM HN).
  - apply rel_exp_under_ctx_proof.
    match goal with HΓ : ⊨ Γ |- _ =>
      exact (rel_exp_under_ctx_instance HΓ HS HA HB HN) end.
Qed.

(** η for a function or for a proof of a [∀]. *)
Lemma sem_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : a_pi r A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ λ A M[↑]ʷ $ #0 : a_pi r A B ).
Proof.
  intros * HA HS HB HM; sem_intro; [ assumption |].
  destruct r; cbn [relevance_sort] in *.
  - destruct (rel_pi_parts HS HA HA HB) as [k [Hl [_ Hk]]].
    exact (rel_exp_under_ctx_fn_eta Hl Hk HM).
  - exact (rel_exp_under_ctx_proof (rel_all_of_parts HS HA HA HB)).
Qed.

#[export]
Hint Resolve rel_exp_under_ctx_pi_cong rel_exp_under_ctx_pi_cong_small rel_exp_under_ctx_all
  rel_exp_under_ctx_fn_cong rel_exp_under_ctx_app_cong : mctt.
