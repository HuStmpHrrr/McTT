(** * Fundamental Theorem: Π-Types and Universal Propositions

    Substitution pushes through [Π], [λ] and application by computation of
    [exp_sub]: [(a_pi r A B)[σ]] is [a_pi r (A[σ]) (B[q σ])].  So only the
    congruence, β and η rules are validated here.

    A [Π] carries a relevance tag.  At [relevant] it is a type of functions
    in a universe: its domain is a type of that universe, a proposition (a
    function of a proof) or a type of levels, and its codomain is a type of
    the universe.  At [propositional] it is the impredicative [∀]: its
    domain is a type of any sort and its codomain a family of propositions,
    and it is itself a proposition.

    The relevant case is organised around [rel_typ_of_pi]: the type judgment
    of a Π, at the canonical element PER [per_pi].  The rules whose type is a
    Π read their four values off it; application and β, whose type is the
    instantiated codomain, read it off [rel_typ_of_instance] at a relevant
    domain and off [rel_typ_of_instance_prop] at a propositional one, whose
    argument is kept as a proof [⋆ᵈ⟨N, ρ⟩].

    Extensions carry the type of their head.  A closure extends by the value
    of its own domain, [per_pi] by those of its type's, an instance by
    [substituted_type]; [per_head_codomain_resp] moves a codomain's head PER
    between any two of these.

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
  intros * [i | |] H.
  - exists i; intros j Hj; exact (rel_type_of_typ (rel_exp_cumu_ge Hj H)).
  - exists 0; intros j _; exact (rel_type_of_prop j H).
  - exists 0; intros j _; exact (rel_type_of_level_sort j H).
Qed.

(** Related arguments read back at each of the four values of a chain of
    types: the entry types of the four extensions of a Π-pattern. *)
Lemma args_readable_of_chain : forall {i R a1 a2 a3 a4 c c'},
    rel_chain (per_univ_elem i R) ([a1; a2; a3; a4]) -> Dom c ≈ c' ∈ R ->
    args_readable_at c c' ([entry_type_value a1; entry_type_value a2; entry_type_value a3; entry_type_value a4]).
Proof.
  intros * Hc Hcc.
  assert (H11 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (H22 : DF a2 ≈ a2 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (H33 : DF a3 ≈ a3 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (H44 : DF a4 ≈ a4 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (PER R) by (eapply per_elem_PER; exact H11).
  assert (Hc1 : Dom c ≈ c ∈ R) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
  assert (Hc2 : Dom c' ≈ c' ∈ R) by (etransitivity; [ symmetry; exact Hcc | exact Hcc ]).
  repeat constructor;
    first [ exact (proj1 (entry_readable_of_elem H11 Hc1)) | exact (proj1 (entry_readable_of_elem H11 Hc2))
          | exact (proj1 (entry_readable_of_elem H22 Hc1)) | exact (proj1 (entry_readable_of_elem H22 Hc2))
          | exact (proj1 (entry_readable_of_elem H33 Hc1)) | exact (proj1 (entry_readable_of_elem H33 Hc2))
          | exact (proj1 (entry_readable_of_elem H44 Hc1)) | exact (proj1 (entry_readable_of_elem H44 Hc2)) ].
Qed.

(** The head PER of a codomain at two extensions of a related pair of
    tails, by arguments related at the domain, is the one at any other
    such pair.  The tags of the four extensions need only be readable: for
    example, the closures of a λ extend by the values of their own
    domains, a [per_pi] by those of its type's, an instance by
    [substituted_type]. *)
Lemma per_head_codomain_resp : forall {Γ A B} {i k : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ▹ A ⊨ᵗ B ≈ B at k ->
    forall ρ ρ' a a' j R x y u v t t' s s',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      ⟦ A ⟧ ρ ↘ a -> ⟦ A ⟧ ρ' ↘ a' -> DF a ≈ a' ∈ per_univ_elem j ↘ R ->
      Dom x ≈ y ∈ R -> Dom u ≈ v ∈ R -> Dom u ≈ y ∈ R ->
      entry_readable (de_term x t) -> entry_readable (de_term y t') ->
      entry_readable (de_term u s) -> entry_readable (de_term v s') ->
      per_head B B (ρ ↦ x ⦂ t) (ρ' ↦ y ⦂ t') <~> per_head B B (ρ ↦ u ⦂ s) (ρ' ↦ v ⦂ s').
Proof.
  intros * HΓ HA HB * Hρ Ha Ha' HR Hxy Huv Huy Rx Ry Ru Rv.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  assert (PER (per_env_extend A A env_relΓ)) by (eapply per_env_PER; exact HΓA).
  assert (H1 : Dom ρ ↦ x ⦂ t ≈ ρ' ↦ y ⦂ t' ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro'; [ exact Hρ | eapply per_head_of; eassumption | exact Rx | exact Ry ]).
  assert (H2 : Dom ρ ↦ u ⦂ s ≈ ρ' ↦ y ⦂ t' ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro'; [ exact Hρ | eapply per_head_of; eassumption | exact Ru | exact Ry ]).
  assert (H3 : Dom ρ ↦ u ⦂ s ≈ ρ' ↦ v ⦂ s' ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro'; [ exact Hρ | eapply per_head_of; eassumption | exact Ru | exact Rv ]).
  eapply (per_head_of_type_resp HΓA HB).
  apply rel_chain_4; [ exact H1 | symmetry; exact H2 | exact H3 ].
Qed.

(** The codomain of a Π along a lifted substitution is a relevant type, at
    the left environment: its four values are relevant types of a
    universe. *)
Lemma rel_typ_sort_of_univ_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B' u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ▹ A ⊨ B ≈ B' : universe_index_term u ->
    forall ρ ρ' ρσ ρ'σ' c c' t1 t2 t3 t4,
      Dom ρ ↦ c ⦂ t1 ≈ ρ' ↦ c' ⦂ t4 ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      args_readable_at c c' ([t1; t2; t3; t4]) ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      rel_typ_sort B[q σ] (ρ ↦ c ⦂ t1) relevant.
Proof.
  intros * HΓ Hσj HA HB * Hpair Hts Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_univ_inversion HB) as [env_relΔA [HΔA HBgen]].
  destruct (rel_sub_under_ctx_q_at HΓ HΔA Hσj HA _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
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
    pose proof (args_readable_of_chain Hachain Hc) as Hts;
    inversion Hts as [| ? ? [Hr1 Hr1'] Hts2]; subst; inversion Hts2 as [| ? ? [Hr2 Hr2'] Hts3]; subst;
      inversion Hts3 as [| ? ? [Hr3 Hr3'] Hts4]; subst; inversion Hts4 as [| ? ? [Hr4 Hr4'] _]; subst;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc Hr1 Hr4') as Hpair;
    [ destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HAself HB _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
        as [O1 [O2 O3]]; eassumption .. |].
  exact (rel_typ_sort_of_univ_under_ctx_q (u := ul i) HΓ' Hσj HAself HB _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev').
Qed.

(** A Π whose codomain is no type of levels is none: a type of levels
    has codomains of levels at every argument ([level_code_pi_codomain]),
    and its domain has one, a variable ([var_per_elem]). *)
Lemma pi_not_level_code : forall {i R a a' ρ B},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    (forall c, Dom c ≈ c ∈ R -> exists b, ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\ ~ level_code b) ->
    ~ level_code (Πᵈ a ρ B).
Proof.
  intros * Ha HB Hlc.
  assert (Haa : DF a ≈ a ∈ per_univ_elem i ↘ R) by (etransitivity; [ exact Ha | symmetry; exact Ha ]).
  pose proof (var_per_elem 0 Haa) as Hc.
  destruct (HB _ Hc) as (b & Eb & Hb).
  exact (Hb (level_code_pi_codomain _ _ _ _ _ _ Hlc Haa _ _ Hc Eb)).
Qed.

(** The codomain of a Π along a lifted substitution is no type of levels
    at the outer environments: the outer values of its chain are elements
    of a universe. *)
Lemma rel_typ_nonlevel_of_univ_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B' u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ▹ A ⊨ B ≈ B' : universe_index_term u ->
    forall ρ ρ' ρσ ρ'σ' c c' t1 t2 t3 t4,
      Dom ρ ↦ c ⦂ t1 ≈ ρ' ↦ c' ⦂ t4 ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      args_readable_at c c' ([t1; t2; t3; t4]) ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      (exists b, ⟦ B[q σ] ⟧ ρ ↦ c ⦂ t1 ↘ b /\ ~ level_code b) /\
      (exists b, ⟦ B'[q σ'] ⟧ ρ' ↦ c' ⦂ t4 ↘ b /\ ~ level_code b).
Proof.
  intros * HΓ Hσj HA HB * Hpair Hts Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_univ_inversion HB) as [env_relΔA [HΔA HBgen]].
  destruct (rel_sub_under_ctx_q_at HΓ HΔA Hσj HA _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
    as [s [s' [Hq [Hq' _]]]].
  destruct (HBgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq')
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hc].
  assert (H12 : per_relevant_nonlevel (per_univ u) b1 b2) by pairwise.
  assert (H34 : per_relevant_nonlevel (per_univ u) b3 b4) by pairwise.
  split; [ exists b1 | exists b4 ]; split; try assumption;
    [ exact (per_relevant_nonlevel_left_nonlevel _ _ _ H12) | exact (per_relevant_nonlevel_right_nonlevel _ _ _ H34) ].
Qed.

(** A codomain of a universe at an environment of its context extended
    by an element of the domain: it has a value, no type of levels. *)
Lemma codomain_nonlevel_at : forall {Γ A B} {i k : nat} {R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ▹ A ⊨ B : Typeω@k ->
    forall ρ a Ra c t, Dom ρ ≈ ρ ∈ R -> ⟦ A ⟧ ρ ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ Ra -> Dom c ≈ c ∈ Ra ->
      entry_readable (de_term c t) ->
      exists b, ⟦ B ⟧ ρ ↦ c ⦂ t ↘ b /\ ~ level_code b.
Proof.
  intros * HΓ HA HB * Hρ Ha HRa Hc Hrd.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  assert (Henv : Dom ρ ↦ c ⦂ t ≈ ρ ↦ c ⦂ t ∈ per_env_extend A A R)
    by (apply per_env_extend_intro'; [ exact Hρ | eapply per_head_of; eassumption | exact Hrd | exact Hrd ]).
  destruct (rel_exp_of_typ_inversion_simple_at HΓA HB _ _ Henv) as (b & b' & Eb & _ & _).
  exists b; split; [ exact Eb | exact (rel_exp_of_typ_nonlevel_at HΓA HB _ _ Henv _ Eb) ].
Qed.

(** The four Π-values of a stage of [Π A B ≈ Π A' B'] are no types of
    levels: their codomains are elements of a universe. *)
Lemma pi_values_nonlevel : forall {Γ A A'} {i : nat} {B B'},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ᵗ A ≈ A' at i ->
    Γ ▹ A ⊨ B ≈ B' : Typeω@i ->
    forall Γ' env_rel', EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ' in_rel a1 a2 a3 a4,
        Γ' ⊨ˢ σ ≈ σ' : Γ -> Dom ρ ≈ ρ' ∈ env_rel' -> ⟦ σ : Γ ⟧s ρ ↘ ρσ -> ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        ⟦ A[σ] ⟧ ρ ↘ a1 -> ⟦ A ⟧ ρσ ↘ a2 -> ⟦ A' ⟧ ρ'σ' ↘ a3 -> ⟦ A'[σ'] ⟧ ρ' ↘ a4 ->
        DF a1 ≈ a4 ∈ per_univ_elem i ↘ in_rel -> DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel ->
        ~ level_code (Πᵈ a1 ρ B[q σ]) /\ ~ level_code (Πᵈ a2 ρσ B) /\
        ~ level_code (Πᵈ a3 ρ'σ' B') /\ ~ level_code (Πᵈ a4 ρ' B'[q σ']).
Proof.
  intros * HAself HA HB * HΓ' * Hσj Hρ Hev Hev' Ha1 Ha2 Ha3 Ha4 Houter Hmid.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ _]].
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρσl : Dom ρσ ≈ ρσ ∈ env_relΓ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  assert (Hρσr : Dom ρ'σ' ≈ ρ'σ' ∈ env_relΓ) by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  assert (H11 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ in_rel) by (etransitivity; [ exact Houter | symmetry; exact Houter ]).
  assert (H44 : DF a4 ≈ a4 ∈ per_univ_elem i ↘ in_rel) by (etransitivity; [ symmetry; exact Houter | exact Houter ]).
  assert (H22 : DF a2 ≈ a2 ∈ per_univ_elem i ↘ in_rel) by (etransitivity; [ exact Hmid | symmetry; exact Hmid ]).
  assert (H33 : DF a3 ≈ a3 ∈ per_univ_elem i ↘ in_rel) by (etransitivity; [ symmetry; exact Hmid | exact Hmid ]).
  (** The outer two along [q σ] and [q σ'], at a pair of equal arguments. *)
  assert (Hout : forall c, Dom c ≈ c ∈ in_rel ->
                   (exists b, ⟦ B[q σ] ⟧ ρ ↦ c ⦂ entry_type_value a1 ↘ b /\ ~ level_code b) /\
                   (exists b, ⟦ B'[q σ'] ⟧ ρ' ↦ c ⦂ entry_type_value a4 ↘ b /\ ~ level_code b)).
  { intros c Hc.
    pose proof (entry_readable_of_elem Houter Hc) as [Hr1 Hr4].
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc Hr1 Hr4) as Hpair.
    assert (Hts : args_readable_at c c ([entry_type_value a1; substituted_type; substituted_type; entry_type_value a4]))
      by (repeat constructor; first [ exact Hr1 | exact Hr4 | apply substituted_entry_readable ]).
    exact (rel_typ_nonlevel_of_univ_under_ctx_q (u := ul i) HΓ' Hσj HAself HB _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev'). }
  split; [| split; [| split ]].
  - apply (pi_not_level_code H11); intros c Hc; exact (proj1 (Hout c Hc)).
  - apply (pi_not_level_code H22); intros c Hc.
    exact (codomain_nonlevel_at HΓ HAself (rel_exp_under_ctx_refl_left HB) _ _ _ _ _ Hρσl Ha2 H22 Hc
             (proj1 (entry_readable_of_elem H22 Hc))).
  - apply (pi_not_level_code H33); intros c Hc.
    (** [B'] at the value of [A'], read through [A]'s at the same
        environment, which [A ≈ A'] relates to it. *)
    destruct (rel_type_inversion_simple_at HΓ HA _ _ Hρσr) as (x & x' & Ex & Ex' & [Rx HRx]).
    assert (x' = a3) as -> by (eapply functional_eval_exp; eassumption).
    assert (Ex3 : Rx <~> in_rel) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRx Hmid).
    assert (Hxx : DF x ≈ x ∈ per_univ_elem i ↘ Rx) by (etransitivity; [ exact HRx | symmetry; exact HRx ]).
    exact (codomain_nonlevel_at HΓ HAself (rel_exp_under_ctx_refl_right HB) _ _ _ _ _ Hρσr Ex Hxx (proj2 (Ex3 _ _) Hc)
             (proj1 (entry_readable_of_elem H33 Hc))).
  - apply (pi_not_level_code H44); intros c Hc; exact (proj2 (Hout c Hc)).
Qed.

(** A chain of Π-values in [per_univ i] is one of relevant types of the
    universe at [i], none of them a type of levels. *)
Lemma rel_chain_pi_relevant : forall {i R a1 a2 a3 a4 ρ1 ρ2 ρ3 ρ4 B1 B2 B3 B4},
    rel_chain (per_univ_elem i R) ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2; Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]) ->
    ~ level_code (Πᵈ a1 ρ1 B1) -> ~ level_code (Πᵈ a2 ρ2 B2) ->
    ~ level_code (Πᵈ a3 ρ3 B3) -> ~ level_code (Πᵈ a4 ρ4 B4) ->
    rel_chain (per_relevant_nonlevel (per_univ i)) ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2; Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]).
Proof.
  intros * (H12 & H23 & H34) N1 N2 N3 N4.
  apply rel_chain_4; (constructor; [ eexists; eassumption | reflexivity | reflexivity | assumption | assumption ]).
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
  destruct (pi_values_nonlevel HAself HA HB _ _ HΓ' _ _ _ _ _ _ _ _ _ _ _ Hσj Hρ Hev Hev' Ha1 Ha2 Ha3 Ha4 Houter Hmid)
    as (N1 & N2 & N3 & N4).
  destruct Htyp as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  inversion Hd1; inversion Hd2; inversion Hd3; inversion Hd4; subst.
  functional_eval_rewrite_clear.
  apply (mk_rel_exp _ _ _ _ Hd1 Hd2 Hd3 Hd4).
  exact (rel_chain_pi_relevant Hdchain N1 N2 N3 N4).
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
    forall e x e' x' et et' t1 t2,
      Dom e ↦ x ⦂ et ≈ e' ↦ x' ⦂ et' ∈ env_relΔA ->
      ⟦ L[↑]ʷ ⟧ e ↦ x ⦂ et ↘ t1 ->
      ⟦ L ⟧ e' ↘ t2 ->
      domain_level_real t1 = domain_level_real t2.
Proof.
  intros * HA HL HΔA * Hee Ht1 Ht2.
  pose proof (rel_exp_of_level_inversion HL) as [env_relΔ [HΔ _]].
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA'.
  handle_per_ctx_env_irrel.
  assert (Hlr : forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔ -> rel_typ_sort Level@n ρ relevant)
    by (intros; eexists; split; [ apply eval_exp_level | reflexivity ]).
  destruct (rel_exp_under_ctx_shift_at HΔ HA HL Hlr _ _ _ _ _ _ Hee)
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
    [ρσ] ([suniv_real_shift]), so all five chains are in one small universe,
    of relevant types none of which is a type of levels. *)
Lemma rel_exp_of_suniv_under_ctx_q : forall {Γ Δ σ σ' A} {i n : nat} {B B' L env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ⊨ L : Level@n ->
    Δ ▹ A ⊨ B ≈ B' : Type⟨L[↑]ʷ⟩ ->
    forall ρ ρ' ρσ ρ'σ' c c' t1 t2 t3 t4 t,
      Dom ρ ↦ c ⦂ t1 ≈ ρ' ↦ c' ⦂ t4 ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      args_readable_at c c' ([t1; t2; t3; t4]) ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      ⟦ L ⟧ ρσ ↘ t ->
      rel_typ_sort B[q σ] (ρ ↦ c ⦂ t1) relevant /\
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ⦂ t1 ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ⦂ t2 ↘ b' /\
          Dom b ≈ b' ∈ per_relevant_nonlevel (per_univ (us (domain_level_real t)))) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ⦂ t2 ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ⦂ t3 ↘ b' /\
          Dom b ≈ b' ∈ per_relevant_nonlevel (per_univ (us (domain_level_real t)))) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ⦂ t3 ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ⦂ t4 ↘ b' /\
          Dom b ≈ b' ∈ per_relevant_nonlevel (per_univ (us (domain_level_real t)))).
Proof.
  intros * HΓ Hσj HA HL HB * Hpair Hts Hev Hev' Ht.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_suniv_tm_inversion HB) as [env_relΔA [HΔA HBgen]].
  pose proof (rel_exp_of_suniv_tm_inversion_simple (rel_exp_under_ctx_refl_left HB))
    as [env_relΔA2 [HΔA2 HBl]].
  pose proof (rel_exp_of_suniv_tm_inversion_simple (rel_exp_under_ctx_refl_right HB))
    as [env_relΔA3 [HΔA3 HBr]].
  handle_per_ctx_env_irrel.
  destruct (rel_sub_under_ctx_q_at HΓ HΔA3 Hσj HA _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
    as [s [s' [Hq [Hq' Hchain]]]].
  destruct (HBgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq')
    as [t0 [Ht0 [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain]]].
  assert (Hrel : rel_typ_sort B[q σ] (ρ ↦ c ⦂ t1) relevant)
    by (exists b1; split; [ exact Hb1 | destruct Hbchain as [[_ Hr _] _]; exact Hr ]).
  assert (P1 : Dom s ↦ c ⦂ t1 ≈ ρσ ↦ c' ⦂ t2 ∈ env_relΔA) by pairwise.
  assert (P2 : Dom ρσ ↦ c ⦂ t2 ≈ s ↦ c ⦂ t1 ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ⦂ t4 ≈ ρ'σ' ↦ c' ⦂ t3 ∈ env_relΔA) by pairwise.
  assert (P4 : Dom ρ'σ' ↦ c ⦂ t3 ≈ s' ↦ c' ⦂ t4 ∈ env_relΔA) by pairwise.
  destruct (HBl _ _ P1) as [x1 [x2 [l1 [Hx1 [Hx2 [Hl1 Hx]]]]]].
  destruct (HBl _ _ P2) as [y1 [y2 [l2 [Hy1 [Hy2 [Hl2 Hy]]]]]].
  destruct (HBr _ _ P3) as [z1 [z2 [l3 [Hz1 [Hz2 [Hl3 Hz]]]]]].
  destruct (HBr _ _ P4) as [u1 [u2 [l4 [Hu1 [Hu2 [Hl4 Hu]]]]]].
  (** All five realisers are [L]'s at [ρσ]. *)
  assert (R0 : domain_level_real t0 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s c ρσ c t1 t2); [ pairwise | exact Ht0 | exact Ht ]).
  assert (R1 : domain_level_real l1 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s c ρσ c t1 t2); [ pairwise | exact Hl1 | exact Ht ]).
  assert (R2 : domain_level_real l2 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 ρσ c ρσ c t2 t2); [ pairwise | exact Hl2 | exact Ht ]).
  assert (R3 : domain_level_real l3 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 s' c' ρσ c t4 t2); [ pairwise | exact Hl3 | exact Ht ]).
  assert (R4 : domain_level_real l4 = domain_level_real t)
    by (eapply (suniv_real_shift HA HL HΔA3 ρ'σ' c ρσ c t3 t2); [ pairwise | exact Hl4 | exact Ht ]).
  rewrite R0 in Hbchain; rewrite R1 in Hx; rewrite R2 in Hy; rewrite R3 in Hz; rewrite R4 in Hu.
  assert (x1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (y2 = b2) by (eapply functional_eval_exp; eassumption).
  assert (z1 = b3) by (eapply functional_eval_exp; eassumption).
  assert (u2 = b3) by (eapply functional_eval_exp; eassumption).
  subst.
  apply rel_chain_of_pair in Hx, Hy, Hz, Hu.
  set (j := us (domain_level_real t)) in *.
  assert (M1 : rel_chain (per_relevant_nonlevel (per_univ j)) ([b1; b2; b3; b4; x2]))
    by (merge_rel_chain Hbchain Hx b2).
  assert (M2 : rel_chain (per_relevant_nonlevel (per_univ j)) ([y1; b1; b2; b3; b4; x2]))
    by (merge_rel_chain M1 Hy b2).
  assert (M3 : rel_chain (per_relevant_nonlevel (per_univ j)) ([y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M2 Hz b3).
  assert (M4 : rel_chain (per_relevant_nonlevel (per_univ j)) ([u1; y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M3 Hu b3).
  split; [ exact Hrel |].
  split; [| split ].
  - exists b1, x2; split; [ eassumption | split; [ eassumption | pairwise ] ].
  - exists y1, z2; split; [ eassumption | split; [ eassumption | pairwise ] ].
  - exists u1, b4; split; [ eassumption | split; [ eassumption | pairwise ] ].
Qed.

(** The four values of a domain of the small [Π] at a level, at the
    realiser of the level's inner value: a type of the small universe there,
    a proposition, or a type of levels. *)
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
  - pose proof (rel_exp_of_level_sort_inversion HA) as [env_relΓ [HΓ HAgen]].
    eexists; eexists; [ eassumption |].
    intros * HΓ' * Hσj * Hρ Hev Hev' Ht.
    destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hc].
    econstructor; try eassumption.
    eapply rel_chain_mono; [| exact Hc ]; intros ? ? Hp; exact (per_univ_elem_of_level_sort _ _ _ Hp).
Qed.

(** A domain of the small [Π] at a level is a type of index [0]. *)
Lemma rel_type_of_domain_suniv : forall {Γ L A A' Srt},
    pi_domain_sort Type⟨L⟩ Srt ->
    Γ ⊨ A ≈ A' : Srt ->
    Γ ⊨ᵗ A ≈ A' at 0.
Proof.
  intros * [] HA;
    [ exact (rel_type_of_typ (rel_exp_suniv_tm_large (i := 0) HA)) | exact (rel_type_of_prop 0 HA)
    | exact (rel_type_of_level_sort 0 HA) ].
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
  set (j := us (domain_level_real t)) in *.
  (** The codomain obligations at a related pair of arguments, each tagged
      with the entry type of its own extension. *)
  assert (Hobl : forall c c', Dom c ≈ c' ∈ in_rel ->
             rel_typ_sort B[q σ] (ρ ↦ c ⦂ entry_type_value a1) relevant /\
             (exists b b',
                 ⟦ B[q σ] ⟧ ρ ↦ c ⦂ entry_type_value a1 ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ⦂ entry_type_value a2 ↘ b' /\
                 Dom b ≈ b' ∈ per_relevant_nonlevel (per_univ j)) /\
             (exists b b',
                 ⟦ B ⟧ ρσ ↦ c ⦂ entry_type_value a2 ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ⦂ entry_type_value a3 ↘ b' /\
                 Dom b ≈ b' ∈ per_relevant_nonlevel (per_univ j)) /\
             (exists b b',
                 ⟦ B' ⟧ ρ'σ' ↦ c ⦂ entry_type_value a3 ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ⦂ entry_type_value a4 ↘ b' /\
                 Dom b ≈ b' ∈ per_relevant_nonlevel (per_univ j))).
  { intros c c' Hc.
    pose proof (args_readable_of_chain Hachain Hc) as Hts.
    assert (H14 : DF a1 ≈ a4 ∈ per_univ_elem j ↘ in_rel) by pairwise.
    pose proof (entry_readable_of_elem H14 Hc) as [Hr1 Hr4].
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc Hr1 Hr4) as Hpair.
    exact (rel_exp_of_suniv_under_ctx_q HΓ' Hσj HAself HL HB _ _ _ _ _ _ _ _ _ _ t Hpair Hts Hev Hev' Ht). }
  assert (H11 : DF a1 ≈ a1 ∈ per_univ_elem j ↘ in_rel) by pairwise.
  assert (H22 : DF a2 ≈ a2 ∈ per_univ_elem j ↘ in_rel) by pairwise.
  assert (H33 : DF a3 ≈ a3 ∈ per_univ_elem j ↘ in_rel) by pairwise.
  assert (H44 : DF a4 ≈ a4 ∈ per_univ_elem j ↘ in_rel) by pairwise.
  apply (rel_chain_pi_relevant (i := j) (R := per_pi a2 a3 in_rel B ρσ B' ρ'σ')).
  - eapply per_univ_elem_pi_chain; [ exact Hachain | | | |];
      intros c c' Hc;
      destruct (Hobl _ _ Hc)
        as (Or & (b1 & b1' & E1 & E1' & H1) & (b2 & b2' & E2 & E2' & H2) & (b3 & b3' & E3 & E3' & H3));
      first [ exact Or
            | exists b1, b1'; split; [ exact E1 | split; [ exact E1' | exact (per_relevant_nonlevel_univ_rel H1) ] ]
            | exists b2, b2'; split; [ exact E2 | split; [ exact E2' | exact (per_relevant_nonlevel_univ_rel H2) ] ]
            | exists b3, b3'; split; [ exact E3 | split; [ exact E3' | exact (per_relevant_nonlevel_univ_rel H3) ] ] ].
  (** No value is a type of levels: each codomain, at an argument related
      to itself, is a value the obligations report as none. *)
  - apply (pi_not_level_code H11); intros c Hc.
    destruct (Hobl _ _ Hc) as (_ & (b & b' & E & _ & Hbb) & _).
    exists b; split; [ exact E | exact (per_relevant_nonlevel_left_nonlevel _ _ _ Hbb) ].
  - apply (pi_not_level_code H22); intros c Hc.
    destruct (Hobl _ _ Hc) as (_ & _ & (b & b' & E & _ & Hbb) & _).
    exists b; split; [ exact E | exact (per_relevant_nonlevel_left_nonlevel _ _ _ Hbb) ].
  - apply (pi_not_level_code H33); intros c Hc.
    destruct (Hobl _ _ Hc) as (_ & _ & (b & b' & _ & E & Hbb) & _).
    exists b'; split; [ exact E | exact (per_relevant_nonlevel_right_nonlevel _ _ _ Hbb) ].
  - apply (pi_not_level_code H44); intros c Hc.
    destruct (Hobl _ _ Hc) as (_ & _ & _ & (b & b' & _ & E & Hbb)).
    exists b'; split; [ exact E | exact (per_relevant_nonlevel_right_nonlevel _ _ _ Hbb) ].
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
        exists b b', ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\ ⟦ B' ⟧ ρ' ↦ c' ⦂ entry_type_value a' ↘ b' /\
                     Dom b ≈ b' ∈ per_prop) ->
    Dom ∀ₚᵈ a ρ B ≈ ∀ₚᵈ a' ρ' B' ∈ per_prop.
Proof.
  intros * Ha HB.
  constructor; [ reflexivity | reflexivity |].
  intros s.
  destruct (per_univ_then_per_top_typ Ha s) as [A A' HA HA' HEA].
  pose proof (per_bot_then_per_elem Ha (var_per_bot (n := s))) as Hvar.
  destruct (HB _ _ Hvar) as [b [b' [Hb [Hb' [_ _ Hbb]]]]].
  destruct (Hbb (S s)) as [P P' HP HP' HEP].
  apply (mk_type_reads_alike _ _ _ (∀ₚⁿ A P) (∀ₚⁿ A' P'));
    [ eapply read_typ_all; eassumption | eapply read_typ_all; eassumption | cbn [nf_erase]; congruence ].
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
             (exists b b', ⟦ B[q σ] ⟧ ρ ↦ c ⦂ entry_type_value a1 ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ⦂ entry_type_value a2 ↘ b' /\
                           Dom b ≈ b' ∈ per_prop) /\
             (exists b b', ⟦ B ⟧ ρσ ↦ c ⦂ entry_type_value a2 ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ⦂ entry_type_value a3 ↘ b' /\
                           Dom b ≈ b' ∈ per_prop) /\
             (exists b b', ⟦ B' ⟧ ρ'σ' ↦ c ⦂ entry_type_value a3 ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ⦂ entry_type_value a4 ↘ b' /\
                           Dom b ≈ b' ∈ per_prop)).
  { intros c c' Hc.
    pose proof (args_readable_of_chain Hachain Hc) as Hts.
    pose proof (entry_readable_of_elem Ha14 Hc) as [Hr1 Hr4].
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ _ _ Hρ Ha1 Ha14 Hc Hr1 Hr4) as Hpair.
    exact (rel_exp_of_prop_under_ctx_q HΓ' Hσj HAself HB _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev'). }
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
      * eapply rel_exp_under_ctx_pi_cong;
          [ apply rel_type_of_level_sort; exact HA0 | apply rel_type_of_level_sort; exact HA | exact HB ].
    + eapply rel_exp_under_ctx_pi_cong_small; eassumption.
  - destruct HU as [[? ->] | (? & ? & -> & ?)].
    + assert (HSrt : type_sort Srt)
        by (destruct HS; [ apply type_sort_universe | apply type_sort_prop | apply type_sort_level ]).
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
  (** The chain of the domains of the four closures, at the domain PER. *)
  assert (H12 : Dom a1 ≈ a2 ∈ per_univ i) by pairwise.
  destruct H12 as [R12 H12].
  assert (H21 : DF a2 ≈ a1 ∈ per_univ_elem i ↘ R12) by (symmetry; exact H12).
  assert (H41 : DF a4 ≈ a1 ∈ per_univ_elem i ↘ in_rel) by (symmetry; exact Houter).
  assert (E12 : R12 <~> in_rel) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ H21 H41).
  assert (Hbc' : rel_chain (per_univ_elem i in_rel) ([a1; a2; b3; b4]))
    by (eapply per_univ_chain_at_in; [ exact Hbc | | | exact (per_univ_elem_resp_iff H12 E12) ]; solve_in).
  assert (H1b4 : DF a1 ≈ b4 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H2b3 : DF a2 ≈ b3 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  pose proof (per_univ_elem_relevance _ _ _ _ (per_univ_elem_resp_iff H12 E12)) as Er12.
  pose proof (per_univ_elem_relevance _ _ _ _ H2b3) as Er23.
  assert (H34 : DF b3 ≈ b4 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  pose proof (per_univ_elem_relevance _ _ _ _ H34) as Er34.
  pose proof (per_univ_elem_relevance _ _ _ _ Hmid) as Er23'.
  (** The tails, related along [σ ≈ σ']. *)
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  (** The codomain's head PER, read at the right closure's domain value
      [b3] of [A'], is the one [per_pi] names, at the type's domain value
      [a3] of [A]: the two extensions are related. *)
  assert (Hmove : forall c c', Dom c ≈ c' ∈ in_rel ->
             per_head B B (ρσ ↦ c ⦂ entry_type_value a2) (ρ'σ' ↦ c' ⦂ entry_type_value b3) <~>
             per_head B B (ρσ ↦ c ⦂ entry_type_value a2) (ρ'σ' ↦ c' ⦂ entry_type_value a3)).
  { intros c c' Hc.
    pose proof (entry_readable_of_elem Hmid Hc) as [Hr2 Hr3].
    pose proof (entry_readable_of_elem H2b3 Hc) as [_ Hr3b].
    exact (per_head_codomain_resp HΓ HAself (rel_type_of_typ HB) _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hρσ Ha2 Ha3 Hmid Hc Hc Hc Hr2 Hr3b Hr2 Hr3). }
  apply (mk_rel_exp λᵈ a1 ρ M[q σ] λᵈ a2 ρσ M λᵈ b3 ρ'σ' M' λᵈ b4 ρ' M'[q σ']);
    [ apply eval_exp_fn; exact Ha1 | apply eval_exp_fn; exact Ha2 | apply eval_exp_fn; exact Hb3 | apply eval_exp_fn; exact Hb4 |].
  apply rel_chain_4; (constructor; [ cbn; congruence | cbn; congruence |]); intros c c' Hc;
    pose proof (args_readable_of_chain Hbc' Hc) as Hts;
    pose proof (entry_readable_of_elem H1b4 Hc) as [Hr1 Hr4];
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ _ _ Hρ Ha1 H1b4 Hc Hr1 Hr4)
      as Hpair;
    destruct (rel_exp_under_ctx_q HΓ' Hσj HAself HM HBrel _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
      as [[m1 [m2 [Hm1 [Hm2 Hm]]]]
            [[n1 [n2 [Hn1 [Hn2 Hn]]]] [p1 [p2 [Hp1 [Hp2 Hp]]]]]].
  - econstructor; [ apply eval_app_fn; exact Hm1 | apply eval_app_fn; exact Hm2 | apply (Hmove _ _ Hc); exact Hm ].
  - econstructor; [ apply eval_app_fn; exact Hn1 | apply eval_app_fn; exact Hn2 | apply (Hmove _ _ Hc); exact Hn ].
  - econstructor; [ apply eval_app_fn; exact Hp1 | apply eval_app_fn; exact Hp2 | apply (Hmove _ _ Hc); exact Hp ].
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
    the head PER of its own pair of arguments, and [per_head_codomain_resp]
    moves it. *)
Lemma rel_exp_under_ctx_app_cong : forall {Γ A} {i j : nat} {B M M' N N'},
    Γ ⊨ᵗ A ≈ A at j ->
    rel_type_relevant Γ A ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ M ≈ M' : Π A B ->
    Γ ⊨ N ≈ N' : A ->
    exp_scoped (List.length Γ) N ->
    Γ ⊨ M $ N ≈ M' $ N' : B[Id ,, N].
Proof.
  intros * HA HArel HB HM HN HNs.
  (** The type mentions [N] on both sides, so the type judgment is built from the
    reflexive-left form of [HN]; [HN] itself is used only for the term chain. *)
  pose proof (rel_exp_under_ctx_refl_left HN) as HNl.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ _]].
  destruct HM as [? ? k HMgen].
  destruct HN as [? ? l HNgen].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance HA HArel HB HNl HNs _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l' [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [_ Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ p2 ⦂ substituted_type) (ρ'σ' ↦ p3 ⦂ substituted_type)).
  split; [ exact Htyp |]; right.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** The domain is relevant. *)
  destruct (HArel _ HΓ _ _ Hρσ) as (a2' & Ha2' & Er2).
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
  (** Each link arrives in the head PER of its own argument pair, at the
      tags of the type's domain values; [per_head_codomain_resp] moves it to
      the instance's. *)
  assert (Hmove : forall x y, Dom x ≈ y ∈ RN -> Dom n2 ≈ y ∈ RN ->
             per_head B B (ρσ ↦ x ⦂ entry_type_value a2) (ρ'σ' ↦ y ⦂ entry_type_value a3) <~>
             per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ p3 ⦂ substituted_type)).
  { intros x y Hxy Huy.
    pose proof (entry_readable_of_elem Hmid Hxy) as [Rx Ry].
    exact (per_head_codomain_resp HΓ HA (rel_type_of_typ HB) _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hρσ Ha2 Ha3 Hmid Hxy Hn2p3 Huy Rx Ry (substituted_entry_readable _) (substituted_entry_readable _)). }
  apply rel_chain_4;
    [ apply (Hmove _ _ Hn12 Hn22); exact Hr
    | apply (Hmove _ _ Hn23 Hn23); exact Hs
    | apply (Hmove _ _ Hn34 Hn24); exact Hu ].
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
    is a proof, kept unevaluated, so every instantiating environment holds
    a kept proof at the head ([eval_sub_extend_proof]): [⋆ᵈ⟨N[σ], ρ⟩] along
    [σ ,, N[σ]], and [⋆ᵈ⟨N, ρσ⟩] along [Id ,, N] at the substituted
    environments.  Any two readable proofs are related at the head of a
    proposition ([per_head_proof]), and they read back as [N] is scoped.
    The shape is that of [rel_typ_of_instance]: two instantiations and the
    bridge between them, at the pair of kept proofs crossing from one to the
    other.  The element PER is the head PER of [B] at the kept proofs of
    the second instantiation. *)
Lemma rel_typ_of_instance_prop : forall {Γ A} {i : nat} {B N},
    Γ ⊨ A : Propₘ ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ N ≈ N : A ->
    exp_scoped (List.length Γ) N ->
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
          Definitions.rel_typ i B[Id,,N] σ ρ ρσ B[Id,,N] σ' ρ' ρ'σ'
            (per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type)).
Proof.
  intros * HA HB HN HNs * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ [HΓ HAgen]].
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓA [HΓA HBgen]].
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN HNs HNs) as HidN.
  rewrite exp_sub_id in HidN.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  pose proof Hachain as (_ & [Hr2 Hr3 _] & _).
  pose proof (head_propositional_of_value (Γ := Γ) Ha2 Hr2) as Hp2.
  pose proof (head_propositional_of_value (Γ := Γ) Ha3 Hr3) as Hp3.
  (** *** The Kept Proofs

      [N] is scoped by [Γ], and [N[σ]], [N[σ']] by [Γ'], so the kept
      proofs read back. *)
  pose proof Hσj as [? _ ? _ _ Hσs].
  assert (HNσ : exp_scoped (List.length Γ') N[σ])
    by (eapply exp_scoped_sub; [ exact HNs | intros x Hx; exact (proj1 (Hσs x Hx)) ]).
  destruct (per_ctx_env_kept_proof_readable _ _ _ N[σ] HΓ' (exp_scoped_free_bound _ _ HNσ) _ _ Hρ) as [Rp1 _].
  destruct (per_ctx_env_kept_proof_readable _ _ _ N HΓ (exp_scoped_free_bound _ _ HNs) _ _ Hρσ) as [Rp2 Rp3].
  (** *** The Two Instantiations

      The first along [σ ,, N[σ]], its outer values rewritten into the
      goal's spelling. *)
  destruct (HBgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN HNs HNs) _ _ _ _ Hρ
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev Hp2)
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev' Hp3))
    as [t1 tA2 tA3 t4 Ht1 HtA2 HtA3 Ht4 HtAchain].
  apply rel_chain_relevant_univ in HtAchain.
  rewrite <- exp_sub_extend_sub in Ht1, Ht4.
  (** The second along [Id,,N], whose results are the extensions of the
      restamped environments; read at the extensions of the environments
      themselves ([rel_type_body_of_retagged]). *)
  destruct (rel_exp_of_prop_inversion_simple_at HΓ HA _ _ (per_ctx_env_restamp HΓ _ _ Hρσ))
    as (a2r & a3r & Ha2r & Ha3r & [Hl2r Hr3r _]).
  pose proof (head_propositional_of_value (Γ := Γ) Ha2r Hl2r) as Hp2r.
  pose proof (head_propositional_of_value (Γ := Γ) Ha3r Hr3r) as Hp3r.
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  pose proof (per_ctx_env_of_typ HΓ (rel_type_of_prop 0 HA)) as HΓA0.
  assert (EA : env_relΓA <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hext : Dom ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type ≈ ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type ∈ env_relΓA).
  { apply EA; apply per_env_extend_intro';
      [ exact Hρσ | eapply per_head_proof; [ exact Ha2 | exact Hr2 | exact Rp2 | exact Rp3 ]
      | apply substituted_entry_readable | apply substituted_entry_readable ]. }
  destruct (rel_type_body_of_retagged HΓA HBgen _ _ HΓ _ _ HidN ρσ ρ'σ'
              (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type) Hρσ
              (eval_sub_extend_proof _ _ _ _ _ _ Hid2 Hp2r) (eval_sub_extend_proof _ _ _ _ _ _ Hid3 Hp3r) Hext)
    as [t2 tB2 tB3 t3 Ht2 HtB2 HtB3 Ht3 HtBchain].
  apply rel_chain_relevant_univ in HtBchain.
  (** *** The Bridge

      [B] at the kept proof of the first instantiation against the one of
      the second, at the substituted pair. *)
  assert (Hx : Dom ρσ ↦ ⋆ᵈ⟨N[σ], ρ⟩ ⦂ substituted_type ≈ ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type
                 ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ exact Hρσ | eapply per_head_proof; [ exact Ha2 | exact Hr2 | exact Rp1 | exact Rp3 ]
        | apply substituted_entry_readable | apply substituted_entry_readable ]).
  destruct (rel_exp_of_typ_extend_simple HΓ (rel_type_of_prop 0 HA) HB _ _ Hx) as [d1 [d2 [Hd1 [Hd2 Hd]]]].
  assert (d1 = tA2) as -> by (eapply functional_eval_exp; [ exact Hd1 | exact HtA2 ]).
  assert (d2 = tB3) as -> by (eapply functional_eval_exp; [ exact Hd2 | exact HtB3 ]).
  assert (Hbridge : rel_chain (per_univ i) ([tA2; tB3]))
    by (apply rel_chain_of_pair; exact Hd).
  assert (Hchain1 : rel_chain (per_univ i) ([t1; tA2; tB3; t4]))
    by (merge_rel_chain HtAchain Hbridge tA2).
  assert (Hall : rel_chain (per_univ i) ([t1; t2; tB2; tB3; t3; t4]))
    by (merge_rel_chain Hchain1 HtBchain tB3).
  (** Anchored at the head PER of the second instantiation. *)
  assert (Hmid : Dom tB2 ≈ tB3 ∈ per_univ i) by pairwise.
  pose proof (per_univ_elem_at_head HtB2 HtB3 Hmid) as Hanchor.
  assert (HallR : rel_chain (per_univ_elem i (per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type)
                                                       (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type)))
                    ([t1; t2; tB2; tB3; t3; t4]))
    by (eapply per_univ_chain_at_in; [ exact Hall | | | exact Hanchor ]; solve_in).
  exists a1, a2, a3, a4.
  do 5 (split; [ assumption |]).
  apply (mk_rel_exp t1 t2 t3 t4); try eassumption.
  solve_rel_chain.
Qed.

(** Application of a function of a proof: the argument is not evaluated,
    and every link applies the two functions to the two kept proofs of its
    environments, [⋆ᵈ⟨N[σ], ρ⟩], [⋆ᵈ⟨N, ρσ⟩], [⋆ᵈ⟨N', ρ'σ'⟩] and
    [⋆ᵈ⟨N'[σ'], ρ'⟩] in turn. *)
Lemma rel_exp_under_ctx_app_cong_prop : forall {Γ A} {i : nat} {B M M' N N'},
    Γ ⊨ A : Propₘ ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ M ≈ M' : Π A B ->
    Γ ⊨ N ≈ N' : A ->
    exp_scoped (List.length Γ) N ->
    exp_scoped (List.length Γ) N' ->
    Γ ⊨ M $ N ≈ M' $ N' : B[Id ,, N].
Proof.
  intros * HA HB HM HN HNs HN's.
  pose proof (rel_exp_under_ctx_refl_left HN) as HNl.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ [HΓ _]].
  destruct HM as [? ? k HMgen].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance_prop HA HB HNl HNs _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Hachain Htyp]]]]]]]]].
  exists (per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type)).
  split; [ exact Htyp |]; right.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  pose proof Hachain as (_ & H23 & _).
  pose proof (per_univ_elem_of_prop k _ _ H23) as Hmid.
  destruct H23 as [Er2 Er3 _].
  (** *** The Kept Proofs

      The four arguments and the instance's, all readable as the arguments
      are scoped. *)
  pose proof Hσj as [? _ ? _ _ Hσs].
  assert (HNσ : exp_scoped (List.length Γ') N[σ])
    by (eapply exp_scoped_sub; [ exact HNs | intros x Hx; exact (proj1 (Hσs x Hx)) ]).
  assert (HN'σ' : exp_scoped (List.length Γ') N'[σ'])
    by (eapply exp_scoped_sub; [ exact HN's | intros x Hx; exact (proj2 (Hσs x Hx)) ]).
  destruct (per_ctx_env_kept_proof_readable _ _ _ N[σ] HΓ' (exp_scoped_free_bound _ _ HNσ) _ _ Hρ) as [Rp1 _].
  destruct (per_ctx_env_kept_proof_readable _ _ _ N'[σ'] HΓ' (exp_scoped_free_bound _ _ HN'σ') _ _ Hρ) as [_ Rp4].
  destruct (per_ctx_env_kept_proof_readable _ _ _ N HΓ (exp_scoped_free_bound _ _ HNs) _ _ Hρσ) as [Rp2 Rp2'].
  destruct (per_ctx_env_kept_proof_readable _ _ _ N' HΓ (exp_scoped_free_bound _ _ HN's) _ _ Hρσ) as [_ Rp3].
  (** Each link arrives in the head PER of its own pair of proofs, at the
      tags of the type's domain values; [per_head_codomain_resp] moves it
      to the instance's. *)
  assert (Hmove : forall x y, proof_readable x -> proof_readable y ->
             per_head B B (ρσ ↦ x ⦂ entry_type_value a2) (ρ'σ' ↦ y ⦂ entry_type_value a3) <~>
             per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type)).
  { intros x y Rx Ry.
    assert (Hxy : Dom x ≈ y ∈ per_proof) by (split; assumption).
    pose proof (entry_readable_of_elem Hmid Hxy) as [Ex Ey].
    exact (per_head_codomain_resp HΓ (rel_type_of_prop 0 HA) (rel_type_of_typ HB) _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hρσ Ha2 Ha3 Hmid Hxy (conj Rp2 Rp2') (conj Rp2 Ry) Ex Ey
             (substituted_entry_readable _) (substituted_entry_readable _)). }
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
  destruct (pi_elements_app _ _ _ _ _ _ Hpi1 _ _ (conj Rp1 Rp2)) as [r1 r2 Hr1 Hr2 Hr].
  destruct (pi_elements_app _ _ _ _ _ _ Hpi2 _ _ (conj Rp2 Rp3)) as [s1 s2 Hs1 Hs2 Hs].
  destruct (pi_elements_app _ _ _ _ _ _ Hpi3 _ _ (conj Rp3 Rp4)) as [u1 u2 Hu1 Hu2 Hu].
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
  apply rel_chain_4;
    [ apply (Hmove _ _ Rp1 Rp2); exact Hr | apply (Hmove _ _ Rp2 Rp3); exact Hs | apply (Hmove _ _ Rp3 Rp4); exact Hu ].
Qed.

(** The codomain of a [∀] at an argument is a proposition: its instance
    along [Id ,, N], which is built from valid parts. *)
Lemma rel_exp_under_ctx_instance : forall {Γ A Srt B B' C N},
    ⊨ Γ ->
    type_sort Srt ->
    Γ ⊨ A : Srt ->
    Γ ▹ A ⊨ B ≈ B' : C ->
    Γ ⊨ N : A ->
    exp_scoped (List.length Γ) N ->
    Γ ⊨ B[Id,,N] ≈ B'[Id,,N] : C[Id,,N].
Proof.
  intros * HΓ HS HA HB HN HNs.
  eapply rel_exp_under_ctx_gsub; [| exact HB ].
  eapply gsub_ass; [ apply gsub_id; exact HΓ | exact HS | exact HA | rewrite exp_sub_id; exact HN | exact HNs ].
Qed.

End Fixed_GCtx.

(** Application of a function or of a proof of a [∀]. *)
Lemma sem_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : a_pi r A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : A ->
     exp_scoped (List.length Γ) N ->
     exp_scoped (List.length Γ) N' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N ≈ M' $ N' : B[Id,,N] ).
Proof.
  intros * HA HS HB HM HN HNs HN's; sem_intro; [ assumption |].
  destruct r; cbn [relevance_sort] in *.
  - destruct HS as [k | |].
    + exact (rel_exp_under_ctx_app_cong (rel_type_of_typ HA) (rel_type_relevant_of_typ HA) HB HM HN HNs).
    + exact (rel_exp_under_ctx_app_cong_prop HA HB HM HN HNs HN's).
    + exact (rel_exp_under_ctx_app_cong (rel_type_of_level_sort 0 HA) (rel_type_relevant_of_level_sort HA) HB HM HN HNs).
  - apply rel_exp_under_ctx_proof.
    match goal with HΓ : ⊨ Γ |- _ =>
      exact (rel_exp_under_ctx_instance HΓ HS HA HB (rel_exp_under_ctx_refl_left HN) HNs) end.
Qed.

Lemma sem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : a_pi r A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     exp_scoped (List.length Γ) N ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N : B[Id,,N] ).
Proof.
  intros * HA HS HB HM HN HNs; eapply sem_exp_eq_app_cong; [ exact HA | exact HS | exact HB | exact HM | exact HN | exact HNs | exact HNs ].
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
    here is [M] at the crossing pair of arguments.  A second bridge joins the
    redex's second value, [M] at the closure's tag [entry_type_value a2], to the
    inner instantiation's, at [substituted_type].  Merges then select the goal's
    four values, all in the canonical head PER.  The domain is any relevant
    type: of a universe, or of [LevelSort]. *)
Lemma rel_exp_under_ctx_pi_beta : forall {Γ A B M N} {i j : nat},
    Γ ⊨ᵗ A ≈ A at j ->
    rel_type_relevant Γ A ->
    Γ ▹ A ⊨ B : Typeω@i ->
    Γ ▹ A ⊨ M : B ->
    Γ ⊨ N : A ->
    exp_scoped (List.length Γ) N ->
    Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N].
Proof.
  intros * HA HArel HB HM HN HNs.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ HAgen]].
  pose proof HA as HAt.
  pose proof (per_ctx_env_of_typ HΓ HAt) as HΓA.
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN HNs HNs) as HidN.
  rewrite exp_sub_id in HidN.
  assert (HBrel : forall ρ ρ' R, EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R -> rel_typ_sort B ρ relevant)
    by (intros * HR Hρ; exact (rel_exp_of_typ_relevant_at HR HB _ _ Hρ)).
  pose proof HM as [env_relΓAM HΓAM k HMgen].
  assert (EAM : env_relΓAM <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance HA HArel HB HN HNs _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l [RN [a1 [a2 [a3 [a4 [n1 [n2 [n3 [n4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hn1 [Hn2 [Hn3 [Hn4 [Hnchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type)).
  split; [ exact Htyp |]; right.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  pose proof (head_not_propositional_of_relevant (e := ce_ass A) HΓ eq_refl HA HArel _ _ Hρσ) as [Hnp2 Hnp3].
  pose proof (head_not_propositional_of_relevant (e := ce_ass A) HΓ eq_refl HA HArel _ _
                (per_ctx_env_restamp HΓ _ _ Hρσ)) as [Hnp2r Hnp3r].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  (** The argument pairs the links are read at. *)
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn13 : Dom n1 ≈ n3 ∈ RN) by pairwise.
  assert (Hn14 : Dom n1 ≈ n4 ∈ RN) by pairwise.
  assert (Hn22 : Dom n2 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn24 : Dom n2 ≈ n4 ∈ RN) by pairwise.
  (** *** The Redex

      [rel_exp_under_ctx_q] at the argument pair [n1 ≈ n2], with the
      closures' tags on the left: the values of their domains.  Its
      element PER is moved to the instance's ([per_head_codomain_resp]). *)
  pose proof (entry_readable_of_elem Houter Hn12) as [Rn1a1 _].
  pose proof (entry_readable_of_elem Houter Hn22) as [Rn2a1 _].
  pose proof (entry_readable_of_elem Hmid Hn12) as [Rn1a2 _].
  pose proof (entry_readable_of_elem Hmid Hn22) as [Rn2a2 _].
  pose proof (per_env_extend_sub_intro HΓ' Hσj HAt _ _ _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hn12
                Rn1a1 (substituted_entry_readable _)) as Hpair.
  assert (Hts : args_readable_at n1 n2
                  ([entry_type_value a1; entry_type_value a2; substituted_type; substituted_type]))
    by (repeat constructor; first [ assumption | apply substituted_entry_readable ]).
  destruct (rel_exp_under_ctx_q HΓ' Hσj HAt HM HBrel _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
    as [[v1 [v2 [Hv1 [Hv2 Hv]]]] _].
  clear Hpair.
  assert (Hlink1 : Dom v1 ≈ v2 ∈ per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type))
    by (apply (per_head_codomain_resp HΓ HAt (rel_type_of_typ HB) _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 Hρσ Ha2 Ha3 Hmid Hn12 Hn23 Hn22 Rn1a2 (substituted_entry_readable _)
                 (substituted_entry_readable _) (substituted_entry_readable _)); exact Hv).
  apply rel_chain_of_pair in Hlink1.
  (** *** The Outer Instantiation

      Along [σ ,, N[σ] ≈ σ' ,, N[σ']], whose right-hand outer value is the goal's
      fourth once [exp_sub_extend_sub] has rewritten it. *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN HNs HNs) _ _ _ _ Hρ
                  (eval_sub_extend _ _ _ _ _ _ _ Hev Hnp2 Hn1)
                  (eval_sub_extend _ _ _ _ _ _ _ Hev' Hnp3 Hn4))
    as [RA [HAtyp HAexp]].
  apply (rel_exp_or_prop_relevant HAtyp
           (HBrel _ _ _ HΓA (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hn14)
                               (substituted_entry_readable _) (substituted_entry_readable _)))) in HAexp.
  destruct HAtyp as [cA1 cA2 cA3 cA4 HcA1 HcA2 HcA3 HcA4 HcAchain].
  destruct HAexp as [h1 h2 h3 h4 Hh1 Hh2 Hh3 Hh4 Hhchain].
  rewrite <- exp_sub_extend_sub in Hh4.
  destruct (per_head_anchor Hcod n1 n4 n2 n3 Hn14 Hn23 Hn24)
    as [e1 [e2 [He1 [He2 HanchorA]]]].
  assert (e1 = cA2) as -> by (eapply functional_eval_exp; [ exact He1 | exact HcA2 ]).
  assert (e2 = cA3) as -> by (eapply functional_eval_exp; [ exact He2 | exact HcA3 ]).
  retype_rel_chain HcAchain HanchorA Hhchain.
  (** *** The Inner Instantiation

      Along [Id ,, N ≈ Id ,, N] at the substituted environments, whose results
      are the extensions of the restamped environments; read at the
      extensions of the environments themselves ([rel_exp_body_of_retagged]).
      Its second value is the goal's second and its right-hand outer value
      the goal's third. *)
  assert (Hext : Dom ρσ ↦ n2 ⦂ substituted_type ≈ ρ'σ' ↦ n3 ⦂ substituted_type ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ exact Hρσ | exact (per_head_of Ha2 Ha3 Hmid Hn23)
        | apply substituted_entry_readable | apply substituted_entry_readable ]).
  destruct (rel_exp_body_of_retagged HΓAM HMgen _ _ HΓ _ _ HidN ρσ ρ'σ'
              (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type) Hρσ
              (eval_sub_extend _ _ _ _ _ _ _ Hid2 Hnp2r Hn2) (eval_sub_extend _ _ _ _ _ _ _ Hid3 Hnp3r Hn3)
              (proj2 (EAM _ _) Hext))
    as [RB [HBtyp HBexp]].
  apply (rel_exp_or_prop_relevant HBtyp (HBrel _ _ _ HΓA Hext)) in HBexp.
  destruct HBtyp as [cB1 cB2 cB3 cB4 HcB1 HcB2 HcB3 HcB4 HcBchain].
  destruct HBexp as [g1 g2 g3 g4 Hg1 Hg2 Hg3 Hg4 Hgchain].
  destruct (per_head_anchor Hcod n2 n3 n2 n3 Hn23 Hn23 Hn23)
    as [f1 [f2 [Hf1 [Hf2 HanchorB]]]].
  assert (f1 = cB2) as -> by (eapply functional_eval_exp; [ exact Hf1 | exact HcB2 ]).
  assert (f2 = cB3) as -> by (eapply functional_eval_exp; [ exact Hf2 | exact HcB3 ]).
  retype_rel_chain HcBchain HanchorB Hgchain.
  (** The goal's second value is the redex's, [M] at the closure's tag, and
      this instantiation's second is [M] at [substituted_type]: [M] relates
      the two, and the head PER moves along the chain of extensions ending
      at the instance's pair. *)
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend A A env_relΓ)) by (eapply per_env_PER; exact HΓA).
  assert (H22 : DF a2 ≈ a2 ∈ per_univ_elem l ↘ RN) by (etransitivity; [ exact Hmid | symmetry; exact Hmid ]).
  assert (Htag : Dom ρσ ↦ n2 ⦂ entry_type_value a2 ≈ ρσ ↦ n2 ⦂ substituted_type ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ etransitivity; [ exact Hρσ | symmetry; exact Hρσ ] | exact (per_head_of Ha2 Ha2 H22 Hn22)
        | exact Rn2a2 | apply substituted_entry_readable ]).
  destruct (rel_exp_under_ctx_extend_simple HΓ HAt HM _ _ Htag) as [Hp' | [w1 [w2 [Hw1 [Hw2 Hw]]]]].
  { exfalso; destruct (HBrel _ _ _ HΓA Htag) as (x & Ex & Hx).
    destruct Hp' as (y & Ey & Hy); functional_eval_rewrite_clear; congruence. }
  assert (w1 = v2) as -> by (eapply functional_eval_exp; [ exact Hw1 | exact Hv2 ]).
  assert (w2 = g2) as -> by (eapply functional_eval_exp; [ exact Hw2 | exact Hg2 ]).
  assert (Hlink2 : Dom v2 ≈ g2 ∈ per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type)).
  { assert (Hch : rel_chain (per_env_extend A A env_relΓ)
                    ([ρσ ↦ n2 ⦂ entry_type_value a2; ρσ ↦ n2 ⦂ substituted_type;
                      ρσ ↦ n2 ⦂ substituted_type; ρ'σ' ↦ n3 ⦂ substituted_type]))
      by (apply rel_chain_4; [ exact Htag | etransitivity; [ symmetry |]; exact Htag | exact Hext ]).
    pose proof (per_head_of_type_resp HΓA (rel_type_of_typ HB) _ _ _ _ Hch) as Hr.
    apply Hr; exact Hw. }
  apply rel_chain_of_pair in Hlink2.
  (** *** The Bridge

      [M] at the pair of arguments that crosses from the one instantiation to the
      other; the codomain there is relevant. *)
  assert (Hcross : Dom ρσ ↦ n1 ⦂ substituted_type ≈ ρ'σ' ↦ n3 ⦂ substituted_type ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ exact Hρσ | exact (per_head_of Ha2 Ha3 Hmid Hn13)
        | apply substituted_entry_readable | apply substituted_entry_readable ]).
  destruct (rel_exp_under_ctx_extend_simple HΓ HAt HM _ _ Hcross)
    as [Hp | [b1 [b2 [Hb1 [Hb2 Hb]]]]].
  { exfalso; destruct (HBrel _ _ _ HΓA Hcross) as (x & Ex & Hx).
    destruct Hp as (y & Ey & Hy); functional_eval_rewrite_clear; congruence. }
  assert (b1 = h2) as -> by (eapply functional_eval_exp; [ exact Hb1 | exact Hh2 ]).
  assert (b2 = g3) as -> by (eapply functional_eval_exp; [ exact Hb2 | exact Hg3 ]).
  assert (Hbridge : Dom h2 ≈ g3 ∈ per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type))
    by (apply (per_head_of_args Hcod n1 n3 n2 n3 Hn13 Hn23 Hn23); exact Hb).
  apply rel_chain_of_pair in Hbridge.
  (** *** The Four Values *)
  assert (Hmerge1 : rel_chain (per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type)) ([h4; g3]))
    by (merge_rel_chain Hhchain Hbridge h2).
  assert (Hmerge2 : rel_chain (per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type)) ([g2; g4; h4]))
    by (merge_rel_chain Hmerge1 Hgchain g3).
  (** The redex takes a relevant argument on both sides: the values of [A]
      along [σ] are relevant, as [A] is at the substituted environments. *)
  destruct (HArel _ HΓ _ _ Hρσ) as (a2' & Ha2' & Er2).
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [x1 x2 x3 x4 Hx1 Hx2 Hx3 Hx4 Hxchain].
  assert (x1 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (x2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hx12 : Dom a1 ≈ a2 ∈ per_univ j) by pairwise.
  destruct Hx12 as [Rx Hx12].
  assert (Er1 : domain_relevance a1 = relevant) by (rewrite (per_univ_elem_relevance _ _ _ _ Hx12); exact Er2).
  assert (Hmerge3 : rel_chain (per_head B B (ρσ ↦ n2 ⦂ substituted_type) (ρ'σ' ↦ n3 ⦂ substituted_type))
                      ([v2; g2; g4; h4]))
    by (merge_rel_chain Hlink2 Hmerge2 g2).
  apply (mk_rel_exp v1 v2 g4 h4);
    [ eapply eval_exp_app; [ apply eval_exp_fn; exact Ha1 | exact Er1 | exact Hn1 | apply eval_app_fn; exact Hv1 ]
    | eapply eval_exp_app; [ apply eval_exp_fn; exact Ha2 | exact Er2 | exact Hn2 | apply eval_app_fn; exact Hv2 ]
    | exact Hg4
    | exact Hh4
    |].
  merge_rel_chain Hlink1 Hmerge3 v2.
Qed.

(** β for a function of a proof.  The argument is kept unevaluated: the
    redex applies the two closures to [⋆ᵈ⟨N[σ], ρ⟩] and [⋆ᵈ⟨N, ρσ⟩], the
    outer instantiation of [M] extends by [⋆ᵈ⟨N[σ], ρ⟩] and
    [⋆ᵈ⟨N[σ'], ρ'⟩], the inner one by [⋆ᵈ⟨N, ρσ⟩] and [⋆ᵈ⟨N, ρ'σ'⟩].  Any
    two readable proofs are related at the head of a proposition, so the
    shape is that of [rel_exp_under_ctx_pi_beta], each move of a head PER
    between argument pairs by [per_head_codomain_resp]. *)
Lemma rel_exp_under_ctx_pi_beta_prop : forall {Γ A B M N} {i : nat},
    Γ ⊨ A : Propₘ ->
    Γ ▹ A ⊨ B : Typeω@i ->
    Γ ▹ A ⊨ M : B ->
    Γ ⊨ N : A ->
    exp_scoped (List.length Γ) N ->
    Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N].
Proof.
  intros * HA HB HM HN HNs.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (rel_type_of_prop i HA) as HAt.
  pose proof (per_ctx_env_of_typ HΓ HAt) as HΓA.
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN HNs HNs) as HidN.
  rewrite exp_sub_id in HidN.
  assert (HBrel : forall ρ ρ' R, EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R -> rel_typ_sort B ρ relevant)
    by (intros * HR Hρ; exact (rel_exp_of_typ_relevant_at HR HB _ _ Hρ)).
  pose proof HM as [env_relΓAM HΓAM k HMgen].
  assert (EAM : env_relΓAM <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend A A env_relΓ)) by (eapply per_env_PER; exact HΓA).
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance_prop HA HB HN HNs _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Hachain Htyp]]]]]]]]].
  exists (per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type)).
  split; [ exact Htyp |]; right.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  pose proof Hachain as ([Hr1 _ _] & [Hr2 Hr3 _] & _).
  assert (Ha14 : DF a1 ≈ a4 ∈ per_univ_elem i ↘ per_proof) by (apply per_univ_elem_of_prop; pairwise).
  assert (Ha23 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ per_proof) by (apply per_univ_elem_of_prop; pairwise).
  pose proof (head_propositional_of_value (Γ := Γ) Ha2 Hr2) as Hp2.
  pose proof (head_propositional_of_value (Γ := Γ) Ha3 Hr3) as Hp3.
  destruct (rel_exp_of_prop_inversion_simple_at HΓ HA _ _ (per_ctx_env_restamp HΓ _ _ Hρσ))
    as (a2r & a3r & Ha2r & Ha3r & [Hl2r Hr3r _]).
  pose proof (head_propositional_of_value (Γ := Γ) Ha2r Hl2r) as Hp2r.
  pose proof (head_propositional_of_value (Γ := Γ) Ha3r Hr3r) as Hp3r.
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  (** *** The Kept Proofs *)
  pose proof Hσj as [? _ ? _ _ Hσs].
  assert (HNσ : exp_scoped (List.length Γ') N[σ])
    by (eapply exp_scoped_sub; [ exact HNs | intros x Hx; exact (proj1 (Hσs x Hx)) ]).
  assert (HNσ' : exp_scoped (List.length Γ') N[σ'])
    by (eapply exp_scoped_sub; [ exact HNs | intros x Hx; exact (proj2 (Hσs x Hx)) ]).
  destruct (per_ctx_env_kept_proof_readable _ _ _ N[σ] HΓ' (exp_scoped_free_bound _ _ HNσ) _ _ Hρ) as [Rp1 _].
  destruct (per_ctx_env_kept_proof_readable _ _ _ N[σ'] HΓ' (exp_scoped_free_bound _ _ HNσ') _ _ Hρ) as [_ Rp4].
  destruct (per_ctx_env_kept_proof_readable _ _ _ N HΓ (exp_scoped_free_bound _ _ HNs) _ _ Hρσ) as [Rp2 Rp3].
  (** Any head PER of [B] at a pair of readable proofs, at readable tags,
      is the instance's. *)
  assert (Hmove : forall x y t t', proof_readable x -> proof_readable y ->
             entry_readable (de_term x t) -> entry_readable (de_term y t') ->
             per_head B B (ρσ ↦ x ⦂ t) (ρ'σ' ↦ y ⦂ t') <~>
             per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type)).
  { intros x y t t' Rx Ry Ex Ey.
    exact (per_head_codomain_resp HΓ HAt (rel_type_of_typ HB) _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hρσ Ha2 Ha3 Ha23 (conj Rx Ry) (conj Rp2 Rp3) (conj Rp2 Ry) Ex Ey
             (substituted_entry_readable _) (substituted_entry_readable _)). }
  assert (Hext : Dom ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type ≈ ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type
                   ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ exact Hρσ | eapply per_head_proof; [ exact Ha2 | exact Hr2 | exact Rp2 | exact Rp3 ]
        | apply substituted_entry_readable | apply substituted_entry_readable ]).
  (** *** The Redex

      [rel_exp_under_ctx_q] at the pair of kept proofs [⋆ᵈ⟨N[σ], ρ⟩] and
      [⋆ᵈ⟨N, ρσ⟩], with the closures' tags on the left. *)
  pose proof (entry_readable_of_elem Ha14 (conj Rp1 Rp2)) as [Re1a1 _].
  pose proof (entry_readable_of_elem Ha14 (conj Rp2 Rp2)) as [Re2a1 _].
  pose proof (entry_readable_of_elem Ha23 (conj Rp1 Rp2)) as [Re1a2 _].
  pose proof (entry_readable_of_elem Ha23 (conj Rp2 Rp2)) as [Re2a2 _].
  pose proof (per_env_extend_sub_intro HΓ' Hσj HAt _ _ _ _ _ _ _ _ _ _ Hρ Ha1 Ha14 (conj Rp1 Rp2)
                Re1a1 (substituted_entry_readable _)) as Hpair.
  assert (Hts : args_readable_at ⋆ᵈ⟨N[σ], ρ⟩ ⋆ᵈ⟨N, ρσ⟩
                  ([entry_type_value a1; entry_type_value a2; substituted_type; substituted_type]))
    by (repeat constructor; first [ assumption | apply substituted_entry_readable ]).
  destruct (rel_exp_under_ctx_q HΓ' Hσj HAt HM HBrel _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
    as [[v1 [v2 [Hv1 [Hv2 Hv]]]] _].
  clear Hpair.
  assert (Hlink1 : Dom v1 ≈ v2 ∈ per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type))
    by (apply (Hmove _ _ _ _ Rp1 Rp2 Re1a2 (substituted_entry_readable _)); exact Hv).
  apply rel_chain_of_pair in Hlink1.
  (** *** The Outer Instantiation

      Along [σ ,, N[σ] ≈ σ' ,, N[σ']]. *)
  assert (Hext14 : Dom ρσ ↦ ⋆ᵈ⟨N[σ], ρ⟩ ⦂ substituted_type ≈ ρ'σ' ↦ ⋆ᵈ⟨N[σ'], ρ'⟩ ⦂ substituted_type
                     ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ exact Hρσ | eapply per_head_proof; [ exact Ha2 | exact Hr2 | exact Rp1 | exact Rp4 ]
        | apply substituted_entry_readable | apply substituted_entry_readable ]).
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN HNs HNs) _ _ _ _ Hρ
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev Hp2)
                  (eval_sub_extend_proof _ _ _ _ _ _ Hev' Hp3))
    as [RA [HAtyp HAexp]].
  apply (rel_exp_or_prop_relevant HAtyp (HBrel _ _ _ HΓA Hext14)) in HAexp.
  destruct HAtyp as [cA1 cA2 cA3 cA4 HcA1 HcA2 HcA3 HcA4 HcAchain].
  destruct HAexp as [h1 h2 h3 h4 Hh1 Hh2 Hh3 Hh4 Hhchain].
  rewrite <- exp_sub_extend_sub in Hh4.
  assert (HcA23 : Dom cA2 ≈ cA3 ∈ per_univ k) by (eexists; pairwise).
  pose proof (per_univ_elem_resp_iff (per_univ_elem_at_head HcA2 HcA3 HcA23)
                (Hmove _ _ _ _ Rp1 Rp4 (substituted_entry_readable _) (substituted_entry_readable _))) as HanchorA.
  retype_rel_chain HcAchain HanchorA Hhchain.
  (** *** The Inner Instantiation

      Along [Id ,, N ≈ Id ,, N] at the substituted environments, read at
      the extensions of the environments themselves
      ([rel_exp_body_of_retagged]). *)
  destruct (rel_exp_body_of_retagged HΓAM HMgen _ _ HΓ _ _ HidN ρσ ρ'σ'
              (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type) Hρσ
              (eval_sub_extend_proof _ _ _ _ _ _ Hid2 Hp2r) (eval_sub_extend_proof _ _ _ _ _ _ Hid3 Hp3r)
              (proj2 (EAM _ _) Hext))
    as [RB [HBtyp HBexp]].
  apply (rel_exp_or_prop_relevant HBtyp (HBrel _ _ _ HΓA Hext)) in HBexp.
  destruct HBtyp as [cB1 cB2 cB3 cB4 HcB1 HcB2 HcB3 HcB4 HcBchain].
  destruct HBexp as [g1 g2 g3 g4 Hg1 Hg2 Hg3 Hg4 Hgchain].
  assert (HcB23 : Dom cB2 ≈ cB3 ∈ per_univ k) by (eexists; pairwise).
  pose proof (per_univ_elem_at_head HcB2 HcB3 HcB23) as HanchorB.
  retype_rel_chain HcBchain HanchorB Hgchain.
  (** *** The Bridges

      [M] at the pair of kept proofs crossing from the outer instantiation
      to the inner one, and at the redex's tag against the inner one's. *)
  assert (Hcross : Dom ρσ ↦ ⋆ᵈ⟨N[σ], ρ⟩ ⦂ substituted_type ≈ ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type
                     ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ exact Hρσ | eapply per_head_proof; [ exact Ha2 | exact Hr2 | exact Rp1 | exact Rp3 ]
        | apply substituted_entry_readable | apply substituted_entry_readable ]).
  destruct (rel_exp_under_ctx_extend_simple HΓ HAt HM _ _ Hcross) as [Hp | [b1 [b2 [Hb1 [Hb2 Hb]]]]].
  { exfalso; destruct (HBrel _ _ _ HΓA Hcross) as (x & Ex & Hx).
    destruct Hp as (y & Ey & Hy); functional_eval_rewrite_clear; congruence. }
  assert (b1 = h2) as -> by (eapply functional_eval_exp; [ exact Hb1 | exact Hh2 ]).
  assert (b2 = g3) as -> by (eapply functional_eval_exp; [ exact Hb2 | exact Hg3 ]).
  assert (Hbridge : Dom h2 ≈ g3 ∈ per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type))
    by (apply (Hmove _ _ _ _ Rp1 Rp3 (substituted_entry_readable _) (substituted_entry_readable _)); exact Hb).
  apply rel_chain_of_pair in Hbridge.
  assert (Htag : Dom ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ entry_type_value a2 ≈ ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type
                   ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro';
        [ etransitivity; [ exact Hρσ | symmetry; exact Hρσ ] | eapply per_head_proof; [ exact Ha2 | exact Hr2 | exact Rp2 | exact Rp2 ]
        | exact Re2a2 | apply substituted_entry_readable ]).
  destruct (rel_exp_under_ctx_extend_simple HΓ HAt HM _ _ Htag) as [Hp' | [w1 [w2 [Hw1 [Hw2 Hw]]]]].
  { exfalso; destruct (HBrel _ _ _ HΓA Htag) as (x & Ex & Hx).
    destruct Hp' as (y & Ey & Hy); functional_eval_rewrite_clear; congruence. }
  assert (w1 = v2) as -> by (eapply functional_eval_exp; [ exact Hw1 | exact Hv2 ]).
  assert (w2 = g2) as -> by (eapply functional_eval_exp; [ exact Hw2 | exact Hg2 ]).
  assert (Hlink2 : Dom v2 ≈ g2 ∈ per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type)).
  { assert (Hch : rel_chain (per_env_extend A A env_relΓ)
                    ([ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ entry_type_value a2; ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type;
                      ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type; ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type]))
      by (apply rel_chain_4; [ exact Htag | etransitivity; [ symmetry |]; exact Htag | exact Hext ]).
    pose proof (per_head_of_type_resp HΓA (rel_type_of_typ HB) _ _ _ _ Hch) as Hr.
    apply Hr; exact Hw. }
  apply rel_chain_of_pair in Hlink2.
  (** *** The Four Values *)
  assert (Hmerge1 : rel_chain (per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type))
                      ([h4; g3]))
    by (merge_rel_chain Hhchain Hbridge h2).
  assert (Hmerge2 : rel_chain (per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type))
                      ([g2; g4; h4]))
    by (merge_rel_chain Hmerge1 Hgchain g3).
  assert (Hmerge3 : rel_chain (per_head B B (ρσ ↦ ⋆ᵈ⟨N, ρσ⟩ ⦂ substituted_type) (ρ'σ' ↦ ⋆ᵈ⟨N, ρ'σ'⟩ ⦂ substituted_type))
                      ([v2; g2; g4; h4]))
    by (merge_rel_chain Hlink2 Hmerge2 g2).
  apply (mk_rel_exp v1 v2 g4 h4);
    [ eapply eval_exp_app_proof; [ apply eval_exp_fn; exact Ha1 | exact Hr1 | apply eval_app_fn; exact Hv1 ]
    | eapply eval_exp_app_proof; [ apply eval_exp_fn; exact Ha2 | exact Hr2 | apply eval_app_fn; exact Hv2 ]
    | exact Hg4
    | exact Hh4
    |].
  merge_rel_chain Hlink1 Hmerge3 v2.
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
      kept proof [⋆ᵈ⟨#0, ρ'σ' ↦ c'⟩] at a proposition, which is related to
      [c'] there;
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
      relevant domain, to the variable's kept proof at a proposition. *)
  assert (Happ : forall T w c' t r ρ0 a0, ⟦ T ⟧ ρ0 ↦ c' ⦂ t ↘ w ->
                   arg_relevance gc_deps gc_stack w = domain_relevance a0 ->
                   (domain_relevance a0 = relevant -> $| w & c' |↘ r) ->
                   (domain_relevance a0 = propositional -> $| w & ⋆ᵈ⟨#0, ρ0 ↦ c' ⦂ t⟩ |↘ r) ->
                   ⟦ T $ #0 ⟧ ρ0 ↦ c' ⦂ t ↘ r).
  { intros * Hw Ew Hrel Hprop.
    destruct (domain_relevance a0) eqn:Ea0.
    - eapply eval_exp_app; [ exact Hw | exact Ew | apply eval_exp_var_eq; reflexivity | exact (Hrel eq_refl) ].
    - eapply eval_exp_app_proof; [ exact Hw | exact Ew | exact (Hprop eq_refl) ]. }
  (** The four domains are of one sort, and form a chain at the domain
      PER. *)
  pose proof (rel_type_inversion HA) as [env_relΓ0 [HΓ0 HAgen]].
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [e1 e2 e3 e4 He1 He2 He3 He4 Hechain].
  assert (e1 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (e2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (e3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (e4 = a4) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hachain : rel_chain (per_univ_elem i in_rel) ([a1; a2; a3; a4]))
    by (eapply per_univ_chain_at_in; [ exact Hechain | | | exact Hmid ]; solve_in).
  assert (HR1 : DF a1 ≈ a2 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (HR3 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H33 : DF a3 ≈ a3 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  pose proof (per_univ_elem_relevance _ _ _ _ HR1) as Er12.
  pose proof (per_univ_elem_relevance _ _ _ _ HR3) as Er34.
  assert (PER in_rel) by (eapply per_elem_PER; exact Hmid).
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  pose proof (per_ctx_env_of_typ_sub HΓ' Hσj HA) as HΓ'A.
  pose proof (rel_type_of_typ HB) as HBt.
  pose proof Hmchain as (Hpi1 & Hpi2 & Hpi3).
  apply (mk_rel_exp m1 m2 λᵈ a3 ρ'σ' (M[↑]ʷ $ #0) λᵈ a4 ρ' (M[↑]ʷ $ #0)[q σ']);
    [ exact Hm1 | exact Hm2 | apply eval_exp_fn; exact Ha3 | apply eval_exp_fn; exact Ha4 |].
  apply rel_chain_4; [ exact Hpi1 | |].
  - (** η itself: the instance's inner value on the left is [⟦M⟧ρσ], the goal's
      second, and its outer value on the right is [⟦M[↑]ʷ⟧(ρ'σ' ↦ c')], the head
      the closure applies.  At a proposition the closure applies it to the
      variable's kept proof, related to the argument at the domain PER, and
      the result is moved to the argument pair. *)
    constructor; [ rewrite (pi_elements_right _ _ _ _ _ _ Hpi1); congruence | reflexivity |].
    intros c c' Hc.
    pose proof (entry_readable_of_elem Hmid Hc) as [Rc2 Rc'3].
    pose proof (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hc) Rc2 Rc'3) as Hpair.
    destruct (rel_exp_under_ctx_shift_at HΓ HA HM HΠrel _ _ _ _ _ _ Hpair)
      as [j [R [b1 [b2 [b3 [b4 [w1 [w2 [w3 [w4 [Hb1 [Hb2 [Hb3 [Hb4 [Hbouter
         [Hbmid [Hw1 [Hw2 [Hw3 [Hw4 Hwchain]]]]]]]]]]]]]]]]]]]].
    assert (b2 = Πᵈ a2 ρσ B) as -> by (eapply functional_eval_exp; [ exact Hb2 | apply eval_exp_pi; exact Ha2 ]).
    assert (b3 = Πᵈ a3 ρ'σ' B) as -> by (eapply functional_eval_exp; [ exact Hb3 | apply eval_exp_pi; exact Ha3 ]).
    assert (HRpi : R <~> per_pi a2 a3 in_rel B ρσ B ρ'σ') by (eapply per_pi_iff; [ exact Hmid | exact Hbmid ]).
    assert (w2 = m2) as -> by (eapply functional_eval_exp; [ exact Hw2 | exact Hm2 ]).
    rewrite HRpi in Hwchain.
    assert (Hlink : Dom m2 ≈ w4 ∈ per_pi a2 a3 in_rel B ρσ B ρ'σ') by pairwise.
    destruct (domain_relevance a2) eqn:Er2.
    + destruct (pi_elements_app _ _ _ _ _ _ Hlink _ _ Hc) as [r r' Hr Hr' Hrr'].
      econstructor; [ exact Hr | apply eval_app_fn | exact Hrr' ].
      eapply Happ; [ exact Hw4 | exact (pi_elements_right _ _ _ _ _ _ Hlink) | intros _; exact Hr' | intros Hp; congruence ].
    + pose proof (per_univ_elem_propositional _ _ _ _ Hmid Er2) as Eprop.
      pose proof (proj1 (Eprop _ _) Hc) as [Rpc Rpc'].
      destruct (per_ctx_env_kept_proof_readable _ _ _ #0 HΓA ltac:(cbn; lia) _ _ Hpair) as [_ Rp].
      assert (Hcp : Dom c ≈ ⋆ᵈ⟨#0, ρ'σ' ↦ c' ⦂ entry_type_value a3⟩ ∈ in_rel) by (apply Eprop; split; assumption).
      destruct (pi_elements_app _ _ _ _ _ _ Hlink _ _ Hcp) as [r r' Hr Hr' Hrr'].
      pose proof (entry_readable_of_elem Hmid Hcp) as [_ Rp3].
      econstructor;
        [ exact Hr
        | apply eval_app_fn; eapply Happ;
            [ exact Hw4 | exact (pi_elements_right _ _ _ _ _ _ Hlink) | intros Hp; congruence | intros _; exact Hr' ]
        | apply (per_head_codomain_resp HΓ HA HBt _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   Hρσ Ha2 Ha3 Hmid Hcp Hc Hcp Rc2 Rp3 Rc2 Rc'3); exact Hrr' ].
  - (** The closure's right commutation, from the weakened judgment along [q σ'].
      The outer type pair of the weakening instance identifies the [per_head] of
      [(Π A B)[↑]ʷ] it lands in with [per_pi].  At a proposition the two
      closures apply the values to their variables' kept proofs. *)
    constructor; [ cbn; congruence | cbn; congruence |].
    intros c c' Hc.
    pose proof (entry_readable_of_elem Hmid Hc) as [Rc2 Rc'3].
    pose proof (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hc) Rc2 Rc'3) as Hpair.
    destruct (rel_exp_under_ctx_shift_at HΓ HA HM HΠrel _ _ _ _ _ _ Hpair)
      as [j [R [b1 [b2 [b3 [b4 [w1 [w2 [w3 [w4 [Hb1 [Hb2 [Hb3 [Hb4 [Hbouter
         [Hbmid [Hw1 [Hw2 [Hw3 [Hw4 Hwchain]]]]]]]]]]]]]]]]]]]].
    assert (b2 = Πᵈ a2 ρσ B) as -> by (eapply functional_eval_exp; [ exact Hb2 | apply eval_exp_pi; exact Ha2 ]).
    assert (b3 = Πᵈ a3 ρ'σ' B) as -> by (eapply functional_eval_exp; [ exact Hb3 | apply eval_exp_pi; exact Ha3 ]).
    assert (HRpi : R <~> per_pi a2 a3 in_rel B ρσ B ρ'σ') by (eapply per_pi_iff; [ exact Hmid | exact Hbmid ]).
    pose proof (args_readable_of_chain Hachain Hc) as Hts.
    pose proof (entry_readable_of_elem Houter Hc) as [Rc1 Rc'4].
    pose proof (per_env_extend_sub_intro HΓ' Hσj HA _ _ _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc Rc1 Rc'4) as Hpair'.
    destruct (rel_exp_under_ctx_q HΓ' Hσj HA HMwk HΠwkrel _ _ _ _ _ _ _ _ _ _ Hpair' Hts Hev Hev')
      as [_ [_ [u [v [Hu [Hv Huv]]]]]].
    assert (HuvR : Dom u ≈ v ∈ R) by (eapply Huv; [ exact Hb1 | exact Hb4 | exact Hbouter ]).
    apply HRpi in HuvR.
    (** [(M[↑]ʷ #0)[q σ']] is [(M[↑]ʷ[q σ']) #0], since [(#0)[q σ']] is [#0], so
      the head is the value [rel_exp_under_ctx_q] reports. *)
    destruct (domain_relevance a2) eqn:Er2.
    + destruct (pi_elements_app _ _ _ _ _ _ HuvR _ _ Hc) as [r r' Hr Hr' Hrr'].
      econstructor; [ apply eval_app_fn | apply eval_app_fn | exact Hrr' ].
      * eapply Happ; [ exact Hu | exact (pi_elements_left _ _ _ _ _ _ HuvR) | intros _; exact Hr | intros Hp; congruence ].
      * eapply Happ; [ exact Hv | exact (pi_elements_right _ _ _ _ _ _ HuvR) | intros _; exact Hr' | intros Hp; congruence ].
    + pose proof (per_univ_elem_propositional _ _ _ _ Hmid Er2) as Eprop.
      pose proof (proj1 (Eprop _ _) Hc) as [Rpc Rpc'].
      assert (Hcc : Dom c ≈ c ∈ in_rel) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
      pose proof (entry_readable_of_elem H33 Hcc) as [Rc3 _].
      assert (Hself3 : Dom ρ'σ' ↦ c ⦂ entry_type_value a3 ≈ ρ'σ' ↦ c ⦂ entry_type_value a3 ∈ per_env_extend A A env_relΓ)
        by (apply per_env_extend_intro';
            [ etransitivity; [ symmetry; exact Hρσ | exact Hρσ ] | exact (per_head_of Ha3 Ha3 H33 Hcc) | exact Rc3 | exact Rc3 ]).
      destruct (per_ctx_env_kept_proof_readable _ _ _ #0 HΓA ltac:(cbn; lia) _ _ Hself3) as [Rp3 _].
      destruct (per_ctx_env_kept_proof_readable _ _ _ #0 HΓ'A ltac:(cbn; lia) _ _ Hpair') as [_ Rp4].
      assert (Hpp : Dom ⋆ᵈ⟨#0, ρ'σ' ↦ c ⦂ entry_type_value a3⟩ ≈ ⋆ᵈ⟨#0, ρ' ↦ c' ⦂ entry_type_value a4⟩ ∈ in_rel)
        by (apply Eprop; split; assumption).
      assert (Hcp4 : Dom c ≈ ⋆ᵈ⟨#0, ρ' ↦ c' ⦂ entry_type_value a4⟩ ∈ in_rel) by (apply Eprop; split; assumption).
      destruct (pi_elements_app _ _ _ _ _ _ HuvR _ _ Hpp) as [r r' Hr Hr' Hrr'].
      pose proof (entry_readable_of_elem Hmid Hpp) as [Rq2 Rq3].
      econstructor; [ apply eval_app_fn | apply eval_app_fn |].
      * eapply Happ; [ exact Hu | exact (pi_elements_left _ _ _ _ _ _ HuvR) | intros Hp; congruence | intros _; exact Hr ].
      * eapply Happ; [ exact Hv | exact (pi_elements_right _ _ _ _ _ _ HuvR) | intros Hp; congruence | intros _; exact Hr' ].
      * apply (per_head_codomain_resp HΓ HA HBt _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 Hρσ Ha2 Ha3 Hmid Hpp Hc Hcp4 Rq2 Rq3 Rc2 Rc'3); exact Hrr'.
Qed.

End Fixed_GCtx.

(** β for a function or for a proof of a [∀]. *)
Lemma sem_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : relevance_sort r Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     exp_scoped (List.length Γ) N ->
     Θ ⍮ Ξ ⍮ Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] ).
Proof.
  intros * HA HS HB HM HN HNs; sem_intro; [ assumption |].
  destruct r; cbn [relevance_sort] in *.
  - destruct HS as [k | |].
    + exact (rel_exp_under_ctx_pi_beta (rel_type_of_typ HA) (rel_type_relevant_of_typ HA) HB HM HN HNs).
    + exact (rel_exp_under_ctx_pi_beta_prop HA HB HM HN HNs).
    + exact (rel_exp_under_ctx_pi_beta (rel_type_of_level_sort 0 HA) (rel_type_relevant_of_level_sort HA) HB HM HN HNs).
  - apply rel_exp_under_ctx_proof.
    match goal with HΓ : ⊨ Γ |- _ =>
      exact (rel_exp_under_ctx_instance HΓ HS HA HB HN HNs) end.
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
