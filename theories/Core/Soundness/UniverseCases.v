From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation SubtypingCases VariableCases Instances.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Universes at Any Index

    A type at an index [u] is a term of the universe [universe_index_term u], whose value
    [universe_index_value u] is glued at the ambient index [large_level_above u].  The two
    lemmas below are inverse to each other; the large forms used by the rest
    of the development are their instances at [ul i]. *)

Lemma glu_rel_exp_of_univ : forall {Γ Sb A} {u : universe_index},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢ˢ σ ® ρ ∈ Sb ->
        Δ ⊢ A[σ] : universe_index_term u /\
          exists a,
            ⟦ A ⟧ ρ ↘ a /\
              Dom a ≈ a ∈ per_univ u /\
              (forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
              (forall Δ' φ W, Δ' ⊢ᵏ φ : Δ -> Rtyp a in length Δ' ↘ W ->
                         glu_nf_eq Δ' A[σ][φ]ʷ W (universe_index_term u))) ->
    Γ ⊩ A : universe_index_term u.
Proof.
  intros * ? Hbody.
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := large_level_above u); [ eassumption |].
  intros * HΔ.
  destruct (Hbody _ _ _ HΔ) as [H0 [a [? [[] [H3 Hrb]]]]].
  assert (⊢ Δ) by (gen_presups; eassumption).
  assert (exists P El, DG a ∈ glu_univ_elem u ↘ P ↘ El) as [P [El HPEl]] by mauto 3.
  econstructor; [ apply eval_universe_index_term | destruct u; cbn; eassumption
                | apply glu_univ_elem_univ_at, universe_index_lt_large_level_above |].
  rewrite exp_sub_universe_index_term.
  destruct u as [n | j]; cbn [univ_glu_exp_pred_at universe_index_term large_level_above] in *.
  - (** A type of a small universe at a literal level: the level term is the
        literal, and the readback clause is the premise's. *)
    econstructor.
    + exact H0.
    + apply (mk_suniv_glu_typ _ _ _ _ (𝕃ᵒ n) (fst n)); [ apply glu_lvl_lit; [ reflexivity | assumption ] | mauto 3 ].
    + exact (mk_glu_typ_at _ _ _ _ P El HPEl (H3 P El HPEl)).
    + intros Δ' φ W Hφ Hr; pose proof (Hrb _ _ _ Hφ Hr) as Hw; cbn in Hw |- *; exact Hw.
  - econstructor.
    + exact H0.
    + mauto 3.
    + exact (mk_glu_typ_at _ _ _ _ P El HPEl (H3 P El HPEl)).
Qed.

(** The universe at [u] is itself a term of [Typeω@(large_level_above u)]: the
    ambient universe the inversion below is stated at. *)
Lemma glu_rel_exp_univ_tm : forall {Γ} {u : universe_index},
    ⊩ Γ ->
    Γ ⊩ universe_index_term u : Typeω@(large_level_above u).
Proof.
  intros * [Sb HΓ].
  assert (⊢ Γ) by mauto 2.
  eapply (glu_rel_exp_of_univ (u := ul (large_level_above u))); [ eassumption |].
  intros Δ σ ρ HΔ.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  saturate_sub.
  rewrite exp_sub_universe_index_term.
  split; [ apply wf_universe_index_term; assumption |].
  exists (universe_index_value u).
  split; [ apply eval_universe_index_term |].
  split; [ eexists; apply per_univ_elem_universe_index_value, universe_index_lt_large_level_above |].
  split.
  - intros P El HPEl.
    pose proof (glu_univ_elem_univ_at (u := u) (i := ul (large_level_above u)) (universe_index_lt_large_level_above u)).
    handle_functional_glu_univ_elem.
    destruct u as [n | j]; cbn [univ_glu_typ_pred_at universe_index_term large_level_above large_level] in *.
    + apply (mk_suniv_glu_typ _ _ _ _ (𝕃ᵒ n) (fst n)); [ apply glu_lvl_lit; [ reflexivity | assumption ] | mauto 3 ].
    + apply wf_exp_eq_typ_cong; assumption.
  - (** The universe reads back as itself. *)
    intros Δ' φ W Hφ Hr.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    destruct u as [n | j]; cbn [universe_index_value universe_index_term large_level_above] in *;
      inversion Hr; subst; cbn.
    + assert (Hn := read_nf_domain_level_lit n (length Δ')); unfold domain_level_lit in Hn.
      assert (L = lvl_lit n) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption).
      apply glu_nf_eq_intro; cbn; apply wf_exp_eq_univ_cong_large; assumption.
    + apply glu_nf_eq_intro; mauto 3.
Qed.

Lemma glu_rel_exp_of_univ_inversion : forall {Γ Sb A} {u : universe_index},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : universe_index_term u ->
    forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      Δ ⊢ A[σ] : universe_index_term u /\
        exists a,
          ⟦ A ⟧ ρ ↘ a /\
            Dom a ≈ a ∈ per_univ u /\
            (forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
            (forall Δ' φ W, Δ' ⊢ᵏ φ : Δ -> Rtyp a in length Δ' ↘ W ->
                       glu_nf_eq Δ' A[σ][φ]ʷ W (universe_index_term u)).
Proof.
  intros * HΓ HA * HΔ.
  assert (Γ ⊩ universe_index_term u : Typeω@(large_level_above u)) by (eapply glu_rel_exp_univ_tm; eexists; eassumption).
  eapply glu_rel_exp_clean_inversion2 in HA; [| eassumption | eassumption ].
  destruct (HA _ _ _ HΔ).
  pose proof (eval_universe_index_term gc_deps gc_stack u ρ).
  functional_eval_rewrite_clear.
  pose proof (glu_univ_elem_univ_at (u := u) (i := ul (large_level_above u)) (universe_index_lt_large_level_above u)).
  handle_functional_glu_univ_elem.
  (** The element predicate of the ambient universe is the gluing of a type at
      [u]: that is the information the small tier needs.  Its readback clause
      is part of it in the small tier, and realizability in the large one. *)
  destruct u as [n | j]; cbn [univ_glu_exp_pred_at universe_index_term large_level_above] in *.
  - match goal with H : suniv_glu_exp_pred _ _ _ _ _ _ |- _ =>
      destruct H as [HAσ _ [Pm Elm HPEl HP] Hrb] end.
    rewrite ?exp_sub_universe_index_term in *.
    split; [ assumption |].
    exists m; split; [ assumption | split; [| split ] ].
    + eapply glu_univ_elem_per_univ; eassumption.
    + intros P' El' H'.
      handle_functional_glu_univ_elem.
      assumption.
    + exact Hrb.
  - match goal with H : univ_glu_exp_pred _ _ _ _ _ _ |- _ =>
      destruct H as [HAσ Heq [Pm Elm HPEl HP]] end.
    rewrite ?exp_sub_universe_index_term in *.
    split; [ assumption |].
    exists m; split; [ assumption | split; [| split ] ].
    + eapply glu_univ_elem_per_univ; eassumption.
    + intros P' El' H'.
      handle_functional_glu_univ_elem.
      assumption.
    + (** By realizability: a type of a universe reads back as itself up to
          proofs ([realize_glu_typ_top]) *)
      destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant _ HPEl HP HAσ) as [Hk Hnl].
      destruct (realize_glu_typ_top _ _ _ _ HPEl Hnl _ _ HP) as [_ _ Hrd].
      rewrite Hk in Hrd; exact Hrd.
Qed.

(** A type at an index [u] is a type at the large level [large_level u], which is
    the index a context entry is glued at. *)
Lemma glu_rel_typ_with_sub_universe_index : forall {u : universe_index} {Δ A σ ρ},
    (exists a,
        ⟦ A ⟧ ρ ↘ a /\
          Dom a ≈ a ∈ per_univ u /\
          forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    glu_rel_typ_with_sub (large_level u) Δ A σ ρ.
Proof.
  intros * [a [Hae [[R HR] HaP]]].
  assert (exists P El, DG a ∈ glu_univ_elem u ↘ P ↘ El) as [P [El HPEl]] by mauto 3.
  assert (exists P' El', DG a ∈ glu_univ_elem (large_level u) ↘ P' ↘ El') as [P' [El' HPEl']]
      by (eapply (glu_univ_elem_cumu_ge_universe_index (i := u)); [ apply universe_index_le_large_level | exact HPEl ]).
  econstructor; [ exact Hae | exact HPEl' |].
  eapply (glu_univ_elem_typ_cumu_ge_universe_index (i := u) (j := large_level u));
    [ apply universe_index_le_large_level | exact HPEl | exact HPEl' | exact (HaP P El HPEl) ].
Qed.

(** Cumulativity of the gluing judgment, along the order of indices. *)
Lemma glu_rel_exp_lift_universe_index : forall {Γ A} {u v : universe_index},
    universe_index_le u v ->
    Γ ⊩ A : universe_index_term u ->
    Γ ⊩ A : universe_index_term v.
Proof.
  intros * Hle HA.
  assert (⊢ Γ) by mauto 3 using glu_rel_exp_to_wf_exp.
  eapply glu_rel_exp_subtyp;
    [ exact HA
    | eapply glu_rel_exp_univ_tm; destruct HA as [Sb ? ? ?]; eexists; eassumption
    | constructor
    | apply wf_subtyp_universe_index; assumption ].
Qed.

Lemma glu_rel_exp_of_typ : forall {Γ Sb A} {i : nat},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢ˢ σ ® ρ ∈ Sb ->
        Δ ⊢ A[σ] : Typeω@i /\
          exists a,
            ⟦ A ⟧ ρ ↘ a /\
              Dom a ≈ a ∈ per_univ i /\
              forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    Γ ⊩ A : Typeω@i.
Proof.
  intros * ? Hbody.
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := S i); [ mauto |].
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
Qed.

(** The small universe as a term of the next small universe. *)
Lemma glu_rel_exp_suniv : forall {Γ} {a n : nat},
    ⊩ Γ ->
    Γ ⊩ Type⟨𝕃ᵒ(a, n)⟩ : Type⟨𝕃ᵒ(a, S n)⟩.
Proof.
  intros * [Sb HΓ].
  assert (⊢ Γ) by mauto 2.
  eapply (glu_rel_exp_of_univ (u := us (a, S n))); [ eassumption |].
  intros Δ σ ρ HΔ.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  saturate_sub.
  cbn.
  split; [ apply wf_univ_lit; assumption |].
  exists 𝕌@(domain_level_lit (a, n)).
  split; [ apply eval_exp_univ, eval_exp_llit |].
  split; [ eexists; apply (per_univ_elem_universe_index_value (us (a, n)) (us (a, S n))); cbn; ordinal_solve |].
  split.
  - intros P El HPEl.
    pose proof (glu_univ_elem_univ_at (u := us (a, n)) (i := us (a, S n)) ltac:(cbn; ordinal_solve)).
    handle_functional_glu_univ_elem.
    cbn; apply (mk_suniv_glu_typ _ _ _ _ (𝕃ᵒ(a, n)) a); [ apply glu_lvl_lit; [ reflexivity | assumption ] | mauto 3 ].
  - (** The small universe reads back as itself. *)
    intros Δ' φ W Hφ Hr.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    inversion Hr; subst.
    assert (Hn := read_nf_domain_level_lit (a, n) (length Δ')); unfold domain_level_lit in Hn.
    assert (L = lvl_lit (a, n)) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption).
    apply glu_nf_eq_intro; cbn; apply wf_exp_eq_univ_cong_lit; assumption.
Qed.

Hint Resolve glu_rel_exp_suniv : mctt.

Lemma glu_rel_exp_typ : forall {Γ} {i : nat},
    ⊩ Γ ->
    Γ ⊩ Typeω@i : Typeω@(S i).
Proof.
  intros * [].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  cbn.
  mauto 4.
  (** [Typeω@i[σ]] is [Typeω@i], so the equation is reflexivity, which needs
      [⊢ Δ] from a presupposition. *)
  gen_presups; mauto 3.
Qed.

Hint Resolve glu_rel_exp_typ : mctt.

Lemma glu_rel_exp_clean_inversion2' : forall {i : nat} {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : Typeω@i ->
    glu_rel_exp_clean_inversion2_result (S i) Sb M Typeω@i.
Proof.
  intros * ? HM.
  assert (Γ ⊩ Typeω@i : Typeω@(S i)) by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

(** ** The Sorts of Propositions and of Types of Levels

    A proposition, as a term of [Prop], glues by its value, glued as a
    proposition; a type of levels, as a term of [LevelSort], by its value,
    a type of levels glued as a type at the least small index.  Each has
    its inverse, and a proposition's proofs glue by their typing alone
    ([glu_rel_exp_proof]). *)

(** A proposition glues by its value, glued as a proposition. *)
Lemma glu_rel_exp_of_prop : forall {Γ Sb A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢ˢ σ ® ρ ∈ Sb ->
        exists a, ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_prop /\ Δ ⊢ A[σ] ® prop_glu_typ_pred a) ->
    Γ ⊩ A : Propₘ.
Proof.
  intros * HSb Hbody.
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := 0); [ exact HSb |].
  intros Δ σ ρ Hσ.
  destruct (Hbody _ _ _ Hσ) as (a & Ha & Hpa & HaP).
  assert (⊢ Δ) by (eapply glu_ctx_env_sub_escape in Hσ; [| exact HSb ]; gen_presups; assumption).
  destruct (per_univ_glu_univ_elem 0 Propᵈ ltac:(eexists; apply per_univ_elem_prop_univ)) as (P & El & Hglu).
  econstructor; [ constructor | cbn; exact Ha | exact Hglu |].
  basic_invert_glu_univ_elem Hglu; apply_predicate_equivalence.
  econstructor; [ cbn; mauto 3 | destruct HaP; assumption | exact Hpa | exact HaP ].
Qed.

(** The inverse: a glued proposition, at a glued substitution. *)
Lemma glu_rel_exp_prop_inversion : forall {Γ Sb A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : Propₘ ->
    forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      exists a, ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_prop /\ Δ ⊢ A[σ] ® prop_glu_typ_pred a.
Proof.
  intros * HSb HA Δ σ ρ Hσ.
  destruct (glu_rel_exp_clean_inversion1 HSb HA) as [k Hk].
  destruct (Hk _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
  simplify_evals; cbn [domain_kind glu_term_value] in Hm.
  basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
  destruct HAs as [_ _ Hpm HP].
  exact (ex_intro _ m (conj Hm (conj Hpm HP))).
Qed.

(** A type of levels glues by its value, a type of levels glued as a type
    at the least small index. *)
Lemma glu_rel_exp_of_level_sort : forall {Γ Sb A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢ˢ σ ® ρ ∈ Sb ->
        exists a P El, ⟦ A ⟧ ρ ↘ a /\ level_code a /\ Δ ⊢ A[σ] : LevelSort /\
                  DG a ∈ glu_univ_elem (us (0, 0)) ↘ P ↘ El /\ Δ ⊢ A[σ] ® P) ->
    Γ ⊩ A : LevelSort.
Proof.
  intros * HSb Hbody.
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := 0); [ exact HSb |].
  intros Δ σ ρ Hσ.
  destruct (Hbody _ _ _ Hσ) as (a & Pa & Ela & Ha & Hca & HAσ & Hga & HaP).
  destruct (per_univ_glu_univ_elem 0 LevelSortᵈ ltac:(eexists; apply Completeness.UniverseCases.per_univ_elem_level_sort_univ; exact I))
    as (P & El & Hglu).
  econstructor; [ constructor | cbn; exact Ha | exact Hglu |].
  basic_invert_glu_univ_elem Hglu; apply_predicate_equivalence.
  econstructor; [ reflexivity | exact HAσ | exact Hca |].
  econstructor; [ exact Hga | exact HaP ].
Qed.

(** The inverse: a glued type of levels, at a glued substitution. *)
Lemma glu_rel_exp_level_sort_inversion : forall {Γ Sb A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : LevelSort ->
    forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      exists a P El, ⟦ A ⟧ ρ ↘ a /\ level_code a /\ Δ ⊢ A[σ] : LevelSort /\
                DG a ∈ glu_univ_elem (us (0, 0)) ↘ P ↘ El /\ Δ ⊢ A[σ] ® P.
Proof.
  intros * HSb HA Δ σ ρ Hσ.
  destruct (glu_rel_exp_clean_inversion1 HSb HA) as [k Hk].
  destruct (Hk _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
  simplify_evals; cbn [domain_kind glu_term_value] in Hm.
  basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
  destruct HAs as [_ HAσ Hcm [Pm Elm Hgm Hpm]].
  exists m, Pm, Elm; split; [ assumption | split; [ assumption | split; [ assumption | split; assumption ] ] ].
Qed.

(** A proposition is a type at every index, glued as a proposition. *)
Lemma glu_prop_typ_at_index : forall {u : universe_index} {Γ A a},
    Dom a ≈ a ∈ per_prop ->
    Γ ⊢ A ® prop_glu_typ_pred a ->
    Dom a ≈ a ∈ per_univ u /\ forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Γ ⊢ A ® P.
Proof.
  intros * Hpa HaP; split; [ eexists; apply per_univ_elem_of_prop; exact Hpa |].
  intros P El Hg; destruct (glu_univ_elem_prop_inv _ _ _ _ Hpa Hg) as [EP _]; apply EP; exact HaP.
Qed.

(** The least small index is below every index. *)
Lemma universe_index_le_least : forall u, universe_index_le (us (0, 0)) u.
Proof. intros [j | j]; cbn; [ unfold ordinal_le; cbn; lia | exact I ]. Qed.

(** A type glued at the least small index is a type at every index,
    glued there. *)
Lemma glu_least_typ_at_index : forall {u : universe_index} {Γ A a P El},
    DG a ∈ glu_univ_elem (us (0, 0)) ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Dom a ≈ a ∈ per_univ u /\ forall P' El', DG a ∈ glu_univ_elem u ↘ P' ↘ El' -> Γ ⊢ A ® P'.
Proof.
  intros * Hg HaP.
  destruct (glu_univ_elem_cumu_ge_universe_index (universe_index_le_least u) Hg) as (P1 & El1 & Hg1).
  split; [ eapply glu_univ_elem_per_univ; exact Hg1 |].
  intros P' El' Hg'.
  destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg1 Hg') as [EP _].
  apply EP; eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact (universe_index_le_least u) | exact Hg | exact Hg1 | exact HaP ].
Qed.

(** A type of the sort of a kind next to a large universe [Typeω@i], at a
    glued substitution: its value is glued as a type at [i]. *)
Lemma glu_rel_exp_kind_sort_large_inversion : forall {Γ Sb A κ} {i : nat},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : abs_kind_sort κ Typeω@i ->
    forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ Sb ->
      Δ ⊢ A[σ] : abs_kind_sort κ Typeω@i /\
        exists a, ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_univ i /\
             forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
Proof.
  intros * HSb HA Δ σ ρ Hσ.
  destruct κ; cbn [abs_kind_sort] in *.
  - destruct (glu_rel_exp_of_univ_inversion (u := ul i) HSb HA _ _ _ Hσ) as [HAσ (a & Ha & Hpa & HaP & _)].
    split; [ exact HAσ | exists a; split; [ exact Ha | split; [ exact Hpa | exact HaP ] ] ].
  - destruct (glu_rel_exp_prop_inversion HSb HA _ _ _ Hσ) as (a & Ha & Hpa & HaP).
    destruct (glu_prop_typ_at_index (u := ul i) Hpa HaP) as [Hpi HPi].
    split; [ destruct HaP; assumption | exists a; split; [ exact Ha | split; [ exact Hpi | exact HPi ] ] ].
  - destruct (glu_rel_exp_level_sort_inversion HSb HA _ _ _ Hσ) as (a & Pa & Ela & Ha & _ & HAσ & Hga & HaP).
    destruct (glu_least_typ_at_index (u := ul i) Hga HaP) as [Hpi HPi].
    split; [ exact HAσ | exists a; split; [ exact Ha | split; [ exact Hpi | exact HPi ] ] ].
Qed.

(** A type glued at every gluing of its value is glued at the index. *)
Lemma glu_rel_typ_with_sub_of_point : forall {i : nat} {Δ A σ ρ},
    (exists a, ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_univ i /\
          forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * (a & Ha & Hp & HP).
  destruct (per_univ_glu_univ_elem _ _ Hp) as (P & El & Hg).
  econstructor; [ exact Ha | exact Hg | exact (HP _ _ Hg) ].
Qed.

(** A glued type of the sort of a kind next to a large universe glues
    next to every larger one. *)
Lemma glu_rel_exp_kind_sort_lift : forall {Γ A κ} {i k : nat},
    i <= k ->
    Γ ⊩ A : abs_kind_sort κ Typeω@i ->
    Γ ⊩ A : abs_kind_sort κ Typeω@k.
Proof.
  intros * Hle HA; destruct κ; cbn in *; [| exact HA | exact HA ].
  exact (glu_rel_exp_lift_universe_index (u := ul i) (v := ul k) Hle HA).
Qed.

(** A sort of a kind is the sort of the kind next to a large universe. *)
Lemma sort_kind_abs_kind_sort_inv : forall {S κ}, sort_kind S κ -> exists j : nat, S = abs_kind_sort κ Typeω@j.
Proof. intros * []; [ exists i | exists 0 | exists 0 ]; reflexivity. Qed.

(** A proof of a glued proposition glues, kept: its typing is all a proof
    glues by. *)
Lemma glu_rel_exp_proof : forall {Γ M T},
    Γ ⊩ T : Propₘ ->
    Γ ⊢ M : T ->
    Γ ⊩ M : T.
Proof.
  intros * HT HM.
  destruct (presup_ctx_glu_rel_exp HT) as [Sb HSb].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := 0); [ exact HSb |].
  intros Δ σ ρ Hσ.
  destruct (glu_rel_exp_prop_inversion HSb HT _ _ _ Hσ) as (t & Ht & Hpt & HtP).
  pose proof (glu_ctx_env_sub_escape HSb _ _ _ Hσ) as Hσt.
  destruct (per_univ_glu_univ_elem 0 t ltac:(eexists; apply per_univ_elem_of_prop; exact Hpt)) as (P & El & Hg).
  destruct (glu_univ_elem_prop_inv _ _ _ _ Hpt Hg) as [_ EEl].
  econstructor; [ exact Ht | cbn; rewrite (per_prop_left _ _ Hpt); reflexivity | exact Hg |].
  apply EEl; econstructor; [ exact HtP | exact (sub_preserves_exp _ _ _ _ _ _ _ HM Hσt) | |].
  - destruct (glu_ctx_env_per_ctx_env HSb) as [R HR].
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    assert (HsM : exp_scoped (List.length Γ) M) by exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HM))).
    destruct (per_ctx_env_kept_proof_readable _ _ _ M HR (exp_scoped_free_bound _ _ HsM) _ _ Hρ) as [Hr _].
    split; exact Hr.
  - (** The kept proof reads back as the proof, under its lets *)
    intros Δ' φ R Hφ HR.
    apply wf_exp_eq_sym; eapply glu_kept_proof_read; [ exact HSb | exact Hσ | exact HM | exact (glu_rel_exp_to_wf_exp HT) | exact Hφ | exact HR ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_typ glu_rel_exp_suniv : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

Lemma glu_typ :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Typeω@i : Typeω@(S i) ).
Proof. glu_inst_intro; cbn; apply glu_rel_exp_typ; apply Hτ. Qed.

Lemma glu_exp_eq_typ_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_is_univ_large :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵤ Typeω@i ).
Proof. glu_intro; [ assumption | left; eexists; reflexivity ]. Qed.

Lemma glu_is_univ_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵤ Type⟨L⟩ ).
Proof.
  glu_intro; [ eapply glu_rel_exp_under_sub_ctx; eassumption | right; do 2 eexists; split; [ reflexivity | eassumption ] ].
Qed.
Ltac invert_glu_rel_exp H ::=
  (unshelve eapply (glu_rel_exp_clean_inversion2' _) in H; shelve_unifiable; [eassumption |];
   unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
     unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

