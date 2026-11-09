(** * Variables and Presuppositions

    There is no substitution rule: [⟦M[σ]⟧(ρ) = ⟦M⟧(⟦σ⟧ρ)] is not an equation,
    and the gluing predicates are indexed by values, not by relations. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The presuppositions of a glued term: its context glues, and so does
    its type, as a type, at every substitution its context glues: its value
    is glued and the type is glued at it.  The type need not be a term of a
    universe: it may be a proposition, or a type of levels, of [LevelSort]
    (itself in no sort), as [⊢ᵗ] says syntactically. *)
Lemma presup_glu_rel_exp : forall {Γ M A},
    Γ ⊩ M : A ->
    ⊩ Γ /\
      (exists Sb i, EG Γ ∈ glu_ctx_env ↘ Sb /\
                 forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_typ_with_sub i Δ A σ ρ).
Proof.
  intros * [Sb HSb i HM].
  split; [ eexists; eassumption |].
  exists Sb, i; split; [ exact HSb |].
  intros Δ σ ρ Hσ.
  destruct (HM _ _ _ Hσ) as [a m P El Ha Hm Hglu HMg].
  econstructor; [ exact Ha | exact Hglu | eapply glu_univ_elem_trm_typ; eassumption ].
Qed.

Lemma presup_ctx_glu_rel_exp : forall {Γ M A},
    Γ ⊩ M : A ->
    ⊩ Γ.
Proof.
  intros * []%presup_glu_rel_exp.
  eassumption.
Qed.

Hint Resolve presup_ctx_glu_rel_exp : mctt.

Lemma presup_typ_glu_rel_exp : forall {Γ M A},
    Γ ⊩ M : A ->
    exists Sb i, EG Γ ∈ glu_ctx_env ↘ Sb /\
            forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * []%presup_glu_rel_exp.
  eassumption.
Qed.

Hint Resolve presup_typ_glu_rel_exp : mctt.

(** A term of a sort of the kind [κ] is a type glued at an index [i], of
    the sort of [κ] next to [Typeω@i]: a type of a universe at the
    universe's index, a proposition or a type of levels at any. *)
Lemma glu_rel_exp_sort_typ : forall {Γ A S κ},
    Γ ⊩ A : S ->
    sort_kind S κ ->
    exists Sb (i : nat),
      EG Γ ∈ glu_ctx_env ↘ Sb /\
      Γ ⊢ A : abs_kind_sort κ Typeω@i /\
      (forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_typ_with_sub i Δ A σ ρ).
Proof.
  intros * HA HS.
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  destruct HA as [Sb HSb L HAg].
  destruct HS as [j | |].
  - (** A type of a universe *)
    exists Sb, j; repeat split; [ exact HSb | exact HAt |].
    intros Δ σ ρ Hσ; destruct (HAg _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
    simplify_evals; cbn [domain_kind glu_term_value] in Hm.
    basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
    destruct HAs as [_ _ [Pm Elm Hgm Hpm]].
    econstructor; [ exact Hm | exact Hgm | exact Hpm ].
  - (** A proposition: glued as one at any index *)
    exists Sb, 0; repeat split; [ exact HSb | exact HAt |].
    intros Δ σ ρ Hσ; destruct (HAg _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
    simplify_evals; cbn [domain_kind glu_term_value] in Hm.
    basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
    destruct HAs as [_ _ Hpm HP].
    econstructor; [ exact Hm | | exact HP ].
    simp glu_univ_elem; eapply glu_univ_elem_core_prop; [ exact Hpm | reflexivity | reflexivity ].
  - (** A type of levels: glued at the least small index, so at any *)
    exists Sb, 0; repeat split; [ exact HSb | exact HAt |].
    intros Δ σ ρ Hσ; destruct (HAg _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
    simplify_evals; cbn [domain_kind glu_term_value] in Hm.
    basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
    destruct HAs as [_ _ _ [Pm Elm Hgm Hpm]].
    assert (Hle : universe_index_le (us (ordinal_of_nat 0)) (ul 0)) by exact I.
    destruct (glu_univ_elem_cumu_ge_universe_index Hle Hgm) as (P0 & El0 & Hg0).
    econstructor; [ exact Hm | exact Hg0 |].
    eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hle | exact Hgm | exact Hg0 | exact Hpm ].
Qed.

(** A term glued at a type glued at the index [i] is glued at [i]: its
    gluing moves along the indices ([glu_univ_elem_exp_conv]). *)
Lemma glu_rel_exp_at_typ_index : forall {Sb Γ M A} {i : nat},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_typ_with_sub i Δ A σ ρ) ->
    Γ ⊩ M : A ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * HSb HA HM.
  destruct (glu_rel_exp_clean_inversion1 HSb HM) as [k Hk].
  intros Δ σ ρ Hσ.
  destruct (HA _ _ _ Hσ) as [a P El Ea Hg HAg].
  destruct (Hk _ _ _ Hσ) as [a' m P' El' Ea' Hm Hg' HMg].
  functional_eval_rewrite_clear.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hg') as [R HR].
  econstructor; [ eassumption | exact Hm | exact Hg |].
  eapply (glu_univ_elem_exp_conv (k := k)); [ eexists; exact HR | exact Hg' | exact Hg | exact HMg | exact HAg ].
Qed.

(** A sort of types is the sort of a kind next to a large universe. *)
Lemma type_sort_abs_kind_sort_inv : forall S, type_sort S -> exists κ (j : nat), S = abs_kind_sort κ Typeω@j.
Proof. intros S []; [ exists ak_relevant, i | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity. Qed.

(** The value of a type weakened past an entry is related to its value in
    the tail ([completeness_fundamental_typ_shift] at any sort). *)
Lemma glu_typ_shift_per : forall {Γ e κ A} {i : nat} {env_rel ρ},
    ⊢ (e :: Γ)%list ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ env_rel ->
    Dom ρ ≈ ρ ∈ env_rel ->
    exists a a', ⟦ A[↑]ʷ ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ↯ ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * He HA Hper Hρ.
  assert ((e :: Γ)%list ⊨ʷ ↑ : Γ)
    by (apply rel_wk_under_ctx_shift, completeness_fundamental_ctx; eassumption).
  assert (Γ ⊨ᵗ A ≈ A at i) by (eapply rel_type_of_abs_kind_sort, completeness_fundamental_exp; eassumption).
  destruct (rel_type_inversion_wk ltac:(eassumption) ltac:(eassumption)) as [env_rel' [Hper' Hbridge]].
  handle_per_ctx_env_irrel.
  destruct (Hbridge _ _ Hρ) as [a [a' ?]].
  rewrite eval_wk_shift in *.
  exists a, a'; eassumption.
Qed.

(** ** Variables

    Syntactically a variable is direct: [#(S n)[σ]] is [#n[Wk⨟σ]] and
    [ρ (S n)] is [ρ↯ n].  Its type is not: the glued environment glues the
    variable at its declared type's value in the environment's tail, while
    the variable's type is that type weakened, whose value is only related
    to it.  The variable is moved to the weakened type's value
    ([glu_univ_elem_exp_conv]) at the weakened type's gluing, which is the
    witness the lemmas below take. *)

(** The tail of a glued substitution into an extended context glues in
    the tail's gluing. *)
Lemma glu_ctx_env_sub_tail : forall {e Γ Sb TSb Δ σ ρ},
    EG (e :: Γ)%list ∈ glu_ctx_env ↘ Sb ->
    EG Γ ∈ glu_ctx_env ↘ TSb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb.
Proof.
  intros * H HT Hσ.
  inversion H; subst; apply_predicate_equivalence;
    match goal with HT' : EG Γ ∈ glu_ctx_env ↘ ?TSb' |- _ =>
      assert (E : TSb' <∙> TSb) by (eapply functional_glu_ctx_env; eassumption) end;
    destruct Hσ; apply E; eassumption.
Qed.

(** A variable of a glued context is glued, at its value in the
    environment, at a type value related to its type's: the declared type's
    value in the environment's tail, each weakening past an entry relating
    the two ([glu_typ_shift_per]). *)
Lemma glu_ctx_env_lookup_glu : forall Γ x A, Γ ∋ #x : A -> forall Sb, EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb ->
    exists (j : nat) a' P' El', DG a' ∈ glu_univ_elem j ↘ P' ↘ El' /\ Δ ⊢ #x[σ] : A[σ] ® (ρ x) ∈ El' /\
      forall RΓ a1, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> ⟦ A ⟧ ρ ↘ a1 -> Dom a' ≈ a1 ∈ per_univ j.
Proof.
  intros Γ x A Hx; induction Hx; intros Sb HSb Δ σ ρ Hσ;
    assert (He : ⊢ (_ :: Γ)%list) by (eapply glu_ctx_env_wf_ctx; eassumption);
    assert (HT : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HSb; subst; eexists; eassumption);
    destruct HT as [TSb HTSb].
  (** The innermost entry: its head, glued at its type in the tail *)
  - destruct (glu_ctx_env_cons_clean_inversion HTSb HSb) as (i & HA & _ & HSbe).
    pose proof Hσ as Hσ0; apply HSbe in Hσ0; destruct Hσ0 as [? ? ? ? P El Hσt Ea Hglu HN _ _ _].
    exists i, a, P, El; split; [ exact Hglu | split; [ exact HN |] ].
    intros RΓ a1 HR Ea1.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    destruct (glu_typ_shift_per He HA HR Hρ) as (a1' & a2 & Ea1' & Ea2 & Hper).
    functional_eval_rewrite_clear; symmetry; exact Hper.
  - destruct (glu_ctx_env_cons_def_clean_inversion HTSb HSb) as (i & κ & HA & _ & _ & _ & HSbe).
    pose proof Hσ as Hσ0; apply HSbe in Hσ0; destruct Hσ0 as [? ? ? ? P El Hσt Ea Hglu HN _ _ _ _].
    exists i, a, P, El; split; [ exact Hglu | split; [ exact HN |] ].
    intros RΓ a1 HR Ea1.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    destruct (glu_typ_shift_per He HA HR Hρ) as (a1' & a2 & Ea1' & Ea2 & Hper).
    functional_eval_rewrite_clear; symmetry; exact Hper.
  - destruct (glu_ctx_env_cons_dm_clean_inversion HTSb HSb) as (i & HA & _ & _ & _ & _ & HSbe).
    pose proof Hσ as Hσ0; apply HSbe in Hσ0; destruct Hσ0 as [? ? ? ? P El Hσt Ea Hglu HN _ _ _ _ _].
    exists i, a, P, El; split; [ exact Hglu | split; [ exact HN |] ].
    intros RΓ a1 HR Ea1.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    destruct (glu_typ_shift_per (κ := ak_relevant) He HA HR Hρ) as (a1' & a2 & Ea1' & Ea2 & Hper).
    functional_eval_rewrite_clear; symmetry; exact Hper.
  (** Under one more entry: the variable in the tail, its type weakened
      past the entry *)
  - pose proof (glu_ctx_env_sub_tail HSb HTSb Hσ) as Htl.
    destruct (IHHx _ HTSb _ _ _ Htl) as (j & a' & P' & El' & Hg & HN & Hper).
    destruct (ctx_lookup_wf_sorted _ _ _ _ _ (glu_ctx_env_wf_ctx HTSb) Hx) as (S & HS & HAS).
    destruct (type_sort_abs_kind_sort_inv _ HS) as (κ & k & ->).
    destruct (glu_univ_elem_cumu_max_left (j := k) Hg) as (Pm & Elm & Hgm).
    exists (max j k), a', Pm, Elm; split; [ exact Hgm | split ].
    + rewrite exp_sub_shift; replace (ρ (S n)) with (ρ↯ n) by (destruct ρ; reflexivity).
      exact (glu_univ_elem_exp_cumu_max_left Hg Hgm HN).
    + intros RΓ a1 HR Ea1.
      pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
      destruct (glu_typ_shift_per He HAS HR Hρ) as (a1' & a0 & Ea1' & Ea0 & [R0 Hper0]).
      functional_eval_rewrite_clear.
      destruct (glu_ctx_env_per_ctx_env HTSb) as [RT HRT].
      destruct (Hper _ _ HRT Ea0) as [R1 Hper1].
      assert (H1 : Dom a' ≈ a0 ∈ per_univ (max j k)) by (eexists; eapply per_univ_elem_cumu_max_left; exact Hper1).
      assert (H2 : Dom a1 ≈ a0 ∈ per_univ (max j k)) by (eexists; eapply per_univ_elem_cumu_max_right; exact Hper0).
      etransitivity; [ exact H1 | symmetry; exact H2 ].
Qed.

(** A variable of a glued context is glued at its type, given its type's
    gluing: at the variable's value, moved from the declared type's value
    to its type's ([glu_univ_elem_exp_conv]), and at a proposition at the
    proof kept ([glu_term_value_intro]). *)
Lemma glu_rel_exp_var_witness : forall {Γ x A S},
    ⊩ Γ -> Γ ∋ #x : A -> type_sort S -> Γ ⊩ A : S -> Γ ⊩ #x : A.
Proof.
  intros * [Sb HSb] Hx HS HA.
  destruct (type_sort_abs_kind_sort_inv _ HS) as (κ & j0 & ->).
  destruct (glu_rel_exp_sort_typ HA (sort_kind_abs_kind_sort κ _)) as (Sb' & i & HSb' & HAt & HAg).
  assert (E : Sb <∙> Sb') by (eapply functional_glu_ctx_env; eassumption).
  destruct (glu_ctx_env_per_ctx_env HSb) as [RΓ HRΓ].
  assert (Hxt : Γ ⊢ #x : A) by (apply wf_vlookup; [ eapply glu_ctx_env_wf_ctx; exact HSb | exact Hx ]).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HSb |].
  intros Δ σ ρ Hσ.
  pose proof Hσ as Hσ'; apply E in Hσ'.
  destruct (HAg _ _ _ Hσ') as [a1 P1 El1 Ea1 Hg1 HAσ].
  destruct (glu_ctx_env_lookup_glu _ _ _ Hx _ HSb _ _ _ Hσ) as (j & a' & P' & El' & Hg' & HN & Hper).
  pose proof (Hper _ _ HRΓ Ea1) as Hper'.
  pose proof (glu_univ_elem_exp_conv Hper' Hg' Hg1 HN HAσ) as HN1.
  destruct (glu_term_value_intro Hg1 HSb Hσ Hxt (fun _ => eval_exp_var _ _ _ _) HN1) as (m & Hm & HN2).
  econstructor; [ exact Ea1 | exact Hm | exact Hg1 | exact HN2 ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mctt.
#[export]
Hint Resolve presup_typ_glu_rel_exp : mctt.
