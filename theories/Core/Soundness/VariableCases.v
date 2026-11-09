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

(** A variable whose type is weakened past an entry: glued at the value of
    the weakened type, given an element glued at a related value, at the
    variable's value at the kind of the type ([glu_term_value_intro]). *)
Lemma glu_rel_exp_with_sub_var_shift : forall {i j : nat} {Γ' A Δ σ ρ x a1 a2 P El m R},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ ∈ R ->
    Γ' ⊢ #x : A[↑]ʷ ->
    ⟦ A[↑]ʷ ⟧ ρ ↘ a1 ->
    Dom a1 ≈ a2 ∈ per_univ j ->
    DG a2 ∈ glu_univ_elem i ↘ P ↘ El ->
    (evaluated_kind (domain_kind a1) -> ⟦ #x ⟧ ρ ↘ m) ->
    Δ ⊢ #x[σ] : A[↑]ʷ[σ] ® m ∈ El ->
    glu_rel_exp_with_sub (max i j) Δ #x A[↑]ʷ σ ρ.
Proof.
  intros * HR Hρ Hx Ha1 [Ra Ha12] Hglu Hm HN.
  destruct (glu_univ_elem_cumu_max_left (j := j) Hglu) as (P' & El' & Hglu').
  assert (HN' : Δ ⊢ #x[σ] : A[↑]ʷ[σ] ® m ∈ El')
    by (eapply glu_univ_elem_exp_cumu_max_left; [ exact Hglu | exact Hglu' | exact HN ]).
  assert (Hglu1 : DG a1 ∈ glu_univ_elem (max i j) ↘ P' ↘ El').
  { eapply glu_univ_elem_resp_per_univ; [| exact Hglu' ].
    eexists; symmetry; eapply per_univ_elem_cumu_max_right; exact Ha12. }
  destruct (glu_term_value_intro Hglu1 Hx HR Hρ Hm HN') as (m' & Hm' & HN'').
  econstructor; [ exact Ha1 | exact Hm' | exact Hglu1 | exact HN'' ].
Qed.

(** The variable case. Syntactically it is direct: [#(S n)[σ]] is
    [#n[Wk⨟σ]] and [ρ (S n)] is [ρ↯ n], so one [exp_sub_shift] suffices. The
    type value needs more work: [cons_glu_sub_pred] supplies [⟦A⟧(ρ↯)] while
    the goal mentions [⟦A[↑]ʷ⟧(ρ)], and the two are not equal.
    [completeness_fundamental_typ_shift] relates them, and
    [glu_univ_elem_resp_per_univ] moves [P] and [El] across. *)

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

Lemma glu_rel_exp_vlookup : forall {Γ x A},
    ⊩ Γ ->
    Γ ∋ #x : A ->
    Γ ⊩ #x : A.
Proof.
  intros * [Sb HSb] Hx. gen Sb.
  induction Hx; intros;
    assert (He : ⊢ (_ :: Γ)%list) by (eapply glu_ctx_env_wf_ctx; eassumption);
    destruct (glu_ctx_env_per_ctx_env HSb) as [R HR];
    assert (HT : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HSb; subst; eexists; eassumption);
    destruct HT as [TSb HTSb].
  (** The innermost entry: its head, glued at its type in the tail, at the
      value of the weakened type ([glu_typ_shift_per]) *)
  - destruct (glu_ctx_env_cons_clean_inversion HTSb HSb) as (i & HA & _ & HSbe).
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := max i i); [ exact HSb |].
    intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    apply HSbe in Hσ; destruct Hσ as [? ? ? ? P El Hσt Ea Hglu HN _ _ _].
    destruct (glu_typ_shift_per He HA HR Hρ) as (a1 & a2 & Ea1 & Ea2 & Hper).
    functional_eval_rewrite_clear.
    eapply glu_rel_exp_with_sub_var_shift; [ exact HR | exact Hρ | mauto 3 | exact Ea1 | exact Hper | exact Hglu | intros _; constructor | exact HN ].
  - destruct (glu_ctx_env_cons_def_clean_inversion HTSb HSb) as (i & κ & HA & _ & _ & _ & HSbe).
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := max i i); [ exact HSb |].
    intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    apply HSbe in Hσ; destruct Hσ as [? ? ? ? P El Hσt Ea Hglu HN _ _ _ _].
    destruct (glu_typ_shift_per He HA HR Hρ) as (a1 & a2 & Ea1 & Ea2 & Hper).
    functional_eval_rewrite_clear.
    eapply glu_rel_exp_with_sub_var_shift; [ exact HR | exact Hρ | mauto 3 | exact Ea1 | exact Hper | exact Hglu | intros _; constructor | exact HN ].
  - destruct (glu_ctx_env_cons_dm_clean_inversion HTSb HSb) as (i & HA & _ & _ & _ & _ & HSbe).
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := max i i); [ exact HSb |].
    intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    apply HSbe in Hσ; destruct Hσ as [? ? ? ? P El Hσt Ea Hglu HN _ _ _ _ _].
    destruct (glu_typ_shift_per (κ := ak_relevant) He HA HR Hρ) as (a1 & a2 & Ea1 & Ea2 & Hper).
    functional_eval_rewrite_clear.
    eapply glu_rel_exp_with_sub_var_shift; [ exact HR | exact Hρ | mauto 3 | exact Ea1 | exact Hper | exact Hglu | intros _; constructor | exact HN ].
  (** Under one more entry: the variable in the tail, by the induction
      hypothesis, its type weakened past the entry *)
  - pose proof (IHHx _ HTSb) as Hn.
    destruct (glu_rel_exp_clean_inversion1 HTSb Hn) as [k Hk].
    destruct (ctx_lookup_wf_sorted _ _ _ _ _ (glu_ctx_env_wf_ctx HTSb) Hx) as (S & HS & HAS).
    destruct (type_sort_abs_kind_sort_inv _ HS) as (κ & j & ->).
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := max k j); [ exact HSb |].
    intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    pose proof (glu_ctx_env_sub_tail HSb HTSb Hσ) as Htl.
    destruct (Hk _ _ _ Htl) as [a2 m P El Ea2 Hm Hglu HN].
    destruct (glu_typ_shift_per He HAS HR Hρ) as (a1 & a2' & Ea1 & Ea2' & Hper).
    functional_eval_rewrite_clear.
    eapply (glu_rel_exp_with_sub_var_shift (m := m)); [ exact HR | exact Hρ | mauto 3 | exact Ea1 | exact Hper | exact Hglu | | ].
    + (** At an evaluated kind the value is the tail's [n]-th, the [S n]-th *)
      intros Hev.
      destruct Hper as [Ra Ha12]; rewrite (per_univ_elem_kind _ _ _ _ Ha12) in Hev.
      destruct (domain_kind a2); cbn in Hm; [ | inversion Hev | ]; inversion Hm; subst;
        replace (List.tl ρ n) with (ρ (S n)) by (destruct ρ; reflexivity); apply eval_exp_var.
    + rewrite exp_sub_shift; exact HN.
Qed.


Hint Resolve glu_rel_exp_vlookup : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mctt.
#[export]
Hint Resolve presup_typ_glu_rel_exp : mctt.
#[export]
Hint Resolve glu_rel_exp_vlookup : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

(** The case of a rule whose conclusion only glues its context: a premise
    glues the context, or a term glued in it. *)
Ltac glu_ctx_case :=
  glu_intro; first [ assumption | eapply presup_ctx_glu_rel_exp; eassumption ].

Lemma glu_vlookup :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ #x : A ).
Proof. glu_intro; eapply glu_rel_exp_vlookup; eassumption. Qed.

Lemma glu_exp_eq_var :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_var_delta :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
