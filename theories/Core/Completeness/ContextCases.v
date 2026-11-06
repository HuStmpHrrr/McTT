(** * Contexts

    The rules of [wf_ctx] but the module slot's (which is in
    [Modules/MemberTypes.v]), and the two context-subtyping facts that
    [Consequences] needs.  [⊨ Γ] is inductive, so the empty context is
    the constructor [rel_ctx_wf_nil].  The extension step is the one place that
    builds a context PER rather than taking one apart.

    The head relation of the extension is the impredicative [per_head], "whatever
    every [per_univ_elem] relating the values of [A] and [A'] relates", chosen once
    by [per_ctx_env_extend].  This file supplies its premise, which is what
    [rel_exp_of_typ_inversion_simple] delivers. *)

From Stdlib Require Import Morphisms_Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Completeness Require Import LogicalRelation UniverseCases.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_ctx_extend_type : forall {Γ Γ' κ A A'} {i : nat},
    ⊨ Γ ≈ Γ' ->
    Γ ⊨ᵗ A ≈ A' at i ->
    ⊨ Γ ▹{κ} A ≈ Γ' ▹{κ} A'.
Proof.
  intros * [env_relΓΓ' HΓΓ'] H.
  pose proof (rel_type_under_ctx_not_level_sort _ _ _ _ H) as Hn.
  pose proof (rel_type_inversion_simple H) as [env_relΓ [HΓ HA]].
  (** Both witnesses have [Γ] on the left, so they agree up to [<~>].  Naming
    the equivalence, rather than calling [handle_per_ctx_env_irrel], keeps
    [env_relΓΓ'], the only witness for the tail of the goal, in place. *)
  assert (Hirrel : env_relΓΓ' <~> env_relΓ)
    by (eapply per_ctx_env_right_irrel; [exact HΓΓ' | exact HΓ]).
  eexists.
  eapply per_ctx_env_extend; [ eassumption | |].
  - intros ρ ρ' Hρ%Hirrel.
    now apply HA.
  - intros ρ ρ' Hρ%Hirrel; exact (Hn _ HΓ _ _ Hρ).
Qed.

Corollary per_ctx_extend : forall {Γ Γ' κ A A'} {i : nat},
    ⊨ Γ ≈ Γ' ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    ⊨ Γ ▹{κ} A ≈ Γ' ▹{κ} A'.
Proof. intros * HΓ H; exact (per_ctx_extend_type HΓ (rel_type_of_typ H)). Qed.

(** An assumption of a type of a sort, at the sort's kind. *)
Lemma rel_ctx_wf_extend_sort : forall {Γ κ A S},
    ⊨ Γ ->
    sort_kind S κ ->
    Γ ⊨ A : S ->
    ⊨ Γ ▹{κ} A.
Proof.
  intros * HΓ HS HA.
  destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS) HA) as [i Hi].
  pose proof (per_ctx_extend_type (κ := κ) (rel_ctx_wf_per_ctx HΓ) Hi) as [env_relΓA HΓA].
  econstructor; eassumption.
Qed.

Corollary rel_ctx_wf_extend : forall {Γ A} {i : nat},
    ⊨ Γ ->
    Γ ⊨ A : Typeω@i ->
    ⊨ Γ ▹{ak_relevant} A.
Proof. intros * HΓ HA; exact (rel_ctx_wf_extend_sort HΓ (sort_kind_universe i) HA). Qed.

Hint Resolve per_ctx_extend rel_ctx_wf_extend : mctt.

End Fixed_GCtx.

#[local] Generalizable All Variables.

Lemma sem_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▹{κ} A ).
Proof.
  intros * HA HS; sem_intro.
  apply valid_ctx_ass; [ assumption | eapply rel_ctx_wf_extend_sort; eassumption ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** At a type of an evaluated kind, a term judgment relates the values. *)
Lemma rel_exp_under_ctx_simple_at_of_evaluated : forall {Γ A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_evaluated A ρ) ->
    Γ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A A ρ ρ'.
Proof. intros * HΓ HA HM ρ ρ' Hρ; exact (rel_exp_under_ctx_simple_at_evaluated HΓ HM _ _ Hρ (HA _ _ Hρ)). Qed.

(** At a type of a universe, a term judgment relates the values: the type
    is relevant, never a proposition. *)
Corollary rel_exp_under_ctx_simple_at_rel : forall {Γ A M M' env_relΓ} {i : nat},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A A ρ ρ'.
Proof.
  intros * HΓ HA HM.
  exact (rel_exp_under_ctx_simple_at_of_evaluated HΓ
           (fun ρ ρ' Hρ => rel_typ_evaluated_of_kind (rel_exp_of_typ_relevant_at HΓ HA _ _ Hρ) evaluated_kind_relevant) HM).
Qed.

(** ** Definition Entries

    The canonical context PER of [Γ ▸ A ≔ M] is [per_env_extend_def], fed by
    the [Id] instances of the relations of [A] and [M]. *)
Lemma per_ctx_env_of_def : forall {Γ A} {i : nat} {M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ per_env_extend_def A M env_relΓ.
Proof.
  intros * HΓ HA HM.
  eapply (per_ctx_env_extend_def (r := ak_relevant)); [ constructor | eassumption | | |].
  - exact (rel_exp_of_typ_inversion_simple_at HΓ HA).
  - exact (rel_exp_of_typ_relevant_at HΓ HA).
  - exact (rel_exp_under_ctx_simple_at_rel HΓ HA HM).
Qed.

(** The same for a definition of any type of an evaluated kind [r]. *)
Lemma per_ctx_env_of_def_evaluated : forall {Γ A r} {i : nat} {M env_relΓ},
    evaluated_kind r ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A at i ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_kind A ρ r) ->
    Γ ⊨ M : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ per_env_extend_def A M env_relΓ.
Proof.
  intros * Hr HΓ HA HArel HM.
  eapply (per_ctx_env_extend_def (i := i)); [ exact Hr | eassumption | | |].
  - exact (rel_type_inversion_simple_at HΓ HA).
  - exact HArel.
  - exact (rel_exp_under_ctx_simple_at_of_evaluated HΓ (fun ρ ρ' Hρ => rel_typ_evaluated_of_kind (HArel _ _ Hρ) Hr) HM).
Qed.

(** The same for a definition of a type of levels. *)
Corollary per_ctx_env_of_def_level : forall {Γ A M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A : LevelSort ->
    Γ ⊨ M : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ per_env_extend_def A M env_relΓ.
Proof.
  intros * HΓ HA HM.
  exact (per_ctx_env_of_def_evaluated evaluated_kind_level HΓ (rel_type_of_level_sort 0 HA) (rel_exp_of_level_sort_kind_at HΓ HA) HM).
Qed.

(** At a proposition, the canonical context PER of [Γ ▸ A ≔ M] is that of
    [Γ ▹ A]: the body is a proof, neither evaluated nor related, and the
    head is the proof [⋆ᵈ].  Stated for a type whose values at related
    environments are related propositions, as a type moved along a
    substitution is ([rel_exp_of_prop_sub_simple]). *)
Lemma per_ctx_env_of_def_prop_at : forall {Γ A M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_prop) ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ per_env_extend A A env_relΓ.
Proof.
  intros * HΓ HAp.
  assert (HPER : PER env_relΓ) by (eapply per_env_PER; eassumption).
  eapply per_ctx_env_cons_def
    with (head_rel := fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΓ) => per_head A A ρ ρ') (r := ak_propositional);
    [ exact HΓ | exact HPER | | | |].
  - intros ρ ρ' Hρ.
    destruct (HAp _ _ Hρ) as (a & a' & Ha & Ha' & Hp).
    pose proof (per_univ_elem_of_prop 0 _ _ Hp) as HR.
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ.
    destruct (HAp _ _ Hρ) as (a & a' & Ha & Ha' & [Hl _ _]).
    exists a; split; assumption.
  - intros; exact I.
  - intros ρ ρ'; split.
    + intros [Ht Hh Hl Hr Hrl Hrr]; apply (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ Ht);
        [ exact Hh | exact I | exact Hl | exact Hr | exact Hrl | exact Hrr ].
    + intros [Ht Hh _ Hl Hr Hrl Hrr]; exact (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht Hh Hl Hr Hrl Hrr).
Qed.

Corollary per_ctx_env_of_def_prop : forall {Γ A M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A : Propₘ ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ per_env_extend A A env_relΓ.
Proof. intros * HΓ HA; exact (per_ctx_env_of_def_prop_at HΓ (rel_exp_of_prop_inversion_simple_at HΓ HA)). Qed.

(** A definition of a type of either sort. *)
Lemma rel_ctx_wf_extend_def_sort : forall {Γ A S M},
    ⊨ Γ ->
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ M : A ->
    ⊨ Γ ▸ A ≔ M.
Proof.
  intros * HΓ HS HA HM.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [env_relΓ HΓ'].
  destruct HS as [i | |].
  - econstructor; [ eassumption | eapply per_ctx_env_of_def; eassumption | constructor | eassumption | eassumption ].
  - econstructor; [ eassumption | eapply per_ctx_env_of_def_prop; eassumption | constructor | eassumption | eassumption ].
  - econstructor; [ eassumption | eapply per_ctx_env_of_def_level; eassumption | constructor | eassumption | eassumption ].
Qed.

Corollary rel_ctx_wf_extend_def : forall {Γ A} {i : nat} {M},
    ⊨ Γ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    ⊨ Γ ▸ A ≔ M.
Proof. intros * HΓ HA HM; exact (rel_ctx_wf_extend_def_sort HΓ (type_sort_universe i) HA HM). Qed.

Hint Resolve rel_ctx_wf_extend_def : mctt.

End Fixed_GCtx.

Lemma sem_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof.
  intros * HA HS HM; sem_intro.
  apply valid_ctx_def; [ assumption | eapply rel_ctx_wf_extend_def_sort; eassumption ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A definition entry refines an assumption entry of the same type. *)
Lemma per_ctx_env_def_forget : forall {Γ κ A} {i : nat} {M R R'},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R ->
    EF Γ ▹{κ} A ≈ Γ ▹{κ} A ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * HA HM HR HR' ρ ρ' Hρ.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΓ [HΓ HAs]].
  pose proof (per_ctx_env_of_def HΓ HA HM) as Hd.
  pose proof (per_ctx_env_extend (κ := κ) HΓ HAs (rel_exp_of_typ_not_level_sort HA _ HΓ)) as Ha.
  assert (E1 : R <~> per_env_extend_def A M env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R' <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E2; apply E1 in Hρ.
  destruct Hρ as [? _]; assumption.
Qed.

(** The environments the context PER of an entry with a type relates have
    related tails and heads related at the head PER of the type: the part
    the variable rule reads, common to assumptions, definitions, and
    definitions with a module part. *)
Lemma per_ctx_env_head_split : forall {e Γ R A},
    ctx_entry_type (e :: nil) 0 = Some A ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    exists T, EF Γ ≈ Γ ∈ per_ctx_env ↘ T /\
      forall ρ ρ', Dom ρ ≈ ρ' ∈ R ->
        Dom ρ↯ ≈ ρ'↯ ∈ T /\ Dom ρ 0 ≈ ρ' 0 ∈ per_head A A ρ↯ ρ'↯.
Proof.
  intros * He HR.
  inversion HR; subst; cbn in He; try discriminate; injection He as <-;
    eexists; (split; [ eassumption |]); intros ρ ρ' Hρ;
    apply_relation_equivalence;
    destruct Hρ as [Ht Hh];
    (split; [ exact Ht |]);
    match goal with
    | Hty : forall ρ ρ' (_ : _ ρ ρ'), PER.Definitions.rel_typ _ _ _ _ _ _ |- _ =>
        destruct (Hty _ _ Ht)
    end;
    eapply per_head_of; eassumption.
Qed.

(** A type is of the kind [r] at every environment of every context PER
    of its context. *)
Definition rel_type_kind (Γ : ctx) (A : typ) (r : abs_kind) : Prop :=
  forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> rel_typ_kind A ρ r.

(** A type is of one evaluated kind ([rel_type_kind]): a type of a
    universe (of [ak_relevant]) or of [LevelSort] (of [ak_level]) is. *)
Definition rel_type_evaluated (Γ : ctx) (A : typ) : Prop :=
  exists r, evaluated_kind r /\ rel_type_kind Γ A r.

(** A type of a universe is of the relevant kind. *)
Lemma rel_type_kind_of_typ : forall {Γ A} {i : nat}, Γ ⊨ A : Typeω@i -> rel_type_kind Γ A ak_relevant.
Proof. intros * HA R HR ρ ρ' Hρ; exact (rel_exp_of_typ_relevant_at HR HA _ _ Hρ). Qed.

(** A type of levels is of the kind of levels. *)
Lemma rel_type_kind_of_level_sort : forall {Γ A}, Γ ⊨ A : LevelSort -> rel_type_kind Γ A ak_level.
Proof. intros * HA R HR ρ ρ' Hρ; exact (rel_exp_of_level_sort_kind_at HR HA _ _ Hρ). Qed.

Lemma rel_type_evaluated_of_typ : forall {Γ A} {i : nat}, Γ ⊨ A : Typeω@i -> rel_type_evaluated Γ A.
Proof. intros * HA; exists ak_relevant; split; [ constructor | exact (rel_type_kind_of_typ HA) ]. Qed.

Lemma rel_type_evaluated_of_level_sort : forall {Γ A}, Γ ⊨ A : LevelSort -> rel_type_evaluated Γ A.
Proof. intros * HA; exists ak_level; split; [ constructor | exact (rel_type_kind_of_level_sort HA) ]. Qed.

(** A type of an evaluated sort (a universe or [LevelSort]) is of an
    evaluated kind. *)
Lemma rel_type_evaluated_of_evaluated_sort : forall {Γ A Srt}, evaluated_sort Srt -> Γ ⊨ A : Srt -> rel_type_evaluated Γ A.
Proof. intros * [i |] HA; [ exact (rel_type_evaluated_of_typ HA) | exact (rel_type_evaluated_of_level_sort HA) ]. Qed.

(** A parameter type is of an evaluated kind. *)
Lemma rel_param_typed_evaluated : forall {Γ A l}, rel_param_typed Γ A l -> rel_type_evaluated Γ A.
Proof. intros * [HA | HA]; [ exact (rel_type_evaluated_of_typ HA) | exact (rel_type_evaluated_of_level_sort HA) ]. Qed.

(** A type of an evaluated kind is so at every environment of its
    context. *)
Lemma rel_typ_evaluated_at : forall {Γ A R}, rel_type_evaluated Γ A -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> rel_typ_evaluated A ρ.
Proof. intros * (r & Hr & HA) HR ρ ρ' Hρ; exact (rel_typ_evaluated_of_kind (HA _ HR _ _ Hρ) Hr). Qed.

(** An entry of a type of an evaluated kind is no proposition, at either
    environment of a related pair. *)
Lemma head_not_propositional_of_evaluated : forall {Γ e A} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    ctx_entry_type (e :: nil) 0 = Some A ->
    Γ ⊨ᵗ A ≈ A at i ->
    rel_type_evaluated Γ A ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ ->
      ~ head_propositional gc_deps gc_stack e Γ ρ /\ ~ head_propositional gc_deps gc_stack e Γ ρ'.
Proof.
  intros * HΓ He HA (r & Hr & HArel) ρ ρ' Hρ.
  pose proof (rel_type_inversion_simple_at HΓ HA) as HAs.
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (Hnp : forall ρ1 ρ1', Dom ρ1 ≈ ρ1' ∈ env_relΓ -> ~ head_propositional gc_deps gc_stack e Γ ρ1).
  { intros ρ1 ρ1' Hρ1 Hp.
    destruct (HArel _ HΓ _ _ Hρ1) as (a0 & Ea0 & <-).
    apply (head_propositional_iff HΓ He HAs Hρ1 Ea0) in Hp; exact (evaluated_kind_not_propositional _ Hr Hp). }
  split; [ exact (Hnp _ _ Hρ) | apply (Hnp ρ' ρ'); etransitivity; [ symmetry |]; exact Hρ ].
Qed.

(** Readability of the heads a head relation relates, at the stored types
    the values of the type at the two tails. *)
Lemma per_head_entry_readable : forall {S ρ ρ' a a' c c'} {i : nat} {R},
    ⟦ S ⟧ ρ ↘ a -> ⟦ S ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom c ≈ c' ∈ per_head S S ρ ρ' ->
    entry_readable (de_term c (entry_type_value a)) /\ entry_readable (de_term c' (entry_type_value a')).
Proof.
  intros * Ha Ha' HR Hc.
  exact (entry_readable_of_elem HR (Hc _ _ _ _ Ha Ha' HR)).
Qed.

(** The environments the context PER of a definition of a relevant type
    relates, with or without a module part, hold the body's value at both
    heads: what δ reads. *)
Lemma per_ctx_env_def_tie_split : forall {e Γ R A M},
    (e = ce_def A M \/ exists U, e = ce_dm A M U) ->
    rel_type_evaluated Γ A ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> def_tie A M ρ /\ def_tie A M ρ'.
Proof.
  intros * He (r0 & Hr0e & HA) HR ρ ρ' Hρ.
  destruct He as [-> | [U ->]]; inversion HR; subst; apply_relation_equivalence.
  - destruct Hρ as [Ht Hh Hterms _ _].
    (** The kind of the entry is evaluated: its type's is. *)
    destruct (HA _ equiv_Γ_Γ' _ _ Ht) as (b0 & Eb0 & Hr0).
    match goal with
    | Hs : forall ρ ρ' (_ : _ ρ ρ'), rel_typ_kind _ _ _ |- _ => destruct (Hs _ _ Ht) as (b1 & Eb1 & Hr1)
    end.
    assert (Eb : b0 = b1) by (eapply functional_eval_exp; eassumption).
    subst b1; rewrite Hr0 in Hr1; subst r; rewrite (def_heads_at_evaluated _ _ _ _ _ _ Hr0e) in Hterms.
    destruct Hterms as [[m [Hm Hmr]] _ [m' [Hm' Hmr']] _].
    match goal with
    | Hty : forall ρ ρ' (_ : _ ρ ρ'), PER.Definitions.rel_typ _ _ _ _ _ _ |- _ =>
        destruct (Hty _ _ Ht) as [a a' Ea Ea' Ha]
    end.
    split; [ exists m | exists m' ]; (split; [ assumption |]);
      intros k R0 b b' Eb Eb' HR0; functional_eval_rewrite_clear.
    + apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha HR0); exact Hmr.
    + apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Ha) HR0); exact Hmr'.
  - destruct Hρ as [Ht Hh Hterms _ _ _ _].
    destruct Hterms as [[m [Hm Hmr]] _ [m' [Hm' Hmr']] _].
    match goal with
    | Hty : forall ρ ρ' (_ : _ ρ ρ'), PER.Definitions.rel_typ _ _ _ _ _ _ |- _ =>
        destruct (Hty _ _ Ht) as [a a' Ea Ea' Ha]
    end.
    split; [ exists m | exists m' ]; (split; [ assumption |]);
      intros k R0 b b' Eb Eb' HR0; functional_eval_rewrite_clear.
    + apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha HR0); exact Hmr.
    + apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Ha) HR0); exact Hmr'.
Qed.

(** The same at a type of any sort.  At a proposition the two context
    PERs are the same: the body is neither evaluated nor related. *)
Lemma per_ctx_env_def_forget_sort : forall {Γ κ A S M R R'},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ M : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R ->
    EF Γ ▹{κ} A ≈ Γ ▹{κ} A ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * [i | |] HA HM HR HR'; [ eapply per_ctx_env_def_forget; eassumption | |].
  - intros ρ ρ' Hρ.
    pose proof (rel_type_inversion_simple (rel_type_of_prop 0 HA)) as [env_relΓ [HΓ HAs]].
    pose proof (per_ctx_env_of_def_prop (M := M) HΓ HA) as Hd.
    pose proof (per_ctx_env_extend (κ := κ) HΓ HAs (rel_type_not_level_sort_of_sort type_sort_prop HA _ HΓ)) as Ha.
    assert (E1 : R <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    assert (E2 : R' <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    apply E2, E1, Hρ.
  - (** A type of levels: as at a type of a universe, the heads tied to
        the body are heads of the assumption. *)
    intros ρ ρ' Hρ.
    pose proof (rel_type_inversion_simple (rel_type_of_level_sort 0 HA)) as [env_relΓ [HΓ HAs]].
    pose proof (per_ctx_env_of_def_level HΓ HA HM) as Hd.
    pose proof (per_ctx_env_extend (κ := κ) HΓ HAs (rel_type_not_level_sort_of_sort type_sort_level HA _ HΓ)) as Ha.
    assert (E1 : R <~> per_env_extend_def A M env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    assert (E2 : R' <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    apply E2; apply E1 in Hρ.
    destruct Hρ as [? _]; assumption.
Qed.

(** A definition with a module part does not refine an assumption entry:
    its environments' heads are not term entries, which an assumption's
    are ([per_ctx_env_cons_rel]).  Its variable is read directly
    ([valid_exp_under_ctx_var_here_dm]). *)

(** Definition entries of a type of an evaluated kind with related bodies
    relate the same environments. *)
Lemma per_ctx_env_def_conv_evaluated : forall {Γ A} {i : nat} {M M' R R'},
    Γ ⊨ᵗ A ≈ A at i ->
    rel_type_evaluated Γ A ->
    Γ ⊨ M ≈ M' : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R ->
    EF Γ ▸ A ≔ M' ≈ Γ ▸ A ≔ M' ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * HA (r & Hr & HArel) HM HR HR' ρ ρ' Hρ.
  pose proof (rel_type_under_ctx_not_level_sort _ _ _ _ HA) as HAn.
  pose proof (rel_type_inversion_simple HA) as [env_relΓ [HΓ HAs]].
  pose proof (per_ctx_env_of_def_evaluated Hr HΓ HA (HArel _ HΓ) (rel_exp_under_ctx_refl_left HM)) as Hd.
  pose proof (per_ctx_env_of_def_evaluated Hr HΓ HA (HArel _ HΓ) (rel_exp_under_ctx_refl_right HM)) as Hd'.
  pose proof (per_ctx_env_extend (κ := r) HΓ HAs (HAn _ HΓ)) as Ha.
  assert (E1 : R <~> per_env_extend_def A M env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R' <~> per_env_extend_def A M' env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend A A env_relΓ)) by (eapply per_env_PER; eassumption).
  apply E2; apply E1 in Hρ.
  destruct Hρ as [Hρ Ht Ht'].
  assert (Hρρ : Dom ρ ≈ ρ ∈ per_env_extend A A env_relΓ) by solve_per.
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ per_env_extend A A env_relΓ) by solve_per.
  pose proof (rel_type_inversion_simple_at HΓ HA) as HAat.
  pose proof (rel_exp_under_ctx_simple_at_of_evaluated HΓ
                (fun ρ1 ρ1' Hρ1 => rel_typ_evaluated_of_kind (HArel _ HΓ _ _ Hρ1) Hr) HM) as HMat.
  constructor; [ exact Hρ | |].
  - exact (def_tie_resp _ HAat HMat Hρρ Ht).
  - exact (def_tie_resp _ HAat HMat Hρ'ρ' Ht').
Qed.

(** Definition entries with related bodies relate the same environments. *)
Corollary per_ctx_env_def_conv : forall {Γ A} {i : nat} {M M' R R'},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M ≈ M' : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R ->
    EF Γ ▸ A ≔ M' ≈ Γ ▸ A ≔ M' ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * HA; exact (per_ctx_env_def_conv_evaluated (rel_type_of_typ HA) (rel_type_evaluated_of_typ HA)).
Qed.

(** A definition with a module part does not refine the definition entry
    of its term part either, for the same reason; its δ is read directly
    ([rel_exp_under_ctx_var_delta_here_dm]). *)

Lemma rel_ctx_sub_empty :
  SubE ⋅ <: ⋅.
Proof. mauto. Qed.

(** An assumption of a smaller type, the two types of sorts of one kind
    [κ] ([sort_kind]), so the two entries are of [κ]. *)
Lemma rel_ctx_sub_extend : forall {Γ Δ κ Srt Srt' A A'},
  SubE Γ <: Δ ->
  ⊨ Γ ->
  ⊨ Δ ->
  Γ ⊨ A : Srt ->
  sort_kind Srt κ ->
  Δ ⊨ A' : Srt' ->
  sort_kind Srt' κ ->
  Γ ⊨ A ⊆ A' ->
  SubE Γ ▹{κ} A <: Δ ▹{κ} A'.
Proof.
  intros * Hsub HΓ HΔ HA HS HA' HS' Hsubtyp.
  pose proof (rel_ctx_wf_extend_sort HΓ HS HA) as HΓA%rel_ctx_wf_per_ctx_env.
  pose proof (rel_ctx_wf_extend_sort HΔ HS' HA') as HΔA'%rel_ctx_wf_per_ctx_env.
  destruct HΓA as [env_relΓA HΓA], HΔA' as [env_relΔA' HΔA'].
  pose proof (rel_subtyp_under_ctx_simple Hsubtyp) as [env_relΓ [HΓ' [j Hsub2]]].
  econstructor; try eassumption.
  intros ρ ρ' a a' Hρ Ha Ha'.
  destruct (Hsub2 _ _ Hρ) as [a2 [a2' [Ha2 [Ha2' Hsubaa']]]].
  functional_eval_rewrite_clear.
  eassumption.
Qed.

Hint Resolve rel_ctx_sub_empty rel_ctx_sub_extend : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve per_ctx_extend rel_ctx_wf_extend rel_ctx_wf_extend_def : mctt.
#[export]
Hint Resolve rel_ctx_sub_empty rel_ctx_sub_extend : mctt.

(** The empty context, which has no relation of its own: [⊨ ⋅] is a
    constructor. *)
Lemma sem_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊨ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. intros * H; sem_intro; constructor. Qed.
