(** * Fundamental Theorem: the Propositions

    [Prop] is a small type, its elements the propositions ([per_prop]); a
    proposition is a type of every index, its only element the proof
    [⋆ᵈ] ([per_proof]).  The propositions here are [⊤], [⊥] and the
    dependent conjunction [Σₚ]: each is a proposition by its head and reads
    back as itself, so each formation rule is a chain in [per_prop].

    A term judgment at a proposition asks nothing of the terms: at a type
    whose value is a proposition, the terms are proofs, which evaluation
    never reaches ([type_propositional]).  So every proof rule — [⋆], the
    proof of a conjunction and its two components, and proof irrelevance —
    is the one lemma [rel_exp_under_ctx_proof]: a valid proposition is
    inhabited by every pair of terms.

    Ex falso is stuck at its type, a neutral at a relevant one
    ([eval_exp_absurd]), so its rule is realisability: related types relate
    the neutrals of related readbacks.

    The placeholder type is a small relevant type, all of whose elements are
    related ([per_placeholder]). *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Propositions as Elements of [Prop] *)

(** [⊤] and [⊥] are propositions by their heads, and read back as
    themselves. *)
Lemma per_prop_True : Dom ⊤ᵈ ≈ ⊤ᵈ ∈ per_prop.
Proof. constructor; [ reflexivity | reflexivity | intros s; exists ⊤ⁿ; split; constructor ]. Qed.

Lemma per_prop_False : Dom ⊥ᵈ ≈ ⊥ᵈ ∈ per_prop.
Proof. constructor; [ reflexivity | reflexivity | intros s; exists ⊥ⁿ; split; constructor ]. Qed.

(** A closed proposition, in [Prop] at every substitution. *)
Lemma rel_exp_of_prop_const : forall {Γ A a env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    (forall ρ, ⟦ A ⟧ ρ ↘ a) ->
    (forall σ, A[σ] = A) ->
    Dom a ≈ a ∈ per_prop ->
    Γ ⊨ A ≈ A : Propₘ.
Proof.
  intros * HΓ Hev Hs Ha.
  apply rel_exp_of_prop; eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hevσ Hevσ'.
  apply (mk_rel_exp a a a a); [ rewrite Hs; apply Hev | apply Hev | apply Hev | rewrite Hs; apply Hev |].
  apply rel_chain_4; exact Ha.
Qed.

Lemma rel_exp_of_prop_True : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ⊤ ≈ ⊤ : Propₘ.
Proof.
  intros * HΓ; eapply rel_exp_of_prop_const;
    [ exact HΓ | intros; apply eval_exp_True | reflexivity | exact per_prop_True ].
Qed.

Lemma rel_exp_of_prop_False : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ⊥ ≈ ⊥ : Propₘ.
Proof.
  intros * HΓ; eapply rel_exp_of_prop_const;
    [ exact HΓ | intros; apply eval_exp_False | reflexivity | exact per_prop_False ].
Qed.

(** ** Proofs

    Every pair of terms is related at a valid proposition: the type's
    chain is in [per_proof] by [per_univ_elem_of_prop], and the terms are
    not compared. *)
Lemma rel_exp_under_ctx_proof : forall {Γ P M M'},
    Γ ⊨ P : Propₘ ->
    Γ ⊨ M ≈ M' : P.
Proof.
  intros * HP.
  pose proof (rel_exp_of_prop_inversion HP) as [env_relΓ [HΓ HPgen]].
  eexists_rel_exp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HPgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [p1 p2 p3 p4 Hp1 Hp2 Hp3 Hp4 Hchain].
  exists per_proof; split.
  - apply (mk_rel_exp p1 p2 p3 p4); try assumption.
    eapply rel_chain_mono; [| exact Hchain ]; intros ? ? Hp; exact (per_univ_elem_of_prop 0 _ _ Hp).
  - left; exists p1; split; [ exact Hp1 |].
    destruct Hchain as [[Hl _ _] _]; exact Hl.
Qed.

(** ** Ex Falso

    The value of [efq M return C] is the neutral of the value [c] of [C],
    the proof [⋆ᵈ] when [c] is a proposition.  Related types read back
    equally, so the neutrals do, and realisability relates them. *)
Lemma per_bot_absurd : forall {c c'},
    Dom c ≈ c' ∈ per_top_typ ->
    Dom efqᵈ c ≈ efqᵈ c' ∈ per_bot.
Proof.
  intros * Hc s; destruct (Hc s) as [C [HC HC']].
  exists (efqⁿ C); split; constructor; assumption.
Qed.

Lemma per_elem_absurd : forall {i R c c'},
    DF c ≈ c' ∈ per_univ_elem i ↘ R ->
    Dom relevant_value c (⇑ c (efqᵈ c)) ≈ relevant_value c' (⇑ c' (efqᵈ c')) ∈ R.
Proof.
  intros * Hc; apply (per_bot_then_per_elem Hc), per_bot_absurd, (per_univ_then_per_top_typ Hc).
Qed.

Lemma rel_exp_under_ctx_absurd : forall {Γ C C' M M'} {i : nat},
    Γ ⊨ᵗ C ≈ C at i ->
    Γ ⊨ᵗ C ≈ C' at i ->
    Γ ⊨ efq M return C ≈ efq M' return C' : C.
Proof.
  intros * HCl HC.
  pose proof (rel_type_inversion HCl) as [env_relΓl [HΓl HClgen]].
  pose proof (rel_type_inversion HC) as [env_relΓ [HΓ HCgen]].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HClgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hlchain].
  destruct (HCgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [e1 e2 e3 e4 He1 He2 He3 He4 Hchain].
  functional_eval_rewrite_clear.
  functionalize_per_univ_chain Hlchain R.
  (** The type's element PER relates the values of [C] and of [C']. *)
  assert (HR12 : per_univ_elem i R c1 c2) by pairwise.
  assert (Hc' : rel_chain (per_univ_elem i R) ([c1; c2; e3; e4]))
    by (eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR12 ]; solve_in).
  exists R; split.
  - apply (mk_rel_exp c1 c2 c3 c4); assumption.
  - right.
    eapply mk_rel_exp; [ eapply eval_exp_absurd; exact Hc1 | eapply eval_exp_absurd; exact Hc2
                         | eapply eval_exp_absurd; exact He3 | eapply eval_exp_absurd; exact He4 |].
    destruct Hc' as (H12 & H23 & H34).
    apply rel_chain_4; eapply (per_elem_absurd (i := i)); eassumption.
Qed.

(** A type of either sort and one equal to it are types of one index. *)
Lemma rel_type_pair_of_sort : forall {Γ C C' Srt},
    type_sort Srt ->
    Γ ⊨ C : Srt ->
    Γ ⊨ C ≈ C' : Srt ->
    exists i, Γ ⊨ᵗ C ≈ C at i /\ Γ ⊨ᵗ C ≈ C' at i.
Proof.
  intros * [i |] HC HCC'.
  - exists i; split; apply rel_type_of_typ; assumption.
  - exists 0; split; apply rel_type_of_prop; assumption.
Qed.

(** ** The Conjunction

    A conjunction's second component is a family of propositions over its
    first, read back under the proof [⋆ᵈ].  Its instance along a lifted
    substitution, at three pairs of arguments, in [per_prop]: the proof of
    [rel_exp_of_univ_under_ctx_q], at [Prop] rather than at a universe. *)
Lemma rel_exp_of_prop_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ▹ A ⊨ B ≈ B' : Propₘ ->
    forall ρ ρ' ρσ ρ'σ' c c',
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_prop) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_prop) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_prop).
Proof.
  intros * HΓ Hσj HA HB * Hpair Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_prop_inversion HB) as [env_relΔA [HΔA HBgen]].
  pose proof (rel_exp_of_prop_inversion_simple_at HΔA (rel_exp_under_ctx_refl_left HB)) as HBl.
  pose proof (rel_exp_of_prop_inversion_simple_at HΔA (rel_exp_under_ctx_refl_right HB)) as HBr.
  destruct (rel_sub_under_ctx_q_at HΓ HΔA Hσj HA _ _ _ _ _ _ Hpair Hev Hev')
    as [s [s' [Hq [Hq' Hchain]]]].
  destruct (HBgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq')
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  (** The four bridges, at four pairs the chain above relates. *)
  assert (P1 : Dom s ↦ c ≈ ρσ ↦ c' ∈ env_relΔA) by pairwise.
  assert (P2 : Dom ρσ ↦ c ≈ s ↦ c ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ≈ ρ'σ' ↦ c' ∈ env_relΔA) by pairwise.
  assert (P4 : Dom ρ'σ' ↦ c ≈ s' ↦ c' ∈ env_relΔA) by pairwise.
  destruct (HBl _ _ P1) as [x1 [x2 [Hx1 [Hx2 Hx]]]].
  destruct (HBl _ _ P2) as [y1 [y2 [Hy1 [Hy2 Hy]]]].
  destruct (HBr _ _ P3) as [z1 [z2 [Hz1 [Hz2 Hz]]]].
  destruct (HBr _ _ P4) as [t1 [t2 [Ht1 [Ht2 Ht]]]].
  assert (x1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (y2 = b2) by (eapply functional_eval_exp; eassumption).
  assert (z1 = b3) by (eapply functional_eval_exp; eassumption).
  assert (t2 = b3) by (eapply functional_eval_exp; eassumption).
  subst.
  apply rel_chain_of_pair in Hx, Hy, Hz, Ht.
  assert (M1 : rel_chain per_prop ([b1; b2; b3; b4; x2]))
    by (merge_rel_chain Hbchain Hx b2).
  assert (M2 : rel_chain per_prop ([y1; b1; b2; b3; b4; x2]))
    by (merge_rel_chain M1 Hy b2).
  assert (M3 : rel_chain per_prop ([y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M2 Hz b3).
  assert (M4 : rel_chain per_prop ([t1; y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M3 Ht b3).
  split; [| split ].
  - exists b1, x2; split; [ eassumption | split; [ eassumption | pairwise ] ].
  - exists y1, z2; split; [ eassumption | split; [ eassumption | pairwise ] ].
  - exists t1, b4; split; [ eassumption | split; [ eassumption | pairwise ] ].
Qed.

(** Two conjunctions with related first components whose second components
    are related at the proof are related propositions. *)
Lemma per_prop_and : forall {p p' ρ ρ' Q Q' b b'},
    Dom p ≈ p' ∈ per_prop ->
    ⟦ Q ⟧ ρ ↦ ⋆ᵈ ↘ b ->
    ⟦ Q' ⟧ ρ' ↦ ⋆ᵈ ↘ b' ->
    Dom b ≈ b' ∈ per_prop ->
    Dom Σₚᵈ p ρ Q ≈ Σₚᵈ p' ρ' Q' ∈ per_prop.
Proof.
  intros * [Hpl Hpr Hp] Hb Hb' [_ _ Hbb].
  constructor; [ reflexivity | reflexivity |].
  intros s; destruct (Hp s) as [P [HP HP']]; destruct (Hbb (S s)) as [B [HB HB']].
  exists (Σₚⁿ P B); split;
    (eapply read_typ_and; [ eassumption | rewrite relevant_value_propositional by assumption; eassumption
                           | eassumption ]).
Qed.

Lemma rel_exp_under_ctx_and : forall {Γ P P' Q Q'},
    Γ ⊨ P : Propₘ ->
    Γ ⊨ P ≈ P' : Propₘ ->
    Γ ▹ P ⊨ Q ≈ Q' : Propₘ ->
    Γ ⊨ Σₚ P Q ≈ Σₚ P' Q' : Propₘ.
Proof.
  intros * HPl HP HQ.
  pose proof (rel_type_of_prop 0 HPl) as HPt.
  pose proof (rel_exp_of_prop_inversion HP) as [env_relΓ [HΓ HPgen]].
  apply rel_exp_of_prop; eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HPgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [p1 p2 p3 p4 Hp1 Hp2 Hp3 Hp4 Hpchain].
  (** The proofs are related at [P[σ]], a proposition. *)
  assert (Hext : Dom ρ ↦ ⋆ᵈ ≈ ρ' ↦ ⋆ᵈ ∈ per_env_extend P[σ] P[σ] env_rel').
  { apply per_env_extend_intro'; [ exact Hρ |].
    eapply per_head_proof; [ exact Hp1 |]; destruct Hpchain as [[Hl _ _] _]; exact Hl. }
  destruct (rel_exp_of_prop_under_ctx_q HΓ' Hσj HPt HQ _ _ _ _ _ _ Hext Hev Hev')
    as [[b1 [b2 [Hb1 [Hb2 Hb12]]]] [[c2 [c3 [Hc2 [Hc3 Hc23]]]] [d3 [d4 [Hd3 [Hd4 Hd34]]]]]].
  functional_eval_rewrite_clear.
  destruct Hpchain as (H12 & H23 & H34).
  apply (mk_rel_exp (Σₚᵈ p1 ρ Q[q σ]) (Σₚᵈ p2 ρσ Q) (Σₚᵈ p3 ρ'σ' Q') (Σₚᵈ p4 ρ' Q'[q σ']));
    [ econstructor; exact Hp1 | econstructor; exact Hp2 | econstructor; exact Hp3 | econstructor; exact Hp4 |].
  apply rel_chain_4; eapply per_prop_and; eassumption.
Qed.

(** ** [Prop] and the Placeholder Type as Small Types *)

Lemma rel_exp_of_univ_const : forall {Γ A a u R env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    (forall ρ, ⟦ A ⟧ ρ ↘ a) ->
    (forall σ, A[σ] = A) ->
    domain_relevance a = relevant ->
    DF a ≈ a ∈ per_univ_elem u ↘ R ->
    Γ ⊨ A ≈ A : universe_index_term u.
Proof.
  intros * HΓ Hev Hs Hr Ha.
  apply rel_exp_of_univ; eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hevσ Hevσ'.
  apply (mk_rel_exp a a a a); [ rewrite Hs; apply Hev | apply Hev | apply Hev | rewrite Hs; apply Hev |].
  apply rel_chain_4; (constructor; [ eexists; exact Ha | exact Hr | exact Hr ]).
Qed.

Lemma rel_exp_of_univ_prop : forall {Γ u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ Propₘ ≈ Propₘ : universe_index_term u.
Proof.
  intros * HΓ; eapply rel_exp_of_univ_const;
    [ exact HΓ | intros; apply eval_exp_prop | reflexivity | reflexivity | apply per_univ_elem_prop_univ ].
Qed.

Lemma per_univ_elem_placeholder : forall i,
    DF d_placeholder_type ≈ d_placeholder_type ∈ per_univ_elem i ↘ per_placeholder.
Proof. intros; basic_per_univ_elem_econstructor; reflexivity. Qed.

Lemma rel_exp_of_univ_placeholder_type : forall {Γ u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ a_placeholder_type ≈ a_placeholder_type : universe_index_term u.
Proof.
  intros * HΓ; eapply rel_exp_of_univ_const;
    [ exact HΓ | intros; apply eval_exp_placeholder_type | reflexivity | reflexivity
    | apply per_univ_elem_placeholder ].
Qed.

(** Every pair of terms is related at the placeholder type, as soon as they
    have values: its elements are equal by η. *)
Lemma rel_exp_under_ctx_placeholder : forall {Γ M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    (forall σ ρ, exists m, ⟦ M[σ] ⟧ ρ ↘ m) ->
    (forall ρ, exists m, ⟦ M ⟧ ρ ↘ m) ->
    (forall σ ρ, exists m, ⟦ M'[σ] ⟧ ρ ↘ m) ->
    (forall ρ, exists m, ⟦ M' ⟧ ρ ↘ m) ->
    Γ ⊨ M ≈ M' : a_placeholder_type.
Proof.
  intros * HΓ H1 H2 H3 H4.
  eexists_rel_exp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists per_placeholder; split.
  - apply (mk_rel_exp d_placeholder_type d_placeholder_type d_placeholder_type d_placeholder_type);
      try apply eval_exp_placeholder_type.
    apply rel_chain_4; apply per_univ_elem_placeholder.
  - right.
    destruct (H1 σ ρ) as [m1 Hm1]; destruct (H2 ρσ) as [m2 Hm2];
      destruct (H4 ρ'σ') as [m3 Hm3]; destruct (H3 σ' ρ') as [m4 Hm4].
    apply (mk_rel_exp m1 m2 m3 m4); try assumption.
    apply rel_chain_4; exact I.
Qed.

End Fixed_GCtx.

(** ** The Rules *)

Lemma sem_prop :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Propₘ : Type@0 ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_univ_prop (u := us (0, 0)) HΓ).
Qed.

Lemma sem_exp_eq_prop_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Propₘ ≈ Propₘ : Type@0 ).
Proof. intros; eapply sem_prop; eassumption. Qed.

Lemma sem_True :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊤ : Propₘ ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_prop_True HΓ).
Qed.

Lemma sem_exp_eq_True_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊤ ≈ ⊤ : Propₘ ).
Proof. intros; eapply sem_True; eassumption. Qed.

Lemma sem_true :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⋆ : ⊤ ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_under_ctx_proof (rel_exp_of_prop_True HΓ)).
Qed.

Lemma sem_star :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⋆ : P ).
Proof.
  intros * _ HP; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HP).
Qed.

Lemma sem_False :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊥ : Propₘ ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_prop_False HΓ).
Qed.

Lemma sem_exp_eq_False_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊥ ≈ ⊥ : Propₘ ).
Proof. intros; eapply sem_False; eassumption. Qed.

Lemma sem_exp_eq_absurd_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ C : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ C ≈ C' : Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ efq M return C ≈ efq M' return C' : C ).
Proof.
  intros * HC HS HCC' _ _; sem_intro; [ assumption |].
  destruct (rel_type_pair_of_sort HS HC HCC') as [i [Hl Hr]].
  exact (rel_exp_under_ctx_absurd Hl Hr).
Qed.

Lemma sem_absurd :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ C : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ efq M return C : C ).
Proof. intros; eapply sem_exp_eq_absurd_cong; eassumption. Qed.

Lemma sem_exp_eq_and_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ P ≈ P' : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹ P ⊨ Q ≈ Q' : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Σₚ P Q ≈ Σₚ P' Q' : Propₘ ).
Proof.
  intros * HP HPP' HQ; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_and HP HPP' HQ).
Qed.

Lemma sem_and :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹ P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Σₚ P Q : Propₘ ).
Proof. intros; eapply sem_exp_eq_and_cong; eassumption. Qed.

Lemma sem_conj :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ T : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ T ≈ Σₚ P Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹ P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Q[Id,,M] ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_conj T M N : T ).
Proof.
  intros * HT _ _ _ _ _; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HT).
Qed.

Lemma sem_left :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹ P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_left M : P ).
Proof.
  intros * HP _ _; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HP).
Qed.

Lemma sem_right :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹ P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Q[Id,,a_left M] : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_right M : Q[Id,,a_left M] ).
Proof.
  intros * _ _ _ HQ; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HQ).
Qed.

Lemma sem_exp_eq_irrelevant :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : P ).
Proof.
  intros * HP _ _; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HP).
Qed.

Lemma sem_placeholder_type :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_placeholder_type : Type@0 ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_univ_placeholder_type (u := us (0, 0)) HΓ).
Qed.

Lemma sem_exp_eq_placeholder_type_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_placeholder_type ≈ a_placeholder_type : Type@0 ).
Proof. intros; eapply sem_placeholder_type; eassumption. Qed.

Lemma sem_placeholder :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_placeholder : a_placeholder_type ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  apply (rel_exp_under_ctx_placeholder HΓ); intros; eexists; apply eval_exp_placeholder.
Qed.

Lemma sem_exp_eq_placeholder_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_placeholder ≈ a_placeholder : a_placeholder_type ).
Proof. intros; eapply sem_placeholder; eassumption. Qed.

(** η at the placeholder type: the term's values against the placeholder's,
    all related. *)
Lemma sem_exp_eq_placeholder_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : a_placeholder_type ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ a_placeholder : a_placeholder_type ).
Proof.
  intros * HM; sem_intro; [ assumption |].
  destruct HM as [env_relΓ HΓ i HMgen].
  refine (mk_rel_exp_under_ctx _ _ _ _ env_relΓ HΓ 0 _).
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  assert (Hr : rel_typ_sort a_placeholder_type ρσ relevant)
    by (exists d_placeholder_type; split; [ apply eval_exp_placeholder_type | reflexivity ]).
  apply (rel_exp_or_prop_relevant Htyp Hr) in Hexp.
  destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 _].
  exists per_placeholder; split.
  - apply (mk_rel_exp d_placeholder_type d_placeholder_type d_placeholder_type d_placeholder_type);
      try apply eval_exp_placeholder_type.
    apply rel_chain_4; apply per_univ_elem_placeholder.
  - right; apply (mk_rel_exp m1 m2 d_placeholder d_placeholder); try assumption; try apply eval_exp_placeholder.
    apply rel_chain_4; exact I.
Qed.
