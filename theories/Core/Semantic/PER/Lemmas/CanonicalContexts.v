(** * PER Lemmas: Canonical Context PERs

    The sixth part of [Core.Semantic.PER.Lemmas]: the constructors and
    the inversion of [per_ctx_env], and the canonical context PERs of an
    extended context, a definition entry, a definition with a module part
    and a function. *)
From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions PER.Tele.
From Mctt.Core.Semantic.PER.Lemmas Require Export Contexts.
Import Domain_Notations Fixed_Notations.
Import ListNotations.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_env_cons_clean_inversion : forall {Γ Γ' env_relΓ κ A A' env_relΓA},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ ->
    EF Γ ▹{κ} A ≈ Γ' ▹{κ} A' ∈ per_ctx_env ↘ env_relΓA ->
    exists i (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ env_relΓ), relation domain),
      (forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ env_relΓ),
          rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> value_not_level_sort A ρ) /\
        (env_relΓA <~> per_ctx_env_cons_rel env_relΓ (@head_rel) A A').
Proof.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists.
  split; [| split; [ intros ρ ρ' Hρ; match goal with HN : forall ρ ρ', tail_rel ρ ρ' -> value_not_level_sort A _ |- _ =>
                                       apply (HN ρ ρ'); intuition end |] ]; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ i A ρ A' ρ' R ->
                          Dom m ≈ m' ∈ R).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel; intuition.
  - intros ρ ρ'.
    split; intros [Ht Hh Hl Hr];
      [ assert (Ht' : Dom ρ↯ ≈ ρ'↯ ∈ env_relΓ) by intuition
      | assert (Ht' : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition ];
      apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht'); try assumption;
      (on_all_hyp: destruct_rel_by_assumption tail_rel); intros; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel; intuition.
Qed.

End Fixed_GCtx.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; destruct H as [? [? [? []]]])
  + (inversion H; subst).

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** ** A Canonical Extended Context PER

    [per_ctx_env_cons] leaves the head relation of an extended context
    existentially quantified and indexed by the evidence relating the tails.
    The completeness cases for substitutions build the context PER of
    [Δ ▹ S] and relate four environments in it, so they would have to produce
    the head evidence once per link of the chain.

    [per_head] names the head relation once, impredicatively:
    [per_head S S' ρ ρ'] relates what every [per_univ_elem] relating the
    values of [S] and [S'] in [ρ] and [ρ'] relates.  [per_ctx_extend] makes
    the same choice.  [per_head] does not mention the tail evidence, so the
    extended PER [per_env_extend] is a conjunction rather than a dependent
    pair. *)

Definition per_head (S S' : typ) (ρ ρ' : env) : relation domain :=
  fun m m' =>
    forall i R a a',
      ⟦ S ⟧ ρ ↘ a ->
      ⟦ S' ⟧ ρ' ↘ a' ->
      DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m' ∈ R.

Definition per_env_extend (S S' : typ) (R : relation env) : relation env :=
  per_ctx_env_cons_rel R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head S S' ρ ρ') S S'.

(** [per_head] is the PER the types denote, because evaluation is functional
    and [per_univ_elem] is irrelevant in its relation argument.  This direction
    has the content, and it is the one completeness needs: a [per_head] from
    an element PER already at hand. *)
Lemma per_head_of : forall {S S' ρ ρ' i R a a' m m'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom m ≈ m' ∈ R ->
    Dom m ≈ m' ∈ per_head S S' ρ ρ'.
Proof.
  intros * Ha Ha' HR Hm.
  hnf; intros * Ha0 Ha0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** The converse instantiates the universal quantification at the witness. *)
Corollary per_head_iff : forall {S S' ρ ρ' i R a a'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    R <~> per_head S S' ρ ρ'.
Proof.
  intros * Ha Ha' HR m m'; split.
  - intros Hm. eapply per_head_of; eassumption.
  - intros Hm. eapply Hm; eassumption.
Qed.

(** Hence any related pair of type values is a [per_univ_elem] at the head PER
    of the expressions they came from.  A type judgment reports a level and an
    anonymous element PER, whereas a semantic recursion needs its motive at the
    head PER; this lemma keeps the level and replaces the PER. *)
Corollary per_univ_elem_at_head : forall {S S' ρ ρ' i a a'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    Dom a ≈ a' ∈ per_univ i ->
    DF a ≈ a' ∈ per_univ_elem i ↘ (per_head S S' ρ ρ').
Proof.
  intros * Ha Ha' [R HR].
  eapply per_univ_elem_resp_iff; [ exact HR |].
  eapply per_head_iff; eassumption.
Qed.

(** The head PER of a type does not depend on which environments of a related
    family it is read in: any two evaluations of [S] and [S'] whose four values
    form a chain give the same relation.  This lets a judgment proved at one
    pair of environments be used at another, as in every rule whose type is an
    instantiated codomain. *)
Lemma per_head_resp : forall {S S' ρ1 ρ2 ρ3 ρ4 i a1 a2 a3 a4},
    ⟦ S ⟧ ρ1 ↘ a1 ->
    ⟦ S' ⟧ ρ2 ↘ a2 ->
    ⟦ S ⟧ ρ3 ↘ a3 ->
    ⟦ S' ⟧ ρ4 ↘ a4 ->
    rel_chain (per_univ i) ([a1; a2; a3; a4]) ->
    per_head S S' ρ1 ρ2 <~> per_head S S' ρ3 ρ4.
Proof.
  intros * Ha1 Ha2 Ha3 Ha4 Hchain.
  assert (H12 : Dom a1 ≈ a2 ∈ per_univ i) by pairwise.
  destruct H12 as [R HR].
  (** Refining the chain to [R] identifies the two head PERs: each is [R] by
      [per_head_iff], at its own pair of type values. *)
  assert (HchainR : rel_chain (per_univ_elem i R) ([a1; a2; a3; a4]))
    by (eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in).
  assert (H34 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ R) by pairwise.
  etransitivity; [ symmetry; eapply per_head_iff; [ exact Ha1 | exact Ha2 | exact HR ] |].
  eapply per_head_iff; [ exact Ha3 | exact Ha4 | exact H34 ].
Qed.

(** [per_head_resp] for an elimination rule, where the two pairs of
    environments differ only in their heads.  There the codomain judgment is
    available at any related pair of arguments, and each link of the chain is
    an instance of it; the middle one is at the crossing pair [(u, y)].  That
    relatedness is a premise rather than derived: [RN] is a PER at every use,
    but requiring it would oblige every caller to provide the instance. *)
Lemma per_head_of_args : forall {i B ρ ρ' t t' RN},
    (forall x y,
        Dom x ≈ y ∈ RN ->
        exists b b',
          ⟦ B ⟧ ρ ↦ x ⦂ t ↘ b /\ ⟦ B ⟧ ρ' ↦ y ⦂ t' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    forall x y u v,
      Dom x ≈ y ∈ RN ->
      Dom u ≈ v ∈ RN ->
      Dom u ≈ y ∈ RN ->
      per_head B B (ρ ↦ x ⦂ t) (ρ' ↦ y ⦂ t') <~> per_head B B (ρ ↦ u ⦂ t) (ρ' ↦ v ⦂ t').
Proof.
  intros * Hcod * Hxy Huv Huy.
  destruct (Hcod _ _ Hxy) as [bx [by0 [Hbx [Hby0 Hb_xy]]]].
  destruct (Hcod _ _ Huv) as [bu [bv [Hbu [Hbv Hb_uv]]]].
  destruct (Hcod _ _ Huy) as [bu0 [by1 [Hbu0 [Hby1 Hb_uy]]]].
  assert (bu0 = bu) as -> by (eapply functional_eval_exp; eassumption).
  assert (by1 = by0) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Hbx | exact Hby0 | exact Hbu | exact Hbv |].
  apply rel_chain_4; [ exact Hb_xy | symmetry; exact Hb_uy | exact Hb_uv ].
Qed.

(** The codomain at one argument pair, as a [per_univ_elem] at the head PER of
    another pair.  This is how an element PER provided by a judgment is
    identified with the canonical one: irrelevance needs a shared type value,
    which is the codomain's value at the pair the judgment was read at, while
    the PER wanted is the one at the pair the goal names. *)
Corollary per_head_anchor : forall {i B ρ ρ' t t' RN},
    (forall x y,
        Dom x ≈ y ∈ RN ->
        exists b b',
          ⟦ B ⟧ ρ ↦ x ⦂ t ↘ b /\ ⟦ B ⟧ ρ' ↦ y ⦂ t' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    forall x y u v,
      Dom x ≈ y ∈ RN ->
      Dom u ≈ v ∈ RN ->
      Dom u ≈ y ∈ RN ->
      exists b b',
        ⟦ B ⟧ ρ ↦ x ⦂ t ↘ b /\ ⟦ B ⟧ ρ' ↦ y ⦂ t' ↘ b' /\
          DF b ≈ b' ∈ per_univ_elem i
               ↘ (per_head B B (ρ ↦ u ⦂ t) (ρ' ↦ v ⦂ t')).
Proof.
  intros * Hcod * Hxy Huv Huy.
  destruct (Hcod _ _ Hxy) as [b [b' [Hb [Hb' [R HR]]]]].
  exists b, b'.
  do 2 (split; [ eassumption |]).
  eapply per_univ_elem_resp_iff; [ exact HR |].
  etransitivity;
    [ eapply per_head_iff; [ exact Hb | exact Hb' | exact HR ]
    | eapply per_head_of_args; eassumption ].
Qed.

(** The premise of [per_ctx_env_cons], at the canonical head relation.  Its
    own premise has the shape that [rel_exp_of_typ_inversion_simple]
    provides. *)
Lemma per_ctx_env_extend : forall {Δ Δ' κ S S' env_relΔ} {i : nat},
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ env_relΔ ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists a a',
          ⟦ S ⟧ ρ ↘ a /\ ⟦ S' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔ -> value_not_level_sort S ρ) ->
    EF Δ ▹{κ} S ≈ Δ' ▹{κ} S' ∈ per_ctx_env ↘ per_env_extend S S' env_relΔ.
Proof.
  intros * HΔ HS HSn.
  eapply (per_ctx_env_cons' (i := i) (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΔ) => per_head S S' ρ ρ'));
    [ eassumption | | exact HSn | ].
  - intros ρ ρ' Hρ.
    destruct (HS _ _ Hρ) as [a [a' [Ha [Ha' [R HR]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ'; split; intros H; exact H.
Qed.

(** The introduction rule of [per_env_extend].  It applies to any pair of
    environments whose heads are term entries at a proposition, not only
    to literal extensions.  Completeness needs this generality: it places
    both [⟪q ψ⟫ ρ] and [⟦σ ,, M⟧s ρ] in an extended context PER, and only
    the latter is a literal [ρ ↦ m]. *)
Lemma per_env_extend_intro : forall {S S' R ρ ρ'},
    Dom ρ↯ ≈ ρ'↯ ∈ R ->
    Dom (ρ 0) ≈ (ρ' 0) ∈ per_head S S' ρ↯ ρ'↯ ->
    (rel_typ_propositional S ρ↯ -> exists t, env_entry ρ 0 = de_term (ρ 0) t) ->
    (rel_typ_propositional S' ρ'↯ -> exists t, env_entry ρ' 0 = de_term (ρ' 0) t) ->
    head_readable 0 (env_entry ρ 0) ->
    head_readable 0 (env_entry ρ' 0) ->
    Dom ρ ≈ ρ' ∈ per_env_extend S S' R.
Proof.
  intros * Ht Hh Hl Hr Hrl Hrr.
  exact (mk_per_ctx_env_cons_rel _ (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head S S' ρ ρ') _ _ _ _ Ht Hh Hl Hr Hrl Hrr).
Qed.

(** [per_env_extend_intro] for a literal extension [ρ ↦ m ⦂ t].  The
    premises of the general rule mention [(ρ ↦ m ⦂ t) ↯] and
    [(ρ ↦ m ⦂ t) 0]; these are convertible to [ρ] and [m], but the tactics
    that discharge head obligations match syntactically. *)
Corollary per_env_extend_intro' : forall {S S' R ρ ρ' m m' t t'},
    Dom ρ ≈ ρ' ∈ R ->
    Dom m ≈ m' ∈ per_head S S' ρ ρ' ->
    entry_readable (de_term m t) ->
    entry_readable (de_term m' t') ->
    Dom ρ ↦ m ⦂ t ≈ ρ' ↦ m' ⦂ t' ∈ per_env_extend S S' R.
Proof.
  intros * ? ? ? ?; apply per_env_extend_intro;
    first [ assumption | intros _; eexists; reflexivity | split; [ assumption | cbn; lia ] ].
Qed.

(** ** A Canonical Context PER for a Definition Entry

    [def_tie S M ρ] says that the head of [ρ] is the value of [M] in the tail
    of [ρ], up to the head PER of [S].  Two environments are related at
    [Δ ▸ S ≔ M] when they are related at [Δ ▹ S] and each satisfies the
    tie. *)
Definition def_tie (S : typ) (M : exp) (ρ : env) : Prop :=
  exists m, ⟦ M ⟧ ρ↯ ↘ m /\ Dom m ≈ (ρ 0) ∈ per_head S S ρ↯ ρ↯.

Record per_env_extend_def (S : typ) (M : exp) (R : relation env) (ρ ρ' : env) : Prop := mk_per_env_extend_def
  { per_env_extend_def_ext : Dom ρ ≈ ρ' ∈ per_env_extend S S R
  ; per_env_extend_def_tie_left : def_tie S M ρ
  ; per_env_extend_def_tie_right : def_tie S M ρ' }.

(** The head PER of a type is the same at any two related pairs of tails. *)
Lemma per_head_resp_simple : forall {S R i},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    forall ρ1 ρ2 ρ3 ρ4,
      rel_chain R ([ρ1; ρ2; ρ3; ρ4]) ->
      per_head S S ρ1 ρ2 <~> per_head S S ρ3 ρ4.
Proof.
  intros * HPER HS * Hchain.
  assert (H12 : Dom ρ1 ≈ ρ2 ∈ R) by pairwise.
  assert (H32 : Dom ρ3 ≈ ρ2 ∈ R) by pairwise.
  assert (H34 : Dom ρ3 ≈ ρ4 ∈ R) by pairwise.
  destruct (HS _ _ H12) as [a1 [a2 [Ha1 [Ha2 Ha12]]]].
  destruct (HS _ _ H32) as [a3 [a2' [Ha3 [Ha2' Ha32]]]].
  destruct (HS _ _ H34) as [a3' [a4 [Ha3' [Ha4 Ha34]]]].
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 |].
  apply rel_chain_4; [ exact Ha12 | symmetry; exact Ha32 | exact Ha34 ].
Qed.

(** The premise [per_ctx_env_cons_def] asks for, at the canonical relation,
    at a type of an evaluated kind [r]. *)
Lemma per_ctx_env_extend_def : forall {Δ S M env_relΔ r} {i : nat},
    evaluated_kind r ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔ -> rel_typ_kind S ρ r) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    EF Δ ▸ S ≔ M ≈ Δ ▸ S ≔ M ∈ per_ctx_env ↘ per_env_extend_def S M env_relΔ.
Proof.
  intros * Hev HΔ HS HSr HM.
  assert (HPER : PER env_relΔ) by (eapply per_env_PER; eassumption).
  eapply per_ctx_env_cons_def
    with (head_rel := fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΔ) => per_head S S ρ ρ') (r := r);
    [ eassumption | eassumption | | | |].
  - intros ρ ρ' Hρ.
    destruct (HS _ _ Hρ) as [a [a' [Ha [Ha' [R HR]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - exact HSr.
  - intros ρ ρ' Hρ.
    destruct (HM _ _ Hρ) as [m [m' [Hm [Hm' Hmm']]]].
    rewrite def_bodies_at_evaluated by exact Hev.
    econstructor; eassumption.
  - intros ρ ρ'.
    (** A tie at a single environment and a tie read across the related pair
        are the same, since the head PER does not depend on the tails. *)
    assert (Hmove : forall ρ1 ρ2,
               Dom ρ1 ≈ ρ2 ∈ env_relΔ ->
               (per_head S S ρ1 ρ1 <~> per_head S S ρ1 ρ2) /\
                 (per_head S S ρ2 ρ2 <~> per_head S S ρ1 ρ2)).
    { intros ρ1 ρ2 H12.
      assert (H11 : Dom ρ1 ≈ ρ1 ∈ env_relΔ) by solve_per.
      assert (H22 : Dom ρ2 ≈ ρ2 ∈ env_relΔ) by solve_per.
      split; eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per. }
    split.
    + intros [[Ht Hh Hl Hr] [m [Hm Htie]] [m' [Hm' Htie']]].
      destruct (Hmove _ _ Ht) as [H1 H2].
      apply (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ Ht); try assumption.
      rewrite def_heads_at_evaluated by exact Hev; constructor.
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
    + intros [Ht Hh Hd Hl Hr]; rewrite def_heads_at_evaluated in Hd by exact Hev.
      destruct Hd as [[m [Hm Htie]] _ [m' [Hm' Htie']] _].
      destruct (Hmove _ _ Ht) as [H1 H2].
      constructor; [ apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht Hh Hl Hr); assumption | |].
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
Qed.

(** ** A Canonical Context PER for a Definition with a Module Part

    Two environments are related at [Δ ▸ₘ S ≔ M ‖ U] when their tails are
    related, their heads' terms are related and tied to [M], as at
    [Δ ▸ S ≔ M], and the head of each is tied to the closure of [U] over
    its tail.  The heads are not term entries, so the relation is not
    [per_env_extend_def]'s.  [n] is the length of the tail context, which
    scopes the heads' stored units, as for a module slot
    ([per_ctx_env_mod_rel]). *)
Record per_env_extend_dm (S : typ) (M : exp) (U : gunit) (n : nat) (R : relation env) (ρ ρ' : env) : Prop := mk_per_env_extend_dm
  { (** The tails are related *)
    per_env_extend_dm_tail : Dom ρ↯ ≈ ρ'↯ ∈ R
    (** The heads' terms are related at the head PER *)
  ; per_env_extend_dm_head : Dom (ρ 0) ≈ (ρ' 0) ∈ per_head S S ρ↯ ρ'↯
    (** The left head's term is tied to [M] *)
  ; per_env_extend_dm_term_left : def_tie S M ρ
    (** So is the right one's *)
  ; per_env_extend_dm_term_right : def_tie S M ρ'
    (** The left head's module tied to the closure of [U] over its tail *)
  ; per_env_extend_dm_tie_left : tie_mod (env_mod ρ 0) (me_lit U) ρ↯
    (** The right head's module tied likewise *)
  ; per_env_extend_dm_tie_right : tie_mod (env_mod ρ' 0) (me_lit U) ρ'↯
    (** The left head reads back at its stored type, its stored unit
        scoped by the tail *)
  ; per_env_extend_dm_left_readable : head_readable n (env_entry ρ 0)
    (** So does the right one *)
  ; per_env_extend_dm_right_readable : head_readable n (env_entry ρ' 0)
    (** The left head is a definition with a module part, at some type and
        unit *)
  ; per_env_extend_dm_left_kind : exists t U0, env_entry ρ 0 = de_dm (ρ 0) t (env_mod ρ 0) U0
    (** So is the right one *)
  ; per_env_extend_dm_right_kind : exists t U0, env_entry ρ' 0 = de_dm (ρ' 0) t (env_mod ρ' 0) U0 }.

(** The premise [per_ctx_env_cons_dm] asks for, at the canonical relation. *)
Lemma per_ctx_env_extend_dm : forall {Δ S M U env_relΔ} {i : nat},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    gunit_free_bound U <= List.length Δ ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔ -> rel_typ_kind S ρ ak_relevant) ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔ -> rel_modexp_evals (me_lit U) ρ (me_lit U) ρ') ->
    EF Δ ▸ₘ S ≔ M ‖ U ≈ Δ ▸ₘ S ≔ M ‖ U ∈ per_ctx_env ↘ per_env_extend_dm S M U (List.length Δ) env_relΔ.
Proof.
  intros * HΔ HbU HS HM HSr HU.
  assert (HPER : PER env_relΔ) by (eapply per_env_PER; eassumption).
  eapply per_ctx_env_cons_dm
    with (head_rel := fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΔ) => per_head S S ρ ρ') (r := ak_relevant);
    [ eassumption | eassumption | exact HbU | exact HbU | | | | | | reflexivity ].
  - intros ρ ρ' Hρ.
    destruct (HS _ _ Hρ) as [a [a' [Ha [Ha' [R HR]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - exact HSr.
  - intros ρ ρ' Hρ.
    destruct (HM _ _ Hρ) as [m [m' [Hm [Hm' Hmm']]]].
    econstructor; eassumption.
  - exact HU.
  - intros ρ ρ'.
    assert (Hmove : forall ρ1 ρ2,
               Dom ρ1 ≈ ρ2 ∈ env_relΔ ->
               (per_head S S ρ1 ρ1 <~> per_head S S ρ1 ρ2) /\
                 (per_head S S ρ2 ρ2 <~> per_head S S ρ1 ρ2)).
    { intros ρ1 ρ2 H12.
      assert (H11 : Dom ρ1 ≈ ρ1 ∈ env_relΔ) by solve_per.
      assert (H22 : Dom ρ2 ≈ ρ2 ∈ env_relΔ) by solve_per.
      split; eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per. }
    split.
    + intros [Ht Hh [m [Hm Htie]] [m' [Hm' Htie']] Tl Tr Hrl Hrr Hkl Hkr].
      destruct (Hmove _ _ Ht) as [H1 H2].
      exists Ht; try eassumption.
      constructor.
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
    + intros [Ht Hh [[m [Hm Htie]] _ [m' [Hm' Htie']] _] Tl _ Tr _ Hrl Hrr Hkl Hkr].
      destruct (Hmove _ _ Ht) as [H1 H2].
      apply (mk_per_env_extend_dm _ _ _ _ _ _ _ Ht Hh); try eassumption.
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
Qed.

(** The tie propagates along the relation of an assumption entry, and from a
    body to a related one.  So it is enough to establish it at one environment
    of a chain. *)
Lemma def_tie_resp : forall {S M M' R i ρ ρ'},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    Dom ρ ≈ ρ' ∈ per_env_extend S S R ->
    def_tie S M ρ ->
    def_tie S M' ρ'.
Proof.
  intros * HPER HS HM [Ht Hh] [m [Hm Htie]].
  assert (H11 : Dom ρ↯ ≈ ρ↯ ∈ R) by solve_per.
  assert (H22 : Dom ρ'↯ ≈ ρ'↯ ∈ R) by solve_per.
  destruct (HM _ _ Ht) as [m1 [m2 [Hm1 [Hm2 Hm12]]]].
  assert (m1 = m) as -> by (eapply functional_eval_exp; eassumption).
  exists m2; split; [ eassumption |].
  assert (E1 : per_head S S ρ↯ ρ↯ <~> per_head S S ρ↯ ρ'↯)
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  assert (E2 : per_head S S ρ'↯ ρ'↯ <~> per_head S S ρ↯ ρ'↯)
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  apply E2; apply E1 in Htie.
  destruct (HS _ _ Ht) as [a [a' [Ha [Ha' [R' HR']]]]].
  pose proof (per_head_iff Ha Ha' HR') as E3.
  assert (PER R') by (eapply per_elem_PER; eassumption).
  apply E3; apply E3 in Htie, Hh, Hm12.
  solve_per.
Qed.

(** Transporting a [per_head] to another pair of environments, the bridging
    step of the completeness proofs.  The two head relations are equal because
    their types are related in [per_univ]: the first two evaluations and the
    PER describe the source types, the next two evaluations the target types,
    and the last premise relates the two left types.  That suffices because
    [per_univ_elem] is irrelevant on either side. *)
Lemma per_head_bridge : forall {S S' ρ ρ' T T' u u' i R a a' b b' m m'},
    Dom m ≈ m' ∈ per_head S S' ρ ρ' ->
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    ⟦ T ⟧ u ↘ b ->
    ⟦ T' ⟧ u' ↘ b' ->
    Dom a ≈ b ∈ per_univ i ->
    Dom m ≈ m' ∈ per_head T T' u u'.
Proof.
  intros * Hm Ha Ha' HR Hb Hb' [? Hab].
  assert (Hmm : Dom m ≈ m' ∈ R) by (eapply Hm; eassumption).
  hnf; intros * Hb0 Hb0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** ** A Canonical Function PER

    The same construction one level down.  [per_univ_elem_core_pi] leaves the
    codomain family [out_rel] existentially quantified and indexed by the
    evidence relating the two arguments, so a Π-value's element PER is
    determined only up to that choice.  The four-value pattern of a Π-type
    compares Π-values whose codomain expressions and environments all differ
    ([B[q σ]] at [ρ], [B] at [⟦σ⟧ρ], …), yet all its links must be at one
    element PER.

    [per_pi] names the family canonically, with [per_head] as the codomain
    relation: the PER the codomain denotes at [ρ ↦ c] and [ρ' ↦ c'] is a head
    PER.  It is independent of the evidence and of the level, so one [per_pi]
    serves every link. *)

Definition per_pi (a a' : domain) (in_rel : relation domain) (B : typ) (ρ : env) (B' : typ) (ρ' : env) : relation domain :=
  pi_elements a a' in_rel (fun c c' (_ : Dom c ≈ c' ∈ in_rel) =>
    per_head B B' (ρ ↦ c ⦂ entry_type_value a) (ρ' ↦ c' ⦂ entry_type_value a')).

(** Building a Π-value at [per_pi].  The codomain premise has the element PER
    existentially quantified, which is the shape a four-value chain provides
    after [destruct_per_univ_chain]; [per_head_iff] turns any such PER into the
    canonical one. *)
Lemma per_univ_elem_pi_canonical : forall {i κd κc a a' in_rel ρ B ρ' B'},
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b' R,
          ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\
          ⟦ B' ⟧ ρ' ↦ c' ⦂ entry_type_value a' ↘ b' /\
          DF b ≈ b' ∈ per_univ_elem i ↘ R) ->
    (forall c c', Dom c ≈ c' ∈ in_rel -> rel_typ_kind B (ρ ↦ c ⦂ entry_type_value a) κc) ->
    domain_kind a = κd -> domain_kind a' = κd -> pi_kinds κd κc -> evaluated_kind κc ->
    not_level_sort a ->
    (forall c c', Dom c ≈ c' ∈ in_rel -> value_not_level_sort B (ρ ↦ c ⦂ entry_type_value a)) ->
    DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem i ↘ (per_pi a a' in_rel B ρ B' ρ').
Proof.
  intros * Ha HB HBr Hd Hd' Hk Hev Hna HnB.
  eapply (per_univ_elem_pi' _ _ _ _ _ _ _ _ _ in_rel
            (fun c c' (_ : Dom c ≈ c' ∈ in_rel) =>
               per_head B B' (ρ ↦ c ⦂ entry_type_value a) (ρ' ↦ c' ⦂ entry_type_value a')));
    [ eassumption | | exact HBr | exact Hd | exact Hd' | exact Hk | exact Hev | exact Hna | exact HnB | reflexivity ].
  intros c c' equiv_c_c'.
  destruct (HB _ _ equiv_c_c') as [b [b' [R [Hb [Hb' HR]]]]].
  econstructor; try eassumption.
  eapply per_univ_elem_resp_iff; [ eassumption |].
  eapply per_head_iff; eassumption.
Qed.

(** Whatever PER a Π-value carries, it is [per_pi]; this justifies
    application.  The two levels are unrelated, since [per_univ_elem]
    irrelevance is cross-level, so a Π-type from one judgment and a domain from
    another need no lifting. *)
Corollary per_pi_iff : forall {i j κd κc a a' in_rel ρ B ρ' B' R},
    evaluated_kind κc ->
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem j ↘ R ->
    R <~> per_pi a a' in_rel B ρ B' ρ'.
Proof.
  intros * Hev Ha HΠ.
  invert_per_univ_elem HΠ.
  rename x into out_rel; rename H into Hout; rename H0 into HR.
  (** [HR] identifies [R] with the family-indexed relation; it remains to show
      the family is pointwise the canonical head PER.  Transitivity of
      [relation_equivalence] must be used before introducing the two values:
      afterwards the goal is a [pointwise_lifting], where neither [rewrite] nor
      [etransitivity] applies. *)
  etransitivity; [ exact HR |].
  intros f f'; split; intros [Hl Hr Hf]; constructor; try assumption; intros c c' equiv_c_c';
    specialize (Hf _ _ equiv_c_c');
    destruct (Hout _ _ equiv_c_c') as [b b' Hb Hb' Hbb'].
  - rewrite <- (per_head_iff Hb Hb' Hbb'); exact Hf.
  - rewrite (per_head_iff Hb Hb' Hbb'); exact Hf.
Qed.

(** The four-value pattern of a Π-type at one element PER, as required by
    every semantic judgment whose type is a Π.  Each link is built by
    [per_univ_elem_pi_canonical] at its own codomain pair and so carries its
    own [per_pi]; the three agree by irrelevance, since consecutive links share
    a Π-value.  The chain is stated at the inner link's PER: the only link
    whose sides are both unsubstituted, and the one an application reads its
    output PER from.

    The domain is a four-value pattern already at [in_rel], which by weak
    functionality is what a semantic type judgment provides
    ([functionalize_per_univ_chain]).  The three codomain premises are, in
    order, the three obligations produced by [rel_exp_of_typ_under_ctx_q]. *)
Lemma per_univ_elem_pi_chain : forall {i κd κc in_rel a1 a2 a3 a4 B1 ρ1 B2 ρ2 B3 ρ3 B4 ρ4},
    rel_chain (per_univ_elem i in_rel) ([a1; a2; a3; a4]) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B1 ⟧ ρ1 ↦ c ⦂ entry_type_value a1 ↘ b /\ ⟦ B2 ⟧ ρ2 ↦ c' ⦂ entry_type_value a2 ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B2 ⟧ ρ2 ↦ c ⦂ entry_type_value a2 ↘ b /\ ⟦ B3 ⟧ ρ3 ↦ c' ⦂ entry_type_value a3 ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B3 ⟧ ρ3 ↦ c ⦂ entry_type_value a3 ↘ b /\ ⟦ B4 ⟧ ρ4 ↦ c' ⦂ entry_type_value a4 ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    (forall c c', Dom c ≈ c' ∈ in_rel -> rel_typ_kind B1 (ρ1 ↦ c ⦂ entry_type_value a1) κc) ->
    domain_kind a1 = κd -> pi_kinds κd κc -> evaluated_kind κc ->
    not_level_sort a1 ->
    (forall c c', Dom c ≈ c' ∈ in_rel -> value_not_level_sort B1 (ρ1 ↦ c ⦂ entry_type_value a1)) ->
    rel_chain (per_univ_elem i (per_pi a2 a3 in_rel B2 ρ2 B3 ρ3))
      ([d_pi κd κc a1 ρ1 B1; d_pi κd κc a2 ρ2 B2; d_pi κd κc a3 ρ3 B3; d_pi κd κc a4 ρ4 B4]).
Proof.
  intros * Hchain HB12 HB23 HB34 HB1r Hd1 Hk Hev Hn1 HB1n.
  assert (H12 : DF a1 ≈ a2 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H23 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H34 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (Hd2 : domain_kind a2 = κd) by (rewrite <- (per_univ_elem_kind _ _ _ _ H12); exact Hd1).
  assert (Hd3 : domain_kind a3 = κd) by (rewrite <- (per_univ_elem_kind _ _ _ _ H23); exact Hd2).
  assert (Hd4 : domain_kind a4 = κd) by (rewrite <- (per_univ_elem_kind _ _ _ _ H34); exact Hd3).
  pose proof (per_elem_PER H12) as Hin.
  (** The codomains along the chain are relevant, each related to the one
      before at an argument related to itself. *)
  assert (Hmove : forall B ρ t B' ρ' t',
             (forall c c',
                 Dom c ≈ c' ∈ in_rel ->
                 exists b b', ⟦ B ⟧ ρ ↦ c ⦂ t ↘ b /\ ⟦ B' ⟧ ρ' ↦ c' ⦂ t' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
             (forall c c', Dom c ≈ c' ∈ in_rel -> rel_typ_kind B (ρ ↦ c ⦂ t) κc) ->
             (forall c c', Dom c ≈ c' ∈ in_rel -> rel_typ_kind B' (ρ' ↦ c ⦂ t') κc)).
  { intros * HB HBr c c' Hc.
    assert (Hcc : Dom c ≈ c ∈ in_rel) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
    destruct (HB _ _ Hcc) as [b [b' [Hb [Hb' [R HR]]]]].
    destruct (HBr _ _ Hcc) as (b0 & Hb0 & Hr0).
    assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
    exists b'; split; [ exact Hb' | rewrite <- (per_univ_elem_kind _ _ _ _ HR); exact Hr0 ]. }
  pose proof (Hmove _ _ _ _ _ _ HB12 HB1r) as HB2r.
  pose proof (Hmove _ _ _ _ _ _ HB23 HB2r) as HB3r.
  (** So are they not [LevelSort], nor the domains. *)
  assert (Hmoven : forall B ρ t B' ρ' t',
             (forall c c',
                 Dom c ≈ c' ∈ in_rel ->
                 exists b b', ⟦ B ⟧ ρ ↦ c ⦂ t ↘ b /\ ⟦ B' ⟧ ρ' ↦ c' ⦂ t' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
             (forall c c', Dom c ≈ c' ∈ in_rel -> value_not_level_sort B (ρ ↦ c ⦂ t)) ->
             (forall c c', Dom c ≈ c' ∈ in_rel -> value_not_level_sort B' (ρ' ↦ c ⦂ t'))).
  { intros * HB HBn c c' Hc.
    assert (Hcc : Dom c ≈ c ∈ in_rel) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
    destruct (HB _ _ Hcc) as [b [b' [Hb [Hb' [R HR]]]]].
    destruct (HBn _ _ Hcc) as (b0 & Hb0 & Hn0).
    assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
    exists b'; split; [ exact Hb' | exact (proj1 (per_univ_elem_not_level_sort_iff _ _ _ _ HR) Hn0) ]. }
  pose proof (Hmoven _ _ _ _ _ _ HB12 HB1n) as HB2n.
  pose proof (Hmoven _ _ _ _ _ _ HB23 HB2n) as HB3n.
  pose proof (proj1 (per_univ_elem_not_level_sort_iff _ _ _ _ H12) Hn1) as Hn2.
  pose proof (proj1 (per_univ_elem_not_level_sort_iff _ _ _ _ H23) Hn2) as Hn3.
  (** One [per_univ_elem_pi_canonical] per link, adapting the premise's
      [per_univ] to the [exists R] the lemma wants. *)
  assert (Hlink : forall B ρ B' ρ' a a',
             DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
             (forall c c',
                 Dom c ≈ c' ∈ in_rel ->
                 exists b b', ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\ ⟦ B' ⟧ ρ' ↦ c' ⦂ entry_type_value a' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
             (forall c c', Dom c ≈ c' ∈ in_rel -> rel_typ_kind B (ρ ↦ c ⦂ entry_type_value a) κc) ->
             domain_kind a = κd -> domain_kind a' = κd ->
             not_level_sort a ->
             (forall c c', Dom c ≈ c' ∈ in_rel -> value_not_level_sort B (ρ ↦ c ⦂ entry_type_value a)) ->
             DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem i ↘ (per_pi a a' in_rel B ρ B' ρ')).
  { intros * Ha HB HBr Hda Hda' Hna HBn.
    apply per_univ_elem_pi_canonical;
      [ eassumption | | exact HBr | exact Hda | exact Hda' | exact Hk | exact Hev | exact Hna | exact HBn ].
    intros c c' Hc.
    destruct (HB _ _ Hc) as [b [b' [Hb [Hb' [R HR]]]]].
    exists b, b', R; repeat split; eassumption. }
  pose proof (Hlink _ _ _ _ _ _ H12 HB12 HB1r Hd1 Hd2 Hn1 HB1n) as HL1.
  pose proof (Hlink _ _ _ _ _ _ H23 HB23 HB2r Hd2 Hd3 Hn2 HB2n) as HL2.
  pose proof (Hlink _ _ _ _ _ _ H34 HB34 HB3r Hd3 Hd4 Hn3 HB3n) as HL3.
  (** The three links are a chain in [per_univ i], so weak functionality puts
      them at one PER, and uniqueness, with [HL2] as anchor, makes it the inner
      link's.  [handle_per_univ_elem_irrel] would keep an unpredictable one of
      the three [per_pi]s. *)
  assert (Hpi : rel_chain (per_univ i)
                  ([d_pi κd κc a1 ρ1 B1; d_pi κd κc a2 ρ2 B2;
                   d_pi κd κc a3 ρ3 B3; d_pi κd κc a4 ρ4 B4]))
    by (apply rel_chain_4; eexists; eassumption).
  functionalize_per_univ_chain Hpi R.
  retype_rel_chain Hpi HL2 Hpi.
  exact Hpi.
Qed.

(** ** Closing an Extended Context PER Goal

    Every completeness proof in an extended context ends the same way, with
    these three tactics.

    - [destruct_per_univ_chain] turns a four-value chain in [per_univ i] into
      the three [per_univ_elem] hypotheses that [handle_per_univ_elem_irrel]
      works on.  It goes through [per_univ_chain_functional], so the three are
      at one element PER rather than three independent ones.
    - [solve_per_head] discharges a [per_head] goal.  [per_head] quantifies
      over an arbitrary [per_univ_elem] relating the two type values, so the
      proof is always the same: introduce it, identify its two values with
      known ones, let irrelevance identify its PER with that of the term
      chain, and read the pair off that chain.
    - [solve_per_env_extend_chain] relates a chain of extended environments in
      an extended context PER.  [per_env_extend_intro'] splits each link into
      a tail and a head; the tails come from the chain of the underlying
      substitution, and the heads are bridged.  The chain may have any length:
      substitution cases need four environments, while rules with a premise in
      an extended context need every extension of the four tails by either of
      the two heads. *)
End Fixed_GCtx.

Ltac destruct_per_univ_chain H :=
  apply per_univ_chain_functional in H;
  destruct H as [? H];
  destruct H as [? [? ?]].

Ltac solve_per_head :=
  hnf; intros ? ? ? ? ? ? ?;
  functional_eval_rewrite_clear;
  handle_per_univ_elem_irrel;
  pairwise.

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** The links are peeled by matching the goal's shape rather than with
    [first]: [rel_chain R [x; y]] is convertible to [R x y], so an unguarded
    [apply rel_chain_of_pair] would also fire on a link goal, and an unguarded
    [apply rel_chain_cons] would peel past the last link. *)
Ltac solve_per_env_extend_chain :=
  repeat
    match goal with
    | |- rel_chain _ ([_; _]) => apply rel_chain_of_pair
    | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
    end;
  apply per_env_extend_intro';
    first [ pairwise | solve_per_head | assumption ].

