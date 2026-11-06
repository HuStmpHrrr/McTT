(** * PER Lemmas: Types of Levels, Cumulativity and Subtyping

    The third part of [Core.Semantic.PER.Lemmas]: the types of levels in
    the universe PER, its constructors and inversion, cumulativity and
    the subtyping PER [per_subtyp]. *)
From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions PER.Tele.
From Mctt.Core.Semantic.PER.Lemmas Require Export Universe.
Import Domain_Notations Fixed_Notations.
Import ListNotations.

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** [pairwise] at a [per_univ i] goal, supplying the existential that the
    refined chain no longer carries. *)
Ltac pairwise_univ := first [ pairwise | eexists; pairwise ].

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The other half of weak functionality: the output PER is unique, so
    [S ⊆_R ↘ R'] is well defined.  One value shared with any other element of
    the universe determines [R']: the chain is at a PER, so it is reflexive at
    that value, and irrelevance then needs no second value. *)
Lemma per_univ_chain_rel_irrel : forall {i j R R' l x y},
    rel_chain (per_univ_elem i R) l ->
    DF x ≈ y ∈ per_univ_elem j ↘ R' ->
    In x l ->
    R <~> R'.
Proof.
  intros * Hchain Hanchor Hx.
  assert (Hxx : DF x ≈ x ∈ per_univ_elem i ↘ R)
    by (eapply rel_chain_refl; first [ eassumption | solve_chain_PER ]).
  eapply per_univ_elem_right_irrel; [ exact Hxx | exact Hanchor ].
Qed.

End Fixed_GCtx.

(** [retype_rel_chain Htyp Hanchor H] moves [H] between the element PER of the
    type chain [Htyp] and the one [Hanchor] names.  The two need share only
    one value.  Only [H] determines the direction, so both are tried.  [H] may
    be a [rel_chain] (rewritten through [rel_chain_Proper]) or a bare pair,
    either at the relation itself or under the [per_head] of a type the anchor
    is about. *)
Ltac retype_rel_chain Htyp Hanchor H :=
  let Hiff := fresh "Hiff" in
  pose proof (per_univ_chain_rel_irrel Htyp Hanchor ltac:(solve_in)) as Hiff;
  first [ rewrite Hiff in H | rewrite <- Hiff in H ];
  clear Hiff.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** A value of the kind of levels is not the sort [LevelSort], which is of
    the relevant kind. *)
Lemma level_kind_not_level_sort : forall a, domain_kind a = ak_level -> not_level_sort a.
Proof. intros a Hk ->; discriminate Hk. Qed.

(** Nor is a proposition. *)
Lemma propositional_kind_not_level_sort : forall a, domain_kind a = ak_propositional -> not_level_sort a.
Proof. intros a Hk ->; discriminate Hk. Qed.

(** Two elements of a sort's PER — a universe's or [Prop]'s — are not the
    sort [LevelSort]: it is of no sort ([per_universe_elements],
    [per_prop]). *)
Lemma sort_element_not_level_sort : forall i R s s' a a',
    DF s ≈ s' ∈ per_univ_elem i ↘ R ->
    (exists j, s = 𝕌ω@j) \/ (exists l, s = 𝕌@l) \/ s = Propᵈ ->
    Dom a ≈ a' ∈ R ->
    not_level_sort a /\ not_level_sort a'.
Proof.
  intros * H Hs Ha.
  destruct Hs as [[j ->] | [[l ->] | ->]]; basic_invert_per_univ_elem H; apply_relation_equivalence.
  1-2: destruct Ha as [_ _ _ Hnl Hnr]; split; assumption.
  destruct Ha as [Hl Hr _]; split; apply propositional_kind_not_level_sort; assumption.
Qed.

(** The [per_univ_elem] rule for [Π] without its PER premise. *)
Lemma per_univ_elem_pi' :
  forall i κd κc a a' ρ B ρ' B'
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain)
    elem_rel,
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    (forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
        rel_mod_eval (per_univ_elem i) B (ρ ↦ c ⦂ entry_type_value a) B' (ρ' ↦ c' ⦂ entry_type_value a') (out_rel equiv_c_c')) ->
    (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_typ_kind B (ρ ↦ c ⦂ entry_type_value a) κc) ->
    domain_kind a = κd ->
    domain_kind a' = κd ->
    pi_kinds κd κc ->
    evaluated_kind κc ->
    not_level_sort a ->
    (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), value_not_level_sort B (ρ ↦ c ⦂ entry_type_value a)) ->
    (elem_rel <~> pi_elements a a' in_rel (@out_rel)) ->
    DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem i ↘ elem_rel.
Proof.
  intros.
  basic_per_univ_elem_econstructor; eauto.
  typeclasses eauto.
Qed.

(** ** Types of Levels *)

(** A type of levels is of the kind of levels. *)
Lemma level_code_kind : forall a, level_code a -> domain_kind a = ak_level.
Proof. intros a (R & a' & [H | H]); apply per_level_code_kind in H; destruct H; assumption. Qed.

(** The heads of a type of levels: [Level@n] or a [Π] between types of
    levels.  No variable is of [LevelSort], so no neutral is a type of
    levels. *)
Lemma level_code_head : forall a, level_code a ->
    (exists n, a = Levelᵈ@n) \/ (exists a0 ρ B, a = Πₗᵈ a0 ρ B).
Proof.
  intros a (R & a' & [H | H]); destruct H;
    first [ left; eexists; reflexivity | right; do 3 eexists; reflexivity ].
Qed.

(** Every type of levels is a type of every universe index. *)
Lemma per_level_code_univ_elem : forall R a a', per_level_code R a a' ->
    forall i, DF a ≈ a' ∈ per_univ_elem i ↘ R.
Proof.
  apply (per_level_code_strong_ind (fun R a a' => forall i, DF a ≈ a' ∈ per_univ_elem i ↘ R)).
  - intros n elem_rel HE i; basic_per_univ_elem_econstructor; exact HE.
  - intros a a' ρ ρ' B B' in_rel out_rel elem_rel Ha IHa Hper HT HE i.
    destruct (per_level_code_kind _ _ _ Ha) as [Hk Hk'].
    eapply (per_univ_elem_pi' _ _ _ _ _ _ _ _ _ in_rel (@out_rel));
      [ apply IHa | | | exact Hk | exact Hk' | constructor | constructor | | | exact HE ].
    + intros c c' Hc; destruct (HT _ _ Hc) as [b b' Eb Eb' [Hb IHb]].
      econstructor; [ exact Eb | exact Eb' | apply IHb ].
    + intros c c' Hc; destruct (HT _ _ Hc) as [b b' Eb Eb' [Hb _]].
      exists b; split; [ exact Eb | exact (proj1 (per_level_code_kind _ _ _ Hb)) ].
    + exact (level_kind_not_level_sort _ Hk).
    + intros c c' Hc; destruct (HT _ _ Hc) as [b b' Eb Eb' [Hb _]].
      exists b; split; [ exact Eb | exact (level_kind_not_level_sort _ (proj1 (per_level_code_kind _ _ _ Hb))) ].
Qed.

(** The domain of a [Π] type of levels is one. *)
Lemma level_code_pi_domain : forall a ρ B, level_code (Πₗᵈ a ρ B) -> level_code a.
Proof.
  intros * (R & z & [H | H]); inversion H; subst; do 2 eexists; [ left | right ]; eassumption.
Qed.

(** Its codomain is one at every argument its domain's PER relates to
    itself, whatever type the PER is read at. *)
Lemma level_code_pi_codomain : forall a ρ B i in_rel a2,
    level_code (Πₗᵈ a ρ B) ->
    DF a ≈ a2 ∈ per_univ_elem i ↘ in_rel ->
    forall c b, Dom c ≈ c ∈ in_rel -> ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b -> level_code b.
Proof.
  intros * (R & z & [H | H]) Ha c b Hc Eb; inversion H; subst.
  - match goal with Hd : per_level_code ?in0 a ?a0 |- _ =>
      assert (E : in_rel <~> in0) by (eapply per_univ_elem_right_irrel; [ exact Ha | exact (per_level_code_univ_elem _ _ _ Hd i) ])
    end.
    match goal with HT : forall c c' (_ : ?in0 c c'), rel_mod_eval per_level_code B _ _ _ _ |- _ =>
      destruct (HT c c (proj1 (E c c) Hc)) as [b1 b1' Eb1 _ Hb1]
    end.
    assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
    do 2 eexists; left; exact Hb1.
  - match goal with Hd : per_level_code ?in0 ?a0 a |- _ =>
      assert (E : in_rel <~> in0) by (eapply per_univ_elem_cross_irrel; [ exact Ha | exact (per_level_code_univ_elem _ _ _ Hd i) ])
    end.
    match goal with HT : forall c c' (_ : ?in0 c c'), rel_mod_eval per_level_code _ _ B _ _ |- _ =>
      destruct (HT c c (proj1 (E c c) Hc)) as [b1 b1' _ Eb1' Hb1]
    end.
    assert (b1' = b) as -> by (eapply functional_eval_exp; eassumption).
    do 2 eexists; right; exact Hb1.
Qed.

(** Two related types of a universe index that are types of levels are
    related types of levels, at the same relation. *)
Lemma per_univ_elem_level_code : forall i R a a',
    DF a ≈ a' ∈ per_univ_elem i ↘ R -> level_code a -> level_code a' -> per_level_code R a a'.
Proof.
  intros * H; per_univ_elem_induction H; intros Hl Hl'.
  all: try (destruct (level_code_head _ Hl) as [(? & [=]) | (? & ? & ? & [=])]; fail).
  - econstructor; eassumption.
  - exfalso; match goal with Hp : per_prop _ _ |- _ =>
      destruct Hp as [Hpl _ _]; rewrite (level_code_kind _ Hl) in Hpl; discriminate Hpl end.
  - (** A [Π]: between types of levels, the domains and the codomains
        are types of levels. *)
    destruct (level_code_head _ Hl) as [(? & [=]) | (? & ? & ? & [= -> -> <- <- <-])].
    destruct_conjs.
    econstructor; [ apply IHH; [ eapply level_code_pi_domain; exact Hl | eapply level_code_pi_domain; exact Hl' ]
                  | eassumption | | eassumption ].
    intros c c' Hc.
    assert (Hcc : Dom c ≈ c ∈ in_rel) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
    assert (Hc'c' : Dom c' ≈ c' ∈ in_rel) by (etransitivity; [ symmetry; exact Hc | exact Hc ]).
    match goal with HT : forall c c' (_ : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
      destruct (HT _ _ Hc) as [b b' Eb Eb' [Hb IHb]]
    end.
    econstructor; [ exact Eb | exact Eb' |].
    apply IHb.
    + eapply level_code_pi_codomain; [ exact Hl | eassumption | exact Hcc | exact Eb ].
    + eapply level_code_pi_codomain; [ exact Hl' | apply per_univ_sym; eassumption | exact Hc'c' | exact Eb' ].
Qed.

(** A type related to a type of levels is one: the types of levels are
    [Level@n] and the [Π]s between them. *)
Lemma per_univ_elem_level_code_right : forall i R a a',
    DF a ≈ a' ∈ per_univ_elem i ↘ R -> level_code a -> level_code a'.
Proof.
  intros * H; per_univ_elem_induction H; intros Hl.
  all: try (destruct (level_code_head _ Hl) as [(? & [=]) | (? & ? & ? & [=])]; fail).
  - exists (per_lvl_at n), Levelᵈ@n; left; constructor; reflexivity.
  - exfalso; match goal with Hp : per_prop _ _ |- _ =>
      destruct Hp as [Hpl _ _]; rewrite (level_code_kind _ Hl) in Hpl; discriminate Hpl end.
  - (** A [Π]: between types of levels, the domains and the codomains
        are types of levels. *)
    destruct (level_code_head _ Hl) as [(? & [=]) | (? & ? & ? & [= -> -> <- <- <-])].
    destruct_conjs.
    assert (Hd : level_code a) by (eapply level_code_pi_domain; exact Hl).
    assert (Hd' : level_code a') by (apply IHH; exact Hd).
    do 2 eexists; right.
    econstructor; [ eapply per_univ_elem_level_code; eassumption | eassumption | | eassumption ].
    intros c c' Hc.
    assert (Hcc : Dom c ≈ c ∈ in_rel) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
    match goal with HT : forall c c' (_ : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
      destruct (HT _ _ Hc) as [b b' Eb Eb' [Hb IHb]]
    end.
    econstructor; [ exact Eb | exact Eb' |].
    assert (Hlb : level_code b) by (eapply level_code_pi_codomain; [ exact Hl | eassumption | exact Hcc | exact Eb ]).
    exact (per_univ_elem_level_code _ _ _ _ Hb Hlb (IHb Hlb)).
Qed.

(** Related types of levels stay so at an equivalent relation. *)
Lemma per_level_code_resp_iff : forall R R' a a', R <~> R' -> per_level_code R a a' -> per_level_code R' a a'.
Proof.
  intros * HE H; destruct H.
  - econstructor; etransitivity; [ symmetry; exact HE | eassumption ].
  - econstructor; try eassumption; etransitivity; [ symmetry; exact HE | eassumption ].
Qed.

(** The converse of [per_univ_elem_level_code_right]. *)
Corollary per_univ_elem_level_code_left : forall i R a a',
    DF a ≈ a' ∈ per_univ_elem i ↘ R -> level_code a' -> level_code a.
Proof.
  intros * H Hl; destruct (per_univ_elem_sym _ _ _ _ H) as [H' _].
  exact (per_univ_elem_level_code_right _ _ _ _ H' Hl).
Qed.

End Fixed_GCtx.

(** A type of a head other than those of the types of levels is none of
    them ([level_code_head]). *)
Ltac solve_not_level_code :=
  let Hlc := fresh "Hlc" in
  intro Hlc; destruct (level_code_head _ Hlc) as [(? & [=]) | (? & ? & ? & [=])].

Ltac per_univ_elem_econstructor :=
  (repeat intro; hnf; eapply per_univ_elem_pi') + basic_per_univ_elem_econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Hint Resolve per_univ_elem_pi' : mctt.

Lemma per_univ_elem_pi_clean_inversion : forall {i j κd κc a a' in_rel ρ ρ' B B' elem_rel},
    evaluated_kind κc ->
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem j ↘ elem_rel ->
    exists (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain),
      (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
          rel_mod_eval (per_univ_elem j) B (ρ ↦ c ⦂ entry_type_value a) B' (ρ' ↦ c' ⦂ entry_type_value a') (out_rel equiv_c_c')) /\
        (elem_rel <~> pi_elements a a' in_rel (@out_rel)).
Proof.
  intros * Hev Ha HΠ.
  basic_invert_per_univ_elem HΠ.
  handle_per_univ_elem_irrel.
  eexists.
  split.
  - instantiate (1 := fun c c' (equiv_c_c' : in_rel c c') m m' =>
                        forall R,
                          rel_mod_eval (per_univ_elem j) B (ρ ↦ c ⦂ entry_type_value a) B' (ρ' ↦ c' ⦂ entry_type_value a') R ->
                          R m m').
    intros.
    assert (in_rel0 c c') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intuition.
    destruct_by_head rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
  - intros f f'; split; intros [Hl Hr Happ]; constructor; try assumption; intros.
    all: [> assert (in_rel0 c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
         | assert (in_rel c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_pi' : mctt.
Ltac invert_per_univ_elem H :=
  (unshelve eapply (per_univ_elem_pi_clean_inversion _ _) in H; shelve_unifiable;
     [ first [ eassumption | constructor ] | eassumption |]; destruct H as [? []])
  + basic_invert_per_univ_elem H.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** Cumulativity, along the order of universe indices: in particular, a
    small universe is in every large one. *)
Lemma per_univ_elem_cumu_universe_index : forall i a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    forall i', universe_index_le i i' ->
    DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R.
Proof.
  simpl.
  per_univ_elem_induction1; intros; subst;
    per_univ_elem_econstructor; eauto; try solve_universe_index.
  1: intros; destruct_rel_mod_eval; econstructor; solve [eauto].
  (** An inductive type, a record type: their telescopes, lifted one by
      one. *)
  all: unfold nparams_evals, args_evals, doms_evals, fields_evals in *; intros;
    match goal with
    | H : forall m Mm, _ |- rel_mod_eval _ _ _ _ _ _ =>
        edestruct H as [a a' Ea Ea' [_ HIH]]; try eassumption;
        econstructor; [ exact Ea | exact Ea' | apply HIH; assumption ]
    | H : forall k f T vs vs', List.nth_error (record_fields _) k = Some (f, T) -> _ |- rel_mod_eval _ _ _ _ _ _ =>
        edestruct H as [a a' Ea Ea' [_ HIH]]; try eassumption;
        econstructor; [ exact Ea | exact Ea' | apply HIH; assumption ]
    end.
Qed.

Lemma per_univ_elem_cumu : forall (i : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (S i) ↘ R.
Proof.
  intros; eapply per_univ_elem_cumu_universe_index; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_univ_elem_cumu : mctt.

Lemma per_univ_elem_cumu_ge : forall (i i' : nat) a0 a1 R,
    i <= i' ->
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R.
Proof.
  intros; eapply per_univ_elem_cumu_universe_index; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_univ_elem_cumu_ge : mctt.

Lemma per_univ_elem_cumu_max_left : forall (i j : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R.
Proof.
  intros.
  assert (i <= max i j) by lia; mautosolve.
Qed.

Lemma per_univ_elem_cumu_max_right : forall (i j : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem j ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R.
Proof.
  intros.
  assert (j <= max i j) by lia; mautosolve.
Qed.


Lemma per_elem_subtyping : forall A B i,
    Sub A <: B at i ->
    forall R R' a b,
      DF A ≈ A ∈ per_univ_elem i ↘ R ->
      DF B ≈ B ∈ per_univ_elem i ↘ R' ->
      R a b ->
      R' a b.
Proof.
  induction 1; intros;
    handle_per_univ_elem_irrel;
    saturate_refl;
    (on_all_hyp: fun H => directed invert_per_univ_elem H);
    handle_per_univ_elem_irrel;
    clear_refl_eqs;
    trivial.
  (** Two neutral types: both relations are [per_ne]. *)
  1: { do 2 match goal with H : per_univ_elem _ _ (⇑ _ _) (⇑ _ _) |- _ => basic_invert_per_univ_elem H end.
       handle_per_univ_elem_irrel; trivial. }
  (** The types of levels: the levels of a smaller sort are levels of the
      larger one. *)
  1: eapply per_lvl_at_mono; eassumption.
  (** The three universe cases cumulate the elements of the smaller universe
      to the larger: inside the large tier along the order on levels, inside
      the small one along the order on the realisers, which [per_sublvl]
      bounds, and across the tiers immediately. *)
  1-3: match goal with H : per_universe_elements _ ?a ?b |- per_universe_elements _ ?a ?b => destruct H as [[R0 HR0] Hl Hr Hnl Hnr] end;
    constructor; [| exact Hl | exact Hr | exact Hnl | exact Hnr ];
    eexists; eapply per_univ_elem_cumu_universe_index;
      [ eassumption
      | cbn; first [ apply per_sublvl_real; assumption | exact I | lia ] ].
  (** Two [Π]s: the functions take arguments of the domains' common
      sort. *)
  1: { match goal with H : pi_elements _ _ _ _ ?x ?y |- pi_elements _ _ _ _ ?x ?y => destruct H as [Hl Hr Happ] end.
       match goal with H : per_univ_elem _ in_rel a a' |- _ => pose proof (per_univ_elem_kind _ _ _ _ H) as Ea end.
       constructor; [ congruence | congruence |].
       intros.
       handle_per_univ_elem_irrel.
       destruct_rel_mod_eval.
       saturate_refl_for per_univ_elem.
       destruct_rel_mod_app.
       simplify_evals.
       econstructor; eauto.
       intuition. }
  (** Two propositions: both relations are [per_proof]. *)
  do 2 match goal with H : per_univ_elem _ _ ?x ?x, Hp : per_prop ?x ?x |- _ => basic_invert_per_univ_elem H end.
  handle_per_univ_elem_irrel; trivial.
Qed.

Lemma per_subtyp_refl1 : forall a b i R,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Sub a <: b at i.
Proof.
  simpl; per_univ_elem_induction1;
    subst;
    (** A small universe is below another with a related level, at the index
        of the realiser both levels share. *)
    try (match goal with
         | H : per_lvl ?l ?l' |- per_subtyp ?i 𝕌@?l 𝕌@?l' =>
             apply per_subtyp_suniv;
               [ apply per_sublvl_of_per_lvl; exact H
               | rewrite <- (per_lvl_real _ _ H); assumption ]
         end);
    mauto;
    destruct_all.
  (** A record type: rebuilt without the induction hypotheses. *)
  3: { eapply per_subtyp_record; basic_per_univ_elem_econstructor; try eassumption;
       unfold fields_evals in *; intros; eapply rel_mod_eval_proj1;
       match goal with H : forall k f T vs vs', _ |- _ => eapply H; eassumption end. }
  (** An inductive type: rebuilt without the induction hypotheses. *)
  2: { eapply per_subtyp_indty; basic_per_univ_elem_econstructor; try eassumption;
       unfold nparams_evals, args_evals, doms_evals in *; intros; eapply rel_mod_eval_proj1;
       match goal with H : forall m Mm, _ |- _ => eapply H; eassumption end. }
  match goal with |- per_subtyp _ (d_pi ?kd ?kc a ρ B) _ =>
    assert (DF d_pi kd kc a ρ B ≈ d_pi kd kc a' ρ' B' ∈ per_univ_elem i ↘ elem_rel)
      by (eapply per_univ_elem_pi'; eauto; intros; destruct_rel_mod_eval; mauto) end.
  saturate_refl.
  econstructor; eauto.
  intros;
    destruct_rel_mod_eval;
    functional_eval_rewrite_clear;
    trivial.
Qed.

Hint Resolve per_subtyp_refl1 : mctt.

Lemma per_subtyp_refl2 : forall a b i R,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Sub b <: a at i.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

Hint Resolve per_subtyp_refl2 : mctt.

Lemma per_subtyp_trans : forall a1 a2 i,
    Sub a1 <: a2 at i ->
    forall a3,
      Sub a2 <: a3 at i ->
      Sub a1 <: a3 at i.
Proof.
  induction 1; intros ? Hsub.
  (** Each inversion of the second step drops the proposition case at a
      relevant head ([clear_wrong_kind]). *)
  1: { dependent destruction Hsub; try solve [ exfalso; clear_wrong_kind ].
       apply per_subtyp_neut; [ assumption | assumption | etransitivity; eassumption ]. }
  (** The closed types and the universes, a small universe below a small
      one composing by the transitivity of the order on levels. *)
  1-6: dependent destruction Hsub; try solve [ exfalso; clear_wrong_kind ]; simpl in *; mauto.
  all: try solve [ econstructor; solve [ lia | solve_universe_index ] ].
  - dependent destruction Hsub; try solve [ exfalso; clear_wrong_kind ].
    handle_per_univ_elem_irrel.
    eapply per_subtyp_pi; eauto.
    + etransitivity; [ exact H0 | eassumption ].
    + intros.
      saturate_refl.
      (on_all_hyp: fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      intuition.
  - (** Inductive types: their equalities compose. *)
    inversion Hsub; subst; try solve [ exfalso; clear_wrong_kind ].
    match goal with H : per_univ_elem _ ?R (d_ind _ _ ?x) (d_ind _ _ ?y), HR' : per_univ_elem _ ?R' (d_ind _ _ ?y) (d_ind _ _ ?z) |- _ =>
      assert (HRR : R <~> R') by (eapply per_univ_elem_left_irrel; [ exact H | apply per_univ_sym; exact HR' ]);
      eapply per_subtyp_indty; eapply per_univ_trans; [ exact H | eapply per_univ_elem_resp_iff; [ exact HR' | symmetry; exact HRR ] ]
    end.
  - (** Record types: their equalities compose. *)
    inversion Hsub; subst; try solve [ exfalso; clear_wrong_kind ].
    match goal with H : per_univ_elem _ ?R (d_record _ ?x) (d_record _ ?y), HR' : per_univ_elem _ ?R' (d_record _ ?y) (d_record _ ?z) |- _ =>
      assert (HRR : R <~> R') by (eapply per_univ_elem_left_irrel; [ exact H | apply per_univ_sym; exact HR' ]);
      eapply per_subtyp_record; eapply per_univ_trans; [ exact H | eapply per_univ_elem_resp_iff; [ exact HR' | symmetry; exact HRR ] ]
    end.
  - (** Propositions: the second step is between propositions too. *)
    dependent destruction Hsub; try solve [ exfalso; clear_wrong_kind ].
    apply per_subtyp_prop; etransitivity; eassumption.
Qed.

Hint Resolve per_subtyp_trans : mctt.

#[local] Instance per_subtyp_trans_instance i : Transitive (per_subtyp i).
Proof.
  eauto using per_subtyp_trans.
Qed.

Lemma per_subtyp_transp : forall a b i a' b' R R',
    Sub a <: b at i ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    DF b ≈ b' ∈ per_univ_elem i ↘ R' ->
    Sub a' <: b' at i.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

Lemma per_subtyp_cumu_universe_index : forall a1 a2 i,
    Sub a1 <: a2 at i ->
    forall j,
      universe_index_le i j ->
      Sub a1 <: a2 at j.
Proof.
  induction 1; intros; econstructor; eauto using per_univ_elem_cumu_universe_index; solve_universe_index.
Qed.

Lemma per_subtyp_cumu : forall a1 a2 (i : nat),
    Sub a1 <: a2 at i ->
    forall (j : nat),
      i <= j ->
      Sub a1 <: a2 at j.
Proof.
  intros; eapply per_subtyp_cumu_universe_index; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_subtyp_cumu : mctt.

Lemma per_subtyp_cumu_left : forall a1 a2 (i j : nat),
    Sub a1 <: a2 at i ->
    Sub a1 <: a2 at max i j.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

Lemma per_subtyp_cumu_right : forall a1 a2 (i j : nat),
    Sub a1 <: a2 at i ->
    Sub a1 <: a2 at max j i.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

(** * The Module PER is a PER *)

(** ** Related Types, Seen from Either Side *)

Lemma rel_typ_sym : forall {i A ρ A' ρ' R},
    rel_typ i A ρ A' ρ' R ->
    rel_typ i A' ρ' A ρ R /\ (forall m m', R m m' -> R m' m).
Proof.
  intros * [a a' Ha Ha' HR]; pose proof (per_univ_elem_sym _ _ _ _ HR) as [HR' Hs].
  split; [ econstructor; eassumption | exact Hs ].
Qed.

Lemma rel_typ_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R'},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    (R <~> R') /\ rel_typ i A1 ρ1 A3 ρ3 R /\ (forall m1 m2 m3, R m1 m2 -> R m2 m3 -> R m1 m3).
Proof.
  intros * [a1 a2 H1 H2 HR] [a2' a3 H2' H3 HR'].
  functional_eval_rewrite_clear.
  assert (HRR' : R <~> R') by first [ symmetry; eapply per_univ_elem_cross_irrel; [ exact HR' | exact HR ]
                                     | eapply per_univ_elem_cross_irrel; [ exact HR | exact HR' ] ].
  split; [ exact HRR' | split ].
  - econstructor; [ eassumption | eassumption |].
    eapply per_univ_trans; [ exact HR |].
    eapply per_univ_elem_resp_iff; [ exact HR' | symmetry; exact HRR' ].
  - intros; eapply per_elem_trans; eassumption.
Qed.

Lemma rel_elem_sym : forall {i A ρ A' ρ' R M M'},
    rel_typ i A ρ A' ρ' R ->
    rel_elem M ρ M' ρ' R -> rel_elem M' ρ' M ρ R.
Proof.
  intros * HT [m m' Hm Hm' HR]; destruct (rel_typ_sym HT) as [_ Hs].
  econstructor; [ eassumption | eassumption | apply Hs; exact HR ].
Qed.

Lemma rel_elem_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R' M1 M2 M3},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    rel_elem M1 ρ1 M2 ρ2 R -> rel_elem M2 ρ2 M3 ρ3 R' -> rel_elem M1 ρ1 M3 ρ3 R.
Proof.
  intros * HT HT' [m1 m2 H1 H2 HR] [m2' m3 H2' H3 HR'].
  functional_eval_rewrite_clear.
  destruct (rel_typ_trans HT HT') as (HRR' & _ & Ht).
  econstructor; [ eassumption | eassumption |].
  eapply Ht; [ exact HR | apply HRR'; exact HR' ].
Qed.

(** A type is of one sort in an environment. *)
Lemma rel_typ_kind_unique : forall A ρ r r', rel_typ_kind A ρ r -> rel_typ_kind A ρ r' -> r = r'.
Proof. intros * (a & Ha & <-) (a' & Ha' & <-); functional_eval_rewrite_clear; reflexivity. Qed.

(** Related types are of one sort. *)
Lemma rel_typ_kind_right : forall {i A ρ A' ρ' R r},
    rel_typ i A ρ A' ρ' R -> rel_typ_kind A ρ r -> rel_typ_kind A' ρ' r.
Proof.
  intros * [a a' Ha Ha' HR] (a0 & Ha0 & Hr).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  exists a'; split; [ exact Ha' | rewrite <- (per_univ_elem_kind _ _ _ _ HR); exact Hr ].
Qed.

(** A kind is the propositions' or an evaluated one. *)
Lemma kind_cases : forall r, r = ak_propositional \/ evaluated_kind r.
Proof. intros []; [ right; constructor | left; reflexivity | right; constructor ]. Qed.

(** At an evaluated kind the bodies' values are related and the heads
    tied to them. *)
Lemma def_bodies_at_evaluated : forall r M ρ M' ρ' R,
    evaluated_kind r -> def_bodies_at r M ρ M' ρ' R = rel_elem M ρ M' ρ' R.
Proof. intros * []; reflexivity. Qed.

Lemma def_heads_at_evaluated : forall r R M M' ρ ρ',
    evaluated_kind r -> def_heads_at r R M M' ρ ρ' = def_heads R M M' ρ ρ'.
Proof. intros * []; reflexivity. Qed.

(** The heads tied to two bodies are tied to them in either order. *)
Lemma def_heads_at_swap : forall r R M M' ρ ρ',
    def_heads_at r R M M' ρ ρ' -> def_heads_at r R M' M ρ ρ'.
Proof. intros [] * H; cbn in *; first [ exact I | destruct H; constructor; assumption ]. Qed.

(** A proposition is related only to propositions. *)
Lemma rel_typ_propositional_right : forall {i A ρ A' ρ' R},
    rel_typ i A ρ A' ρ' R -> rel_typ_propositional A ρ -> rel_typ_propositional A' ρ'.
Proof.
  intros * [a a' Ha Ha' HR] (a0 & Ha0 & Hp).
  functional_eval_rewrite_clear.
  exists a'; split; [ exact Ha' | rewrite <- (per_univ_elem_kind _ _ _ _ HR); exact Hp ].
Qed.

Lemma rel_typ_propositional_left : forall {i A ρ A' ρ' R},
    rel_typ i A ρ A' ρ' R -> rel_typ_propositional A' ρ' -> rel_typ_propositional A ρ.
Proof. intros * HT; exact (rel_typ_propositional_right (proj1 (rel_typ_sym HT))). Qed.

(** Two terms of related types, related unless the types are
    propositions, the other way around. *)
Lemma rel_elem_at_sym : forall {i A ρ A' ρ' R M M'},
    rel_typ i A ρ A' ρ' R ->
    rel_typ_propositional A ρ \/ rel_elem M ρ M' ρ' R ->
    rel_typ_propositional A' ρ' \/ rel_elem M' ρ' M ρ R.
Proof.
  intros * HT [Hp | HM]; [ left; exact (rel_typ_propositional_right HT Hp) | right; exact (rel_elem_sym HT HM) ].
Qed.

(** And composed. *)
Lemma rel_elem_at_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R' M1 M2 M3},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    rel_typ_propositional A1 ρ1 \/ rel_elem M1 ρ1 M2 ρ2 R ->
    rel_typ_propositional A2 ρ2 \/ rel_elem M2 ρ2 M3 ρ3 R' ->
    rel_typ_propositional A1 ρ1 \/ rel_elem M1 ρ1 M3 ρ3 R.
Proof.
  intros * HT HT' [Hp | HM] [Hp' | HM']; try (left; assumption).
  - left; exact (rel_typ_propositional_left HT Hp').
  - right; exact (rel_elem_trans HT HT' HM HM').
Qed.

(** The same for two terms related unless the kind of their types is
    [ak_propositional], the kind their definitions are tagged with. *)
Lemma rel_elem_tag_sym : forall {i A ρ A' ρ' R M M' r},
    rel_typ i A ρ A' ρ' R ->
    r = ak_propositional \/ rel_elem M ρ M' ρ' R ->
    r = ak_propositional \/ rel_elem M' ρ' M ρ R.
Proof. intros * HT [Hp | HM]; [ left; exact Hp | right; exact (rel_elem_sym HT HM) ]. Qed.

Lemma rel_elem_tag_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R' M1 M2 M3 r},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    r = ak_propositional \/ rel_elem M1 ρ1 M2 ρ2 R ->
    r = ak_propositional \/ rel_elem M2 ρ2 M3 ρ3 R' ->
    r = ak_propositional \/ rel_elem M1 ρ1 M3 ρ3 R.
Proof.
  intros * HT HT' [Hp | HM] [Hp' | HM']; try (left; assumption).
  right; exact (rel_elem_trans HT HT' HM HM').
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_cumu : mctt.
#[export]
Hint Resolve per_univ_elem_cumu_ge : mctt.
#[export]
Hint Resolve per_subtyp_refl1 : mctt.
#[export]
Hint Resolve per_subtyp_refl2 : mctt.
#[export]
Hint Resolve per_subtyp_trans : mctt.
#[export] Existing Instance per_subtyp_trans_instance.
#[export]
Hint Resolve per_subtyp_cumu : mctt.

