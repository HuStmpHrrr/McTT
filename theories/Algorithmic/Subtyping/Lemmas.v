From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Subtyping Require Import Definitions.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import CoreInversions.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core Require Import Semantic.Levels Consequences.Consistency.
From Mctt.Core.Completeness.Consequences Require Import Rules.
From Mctt.Core.Completeness Require Import UniverseCases ContextCases.
Import Syntax_Notations Fixed_Notations.

#[local]
Ltac apply_subtyping :=
  repeat match goal with
    | H : (?Γ ⊢ ?M : ?A),
        H1 : ?Γ ⊢ ?A ⊆ ?B |- _ =>
        assert (Γ ⊢ M : B) by mauto; clear H
    end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The codomain of a [Π] in normal form is the normal form of the codomain,
    in the context extended by the domain: the readback of a [Π] reads its
    codomain at the next variable, which is the initial environment of the
    extended context. *)
Lemma nbe_ty_pi_cod : forall Γ A B A' B',
    nbe_ty_f Γ (Π A B) (Πⁿ A' B') ->
    nbe_ty_f (Γ ▹ A) B B'.
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  econstructor; [ econstructor; eassumption | eassumption | cbn; eassumption ].
Qed.

(** The normal form of a [Π] of the sort [r]: the [Π] of its domain's
    normal form and of its codomain's, in the context extended by the
    domain. *)
Lemma nbe_ty_pi_inv : forall Γ r A B W,
    nbe_ty_f Γ (a_pi r A B) W ->
    exists WA WB, W = nf_pi r WA WB /\ nbe_ty_f Γ A WA /\ nbe_ty_f (Γ ▹ A) B WB.
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  inversion nbe_ty_read; subst.
  all: do 2 eexists; split; [ reflexivity | split ];
    [ econstructor; eassumption | econstructor; [ econstructor; eassumption | eassumption | cbn; eassumption ] ].
Qed.

(** The normal form of a [Σₚ]: the [Σₚ] of its parts' normal forms, the
    first's in the context, the second's in the context extended by the
    first. *)
Lemma nbe_ty_and_inv : forall Γ P Q W,
    nbe_ty_f Γ (Σₚ P Q) W ->
    exists WP WQ, W = Σₚⁿ WP WQ /\ nbe_ty_f Γ P WP /\ nbe_ty_f (Γ ▹ P) Q WQ.
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  do 2 eexists; split; [ reflexivity | split ];
    [ econstructor; eassumption | econstructor; [ econstructor; eassumption | eassumption | cbn; eassumption ] ].
Qed.

(** Conversely, a [Π]'s normal form is the [Π] of its domain's and of its
    codomain's, in the context extended by the domain, at either sort. *)
Lemma nbe_ty_pi_intro : forall Γ r A B WA WB,
    nbe_ty_f Γ A WA ->
    nbe_ty_f (Γ ▹ A) B WB ->
    nbe_ty_f Γ (a_pi r A B) (nf_pi r WA WB).
Proof.
  intros * [ρ a Hi Ha Hr] [ρ' b Hi' Hb Hr'].
  inversion Hi'; subst.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  econstructor; [ exact Hi | constructor; exact Ha | destruct r; econstructor; eassumption ].
Qed.

(** The two normal forms are their own normal forms, as the normal forms
    algorithmic subtyping compares are: the sorts their level atoms carry are
    then the sorts of the atoms ([univ_nf_well_scoped]), which the absorption step of
    [lvl_exp_of_le] needs. *)
Lemma alg_subtyping_nf_sound : forall A B,
    ⊢anf A ⊆ B ->
    forall Γ i,
      Γ ⊢ A : Typeω@i ->
      Γ ⊢ B : Typeω@i ->
      nbe_ty_f Γ A A ->
      nbe_ty_f Γ B B ->
      Γ ⊢ A ⊆ B.
Proof.
  induction 1; intros * HA HB HnA HnB; subst; simpl in *.
  - eapply wf_subtyp_refl'; mauto.
  - assert (i < j \/ i = j) as [] by lia; mauto 3.
  (** Two small universes: the order on canonical levels is the level
      equation [lvl_exp_of_le], at a sort both levels are of. *)
  - gen_presups.
    destruct (univ_nf_well_scoped HA HnA) as (n1 & Ht & Hc & Hxs).
    destruct (univ_nf_well_scoped HB HnB) as (n2 & Ht' & Hd & Hys).
    assert (Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@(Nat.max n1 n2))
      by (eapply wf_exp_subtyp'; [ exact Ht | apply wf_subtyp_level; [ lia | mauto 2 ] ]).
    assert (Γ ⊢ lvl_exp_of d (List.map atom_exp ys) : Level@(Nat.max n1 n2))
      by (eapply wf_exp_subtyp'; [ exact Ht' | apply wf_subtyp_level; [ lia | mauto 2 ] ]).
    eapply wf_subtyp_suniv; [ assumption | eassumption | eassumption |].
    apply lvl_exp_of_le; [ lia | lia | assumption
                         | eapply level_atoms_well_scoped_mono; [| exact Hxs ]; lia
                         | eapply level_atoms_well_scoped_mono; [| exact Hys ]; lia | assumption ].
  - gen_presups.
    assert (exists n, Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@n) as [n Ht]
      by (eapply wf_univ_lvl_inversion; eassumption).
    eapply wf_subtyp_small_large; [ assumption | exact Ht ].
  - gen_presups; apply wf_subtyp_level; assumption.
  - (** Two [Π]s over one domain, a type or a proposition: the codomains
        compare in the context extended by it. *)
    pose proof (nbe_ty_pi_cod _ _ _ _ _ HnA) as HnB1; pose proof (nbe_ty_pi_cod _ _ _ _ _ HnB) as HnB2.
    apply wf_pi_inversion' in HA as [HdA HB1]; apply wf_pi_inversion' in HB as [_ HB2].
    assert (IH : Γ ▹ A' ⊢ B ⊆ B') by (eapply IHalg_subtyping_nf; eassumption).
    destruct HdA as [HdA | HdA];
      (eapply wf_subtyp_pi; [ exact HdA | exact HdA | constructor | apply wf_exp_eq_refl; exact HdA
                            | exact HB1 | exact HB2 | exact IH ]).
Qed.

Lemma alg_subtyping_nf_trans : forall A0 A1 A2,
    ⊢anf A0 ⊆ A1 ->
    ⊢anf A1 ⊆ A2 ->
    ⊢anf A0 ⊆ A2.
Proof.
  intros * H1; gen A2.
  induction H1; subst; intros ? H2;
    dependent destruction H2;
    simpl in *;
    try contradiction;
    mauto 3.

  all: constructor; first [ lia | eapply lvl_le_trans; eassumption ].
Qed.

Lemma alg_subtyping_nf_refl : forall A,
    ⊢anf A ⊆ A.
Proof.
  induction A.
  (** A relevant [Π] by its codomain; a propositional one is no subtype
      but of itself *)
  all: try (match goal with |- ⊢anf nf_pi ?r _ _ ⊆ _ => destruct r end).
  all: first [ apply alg_subtyping_nf_refl_case; [ exact I | reflexivity ]
             | apply alg_subtyping_nf_univ; lia
             | apply alg_subtyping_nf_suniv, lvl_le_refl
             | apply alg_subtyping_nf_level; reflexivity
             | apply alg_subtyping_nf_pi; [ reflexivity | assumption ] ].
Qed.

#[local]
Hint Resolve alg_subtyping_nf_trans alg_subtyping_nf_refl : mctt.

Lemma alg_subtyping_trans : forall Γ A0 A1 A2,
    Γ ⊢a A0 ⊆ A1 ->
    Γ ⊢a A1 ⊆ A2 ->
    Γ ⊢a A0 ⊆ A2.
Proof.
  intros. progressive_inversion.
  functional_nbe_rewrite_clear.
  mauto.
Qed.

#[local]
Hint Resolve alg_subtyping_trans : mctt.

Lemma alg_subtyping_complete : forall Γ A B,
    Γ ⊢ A ⊆ B ->
    Γ ⊢a A ⊆ B.
Proof.
  (** The global context is an index of [wf_subtyp], so it is fixed for the
      induction, as in [subtyp_spec]. *)
  intros * H.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  induction H; subst;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
    mauto.
  - (** An equation at a sort: one normal form *)
    match goal with H : _ ⊢ _ ≈ _ : ?S, HS : type_sort ?S |- _ => destruct (completeness_ty_sort HS H) as (W & Hn1 & Hn2) end.
    econstructor; [ exact Hn1 | exact Hn2 | apply alg_subtyping_nf_refl ].
  - assert (Γ ⊢ Typeω@i : Typeω@(S i)) as (W1 & HW1 & _)%soundness_ty by (apply wf_typ; assumption).
    assert (Γ ⊢ Typeω@j : Typeω@(S j)) as (W2 & HW2 & _)%soundness_ty by (apply wf_typ; assumption).
    econstructor; [ exact HW1 | exact HW2 |].
    inversion HW1 as [? ? _ He1 Hr1]; inversion HW2 as [? ? _ He2 Hr2]; subst.
    inversion He1; subst; inversion He2; subst; inversion Hr1; subst; inversion Hr2; subst.
    constructor; lia.
  (** The two small-universe rules: a small universe is its own normal
      form, read back by [read_typ_suniv]. *)
  - (** The order on the two canonical levels is read off the normal form of
        the premise [maxl M M' ≈ M'] ([read_max_lvl_le]). *)
    match goal with H : wf_exp_eq _ _ _ _ (maxl _ _) _ |- _ =>
      apply completeness in H as [W [Hn1 Hn2]] end.
    assert (Γ ⊢ Type⟨M⟩ : Typeω@0) as (WA & HA & _)%soundness_ty by (eapply wf_univ_large_tm; eassumption).
    assert (Γ ⊢ Type⟨M'⟩ : Typeω@0) as (WB & HB & _)%soundness_ty by (eapply wf_univ_large_tm; eassumption).
    econstructor; [ exact HA | exact HB |].
    (** The two levels and their maximum, evaluated and read back at one
        environment; levels are relevant *)
    destruct Hn1 as [ρ1 a1 Hi1 Ha1 Ht1]; destruct Hn2 as [ρ2 a2 Hi2 Ha2 Ht2].
    destruct HA as [ρ3 m3 Hi3 He3 Hr3]; destruct HB as [ρ4 m4 Hi4 He4 Hr4].
    functional_initial_env_rewrite_clear.
    inversion Ha1; subst; inversion Ha2; subst.
    destruct Ht1 as [Hp | ? ? _ Hm1 Hw1]; [ cbn in Hp; discriminate |].
    destruct Ht2 as [Hp | ? ? _ Hm2 Hw2]; [ cbn in Hp; discriminate |].
    inversion He3; subst; inversion He4; subst; inversion Hm1; subst.
    inversion Hr3; subst; inversion Hr4; subst.
    functional_eval_rewrite_clear.
    apply alg_subtyping_nf_suniv; eapply read_max_lvl_le; eassumption.
  (** The types of levels are their own normal forms. *)
  - assert (Γ ⊢ Level@m : Typeω@0) as (W1 & HW1 & _)%soundness_ty by mauto 3.
    assert (Γ ⊢ Level@n : Typeω@0) as (W2 & HW2 & _)%soundness_ty by mauto 3.
    econstructor; [ exact HW1 | exact HW2 |].
    inversion HW1 as [? ? _ He1 Hr1]; inversion HW2 as [? ? _ He2 Hr2]; subst.
    inversion He1; subst; inversion He2; subst; inversion Hr1; subst; inversion Hr2; subst.
    apply alg_subtyping_nf_level; assumption.
  - assert (Γ ⊢ Type⟨M⟩ : Typeω@0) as (W1 & HW1 & _)%soundness_ty by (eapply wf_univ_large_tm; eassumption).
    assert (Γ ⊢ Typeω@i : Typeω@(S i)) as (W2 & HW2 & _)%soundness_ty by (apply wf_typ; assumption).
    econstructor; [ exact HW1 | exact HW2 |].
    inversion HW1 as [? ? _ He1 Hr1]; inversion HW2 as [? ? _ He2 Hr2]; subst.
    inversion He1; subst; inversion He2; subst; inversion Hr1; subst; inversion Hr2; subst.
    apply alg_subtyping_nf_small_large.
  - (** The domains have one normal form; the codomain's, read back in
        [Γ ▹ A], is the one in [Γ ▹ A'] the induction hypothesis gives:
        [ctxeq_nbe_eq] moves it, at the semantic context equality the
        domains give. *)
    match goal with
    | HS : pi_domain_sort _ ?S, HAA : _ ⊢ A ≈ A' : ?S, HB : _ ▹ A ⊢ B : Typeω@i, IH : _ ▹ A' ⊢a B ⊆ B' |- _ =>
        assert (type_sort S) as HS' by (destruct HS; constructor);
        rename HAA into HAA', HB into HB', IH into IH'
    end.
    assert (HΓA : ⊨ Γ ▹ A ≈ Γ ▹ A').
    { destruct (rel_type_of_sort HS' (completeness_fundamental_exp_eq _ _ _ _ HAA')) as [k Hk].
      eapply per_ctx_extend_type; [| exact Hk ].
      apply rel_ctx_wf_per_ctx, completeness_fundamental_ctx; gen_presups; assumption. }
    destruct (ctxeq_nbe_eq _ _ _ _ HB' HΓA) as (WB & HWB1 & HWB2).
    destruct IH' as [X Y HX HY Hsub].
    apply nbe_type_to_nbe_ty in HWB1, HWB2.
    functional_nbe_rewrite_clear.
    destruct (completeness_ty_sort HS' HAA') as (WA & HWA1 & HWA2).
    econstructor; [ eapply nbe_ty_pi_intro; eassumption | eapply nbe_ty_pi_intro; eassumption |].
    apply alg_subtyping_nf_pi; [ reflexivity | exact Hsub ].
Qed.

Lemma alg_subtyping_sound : forall Γ A B i,
    Γ ⊢a A ⊆ B ->
    Γ ⊢ A : Typeω@i ->
    Γ ⊢ B : Typeω@i ->
    Γ ⊢ A ⊆ B.
Proof.
  intros. destruct H.
  on_all_hyp: fun H => apply soundness in H.
  destruct_all.
  on_all_hyp: fun H => apply nbe_type_to_nbe_ty in H.
  functional_nbe_rewrite_clear.
  gen_presups.
  (** The normal forms are their own normal forms. *)
  assert (nbe_ty_f Γ A' A').
  { destruct (soundness_ty (A := A') ltac:(eassumption)) as (C & HC & _).
    assert (A' = C) as <-
      by (match goal with H1 : nbe_ty_f Γ ?X A', H2 : Γ ⊢ ?X : Typeω@_ |- _ => exact (idempotent_nbe_ty H2 H1 HC) end).
    exact HC. }
  assert (nbe_ty_f Γ B' B').
  { destruct (soundness_ty (A := B') ltac:(eassumption)) as (C & HC & _).
    assert (B' = C) as <-
      by (match goal with H1 : nbe_ty_f Γ ?X B', H2 : Γ ⊢ ?X : Typeω@_ |- _ => exact (idempotent_nbe_ty H2 H1 HC) end).
    exact HC. }
  assert (Γ ⊢ A' ⊆ B') by (eapply alg_subtyping_nf_sound; eassumption).
  transitivity A'; [mauto |].
  transitivity B'; [eassumption |].
  mauto.
Qed.

(** The normal form of a proposition is neither a universe, a type of
    levels nor a relevant [Π]: each of those is a type of a large universe,
    which no proposition is ([typ_prop_absurd]). *)
Lemma nbe_ty_prop_not_univ_pi : forall Γ A W,
    Γ ⊢ A : Propₘ -> nbe_ty_f Γ A W -> not_univ_pi W.
Proof.
  intros * HA Hn.
  pose proof (soundness_ty_at_sort type_sort_prop HA Hn) as HE.
  assert (HW : Γ ⊢ W : Propₘ) by (gen_presups; assumption).
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct W; try match goal with |- not_univ_pi (nf_pi ?r _ _) => destruct r end;
    cbn; try exact I; exfalso; cbn [nf_to_exp] in HW.
  - exact (typ_prop_absurd (wf_typ _ _ _ _ HΓ) HW).
  - destruct (wf_univ_lvl_inversion HW) as [nL HL]; exact (typ_prop_absurd (wf_univ_large_tm (i := 0) HΓ HL) HW).
  - exact (typ_prop_absurd (wf_level_large (i := 0) HΓ) HW).
  - destruct (wf_pi_typed_large HW) as [k Hk]; exact (typ_prop_absurd Hk HW).
Qed.

(** Normal forms one of which is no universe, type of levels or relevant
    [Π] are subtypes only if equal. *)
Lemma alg_subtyping_nf_not_univ_pi_eq : forall A B,
    ⊢anf A ⊆ B -> not_univ_pi A \/ not_univ_pi B -> A = B.
Proof. intros * Hs Hn; inversion Hs; subst; [ reflexivity | .. ]; cbn in Hn; destruct Hn; contradiction. Qed.

(** Algorithmic subtyping is sound for types of any sorts. *)
Lemma alg_subtyping_sound_sort : forall Γ A B S S',
    type_sort S -> type_sort S' ->
    Γ ⊢a A ⊆ B ->
    Γ ⊢ A : S ->
    Γ ⊢ B : S' ->
    Γ ⊢ A ⊆ B.
Proof.
  intros * HS HS' Hs HA HB.
  destruct HS as [i |], HS' as [j |];
    [ eapply (alg_subtyping_sound _ _ _ (max i j)); [ exact Hs | eapply lift_exp_max_left; exact HA | eapply lift_exp_max_right; exact HB ]
    | .. ].
  (** A proposition on a side: the normal forms are equal, so are the types. *)
  all: destruct Hs as [A' B' HnA HnB Hsub].
  all: assert (A' = B') as <-
         by (apply alg_subtyping_nf_not_univ_pi_eq; [ exact Hsub |];
             first [ right; eapply nbe_ty_prop_not_univ_pi; eassumption | left; eapply nbe_ty_prop_not_univ_pi; eassumption ]).
  all: let E := fresh "E" in
       first [ pose proof (exp_eq_of_nbe_ty_same (or_introl HA) (or_intror HB) HnA HnB) as E
             | pose proof (exp_eq_of_nbe_ty_same (or_intror HA) (or_introl HB) HnA HnB) as E
             | pose proof (exp_eq_of_nbe_ty_same (i := 0) (or_intror HA) (or_intror HB) HnA HnB) as E ];
       destruct E as [HE | HE];
       exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE)
                       ltac:(constructor) HE)).
Qed.

End Fixed_GCtx.
