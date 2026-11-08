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
Lemma nbe_ty_pi_cod : forall Γ κd κc A B A' B',
    nbe_ty_f Γ (a_pi κd κc A B) (nf_pi κd κc A' B') ->
    nbe_ty_f (Γ ▹{κd} A) B B'.
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  econstructor; [ econstructor; eassumption | eassumption | cbn; eassumption ].
Qed.

(** The normal form of a [Π] at the kinds [κd] and [κc]: the [Π] of its
    domain's normal form and of its codomain's, in the context extended by
    the domain. *)
Lemma nbe_ty_pi_inv : forall Γ κd κc A B W,
    nbe_ty_f Γ (a_pi κd κc A B) W ->
    exists WA WB, W = nf_pi κd κc WA WB /\ nbe_ty_f Γ A WA /\ nbe_ty_f (Γ ▹{κd} A) B WB.
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
    exists WP WQ, W = Σₚⁿ WP WQ /\ nbe_ty_f Γ P WP /\ nbe_ty_f (Γ ▹{ak_propositional} P) Q WQ.
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  do 2 eexists; split; [ reflexivity | split ];
    [ econstructor; eassumption | econstructor; [ econstructor; eassumption | eassumption | cbn; eassumption ] ].
Qed.

(** Conversely, a [Π]'s normal form is the [Π] of its domain's and of its
    codomain's, in the context extended by the domain, at any kinds. *)
Lemma nbe_ty_pi_intro : forall Γ κd κc A B WA WB,
    nbe_ty_f Γ A WA ->
    nbe_ty_f (Γ ▹{κd} A) B WB ->
    nbe_ty_f Γ (a_pi κd κc A B) (nf_pi κd κc WA WB).
Proof.
  intros * [ρ a Hi Ha Hr] [ρ' b Hi' Hb Hr'].
  inversion Hi'; subst.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  econstructor; [ exact Hi | constructor; exact Ha | econstructor; eassumption ].
Qed.

(** A normal form of a type is its own normal form up to proofs: the
    normal forms of normal forms are those of their source types
    ([idempotent_nbe_ty_sort]), so this is what the normal forms
    algorithmic subtyping compares are. *)
Definition nbe_ty_fixed_upto_proofs (Γ : ctx) (A : nf) : Prop :=
  exists W, nbe_ty_f Γ A W /\ nf_eq_upto_proofs W A.

(** The two normal forms are their own normal forms up to proofs, as the
    normal forms algorithmic subtyping compares are: the sorts their level
    atoms carry are then the sorts of the atoms ([univ_nf_well_scoped]),
    which the absorption step of [lvl_exp_of_le] needs. *)
Lemma alg_subtyping_nf_sound : forall A B,
    ⊢anf A ⊆ B ->
    forall Γ S,
      type_sort S ->
      Γ ⊢ A : S ->
      Γ ⊢ B : S ->
      nbe_ty_fixed_upto_proofs Γ A ->
      nbe_ty_fixed_upto_proofs Γ B ->
      Γ ⊢ A ⊆ B.
Proof.
  induction 1; intros * HS HA HB [WA [HnA HWA]] [WB [HnB HWB]]; subst; simpl in *.
  (** Normal forms equal up to proofs are equal types. *)
  - refine (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HA HB HS _)).
    eapply exp_eq_of_nbe_ty_same; [ exact HS | exact HA | exact HB | exact HnA | exact HnB |].
    etransitivity; [ exact HWA |]; etransitivity; [ eassumption | symmetry; exact HWB ].
  - assert (i < j \/ i = j) as [] by lia; mauto 3.
  (** Two small universes: the order on canonical levels is the level
      equation [lvl_exp_of_le], at a sort both levels are of. *)
  - (** The normal forms of the two universes are at levels [xs'] and
        [ys'] equal up to proofs to [xs] and [ys]; their level terms are
        equal to those, whose atoms are coherent. *)
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    apply (nf_univ_of_upto_proofs_inv _ (c, xs)) in HWA as ([c' xs'] & -> & [Hc' Hxs']);
      apply (nf_univ_of_upto_proofs_inv _ (d, ys)) in HWB as ([d' ys'] & -> & [Hd' Hys']); cbn [fst snd] in *; subst c' d'.
    destruct (univ_nf_level_of_nbe HA HnA) as [n1 HL1 Hc Hxs Hatx].
    destruct (univ_nf_level_of_nbe HB HnB) as [n2 HL2 Hd Hys Haty].
    cbn [fst snd] in *.
    assert (HL1N : Γ ⊢ lvl_exp_of c (List.map atom_exp xs) ≈ lvl_exp_of c (List.map atom_exp xs') : Level@(Nat.max n1 n2))
      by (eapply wf_exp_eq_subtyp'; [ exact HL1 | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
    assert (HL2N : Γ ⊢ lvl_exp_of d (List.map atom_exp ys) ≈ lvl_exp_of d (List.map atom_exp ys') : Level@(Nat.max n1 n2))
      by (eapply wf_exp_eq_subtyp'; [ exact HL2 | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
    assert (Hle : lvl_le (c, xs') (d, ys'))
      by (apply (lvl_le_upto_proofs (c, xs) (c, xs') (d, ys) (d, ys'));
          [ symmetry; split; [ reflexivity | exact Hxs' ] | symmetry; split; [ reflexivity | exact Hys' ] | exact H ]).
    assert (HT1 : Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@(Nat.max n1 n2)) by (gen_presups; assumption).
    assert (HT2 : Γ ⊢ lvl_exp_of d (List.map atom_exp ys) : Level@(Nat.max n1 n2)) by (gen_presups; assumption).
    eapply wf_subtyp_suniv with (n := Nat.max n1 n2); [ exact HΓ | exact HT1 | exact HT2 |].
    transitivity (maxl (lvl_exp_of c (List.map atom_exp xs')) (lvl_exp_of d (List.map atom_exp ys')));
      [ apply wf_exp_eq_maxl_cong; assumption |].
    transitivity (lvl_exp_of d (List.map atom_exp ys')); [| symmetry; exact HL2N ].
    apply lvl_exp_of_le; [ lia | lia | exact HΓ
                         | eapply level_atoms_well_scoped_mono; [| exact Hxs ]; lia
                         | eapply level_atoms_well_scoped_mono; [| exact Hys ]; lia
                         | | exact Hle ].
    eapply univ_nfs_coherent; [ exact HA | exact HnA | exact HB | exact HnB ].
  - gen_presups.
    assert (exists n, Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@n) as [n Ht]
      by (eapply wf_univ_lvl_inversion; eassumption).
    eapply wf_subtyp_small_large; [ assumption | exact Ht ].
  - gen_presups; apply wf_subtyp_level; assumption.
  - (** Two [Π]s over domains equal up to proofs: the domains are equal
        types, and the codomains compare in the context extended by the
        second, where the first is a type of the same normal form up to
        proofs ([ctxeq_nbe_ty_eq_sort]). *)
    destruct (nbe_ty_pi_inv _ _ _ _ _ _ HnA) as (WA1 & WA2 & -> & HnA1 & HnA2).
    destruct (nbe_ty_pi_inv _ _ _ _ _ _ HnB) as (WB1 & WB2 & -> & HnB1 & HnB2).
    apply nf_pi_upto_proofs_inv in HWA as (_ & _ & HWA1 & HWA2).
    apply nf_pi_upto_proofs_inv in HWB as (_ & _ & HWB1 & HWB2).
    destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HA) as [SA iA HSA HdA HcA Hk].
    destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HB) as [SB iB HSB HdB HcB _].
    destruct (sort_kind_common HSA HSB HdA HdB) as [k0 [HdA' HdB']].
    remember (Nat.max k0 (Nat.max iA iB)) as k eqn:Hkmax.
    assert (HdAk : Γ ⊢ A : abs_kind_sort κd Typeω@k) by (eapply abs_kind_sort_lift; [ exact HdA' | ]; lia).
    assert (HdBk : Γ ⊢ A' : abs_kind_sort κd Typeω@k) by (eapply abs_kind_sort_lift; [ exact HdB' | ]; lia).
    assert (HcAk : Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@k) by (eapply abs_kind_sort_lift; [ exact HcA | ]; lia).
    assert (HcBk : Γ ▹{κd} A' ⊢ B' : abs_kind_sort κc Typeω@k) by (eapply abs_kind_sort_lift; [ exact HcB | ]; lia).
    pose proof (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κd k)) as HSd;
      pose proof (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κc k)) as HSc.
    assert (HAA : Γ ⊢ A ≈ A' : abs_kind_sort κd Typeω@k).
    { eapply exp_eq_of_nbe_ty_same; [ exact HSd | exact HdAk | exact HdBk | exact HnA1 | exact HnB1 |].
      etransitivity; [ exact HWA1 |]; etransitivity; [ eassumption | symmetry; exact HWB1 ]. }
    assert (Hsub : Γ ▹{κd} A' ⊢ˢ Id : Γ ▹{κd} A)
      by (apply ctx_sub_escape; eapply ctx_sub_extend_eq; [ exact HdAk | exact HdBk | apply sort_kind_abs_kind_sort | exact HAA ]).
    assert (HcA' : Γ ▹{κd} A' ⊢ B : abs_kind_sort κc Typeω@k) by (eapply ctxsub_exp; [ exact Hsub | exact HcAk ]).
    (** The codomain [B]'s normal form in the second context. *)
    destruct (nbe_ty_exists_sort HSc HcA') as [WA2' HnA2'].
    assert (HWA2' : nf_eq_upto_proofs WA2 WA2').
    { eapply ctxeq_nbe_ty_eq_sort; [ exact HSc | exact HcAk | eapply ctx_extend_sem_eq; [ exact HSd | exact HAA ]
                                   | eapply wf_ctx_scoped_exp; exact HcA' | exact HnA2 | exact HnA2' ]. }
    eapply wf_subtyp_pi; [ exact HdAk | exact HdBk | exact HAA | exact HcAk | exact HcBk | | assumption | assumption ].
    eapply IHalg_subtyping_nf; [ exact HSc | exact HcA' | exact HcBk | | exists WB2; split; assumption ].
    exists WA2'; split; [ exact HnA2' |]; etransitivity; [ symmetry; exact HWA2' | exact HWA2 ].
Qed.

(** The normal forms of the other case are closed under equality up to
    proofs: it keeps the head and the kinds of a [Π]. *)
Lemma not_univ_pi_upto_proofs : forall A A', nf_eq_upto_proofs A A' -> not_univ_pi A -> not_univ_pi A'.
Proof.
  intros [] [] H; try (apply nf_pi_upto_proofs_inv in H as (<- & <- & _ & _); tauto);
    unfold nf_eq_upto_proofs in H; cbn in H; try discriminate; cbn; tauto.
Qed.

Lemma alg_subtyping_nf_trans : forall A0 A1 A2,
    ⊢anf A0 ⊆ A1 ->
    ⊢anf A1 ⊆ A2 ->
    ⊢anf A0 ⊆ A2.
Proof.
  intros * H1; gen A2.
  induction H1 as [A A' Hn Heq | | | | | κd κc A B A' B' Hk Heq Hsub IH]; intros A2 H2.
  1: { (** The first step is in the other case, so is the second. *)
    pose proof (not_univ_pi_upto_proofs _ _ Heq Hn) as Hn'.
    inversion H2; subst; cbn in Hn'; try contradiction;
      try match goal with He : evaluated_kind _ |- _ => inversion He; subst; contradiction end.
    apply alg_subtyping_nf_refl_case; [ exact Hn | etransitivity; eassumption ]. }
  (** The other cases: the second step is of the same case. *)
  all: inversion H2; subst; cbn in *; try contradiction;
    try match goal with He : evaluated_kind _ |- _ => solve [ inversion He; subst; contradiction ] end;
    first [ apply alg_subtyping_nf_small_large
          | apply alg_subtyping_nf_pi; [ exact Hk | etransitivity; eassumption | apply IH; assumption ]
          | apply alg_subtyping_nf_univ; lia
          | apply alg_subtyping_nf_level; lia
          | apply alg_subtyping_nf_suniv; eapply lvl_le_trans; eassumption ].
Qed.

Lemma alg_subtyping_nf_refl : forall A,
    ⊢anf A ⊆ A.
Proof.
  induction A.
  (** A [Π] into an evaluated kind by its codomain; another one is in the
      other case *)
  all: try (match goal with |- ⊢anf nf_pi _ ?r _ _ ⊆ _ => destruct r end).
  all: first [ apply alg_subtyping_nf_refl_case; [ exact I | reflexivity ]
             | apply alg_subtyping_nf_univ; lia
             | apply alg_subtyping_nf_suniv, lvl_le_refl
             | apply alg_subtyping_nf_level; reflexivity
             | apply alg_subtyping_nf_pi; [ constructor | reflexivity | assumption ] ].
Qed.

(** Normal forms equal up to proofs are subtypes: the normal forms
    completeness gives equal types. *)
Lemma alg_subtyping_nf_of_upto_proofs : forall A A',
    nf_eq_upto_proofs A A' ->
    ⊢anf A ⊆ A'.
Proof.
  intros A; induction A; intros A' Hup.
  all: try (match goal with |- ⊢anf nf_pi _ ?r _ _ ⊆ _ => destruct r end).
  all: try (apply alg_subtyping_nf_refl_case; [ exact I | exact Hup ]).
  (** A [Π] into an evaluated kind: by its codomain *)
  all: try (destruct A'; try (unfold nf_eq_upto_proofs in Hup; cbn in Hup; discriminate);
            apply nf_pi_upto_proofs_inv in Hup as (<- & <- & HA & HB);
            apply alg_subtyping_nf_pi; [ constructor | exact HA | auto ]).
  (** A universe or a type of levels *)
  all: destruct A'; unfold nf_eq_upto_proofs in Hup; cbn in Hup; try discriminate; eqb_split; eqb_leaves; subst.
  all: first [ apply alg_subtyping_nf_univ; lia
             | apply alg_subtyping_nf_level; lia
             | apply alg_subtyping_nf_suniv, lvl_le_of_upto_proofs; split; [ reflexivity | assumption ] ].
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
  - (** An equation at a sort: normal forms equal up to proofs *)
    match goal with H : _ ⊢ _ ≈ _ : ?S, HS : type_sort ?S |- _ => destruct (completeness_ty_sort HS H) as (W & W' & Hn1 & Hn2 & HE) end.
    econstructor; [ exact Hn1 | exact Hn2 | apply alg_subtyping_nf_of_upto_proofs; exact HE ].
  - assert (Γ ⊢ Typeω@i : Typeω@(S i)) as (W1 & HW1 & _)%soundness_ty by (apply wf_typ; assumption).
    assert (Γ ⊢ Typeω@j : Typeω@(S j)) as (W2 & HW2 & _)%soundness_ty by (apply wf_typ; assumption).
    econstructor; [ exact HW1 | exact HW2 |].
    inversion HW1 as [? ? _ He1 Hr1]; inversion HW2 as [? ? _ He2 Hr2]; subst.
    inversion He1; subst; inversion He2; subst; inversion Hr1; subst; inversion Hr2; subst.
    constructor; lia.
  (** The two small-universe rules: a small universe is its own normal
      form, read back by [read_typ_suniv]. *)
  - (** The order on the two canonical levels is read off the subtyping
        itself ([subtyp_suniv_bound]). *)
    assert (Hs : Γ ⊢ Type⟨M⟩ ⊆ Type⟨M'⟩) by (eapply wf_subtyp_suniv; eassumption).
    assert (Γ ⊢ Type⟨M⟩ : Typeω@0) as (WA & HA & _)%soundness_ty by (eapply wf_univ_large_tm; eassumption).
    assert (Γ ⊢ Type⟨M'⟩ : Typeω@0) as (WB & HB & _)%soundness_ty by (eapply wf_univ_large_tm; eassumption).
    econstructor; [ exact HA | exact HB |].
    destruct (nbe_ty_univ_term (T := Type⟨M⟩) ltac:(constructor) HA) as [u ->].
    destruct (nbe_ty_univ_term (T := Type⟨M'⟩) ltac:(constructor) HB) as [v ->].
    destruct (nbe_ty_suniv_univ_nf HA) as ([c xs] & -> & HL).
    destruct (nbe_ty_suniv_univ_nf HB) as ([d ys] & -> & HL').
    apply alg_subtyping_nf_suniv; exact (subtyp_suniv_bound Hs HL HL').
  (** The types of levels are their own normal forms. *)
  - assert (HL1 : Γ ⊢ Level@m : LevelSort) by (apply wf_level; assumption).
    assert (HL2 : Γ ⊢ Level@n : LevelSort) by (apply wf_level; assumption).
    destruct (nbe_ty_exists_sort (S := LevelSort) ltac:(constructor) HL1) as [W1 HW1].
    destruct (nbe_ty_exists_sort (S := LevelSort) ltac:(constructor) HL2) as [W2 HW2].
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
  - (** The domains have normal forms equal up to proofs; the codomain
        [B]'s, read back in [Γ ▹ A], is equal up to proofs to the one in
        [Γ ▹ A'] the induction hypothesis gives ([ctxeq_nbe_ty_eq_sort]). *)
    match goal with
    | HAA : _ ⊢ A ≈ A' : abs_kind_sort κd Typeω@i, HB0 : _ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i,
      HB1 : _ ▹{κd} A' ⊢ B' : _, IH : _ ▹{κd} A' ⊢a B ⊆ B' |- _ =>
        rename HAA into HAA', HB0 into HB', HB1 into HB1', IH into IH'
    end.
    pose proof (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κd i)) as HSd.
    pose proof (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κc i)) as HSc.
    destruct (completeness_ty_sort HSd HAA') as (WA & WA' & HnA & HnA' & HWA).
    destruct IH' as [X Y HX HY Hsub].
    destruct (nbe_ty_exists_sort HSc HB') as [WB HnB].
    assert (HWB : nf_eq_upto_proofs WB X)
      by (eapply ctxeq_nbe_ty_eq_sort; [ exact HSc | exact HB' | eapply ctx_extend_sem_eq; [ exact HSd | exact HAA' ]
                                     | eapply wf_ctx_scoped_exp; exact HB1' | exact HnB | exact HX ]).
    econstructor; [ eapply nbe_ty_pi_intro; [ exact HnA | exact HnB ] | eapply nbe_ty_pi_intro; [ exact HnA' | exact HY ] |].
    apply alg_subtyping_nf_pi; [ assumption | exact HWA |].
    eapply alg_subtyping_nf_trans; [ apply alg_subtyping_nf_of_upto_proofs; exact HWB | exact Hsub ].
Qed.

(** The normal form of a type of a sort is its own normal form up to
    proofs ([idempotent_nbe_ty_sort]). *)
Lemma nbe_ty_fixed_upto_proofs_of_nbe : forall {Γ S A W},
    type_sort S -> Γ ⊢ A : S -> nbe_ty_f Γ A W -> nbe_ty_fixed_upto_proofs Γ W.
Proof.
  intros * HS HA Hn.
  assert (HW : Γ ⊢ (W : exp) : S) by (pose proof (soundness_ty_at_sort HS HA Hn); gen_presups; assumption).
  destruct (nbe_ty_exists_sort HS HW) as [C HC].
  exists C; split; [ exact HC | symmetry; exact (idempotent_nbe_ty_sort HS HA Hn HC) ].
Qed.

(** Algorithmic subtyping is sound for two types of one sort: each is
    equal to its normal form, and those are subtypes. *)
Lemma alg_subtyping_sound_at : forall Γ A B S,
    type_sort S ->
    Γ ⊢a A ⊆ B ->
    Γ ⊢ A : S ->
    Γ ⊢ B : S ->
    Γ ⊢ A ⊆ B.
Proof.
  intros * HS [A' B' HnA HnB Hsub] HA HB.
  pose proof (soundness_ty_at_sort HS HA HnA) as HAA.
  pose proof (soundness_ty_at_sort HS HB HnB) as HBB.
  assert (HA' : Γ ⊢ (A' : exp) : S) by (gen_presups; assumption).
  assert (HB' : Γ ⊢ (B' : exp) : S) by (gen_presups; assumption).
  assert (Hs : Γ ⊢ A' ⊆ B')
    by (eapply alg_subtyping_nf_sound;
        [ exact Hsub | exact HS | exact HA' | exact HB'
        | exact (nbe_ty_fixed_upto_proofs_of_nbe HS HA HnA) | exact (nbe_ty_fixed_upto_proofs_of_nbe HS HB HnB) ]).
  transitivity A'; [ exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HA HA' HS HAA)) |].
  transitivity B'; [ exact Hs |].
  exact (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HB HB' HS HBB)).
Qed.

Lemma alg_subtyping_sound : forall Γ A B i,
    Γ ⊢a A ⊆ B ->
    Γ ⊢ A : Typeω@i ->
    Γ ⊢ B : Typeω@i ->
    Γ ⊢ A ⊆ B.
Proof. intros * Hs HA HB; exact (alg_subtyping_sound_at _ _ _ _ ltac:(constructor) Hs HA HB). Qed.

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
  destruct W; try match goal with |- not_univ_pi (nf_pi _ ?r _ _) => destruct r end;
    cbn; try exact I; exfalso; cbn [nf_to_exp] in HW.
  - exact (typ_prop_absurd (wf_typ _ _ _ _ HΓ) HW).
  - destruct (wf_univ_lvl_inversion HW) as [nL HL]; exact (typ_prop_absurd (wf_univ_large_tm (i := 0) HΓ HL) HW).
  - exact (level_type_not_prop (wf_level _ _ _ _ HΓ) HW).
  - destruct (wf_pi_typed_large HW) as [k Hk]; exact (typ_prop_absurd Hk HW).
  - (** A [Π] between types of levels is a type of levels. *)
    destruct (wf_pi_inversion_at HW) as [U HU HW1 HW2 Hk _].
    assert (HL : Γ ⊢ a_pi _ ak_level W1 W2 : LevelSort)
      by (change LevelSort with (abs_kind_sort ak_level U); eapply wf_pi; eassumption).
    exact (level_type_not_prop HL HW).
Qed.

(** Normal forms one of which is no universe, type of levels or relevant
    [Π] are subtypes only if equal up to proofs. *)
Lemma alg_subtyping_nf_not_univ_pi_eq : forall A B,
    ⊢anf A ⊆ B -> not_univ_pi A \/ not_univ_pi B -> nf_eq_upto_proofs A B.
Proof.
  intros * Hs Hn; inversion Hs; subst; try assumption; cbn in Hn; try (destruct Hn; contradiction).
  match goal with He : evaluated_kind _ |- _ => inversion He; subst; destruct Hn; contradiction end.
Qed.

(** Algorithmic subtyping relates normal forms of one kind
    ([nf_type_kind]): equal up to proofs, the universes, the types of
    levels, and [Π]s at one codomain kind. *)
Lemma alg_subtyping_nf_kind : forall A B, ⊢anf A ⊆ B -> nf_type_kind A = nf_type_kind B.
Proof.
  induction 1; try reflexivity.
  match goal with H : nf_eq_upto_proofs _ _ |- _ => exact (nf_type_kind_upto_proofs _ _ H) end.
Qed.

(** Algorithmic subtyping is sound for types of any sorts: the two normal
    forms are of one kind, so are the two sorts ([nbe_ty_kind_of_sort]),
    and sorts of one kind have a common sort. *)
Lemma alg_subtyping_sound_sort : forall Γ A B S S',
    type_sort S -> type_sort S' ->
    Γ ⊢a A ⊆ B ->
    Γ ⊢ A : S ->
    Γ ⊢ B : S' ->
    Γ ⊢ A ⊆ B.
Proof.
  intros * HS HS' Hs HA HB.
  pose proof Hs as [A' B' HnA HnB Hsub].
  pose proof (eq_trans (eq_sym (nbe_ty_kind_of_sort HS HA HnA))
                (eq_trans (alg_subtyping_nf_kind _ _ Hsub) (nbe_ty_kind_of_sort HS' HB HnB))) as Hk.
  destruct HS as [i | |], HS' as [j | |]; cbn [sort_exp_kind] in Hk; try discriminate Hk.
  - eapply (alg_subtyping_sound _ _ _ (max i j));
      [ exact Hs | eapply lift_exp_max_left; exact HA | eapply lift_exp_max_right; exact HB ].
  - exact (alg_subtyping_sound_at _ _ _ _ type_sort_prop Hs HA HB).
  - exact (alg_subtyping_sound_at _ _ _ _ type_sort_level Hs HA HB).
Qed.

End Fixed_GCtx.
