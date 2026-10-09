From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Subtyping Require Import Definitions.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import CoreInversions LevelEq SystemOpt.
From Mctt.Core.Semantic Require Import Levels.
From Mctt.Core.Completeness.Consequences Require Import Rules.
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

Lemma alg_subtyping_nf_sound : forall A B,
    ⊢anf A ⊆ B ->
    forall Γ i,
      Γ ⊢ A : Typeω@i ->
      Γ ⊢ B : Typeω@i ->
      Γ ⊢ A ⊆ B.
Proof.
  induction 1; intros; subst; simpl in *.
  - eapply wf_subtyp_refl'; mauto.
  - assert (i < j \/ i = j) as [] by lia; mauto 3.
  (** The two small-universe rules are the syntactic rules themselves; the
      order on canonical levels is the level equation [lvl_exp_of_le]. *)
  - gen_presups.
    (** The two level terms are levels of their own sorts; both move to the
        larger of the two, where the order on levels is stated. *)
    match goal with
    | HA : _ ⊢ a_univ ?t : _, HB : _ ⊢ a_univ ?t' : _ |- _ =>
        assert (exists n, Γ ⊢ t : Level@n) as [n1 Ht] by (eapply wf_univ_lvl_inversion; exact HA);
        assert (exists n, Γ ⊢ t' : Level@n) as [n2 Ht'] by (eapply wf_univ_lvl_inversion; exact HB);
        assert (Γ ⊢ t : Level@(Nat.max n1 n2))
          by (eapply wf_exp_subtyp'; [ exact Ht | apply wf_subtyp_level; [ lia | mauto 2 ] ]);
        assert (Γ ⊢ t' : Level@(Nat.max n1 n2))
          by (eapply wf_exp_subtyp'; [ exact Ht' | apply wf_subtyp_level; [ lia | mauto 2 ] ])
    end.
    eapply wf_subtyp_suniv; [ assumption | eassumption | eassumption |].
    apply lvl_exp_of_le; [ assumption | eapply lvl_exp_of_la_wf; eassumption
                         | eapply lvl_exp_of_la_wf; eassumption | assumption ].
  - gen_presups.
    assert (exists n, Γ ⊢ lvl_exp_of c (la_to_list xs) : Level@n) as [n Ht]
      by (eapply wf_univ_lvl_inversion; eassumption).
    eapply wf_subtyp_small_large; [ assumption | exact Ht ].
  - gen_presups; apply wf_subtyp_level; assumption.
  - on_all_hyp: fun H => apply wf_pi_inversion' in H; destruct H as [? ?].
    destruct_all.
    gen_presups.
    (** [Typeω@i[↑]ʷ] is [Typeω@i], so [wf_subtyp_ge] derives [Typeω@i ⊆ Typeω@j]
        in the extended context from [⊢ Γ ▹ A] alone. *)
    apply_subtyping.
    deepexec IHalg_subtyping_nf ltac:(fun H => pose proof H).
    mauto 3.
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
  induction A;
    solve [constructor; simpl; trivial | apply asnf_suniv, lvl_le_refl | apply asnf_level; reflexivity].
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
  - match_by_head1 (wf_exp_eq gc_deps gc_stack) ltac:(fun H => apply completeness in H as [W [? ?]]).
    econstructor; mauto.
  - assert (Γ ⊢ Typeω@i : Typeω@(S i)) by mauto.
    assert (Γ ⊢ Typeω@j : Typeω@(S j)) by mauto.
    on_all_hyp: fun H => apply soundness in H.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    mauto.
  (** The two small-universe rules: a small universe is its own normal
      form, read back by [read_typ_suniv]. *)
  - (** The order on the two canonical levels is read off the normal form of
        the premise [maxl M M' ≈ M'] ([read_max_lvl_le]). *)
    match goal with H : wf_exp_eq _ _ _ _ (maxl _ _) _ |- _ =>
      apply completeness in H as [W [Hn1 Hn2]] end.
    assert (Γ ⊢ Type⟨M⟩ : Typeω@0) as HA%soundness by (eapply wf_univ_large_tm; eassumption).
    assert (Γ ⊢ Type⟨M'⟩ : Typeω@0) as HB%soundness by (eapply wf_univ_large_tm; eassumption).
    destruct HA as [WA [HA _]]; destruct HB as [WB [HB _]].
    econstructor; mauto 2.
    progressive_inversion.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    apply asnf_suniv; eapply read_max_lvl_le; eassumption.
  (** The types of levels are their own normal forms. *)
  - assert (Γ ⊢ Level@m : Typeω@0) by mauto 3.
    assert (Γ ⊢ Level@n : Typeω@0) by mauto 3.
    on_all_hyp: fun H => apply soundness in H.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    apply asnf_level; assumption.
  - assert (Γ ⊢ Type⟨M⟩ : Typeω@0) by (eapply wf_univ_large_tm; eassumption).
    assert (Γ ⊢ Typeω@i : Typeω@(S i)) by mauto.
    on_all_hyp: fun H => apply soundness in H.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    apply asnf_small_large.
  - (** [ctxeq_nbe_eq] takes a semantic context equality, which
        [per_ctx_of_exp_eq] builds from the domains. *)
    assert (⊨ Γ ▹ A ≈ Γ ▹ A') by mauto.
    (** The codomain's normal form is read back in [Γ ▹ A], but the induction
        hypothesis gives it in [Γ ▹ A'], so it is transported.  This is added
        as a fact rather than a rewrite because [Γ ▹ A ⊢ B : Typeω@i] is still
        needed below. *)
    assert (exists W, nbe_f (Γ ▹ A) B Typeω@i W /\ nbe_f (Γ ▹ A') B Typeω@i W)
      by mauto 3 using ctxeq_nbe_eq.
    match_by_head1 (wf_exp_eq gc_deps gc_stack) ltac:(fun H => apply completeness in H).
    assert (Γ ⊢ Π A B : Typeω@i) as ?%soundness by mauto.
    assert (Γ ⊢ Π A' B' : Typeω@i) as ?%soundness by mauto.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    functional_read_rewrite_clear.
    mauto 2.
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
  assert (Γ ⊢ A' ⊆ B') by mauto 3 using alg_subtyping_nf_sound.
  transitivity A'; [mauto |].
  transitivity B'; [eassumption |].
  mauto.
Qed.

End Fixed_GCtx.
