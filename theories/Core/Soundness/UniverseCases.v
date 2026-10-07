From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation SubtypingCases TermStructureCases.
Import Domain_Notations Fixed_Notations.


(** The readback clause of [glu_rel_exp_of_univ] for a closed type former:
    the type reads back as itself, so the clause is its congruence rule at
    the universe ([wf_exp_eq_*_cong_univ]). *)
Ltac closed_typ_readback :=
  let Hφ := fresh "Hφ" in
  let Hr := fresh "Hr" in
  intros ? ? ? Hφ Hr;
  assert (⊢ _) by (eapply kripke_dom; exact Hφ);
  inversion Hr; subst; simplify_subs; cbn [nf_to_exp];
  first [ apply wf_exp_eq_nat_cong_univ | apply wf_exp_eq_True_cong_univ
        | apply wf_exp_eq_False_cong_univ | apply wf_exp_eq_level_cong_univ ];
  assumption.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Universes at Any Index

    A type at an index [u] is a term of the universe [ulvl_tm u], whose value
    [ulvl_val u] is glued at the ambient index [ulvl_above u].  The two
    lemmas below are inverse to each other; the large forms used by the rest
    of the development are their instances at [ul i]. *)

Lemma glu_rel_exp_of_univ : forall {Γ Sb A} {u : uidx},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢s σ ® ρ ∈ Sb ->
        Δ ⊢ A[σ] : ulvl_tm u /\
          exists a,
            ⟦ A ⟧ ρ ↘ a /\
              Dom a ≈ a ∈ per_univ u /\
              (forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
              (forall Δ' φ W, Δ' ⊢k φ : Δ -> Rtyp a in length Δ' ↘ W ->
                         Δ' ⊢ A[σ][φ]ʷ ≈ W : ulvl_tm u)) ->
    Γ ⊩ A : ulvl_tm u.
Proof.
  intros * ? Hbody.
  eexists; split; [ eassumption |].
  exists (ulvl_above u).
  intros * HΔ.
  destruct (Hbody _ _ _ HΔ) as [H0 [a [? [[] [H3 Hrb]]]]].
  assert (⊢ Δ) by (gen_presups; eassumption).
  assert (exists P El, DG a ∈ glu_univ_elem u ↘ P ↘ El) as [P [El HPEl]] by mauto 3.
  econstructor; [ apply eval_ulvl_tm | eassumption
                | apply glu_univ_elem_univ_at, uidx_lt_ulvl_above |].
  rewrite exp_sub_ulvl_tm.
  destruct u as [n | j]; cbn [univ_glu_exp_pred_at ulvl_tm ulvl_above] in *.
  - (** A type of a small universe at a literal level: the level term is the
        literal, and the readback clause is the premise's. *)
    repeat split.
    + exact H0.
    + exists 𝕃@n; split; [ apply glu_lvl_lit; assumption | mauto 3 ].
    + exists P, El; split; [ exact HPEl | exact (H3 P El HPEl) ].
    + exact Hrb.
  - repeat split.
    + exact H0.
    + mauto 3.
    + exists P, El; split; [ exact HPEl | exact (H3 P El HPEl) ].
Qed.

(** The universe at [u] is itself a term of [Type@(ulvl_above u)]: the
    ambient universe the inversion below is stated at. *)
Lemma glu_rel_exp_univ_tm : forall {Γ} {u : uidx},
    ⊩ Γ ->
    Γ ⊩ ulvl_tm u : Type@(ulvl_above u).
Proof.
  intros * [Sb HΓ].
  assert (⊢ Γ) by mauto 2.
  eapply (glu_rel_exp_of_univ (u := ul (ulvl_above u))); [ eassumption |].
  intros Δ σ ρ HΔ.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  rewrite exp_sub_ulvl_tm.
  split; [ apply wf_ulvl_tm; assumption |].
  exists (ulvl_val u).
  split; [ apply eval_ulvl_tm |].
  split; [ eexists; apply per_univ_elem_ulvl_val, uidx_lt_ulvl_above |].
  split.
  - intros P El HPEl.
    pose proof (glu_univ_elem_univ_at (u := u) (i := ul (ulvl_above u)) (uidx_lt_ulvl_above u)).
    handle_functional_glu_univ_elem.
    destruct u as [n | j]; cbn [univ_glu_typ_pred_at ulvl_tm ulvl_above ulvl] in *.
    + exists 𝕃@n; split; [ apply glu_lvl_lit; assumption | mauto 3 ].
    + apply wf_exp_eq_typ_cong; assumption.
  - (** The universe reads back as itself. *)
    intros Δ' φ W Hφ Hr.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    destruct u as [n | j]; cbn [ulvl_val ulvl_tm ulvl_above] in *;
      inversion Hr; subst; cbn.
    + assert (Hn := read_nf_dlvl_lit n (length Δ')); unfold dlvl_lit in Hn.
      assert (L = lvl_lit n) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption).
      cbn; apply wf_exp_eq_univ_cong_large; assumption.
    + mauto 3.
Qed.

Lemma glu_rel_exp_of_univ_inversion : forall {Γ Sb A} {u : uidx},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : ulvl_tm u ->
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      Δ ⊢ A[σ] : ulvl_tm u /\
        exists a,
          ⟦ A ⟧ ρ ↘ a /\
            Dom a ≈ a ∈ per_univ u /\
            (forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
            (forall Δ' φ W, Δ' ⊢k φ : Δ -> Rtyp a in length Δ' ↘ W ->
                       Δ' ⊢ A[σ][φ]ʷ ≈ W : ulvl_tm u).
Proof.
  intros * HΓ HA * HΔ.
  assert (Γ ⊩ ulvl_tm u : Type@(ulvl_above u)) by (eapply glu_rel_exp_univ_tm; eexists; eassumption).
  eapply glu_rel_exp_clean_inversion2 in HA; [| eassumption | eassumption ].
  destruct (HA _ _ _ HΔ).
  pose proof (eval_ulvl_tm gc_deps gc_stack u ρ).
  functional_eval_rewrite_clear.
  pose proof (glu_univ_elem_univ_at (u := u) (i := ul (ulvl_above u)) (uidx_lt_ulvl_above u)).
  handle_functional_glu_univ_elem.
  (** The element predicate of the ambient universe is the gluing of a type at
      [u]: that is the information the small tier needs.  Its readback clause
      is part of it in the small tier, and realizability in the large one. *)
  destruct u as [n | j]; cbn [univ_glu_exp_pred_at ulvl_tm ulvl_above] in *.
  - match goal with H : suniv_glu_exp_pred _ _ _ _ _ _ |- _ =>
      destruct H as [HAσ [_ [[Pm [Elm [HPEl HP]]] Hrb]]] end.
    rewrite ?exp_sub_ulvl_tm in *.
    split; [ assumption |].
    exists m; split; [ assumption | split; [| split ] ].
    + eapply glu_univ_elem_per_univ; eassumption.
    + intros P' El' H'.
      handle_functional_glu_univ_elem.
      assumption.
    + exact Hrb.
  - match goal with H : univ_glu_exp_pred _ _ _ _ _ _ |- _ =>
      destruct H as [HAσ [Heq [Pm [Elm [HPEl HP]]]]] end.
    rewrite ?exp_sub_ulvl_tm in *.
    split; [ assumption |].
    exists m; split; [ assumption | split; [| split ] ].
    + eapply glu_univ_elem_per_univ; eassumption.
    + intros P' El' H'.
      handle_functional_glu_univ_elem.
      assumption.
    + assert (Δ ⊢ A[σ] ® glu_typ_top j m) as [] by mauto 3.
      intros; eauto.
Qed.

(** A type at an index [u] is a type at the large level [ulvl u], which is
    the index a context entry is glued at. *)
Lemma glu_rel_typ_with_sub_uidx : forall {u : uidx} {Δ A σ ρ},
    (exists a,
        ⟦ A ⟧ ρ ↘ a /\
          Dom a ≈ a ∈ per_univ u /\
          forall P El, DG a ∈ glu_univ_elem u ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    glu_rel_typ_with_sub (ulvl u) Δ A σ ρ.
Proof.
  intros * [a [Hae [[R HR] HaP]]].
  assert (exists P El, DG a ∈ glu_univ_elem u ↘ P ↘ El) as [P [El HPEl]] by mauto 3.
  assert (exists P' El', DG a ∈ glu_univ_elem (ulvl u) ↘ P' ↘ El') as [P' [El' HPEl']]
      by (eapply (glu_univ_elem_cumu_ge_uidx (i := u)); [ apply uidx_le_ulvl | exact HPEl ]).
  econstructor; [ exact Hae | exact HPEl' |].
  eapply (glu_univ_elem_typ_cumu_ge_uidx (i := u) (j := ulvl u));
    [ apply uidx_le_ulvl | exact HPEl | exact HPEl' | exact (HaP P El HPEl) ].
Qed.

(** Cumulativity of the gluing judgment, along the order of indices. *)
Lemma glu_rel_exp_lift_uidx : forall {Γ A} {u v : uidx},
    uidx_le u v ->
    Γ ⊩ A : ulvl_tm u ->
    Γ ⊩ A : ulvl_tm v.
Proof.
  intros * Hle HA.
  assert (⊢ Γ) by mauto 3 using glu_rel_exp_to_wf_exp.
  eapply glu_rel_exp_subtyp;
    [ exact HA
    | eapply glu_rel_exp_univ_tm; destruct HA as [Sb []]; eexists; eassumption
    | apply wf_subtyp_uidx; assumption ].
Qed.

Corollary glu_rel_exp_ulvl : forall {Γ A} {u : uidx},
    Γ ⊩ A : ulvl_tm u ->
    Γ ⊩ A : Type@(ulvl u).
Proof.
  intros * HA.
  exact (glu_rel_exp_lift_uidx (u := u) (v := ulvl u) (uidx_le_ulvl u) HA).
Qed.

Lemma glu_rel_exp_of_typ : forall {Γ Sb A} {i : nat},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢s σ ® ρ ∈ Sb ->
        Δ ⊢ A[σ] : Type@i /\
          exists a,
            ⟦ A ⟧ ρ ↘ a /\
              Dom a ≈ a ∈ per_univ i /\
              forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    Γ ⊩ A : Type@i.
Proof.
  intros * ? Hbody.
  eexists; split; mauto.
  exists (S i).
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
Qed.

(** The small universe as a term of the next small universe. *)
Lemma glu_rel_exp_suniv : forall {Γ} {n : nat},
    ⊩ Γ ->
    Γ ⊩ Typeˢ@n : Typeˢ@(S n).
Proof.
  intros * [Sb HΓ].
  assert (⊢ Γ) by mauto 2.
  eapply (glu_rel_exp_of_univ (u := us (S n))); [ eassumption |].
  intros Δ σ ρ HΔ.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  cbn.
  split; [ apply wf_univ_lit; assumption |].
  exists 𝕌ˢ@(dlvl_lit n).
  split; [ apply eval_exp_univ, eval_exp_llit |].
  split; [ eexists; apply (per_univ_elem_ulvl_val (us n) (us (S n))); cbn; lia |].
  split.
  - intros P El HPEl.
    pose proof (glu_univ_elem_univ_at (u := us n) (i := us (S n)) ltac:(cbn; lia)).
    handle_functional_glu_univ_elem.
    cbn; exists 𝕃@n; split; [ apply glu_lvl_lit; assumption | mauto 3 ].
  - (** The small universe reads back as itself. *)
    intros Δ' φ W Hφ Hr.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    inversion Hr; subst.
    assert (Hn := read_nf_dlvl_lit n (length Δ')); unfold dlvl_lit in Hn.
    assert (L = lvl_lit n) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption).
    cbn; apply wf_exp_eq_univ_cong_lit; assumption.
Qed.

Hint Resolve glu_rel_exp_suniv : mctt.

Lemma glu_rel_exp_typ : forall {Γ} {i : nat},
    ⊩ Γ ->
    Γ ⊩ Type@i : Type@(S i).
Proof.
  intros * [].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  cbn.
  mauto 4.
  (** [Type@i[σ]] is [Type@i], so the equation is reflexivity, which needs
      [⊢ Δ] from a presupposition. *)
  gen_presups; mauto 3.
Qed.

Hint Resolve glu_rel_exp_typ : mctt.

Lemma glu_rel_exp_clean_inversion2' : forall {i : nat} {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : Type@i ->
    glu_rel_exp_clean_inversion2_result (S i) Sb M Type@i.
Proof.
  intros * ? HM.
  assert (Γ ⊩ Type@i : Type@(S i)) by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_typ glu_rel_exp_suniv : mctt.
Ltac invert_glu_rel_exp H ::=
  (unshelve eapply (glu_rel_exp_clean_inversion2' _) in H; shelve_unifiable; [eassumption |];
   unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
     unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

