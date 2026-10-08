(** * Levels in the Gluing Model

    Substitution into every level form is definitional, so the congruence steps
    are reflexivity.  A level is glued to a value by its readback ([glu_lvl]),
    and the readback of a level operation is the canonical form of that
    operation on the canonical forms of its arguments
    ([Core.Semantic.Levels]).  So each case is: read the atoms of the arguments,
    and then rewrite the syntax by the level equations until it is the canonical
    form — which is [Core.Syntactic.LevelEq]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LevelCases.
From Mctt.Core.Semantic Require Import Levels Realizability.
From Mctt.Core.Syntactic Require Import LevelEq Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations Wk_Notations.

Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [Level] is a type at every index: the rule gives it the small universe
    [Type@0], and the other forms are instances. *)
Lemma glu_rel_exp_level_univ : forall {Γ} {u : uidx},
    ⊩ Γ ->
    Γ ⊩ Level : ulvl_tm u.
Proof.
  intros * [Sb].
  assert (⊢ Γ) by mauto.
  eapply glu_rel_exp_of_univ; mauto 3.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  split; [ simplify_subs; apply wf_level_univ; assumption |].
  eexists; repeat split; mauto 3; [| closed_typ_readback ].
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  unfold level_glu_typ_pred.
  simplify_subs; apply wf_exp_eq_level_cong_large; assumption.
Qed.

Lemma glu_rel_exp_level : forall {Γ} {i : nat},
    ⊩ Γ ->
    Γ ⊩ Level : Typeω@i.
Proof. intros; apply (glu_rel_exp_level_univ (u := ul i)); assumption. Qed.

Lemma glu_rel_exp_level_small : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ Level : Type@0.
Proof. intros; apply (glu_rel_exp_level_univ (u := us oz)); assumption. Qed.

Hint Resolve glu_rel_exp_level : mctt.

(** ** Terms of Type [Level] *)
Lemma glu_rel_exp_of_level : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢s σ ® ρ ∈ Sb ->
        exists m, ⟦ M ⟧ ρ ↘ m /\ Dom m ≈ m ∈ per_lvl /\ glu_lvl Δ M[σ] m) ->
    Γ ⊩ M : Level.
Proof.
  intros * ? Hbody.
  eexists; split; mauto 3.
  exists 0.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  edestruct Hbody as [? [? []]]; mauto 3.
  econstructor; mauto 3.
  - glu_univ_elem_econstructor; mauto 3; reflexivity.
  - simpl; repeat split; mauto 3.
Qed.

Lemma glu_rel_exp_clean_inversion_level : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : Level ->
    glu_rel_exp_clean_inversion2_result 0 Sb M Level.
Proof.
  intros * ? HM.
  assert (Γ ⊩ Level : Typeω@0) by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

(** The glued level of a term of type [Level]: its value, the canonical form
    the value reads back as, and the equation between the two. *)
Lemma glu_rel_exp_level_elim : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : Level ->
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      exists m, ⟦ M ⟧ ρ ↘ m /\ Dom m ≈ m ∈ per_lvl /\ glu_lvl Δ M[σ] m.
Proof.
  intros * HSb HM * Hσ.
  eapply glu_rel_exp_clean_inversion_level in HM; [| exact HSb ].
  specialize (HM _ _ _ Hσ).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  simpl in *; destruct_conjs.
  eexists; repeat split; eassumption.
Qed.

(** ** The Level Forms

    A literal evaluates to a flat level with no atom, whose readback is the
    literal itself. *)
Lemma glu_rel_exp_llit : forall {Γ n},
    ⊩ Γ ->
    Γ ⊩ 𝕃ᵒ n : Level.
Proof.
  intros * [Sb].
  assert (⊢ Γ) by mauto 2.
  eapply glu_rel_exp_of_level; [ eassumption |].
  intros Δ σ ρ Hσ.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  exists (dlvl_lit n); split; [ mauto 3 | split; [ apply per_lvl_lit |] ].
  intros Δ' φ L Hφ Hr.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  (** The readback of a literal is the literal. *)
  apply dlvl_canon_of_read in Hr as [_ [L' [-> Hc]]].
  assert (L' = lvl_lit n) as ->
    by (eapply dlvl_canon_functional; [ exact Hc | apply dlvl_canon_lit ]).
  simplify_subs; cbn.
  mauto 3.
Qed.

Hint Resolve glu_rel_exp_llit : mctt.

(** The readback of a level is its canonical form, and the canonical form of a
    level operation is the operation on the canonical forms, which the
    equations of [LevelEq] identify with the syntax. *)
Lemma glu_rel_exp_succl : forall {Γ M},
    Γ ⊩ M : Level ->
    Γ ⊩ succl M : Level.
Proof.
  intros * HM.
  assert (⊩ Γ) as [Sb] by mauto 3.
  eapply glu_rel_exp_of_level; [ eassumption |].
  intros Δ σ ρ Hσ.
  destruct (glu_rel_exp_level_elim ltac:(eassumption) HM _ _ _ Hσ) as [m [Hev [Hper Hglu]]].
  exists (dlvl_suc m); split; [ mauto 3 | split; [ apply per_lvl_suc; exact Hper |] ].
  intros Δ' φ L Hφ Hr.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  apply dlvl_canon_of_read in Hr as [_ [L' [-> Hc]]].
  destruct (per_lvl_ex _ _ Hper (length Δ')) as [A HA].
  assert (L' = lvl_canon (lvl_suc A)) as ->
    by (eapply dlvl_canon_functional; [ exact Hc | apply dlvl_canon_suc; exact HA ]).
  assert (Hsh : dlvl_shape m) by (destruct (per_lvl_shape _ _ Hper); assumption).
  assert (HMA : Δ' ⊢ M[σ][φ]ʷ ≈ nf_lvl_of A : Level)
    by (eapply glu_lvl_readback;
        [ exact Hglu | exact Hφ | apply dlvl_canon_read; [ exact Hsh | exact HA ] ]).
  destruct A as [c xs].
  assert (HL : Δ' ⊢ nf_lvl_of (c, xs) : Level) by (gen_presups; eassumption).
  unfold nf_lvl_of in HL; cbn in HL.
  assert (Hwf : la_wf Δ' xs) by (eapply lvl_exp_of_la_wf; exact HL).
  assert (Hwfs : la_wf Δ' (snd (lvl_canon (lvl_suc (c, xs)))))
    by (unfold lvl_canon, lvl_suc; cbn; apply la_wf_sort, la_wf_suc; exact Hwf).
  (** The syntax is the canonical form of the argument; the successor of that
      is, by the level equations, the canonical form of the successor. *)
  simplify_subs; cbn [exp_wk].
  transitivity (succl (nf_lvl_of (c, xs))); [ mauto 3 |].
  unfold nf_lvl_of; cbn [fst snd].
  transitivity (succl (lvl_tm c xs));
    [ apply wf_exp_eq_succl_cong, lvl_exp_of_tm; [ assumption | exact Hwf ] |].
  transitivity (lvl_tm (fst (lvl_suc (c, xs))) (snd (lvl_suc (c, xs))));
    [ apply lvl_tm_suc; [ assumption | exact Hwf ] |].
  transitivity (lvl_tm (fst (lvl_canon (lvl_suc (c, xs)))) (snd (lvl_canon (lvl_suc (c, xs)))));
    [ apply lvl_tm_canon; [ assumption | unfold lvl_suc; cbn; apply la_wf_suc; exact Hwf ] |].
  apply wf_exp_eq_sym, lvl_exp_of_tm; [ assumption | exact Hwfs ].
Qed.

Hint Resolve glu_rel_exp_succl : mctt.

Lemma glu_rel_exp_maxl : forall {Γ M N},
    Γ ⊩ M : Level ->
    Γ ⊩ N : Level ->
    Γ ⊩ maxl M N : Level.
Proof.
  intros * HM HN.
  assert (⊩ Γ) as [Sb] by mauto 3.
  eapply glu_rel_exp_of_level; [ eassumption |].
  intros Δ σ ρ Hσ.
  destruct (glu_rel_exp_level_elim ltac:(eassumption) HM _ _ _ Hσ) as [m [Hev [Hper Hglu]]].
  destruct (glu_rel_exp_level_elim ltac:(eassumption) HN _ _ _ Hσ) as [n [Hev' [Hper' Hglu']]].
  exists (dlvl_max m n); split; [ mauto 3 | split; [ apply per_lvl_max; eassumption |] ].
  intros Δ' φ L Hφ Hr.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  apply dlvl_canon_of_read in Hr as [_ [L' [-> Hc]]].
  destruct (per_lvl_ex _ _ Hper (length Δ')) as [A HA].
  destruct (per_lvl_ex _ _ Hper' (length Δ')) as [B HB].
  assert (L' = lvl_canon (lvl_max A B)) as ->
    by (eapply dlvl_canon_functional; [ exact Hc | apply dlvl_canon_max; eassumption ]).
  assert (Hsh : dlvl_shape m) by (destruct (per_lvl_shape _ _ Hper); assumption).
  assert (Hsh' : dlvl_shape n) by (destruct (per_lvl_shape _ _ Hper'); assumption).
  assert (HMA : Δ' ⊢ M[σ][φ]ʷ ≈ nf_lvl_of A : Level)
    by (eapply glu_lvl_readback;
        [ exact Hglu | exact Hφ | apply dlvl_canon_read; [ exact Hsh | exact HA ] ]).
  assert (HNB : Δ' ⊢ N[σ][φ]ʷ ≈ nf_lvl_of B : Level)
    by (eapply glu_lvl_readback;
        [ exact Hglu' | exact Hφ | apply dlvl_canon_read; [ exact Hsh' | exact HB ] ]).
  destruct A as [c xs]; destruct B as [d ys].
  assert (HLA : Δ' ⊢ nf_lvl_of (c, xs) : Level) by (gen_presups; eassumption).
  assert (HLB : Δ' ⊢ nf_lvl_of (d, ys) : Level) by (gen_presups; eassumption).
  unfold nf_lvl_of in HLA, HLB; cbn in HLA, HLB.
  assert (Hwfx : la_wf Δ' xs) by (eapply lvl_exp_of_la_wf; exact HLA).
  assert (Hwfy : la_wf Δ' ys) by (eapply lvl_exp_of_la_wf; exact HLB).
  assert (Hwfm : la_wf Δ' (snd (lvl_canon (lvl_max (c, xs) (d, ys)))))
    by (unfold lvl_canon, lvl_max; cbn; apply la_wf_sort, la_wf_app; [ exact Hwfx | exact Hwfy ]).
  simplify_subs; cbn [exp_wk].
  transitivity (maxl (nf_lvl_of (c, xs)) (nf_lvl_of (d, ys))); [ mauto 3 |].
  unfold nf_lvl_of; cbn [fst snd].
  transitivity (maxl (lvl_tm c xs) (lvl_tm d ys));
    [ apply wf_exp_eq_maxl_cong; apply lvl_exp_of_tm;
      [ assumption | exact Hwfx | assumption | exact Hwfy ] |].
  transitivity (lvl_tm (fst (lvl_max (c, xs) (d, ys))) (snd (lvl_max (c, xs) (d, ys))));
    [ apply lvl_tm_max; [ assumption | exact Hwfx | exact Hwfy ] |].
  transitivity (lvl_tm (fst (lvl_canon (lvl_max (c, xs) (d, ys))))
                       (snd (lvl_canon (lvl_max (c, xs) (d, ys)))));
    [ apply lvl_tm_canon; [ assumption | unfold lvl_max; cbn; apply la_wf_app; [ exact Hwfx | exact Hwfy ] ] |].
  apply wf_exp_eq_sym, lvl_exp_of_tm; [ assumption | exact Hwfm ].
Qed.

Hint Resolve glu_rel_exp_maxl : mctt.

(** ** The Small Universe at a Level Term

    [Type⟨M⟩] is an element of [Type⟨succl M⟩], glued at the large index [0].
    Its type-level gluing takes the level term [succl M], and its element
    gluing the level term [M], both glued to their values by the level case
    above; its readback is the universe at the readback of [M], which the
    congruence rule of universes equates with it. *)
Lemma glu_rel_exp_univ_lvl : forall {Γ M},
    Γ ⊩ M : Level ->
    Γ ⊩ Type⟨M⟩ : Type⟨succl M⟩.
Proof.
  intros * HM.
  assert (⊩ Γ) as [Sb HSb] by mauto 3.
  pose proof (glu_rel_exp_succl HM) as HSM.
  eexists; split; [ eassumption |].
  exists 0.
  intros Δ σ ρ Hσ.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  destruct (glu_rel_exp_level_elim HSb HM _ _ _ Hσ) as [m [Hev [Hper Hglu]]].
  destruct (glu_rel_exp_level_elim HSb HSM _ _ _ Hσ) as [m' [Hev' [Hper' Hglu']]].
  inversion Hev'; subst; functional_eval_rewrite_clear.
  assert (Δ ⊢ M[σ] : Level) by (eapply (glu_lvl_escape _ _ _ Hper Hglu); assumption).
  econstructor;
    [ apply eval_exp_univ; eassumption
    | apply eval_exp_univ; eassumption
    | apply glu_univ_elem_core_suniv'; [ exact Hper' | exact I | reflexivity | reflexivity ]
    |].
  simplify_subs; cbn [exp_sub] in *.
  repeat split.
  - apply wf_univ; assumption.
  - exists (succl M[σ]); split; [ exact Hglu' |].
    apply wf_exp_eq_univ_cong_large_tm; [ assumption | mauto 3 | mauto 3 ].
  - rewrite dlvl_real_suc.
    do 2 eexists; split;
      [ apply glu_univ_elem_core_suniv'; [ exact Hper | cbn; ord | reflexivity | reflexivity ] |].
    exists M[σ]; split; [ exact Hglu |].
    apply wf_exp_eq_univ_cong_large_tm; [ assumption | assumption | mauto 3 ].
  - intros Δ' φ W Hφ Hr.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    inversion Hr; subst.
    assert (Δ' ⊢ M[σ][φ]ʷ ≈ nf_lvl_of L : Level) by (eapply glu_lvl_readback; eassumption).
    cbn [exp_wk nf_to_exp nf_univ_of].
    apply wf_exp_eq_univ_cong; assumption.
Qed.

Hint Resolve glu_rel_exp_univ_lvl : mctt.

(** ** Types of the Small Universe at a Level Term

    [Type⟨T⟩] is in the least large universe, which is the ambient universe
    its types are glued at; inverting that gluing gives the type-level gluing
    at the realiser of [T]'s value, and the readback clause at [Type⟨T⟩]. *)
Lemma glu_rel_exp_suniv_tm_large : forall {Γ T},
    Γ ⊩ T : Level ->
    Γ ⊩ Type⟨T⟩ : Typeω@0.
Proof.
  intros * HT.
  assert (⊩ Γ) by mauto 3.
  assert (Γ ⊢ T : Level) by (eapply glu_rel_exp_to_wf_exp; exact HT).
  assert (⊢ Γ) by mauto 3.
  eapply glu_rel_exp_subtyp;
    [ apply glu_rel_exp_univ_lvl, HT | apply glu_rel_exp_typ; assumption
    | apply wf_subtyp_small_large; mauto 3 ].
Qed.

(** The same inversion without the level's own gluing: the index of the
    judgment is whatever it is, and the small universe is below it. *)
Lemma glu_rel_exp_of_suniv_tm_inversion' : forall {Γ Sb T A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : Type⟨T⟩ ->
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      exists l,
        ⟦ T ⟧ ρ ↘ l /\ Dom l ≈ l ∈ per_lvl /\
        Δ ⊢ A[σ] : Type⟨T[σ]⟩ /\
        exists a,
          ⟦ A ⟧ ρ ↘ a /\
            Dom a ≈ a ∈ per_univ (us (dlvl_real l)) /\
            (forall P El, DG a ∈ glu_univ_elem (us (dlvl_real l)) ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
            (forall Δ' φ W, Δ' ⊢k φ : Δ -> Rtyp a in length Δ' ↘ W ->
                       Δ' ⊢ A[σ][φ]ʷ ≈ W : Type⟨T[σ][φ]ʷ⟩).
Proof.
  intros * HΓ HA * HΔ.
  destruct (glu_rel_exp_clean_inversion1 HΓ HA) as [i HAi].
  destruct (HAi _ _ _ HΔ) as [a0 m P El Ha0 Hm HPEl Hglu].
  inversion Ha0; subst.
  invert_glu_univ_elem HPEl.
  apply_predicate_equivalence.
  cbn [suniv_glu_exp_pred'] in Hglu.
  destruct Hglu as [HAσ [_ [Hty Hrb]]].
  destruct Hty as [Pm [Elm [HPm HP]]].
  match goal with Hl : ⟦ T ⟧ ρ ↘ ?l |- _ => exists l; split; [ exact Hl |] end.
  split; [ assumption |].
  split; [ exact HAσ |].
  exists m; split; [ assumption | split; [| split ] ].
  - eapply glu_univ_elem_per_univ; eassumption.
  - intros P' El' H'.
    handle_functional_glu_univ_elem.
    assumption.
  - exact Hrb.
Qed.

Lemma glu_rel_exp_of_suniv_tm : forall {Γ Sb T A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ T : Level ->
    (forall Δ σ ρ,
        Δ ⊢s σ ® ρ ∈ Sb ->
        forall l, ⟦ T ⟧ ρ ↘ l ->
        Δ ⊢ A[σ] : Type⟨T[σ]⟩ /\
          exists a,
            ⟦ A ⟧ ρ ↘ a /\
              Dom a ≈ a ∈ per_univ (us (dlvl_real l)) /\
              (forall P El, DG a ∈ glu_univ_elem (us (dlvl_real l)) ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
              (forall Δ' φ W, Δ' ⊢k φ : Δ -> Rtyp a in length Δ' ↘ W ->
                         Δ' ⊢ A[σ][φ]ʷ ≈ W : Type⟨T[σ][φ]ʷ⟩)) ->
    Γ ⊩ A : Type⟨T⟩.
Proof.
  intros * HΓ HT Hbody.
  eexists; split; [ eassumption |].
  exists 0.
  intros Δ σ ρ Hσ.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  destruct (glu_rel_exp_level_elim HΓ HT _ _ _ Hσ) as [l [Hl [Hper Hglu]]].
  destruct (Hbody _ _ _ Hσ l Hl) as [HAσ [a [Ha [Haper [HaP Hrb]]]]].
  assert (Δ ⊢ T[σ] : Level) by (eapply (glu_lvl_escape _ _ _ Hper Hglu); assumption).
  assert (exists P El, DG a ∈ glu_univ_elem (us (dlvl_real l)) ↘ P ↘ El) as [P [El HPEl]] by mauto 3.
  econstructor;
    [ apply eval_exp_univ; eassumption
    | eassumption
    | apply glu_univ_elem_core_suniv'; [ exact Hper | exact I | reflexivity | reflexivity ]
    |].
  cbn [exp_sub suniv_glu_exp_pred'].
  repeat split.
  - exact HAσ.
  - exists T[σ]; split; [ exact Hglu |].
    apply wf_exp_eq_univ_cong_large_tm; [ assumption | assumption | mauto 3 ].
  - exists P, El; split; [ exact HPEl | exact (HaP _ _ HPEl) ].
  - exact Hrb.
Qed.

Lemma glu_rel_exp_of_suniv_tm_inversion : forall {Γ Sb T A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ T : Level ->
    Γ ⊩ A : Type⟨T⟩ ->
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      exists l,
        ⟦ T ⟧ ρ ↘ l /\ Dom l ≈ l ∈ per_lvl /\ glu_lvl Δ T[σ] l /\
        Δ ⊢ A[σ] : Type⟨T[σ]⟩ /\
        exists a,
          ⟦ A ⟧ ρ ↘ a /\
            Dom a ≈ a ∈ per_univ (us (dlvl_real l)) /\
            (forall P El, DG a ∈ glu_univ_elem (us (dlvl_real l)) ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
            (forall Δ' φ W, Δ' ⊢k φ : Δ -> Rtyp a in length Δ' ↘ W ->
                       Δ' ⊢ A[σ][φ]ʷ ≈ W : Type⟨T[σ][φ]ʷ⟩).
Proof.
  intros * HΓ HT HA * HΔ.
  destruct (glu_rel_exp_level_elim HΓ HT _ _ _ HΔ) as [l [Hl [Hlper Hlglu]]].
  pose proof (glu_rel_exp_suniv_tm_large HT) as HU.
  eapply glu_rel_exp_clean_inversion2 in HA; [| eassumption | eassumption ].
  destruct (HA _ _ _ HΔ) as [a0 m P El Ha0 Hm HPEl Hglu].
  inversion Ha0; subst.
  functional_eval_rewrite_clear.
  invert_glu_univ_elem HPEl.
  apply_predicate_equivalence.
  cbn [suniv_glu_exp_pred'] in Hglu.
  destruct Hglu as [HAσ [_ [Hty Hrb]]].
  destruct Hty as [Pm [Elm [HPm HP]]].
  exists l; split; [ assumption | split; [ assumption | split; [ assumption |] ] ].
  split; [ exact HAσ |].
  exists m; split; [ assumption | split; [| split ] ].
  - eapply glu_univ_elem_per_univ; eassumption.
  - intros P' El' H'.
    handle_functional_glu_univ_elem.
    assumption.
  - exact Hrb.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_level glu_rel_exp_level_small glu_rel_exp_llit
  glu_rel_exp_succl glu_rel_exp_maxl glu_rel_exp_univ_lvl : mctt.
