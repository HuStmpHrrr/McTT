(** * Levels in the Gluing Model

    Substitution into every level form is definitional, so the congruence steps
    are reflexivity.  A level is glued to a value by its readback ([glu_lvl]),
    and the readback of a level operation is the canonical form of that
    operation on the canonical forms of its arguments
    ([Core.Semantic.Levels]).  So each case is: read the atoms of the arguments,
    and then rewrite the syntax by the level equations until it is the canonical
    form — which is [Core.Syntactic.LevelEq]. *)

From Stdlib Require Import PeanoNat.
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

(** The sort of the levels is a parameter of the file: the elements of
    [Level@n] are the level values, whatever the sort, so each case is proved
    once for every sort. *)
  Context {n : nat}.

(** [Level@n] is a type at every index: the rule gives it the small universe
    [Type@0], and the other forms are instances. *)
Lemma glu_rel_exp_level_univ : forall {Γ} {u : uidx},
    ⊩ Γ ->
    Γ ⊩ Level@n : ulvl_tm u.
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
    Γ ⊩ Level@n : Typeω@i.
Proof. intros; apply (glu_rel_exp_level_univ (u := ul i)); assumption. Qed.

Lemma glu_rel_exp_level_small : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ Level@n : Type@0.
Proof. intros; apply (glu_rel_exp_level_univ (u := us oz)); assumption. Qed.

Hint Resolve glu_rel_exp_level : mctt.

(** ** Terms of Type [Level@n] *)
Lemma glu_rel_exp_of_level : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ,
        Δ ⊢s σ ® ρ ∈ Sb ->
        exists m, ⟦ M ⟧ ρ ↘ m /\ Dom m ≈ m ∈ per_lvl_at n /\ glu_lvl n Δ M[σ] m) ->
    Γ ⊩ M : Level@n.
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
  - simpl; split; [| split ]; [ mauto 3 | assumption | assumption ].
Qed.

Lemma glu_rel_exp_clean_inversion_level : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : Level@n ->
    glu_rel_exp_clean_inversion2_result 0 Sb M Level@n.
Proof.
  intros * ? HM.
  assert (Γ ⊩ Level@n : Typeω@0) by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

(** The glued level of a term of type [Level@n]: its value, the canonical form
    the value reads back as, and the equation between the two. *)
Lemma glu_rel_exp_level_elim : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : Level@n ->
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      exists m, ⟦ M ⟧ ρ ↘ m /\ Dom m ≈ m ∈ per_lvl_at n /\ glu_lvl n Δ M[σ] m.
Proof.
  intros * HSb HM * Hσ.
  eapply glu_rel_exp_clean_inversion_level in HM; [| exact HSb ].
  specialize (HM _ _ _ Hσ).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  simpl in *; destruct_conjs.
  eexists; split; [| split ]; eassumption.
Qed.

(** ** The Level Forms

    A literal evaluates to a flat level with no atom, whose readback is the
    literal itself. *)
Lemma glu_rel_exp_llit : forall {Γ o},
    fst o <= n ->
    ⊩ Γ ->
    Γ ⊩ 𝕃ᵒ o : Level@n.
Proof.
  intros * Ho [Sb].
  assert (⊢ Γ) by mauto 2.
  eapply glu_rel_exp_of_level; [ eassumption |].
  intros Δ σ ρ Hσ.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  exists (dlvl_lit o); split; [ mauto 3 | split; [ apply per_lvl_at_lit; exact Ho |] ].
  simplify_subs; apply glu_lvl_lit; assumption.
Qed.

Hint Resolve glu_rel_exp_llit : mctt.

(** The readback of a level is its canonical form, and the canonical form of a
    level operation is the operation on the canonical forms, which the
    equations of [LevelEq] identify with the syntax.  The readbacks of the
    arguments are canonical levels of sort [n] (the second half of
    [glu_lvl]), so the canonical form of the operation is too. *)
Lemma glu_rel_exp_succl : forall {Γ M},
    Γ ⊩ M : Level@n ->
    Γ ⊩ succl M : Level@n.
Proof.
  intros * HM.
  assert (⊩ Γ) as [Sb] by mauto 3.
  eapply glu_rel_exp_of_level; [ eassumption |].
  intros Δ σ ρ Hσ.
  destruct (glu_rel_exp_level_elim ltac:(eassumption) HM _ _ _ Hσ) as [m [Hev [Hper Hglu]]].
  pose proof (per_lvl_at_lvl _ _ _ Hper) as Hperl.
  exists (dlvl_suc m); split; [ mauto 3 | split; [ apply per_lvl_at_suc; exact Hper |] ].
  intros Δ' φ L Hφ Hr.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  apply dlvl_canon_of_read in Hr as [_ [L' [-> Hc]]].
  destruct (per_lvl_ex _ _ Hperl (length Δ')) as [A HA].
  assert (L' = lvl_canon (lvl_suc A)) as ->
    by (eapply dlvl_canon_functional; [ exact Hc | apply dlvl_canon_suc; exact HA ]).
  assert (Hsh : dlvl_shape m) by (destruct (per_lvl_shape _ _ Hperl); assumption).
  assert (HrA : Rnf ⇓ Levelᵈ m in length Δ' ↘ nf_lvl_of A) by (apply dlvl_canon_read; [ exact Hsh | exact HA ]).
  destruct (Hglu _ _ _ Hφ HrA) as [HMA HwsA].
  destruct A as [c xs]; cbn in HwsA; destruct HwsA as [Hc0 Hws].
  pose proof (la_ws_wf _ Hws) as Hwf.
  assert (Hcs : fst (osuc c) <= n) by (rewrite osuc_fst; exact Hc0).
  assert (Hws' : @la_ws gc_deps gc_stack n Δ' (la_suc xs)) by (apply la_ws_suc; exact Hws).
  assert (Hcc : fst (fst (lvl_canon (lvl_suc (c, xs)))) <= n)
    by (eapply Nat.le_trans; [ apply lvl_canon_cst_le | exact Hcs ]).
  assert (Hwsc : @la_ws gc_deps gc_stack n Δ' (snd (lvl_canon (lvl_suc (c, xs)))))
    by (unfold lvl_canon, lvl_suc; cbn; apply la_ws_keep, la_ws_sort; exact Hws').
  split.
  - (** The syntax is the canonical form of the argument; the successor of
        that is, by the level equations, the canonical form of the
        successor. *)
    simplify_subs; cbn [exp_wk].
    transitivity (succl (nf_lvl_of (c, xs))); [ mauto 3 |].
    unfold nf_lvl_of; cbn [fst snd].
    transitivity (succl (lvl_tm c xs));
      [ apply wf_exp_eq_succl_cong, lvl_exp_of_tm; [ exact Hc0 | assumption | exact Hwf ] |].
    transitivity (lvl_tm (fst (lvl_suc (c, xs))) (snd (lvl_suc (c, xs))));
      [ apply lvl_tm_suc; [ exact Hc0 | assumption | exact Hwf ] |].
    transitivity (lvl_tm (fst (lvl_canon (lvl_suc (c, xs)))) (snd (lvl_canon (lvl_suc (c, xs)))));
      [ apply lvl_tm_canon; [ exact Hcs | assumption | exact Hws' ] |].
    apply wf_exp_eq_sym, lvl_exp_of_tm; [ exact Hcc | assumption | apply la_ws_wf; exact Hwsc ].
  - unfold nf_lvl_of; cbn; split; assumption.
Qed.

Hint Resolve glu_rel_exp_succl : mctt.

Lemma glu_rel_exp_maxl : forall {Γ M N},
    Γ ⊩ M : Level@n ->
    Γ ⊩ N : Level@n ->
    Γ ⊩ maxl M N : Level@n.
Proof.
  intros * HM HN.
  assert (⊩ Γ) as [Sb] by mauto 3.
  eapply glu_rel_exp_of_level; [ eassumption |].
  intros Δ σ ρ Hσ.
  destruct (glu_rel_exp_level_elim ltac:(eassumption) HM _ _ _ Hσ) as [m [Hev [Hper Hglu]]].
  destruct (glu_rel_exp_level_elim ltac:(eassumption) HN _ _ _ Hσ) as [m' [Hev' [Hper' Hglu']]].
  pose proof (per_lvl_at_lvl _ _ _ Hper) as Hperl.
  pose proof (per_lvl_at_lvl _ _ _ Hper') as Hperl'.
  exists (dlvl_max m m'); split; [ mauto 3 | split; [ apply per_lvl_at_max; eassumption |] ].
  intros Δ' φ L Hφ Hr.
  assert (⊢ Δ') by (eapply kripke_dom; eassumption).
  apply dlvl_canon_of_read in Hr as [_ [L' [-> Hc]]].
  destruct (per_lvl_ex _ _ Hperl (length Δ')) as [A HA].
  destruct (per_lvl_ex _ _ Hperl' (length Δ')) as [B HB].
  assert (L' = lvl_canon (lvl_max A B)) as ->
    by (eapply dlvl_canon_functional; [ exact Hc | apply dlvl_canon_max; eassumption ]).
  assert (Hsh : dlvl_shape m) by (destruct (per_lvl_shape _ _ Hperl); assumption).
  assert (Hsh' : dlvl_shape m') by (destruct (per_lvl_shape _ _ Hperl'); assumption).
  assert (HrA : Rnf ⇓ Levelᵈ m in length Δ' ↘ nf_lvl_of A) by (apply dlvl_canon_read; [ exact Hsh | exact HA ]).
  assert (HrB : Rnf ⇓ Levelᵈ m' in length Δ' ↘ nf_lvl_of B) by (apply dlvl_canon_read; [ exact Hsh' | exact HB ]).
  destruct (Hglu _ _ _ Hφ HrA) as [HMA HwsA].
  destruct (Hglu' _ _ _ Hφ HrB) as [HNB HwsB].
  destruct A as [c xs]; destruct B as [d ys].
  cbn in HwsA, HwsB; destruct HwsA as [Hc0 Hwsx]; destruct HwsB as [Hd0 Hwsy].
  pose proof (la_ws_wf _ Hwsx) as Hwfx; pose proof (la_ws_wf _ Hwsy) as Hwfy.
  assert (Hcd : fst (omax c d) <= n) by (apply omax_fst_le; assumption).
  assert (Hwsa : @la_ws gc_deps gc_stack n Δ' (la_app xs ys)) by (apply la_ws_app; [ exact Hwsx | exact Hwsy ]).
  assert (Hcc : fst (fst (lvl_canon (lvl_max (c, xs) (d, ys)))) <= n)
    by (eapply Nat.le_trans; [ apply lvl_canon_cst_le | exact Hcd ]).
  assert (Hwsm : @la_ws gc_deps gc_stack n Δ' (snd (lvl_canon (lvl_max (c, xs) (d, ys)))))
    by (unfold lvl_canon, lvl_max; cbn; apply la_ws_keep, la_ws_sort; exact Hwsa).
  split.
  - simplify_subs; cbn [exp_wk].
    transitivity (maxl (nf_lvl_of (c, xs)) (nf_lvl_of (d, ys))); [ mauto 3 |].
    unfold nf_lvl_of; cbn [fst snd].
    transitivity (maxl (lvl_tm c xs) (lvl_tm d ys));
      [ apply wf_exp_eq_maxl_cong; apply lvl_exp_of_tm;
        [ exact Hc0 | assumption | exact Hwfx | exact Hd0 | assumption | exact Hwfy ] |].
    transitivity (lvl_tm (fst (lvl_max (c, xs) (d, ys))) (snd (lvl_max (c, xs) (d, ys))));
      [ apply lvl_tm_max; [ exact Hc0 | exact Hd0 | assumption | exact Hwfx | exact Hwfy ] |].
    transitivity (lvl_tm (fst (lvl_canon (lvl_max (c, xs) (d, ys))))
                         (snd (lvl_canon (lvl_max (c, xs) (d, ys)))));
      [ apply lvl_tm_canon; [ exact Hcd | assumption | exact Hwsa ] |].
    apply wf_exp_eq_sym, lvl_exp_of_tm; [ exact Hcc | assumption | apply la_ws_wf; exact Hwsm ].
  - unfold nf_lvl_of; cbn; split; assumption.
Qed.

Hint Resolve glu_rel_exp_maxl : mctt.

(** ** The Small Universe at a Level@n Term

    [Type⟨M⟩] is an element of [Type⟨succl M⟩], glued at the large index [0].
    Its type-level gluing takes the level term [succl M], and its element
    gluing the level term [M], both glued to their values by the level case
    above; its readback is the universe at the readback of [M], which the
    congruence rule of universes equates with it. *)
Lemma glu_rel_exp_univ_lvl : forall {Γ M},
    Γ ⊩ M : Level@n ->
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
  destruct (glu_rel_exp_level_elim HSb HM _ _ _ Hσ) as [m [Hev [Hper0 Hglu]]].
  destruct (glu_rel_exp_level_elim HSb HSM _ _ _ Hσ) as [m' [Hev' [Hper0' Hglu']]].
  pose proof (per_lvl_at_lvl _ _ _ Hper0) as Hper; pose proof (per_lvl_at_lvl _ _ _ Hper0') as Hper'.
  inversion Hev'; subst; functional_eval_rewrite_clear.
  assert (Δ ⊢ M[σ] : Level@n) by (eapply (glu_lvl_escape _ _ _ _ Hper Hglu); assumption).
  econstructor;
    [ apply eval_exp_univ; eassumption
    | apply eval_exp_univ; eassumption
    | apply glu_univ_elem_core_suniv'; [ exact Hper' | exact I | reflexivity | reflexivity ]
    |].
  simplify_subs; cbn [exp_sub] in *.
  repeat split.
  - eapply wf_univ; eassumption.
  - exists (succl M[σ]), n; split; [ exact Hglu' |].
    eapply wf_exp_eq_univ_cong_large_tm; [ assumption | mauto 3 | mauto 3 ].
  - rewrite dlvl_real_suc.
    do 2 eexists; split;
      [ apply glu_univ_elem_core_suniv'; [ exact Hper | cbn; ord | reflexivity | reflexivity ] |].
    exists M[σ], n; split; [ exact Hglu |].
    eapply wf_exp_eq_univ_cong_large_tm; [ assumption | eassumption | mauto 3 ].
  - intros Δ' φ W Hφ Hr.
    assert (⊢ Δ') by (eapply kripke_dom; eassumption).
    inversion Hr; subst.
    assert (Δ' ⊢ M[σ][φ]ʷ ≈ nf_lvl_of L : Level@n) by (eapply glu_lvl_readback; eassumption).
    cbn [exp_wk nf_to_exp nf_univ_of].
    eapply wf_exp_eq_univ_cong; eassumption.
Qed.

Hint Resolve glu_rel_exp_univ_lvl : mctt.

(** ** Types of the Small Universe at a Level Term

    [Type⟨T⟩] is in the least large universe, which is the ambient universe
    its types are glued at; inverting that gluing gives the type-level gluing
    at the realiser of [T]'s value, and the readback clause at [Type⟨T⟩]. *)
Lemma glu_rel_exp_suniv_tm_large : forall {Γ T},
    Γ ⊩ T : Level@n ->
    Γ ⊩ Type⟨T⟩ : Typeω@0.
Proof.
  intros * HT.
  assert (⊩ Γ) by mauto 3.
  assert (Γ ⊢ T : Level@n) by (eapply glu_rel_exp_to_wf_exp; exact HT).
  assert (⊢ Γ) by mauto 3.
  eapply glu_rel_exp_subtyp;
    [ apply glu_rel_exp_univ_lvl, HT | apply glu_rel_exp_typ; assumption
    | eapply wf_subtyp_small_large; mauto 3 ].
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
    Γ ⊩ T : Level@n ->
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
  destruct (glu_rel_exp_level_elim HΓ HT _ _ _ Hσ) as [l [Hl [Hper0 Hglu]]].
  pose proof (per_lvl_at_lvl _ _ _ Hper0) as Hper.
  destruct (Hbody _ _ _ Hσ l Hl) as [HAσ [a [Ha [Haper [HaP Hrb]]]]].
  assert (Δ ⊢ T[σ] : Level@n) by (eapply (glu_lvl_escape _ _ _ _ Hper Hglu); assumption).
  assert (exists P El, DG a ∈ glu_univ_elem (us (dlvl_real l)) ↘ P ↘ El) as [P [El HPEl]] by mauto 3.
  econstructor;
    [ apply eval_exp_univ; eassumption
    | eassumption
    | apply glu_univ_elem_core_suniv'; [ exact Hper | exact I | reflexivity | reflexivity ]
    |].
  cbn [exp_sub suniv_glu_exp_pred'].
  repeat split.
  - exact HAσ.
  - exists T[σ], n; split; [ exact Hglu |].
    eapply wf_exp_eq_univ_cong_large_tm; [ assumption | eassumption | mauto 3 ].
  - exists P, El; split; [ exact HPEl | exact (HaP _ _ HPEl) ].
  - exact Hrb.
Qed.

Lemma glu_rel_exp_of_suniv_tm_inversion : forall {Γ Sb T A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ T : Level@n ->
    Γ ⊩ A : Type⟨T⟩ ->
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      exists l,
        ⟦ T ⟧ ρ ↘ l /\ Dom l ≈ l ∈ per_lvl /\ glu_lvl n Δ T[σ] l /\
        Δ ⊢ A[σ] : Type⟨T[σ]⟩ /\
        exists a,
          ⟦ A ⟧ ρ ↘ a /\
            Dom a ≈ a ∈ per_univ (us (dlvl_real l)) /\
            (forall P El, DG a ∈ glu_univ_elem (us (dlvl_real l)) ↘ P ↘ El -> Δ ⊢ A[σ] ® P) /\
            (forall Δ' φ W, Δ' ⊢k φ : Δ -> Rtyp a in length Δ' ↘ W ->
                       Δ' ⊢ A[σ][φ]ʷ ≈ W : Type⟨T[σ][φ]ʷ⟩).
Proof.
  intros * HΓ HT HA * HΔ.
  destruct (glu_rel_exp_level_elim HΓ HT _ _ _ HΔ) as [l [Hl [Hlper0 Hlglu]]].
  pose proof (per_lvl_at_lvl _ _ _ Hlper0) as Hlper.
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
