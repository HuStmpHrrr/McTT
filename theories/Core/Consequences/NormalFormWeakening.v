(** * NbE Commutes with Weakening

    The semantic route to "the normal form of a weakened term is the
    weakened normal form" ([nbe_wk]):

    - [M] is a term of [Γ], so the fundamental theorem of the PER model,
      along the semantic weakening [Γ ▹{κ} A ⊨ʷ ↑ : Γ], relates the value of
      [M[↑]] at the initial environment of [Γ ▹{κ} A] to the value of [M] at its
      tail, the initial environment of [Γ];
    - related values read back equally at every length ([per_top]), so the
      normal form of [M[↑]] in [Γ ▹{κ} A] is the readback of [⟦M⟧ρΓ] at
      [|Γ| + 1];
    - that is, up to erasure, the weakening of its readback at [|Γ|], the
      normal form of [M] in [Γ] ([Core.Semantic.Rename.read_shift]): a
      proof is read back over the environment it is kept over, which the
      weakening extends.

    Two consequences follow: the normal form of a weakened term is fresh at
    the new variable ([nbe_wk_fresh_sem], an alternative proof of
    [Core.Semantic.Avoid.nbe_wk_fresh] for well-typed terms), and an equation
    between two terms of [Γ] that holds in [Γ ▹{κ} A] holds in [Γ]
    ([exp_eq_strengthen_sem], the case [Δ = nil] of
    [Algorithmic.Strengthening.exp_eq_strengthen]). *)
From Stdlib Require Import Arith Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Completeness Soundness.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Semantic Require Import Realizability Rename Avoid.
From Mctt.Core.Syntactic Require Import Fresh NfRename.
Import Domain_Notations Fixed_Notations Wk_Notations.

Section Fixed_GCtx.
Context {GC : GCtx}.

(** ** NbE Commutes with Weakening

    Up to erasure: a proof of [Γ] is kept over the initial environment of
    [Γ], and its weakening over that of [Γ ▹{κ} A], whose readback binds one
    more position.  For [Γ = (P : Prop) ▹ (h : P)], [A = ⊤] and [M = #0],
    the normal form of [M] in [Γ] is [ℓ h : P ≔ #0 in #0], and that of
    [M[↑]] in [Γ ▹{κ} A] lets-binds both [h] and the new variable, so it is no
    weakening of the first; erased, both are [⋆ⁿ]. *)
Theorem nbe_wk : forall Γ κ A M T W,
    ⊢ Γ ▹{κ} A ->
    Γ ⊢ M : T ->
    nbe_f Γ M T W ->
    exists W', nbe_f (Γ ▹{κ} A) M[↑]ʷ T[↑]ʷ W' /\ nf_erase W' = nf_erase (nf_wk ↑ W).
Proof.
  intros * HΓA HM Hn.
  assert (HA : ⊨ Γ ▹{κ} A) by (apply completeness_fundamental_ctx; exact HΓA).
  assert (exists R1, EF (Γ ▹{κ} A) ≈ (Γ ▹{κ} A) ∈ per_ctx_env ↘ R1) as [R1 HR1]
      by mauto 3 using rel_ctx_wf_per_ctx_env.
  pose proof (wf_ctx_scoped _ _ _ HΓA) as Hs1.
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ HM) as (_ & HsM & _).
  apply completeness_fundamental_exp in HM as [R0 HR0 j HMg].
  (** The initial environment of [Γ ▹{κ} A], related to itself, and its tail,
      that of [Γ]. *)
  destruct (per_ctx_then_per_env_initial_env HR1 Hs1 Hs1) as (ρ1 & ρ1' & Hρ1 & Hρ1' & Hrel1).
  assert (ρ1' = ρ1) as -> by (eapply functional_initial_env; eassumption).
  pose proof Hs1 as Hs0; cbn [ctx_scoped] in Hs0; destruct Hs0 as [_ Hs0].
  inversion Hρ1 as [| ? ρ0 ? a Hρ0 Ha0 | | | |]; subst.
  destruct (per_ctx_then_per_env_initial_env HR0 Hs0 Hs0) as (ρ0' & ρ0'' & Hρ0' & Hρ0'' & Hrel0).
  assert (ρ0' = ρ0) as -> by (eapply functional_initial_env; eassumption).
  assert (ρ0'' = ρ0) as -> by (eapply functional_initial_env; eassumption).
  destruct Hn as [ρ' aT Hρ' HaT Hres].
  assert (ρ' = ρ0) as -> by (eapply functional_initial_env; eassumption).
  (** [M] along the shift from [Γ ▹{κ} A] and along the identity of [Γ]: both
      reach the tail retagged ([eval_sub_shift], [eval_sub_id]). *)
  pose proof (rel_sub_shift HA) as HWk.
  destruct (eval_sub_shift_rel HR1 Hrel1) as [HevW _].
  destruct (HMg _ _ HR1 _ _ HWk _ _ _ _ Hrel1 HevW HevW) as [Rb [HtB HeB]].
  pose proof (rel_sub_id (ex_intro _ R0 HR0)) as HId.
  destruct (eval_sub_id_rel HR0 Hrel0) as [HevI _].
  destruct (HMg _ _ HR0 _ _ HId _ _ _ _ Hrel0 HevI HevI) as [Ra [HtA HeA]].
  destruct HtB as [aσ aR aR' aσ' HaσE HaRE HaR'E Haσ'E HchB].
  destruct HtA as [aI aR2 aR2' aI' HaIE HaR2E HaR2'E HaI'E HchA].
  rewrite exp_sub_id in HaIE, HaI'E.
  rewrite exp_sub_of_shift in HaσE, Haσ'E.
  change (ctx_retag Γ (ρ0 ↦ ⇑! a (length Γ) ⦂ entry_type_value a) ↯) with (ctx_retag Γ ρ0) in *.
  functional_eval_rewrite_clear.
  (** The weakened type and the type are related through the retagged
      tail: one element relation, [Rb]. *)
  assert (HRσR : DF aσ ≈ aR ∈ per_univ_elem j ↘ Rb) by pairwise.
  assert (HRTR : DF aT ≈ aR ∈ per_univ_elem j ↘ Ra) by pairwise.
  destruct (per_univ_elem_sym _ _ _ _ HRσR) as [HRRσ HRbsym].
  destruct (per_univ_elem_sym _ _ _ _ HRTR) as [HRRT HRasym].
  assert (Eab : Rb <~> Ra) by (eapply per_univ_elem_right_irrel; eassumption).
  assert (HRRT' : per_univ_elem j Rb aR aT) by (rewrite Eab; exact HRRT).
  pose proof (proj1 (per_univ_elem_trans _ _ _ _ HRσR) _ _ HRRT') as HRσT.
  pose proof (per_univ_elem_kind _ _ _ _ HRσT) as Erel.
  destruct Hres as [W0 Hp HW0 | m0 W0 Hr Hm0 HW0].
  - (** A proof: both read back as proof terms, erased alike *)
    assert (HsM1 : exp_scoped (length (Γ ▹{κ} A)) M[↑]ʷ) by (eapply exp_scoped_wk; [ exact HsM | intros; cbn; lia ]).
    destruct (per_ctx_env_kept_proof_readable _ _ _ M[↑]ʷ HR1 (exp_scoped_free_bound _ _ HsM1) _ _ Hrel1) as [HP _].
    destruct (HP (length (Γ ▹{κ} A))) as [P HPr].
    exists (nf_proof P); split.
    + econstructor; [ exact Hρ1 | exact HaσE | apply nbe_term_proof; [ congruence | apply read_nf_proof; [ congruence | exact HPr ] ] ].
    + destruct (read_nf_propositional _ _ _ _ Hp HW0) as [P0 ->]; reflexivity.
  - (** A type of an evaluated kind: the value of [M[↑]] is related to
        that of [M], so they read back alike one variable further out,
        where the value of [M] reads back as the weakening of [W]
        ([read_shift]) *)
    destruct HeB as [(a1 & Ea1 & Hp1) | HeB].
    { exfalso; rewrite exp_sub_of_shift in Ea1; functional_eval_rewrite_clear.
      assert (Hk : domain_kind aT = ak_propositional) by congruence; rewrite Hk in Hr; inversion Hr. }
    destruct HeA as [(a2 & Ea2 & Hp2) | HeA].
    { exfalso; rewrite exp_sub_id in Ea2; functional_eval_rewrite_clear.
      assert (Hk : domain_kind aT = ak_propositional) by congruence; rewrite Hk in Hr; inversion Hr. }
    destruct HeB as [mσ m1 m1' mσ' Hmσ Hm1 Hm1' Hmσ' HcB].
    destruct HeA as [mI m2 m2' mI' HmI Hm2 Hm2' HmI' HcA].
    rewrite exp_sub_of_shift in Hmσ, Hmσ'; rewrite exp_sub_id in HmI, HmI'.
    functional_eval_rewrite_clear.
    assert (H1 : Rb mσ m1) by pairwise.
    assert (H2 : Ra m0 m1) by pairwise.
    assert (H3 : Rb mσ m0)
      by (apply (proj2 (per_univ_elem_trans _ _ _ _ HRσR)) with (m2 := m1); [ exact H1 | apply HRbsym; apply Eab; exact H2 ]).
    destruct (per_elem_then_per_top HRσT H3 (S (length Γ))) as [W1 W2 HW1 HW2 HE].
    pose proof (read_shift _ _ Γ ρ0 T M aT m0 W0 W2 Hρ' HaT Hm0 HW0 HW2) as Hs.
    exists W1; split.
    + eapply nbe_evaluated_intro; [ exact Hρ1 | exact HaσE | exact Hmσ | exact HW1 | rewrite Erel; exact Hr ].
    + congruence.
Qed.

Corollary nbe_ty_wk : forall Γ κ A T i W,
    ⊢ Γ ▹{κ} A ->
    Γ ⊢ T : Typeω@i ->
    nbe_ty_f Γ T W ->
    exists W', nbe_ty_f (Γ ▹{κ} A) T[↑]ʷ W' /\ nf_erase W' = nf_erase (nf_wk ↑ W).
Proof.
  intros * HΓA HT Hn.
  destruct (nbe_wk _ _ _ _ _ _ HΓA HT (nbe_ty_to_nbe_type _ _ i _ Hn)) as (W' & HW' & E).
  exists W'; split; [ exact (nbe_type_to_nbe_ty _ _ _ _ HW') | exact E ].
Qed.

(** ** NbE Invents No Variables, Semantically

    Outside its proofs, which name the positions of the environment they
    are kept over ([nbe_wk]).  The invariant of avoided variables
    ([Core.Semantic.Avoid.nbe_wk_fresh]) gives it with no typing. *)
Corollary nbe_wk_fresh_sem : forall Γ κ A M T W,
    ⊢ Γ ▹{κ} A ->
    Γ ⊢ M : T ->
    nbe_f (Γ ▹{κ} A) M[↑]ʷ T[↑]ʷ W ->
    nf_fresh 0 (nf_erase W).
Proof. intros * _ _ Hn; exact (nbe_wk_fresh _ _ _ _ _ _ _ _ Hn). Qed.

Corollary nbe_ty_wk_fresh_sem : forall Γ κ A T i W,
    ⊢ Γ ▹{κ} A ->
    Γ ⊢ T : Typeω@i ->
    nbe_ty_f (Γ ▹{κ} A) T[↑]ʷ W ->
    nf_fresh 0 (nf_erase W).
Proof. intros * _ _ Hn; exact (nbe_ty_wk_fresh _ _ _ _ _ _ _ Hn). Qed.

(** ** Strengthening an Equation

    Both ends are terms of [Γ]: their normal forms in [Γ ▹{κ} A] are, erased,
    the weakenings of their erased normal forms in [Γ], the long equation
    makes the former equal up to erasure, and the weakening is injective;
    terms of [Γ] with normal forms equal up to erasure are equal. *)
Theorem exp_eq_strengthen_sem : forall Γ κ A M N T,
    ⊢ Γ ▹{κ} A ->
    Γ ⊢ M : T ->
    Γ ⊢ N : T ->
    Γ ▹{κ} A ⊢ M[↑]ʷ ≈ N[↑]ʷ : T[↑]ʷ ->
    Γ ⊢ M ≈ N : T.
Proof.
  intros * HΓA HM HN HMN.
  destruct (normalization HM) as [WM HnM].
  destruct (normalization HN) as [WN HnN].
  destruct (completeness HMN) as (W & W' & HnM' & HnN' & HE).
  destruct (nbe_wk _ _ _ _ _ _ HΓA HM HnM) as (WM' & HnM'' & EM).
  destruct (nbe_wk _ _ _ _ _ _ HΓA HN HnN) as (WN' & HnN'' & EN).
  functional_nbe_rewrite_clear.
  assert (Eerase : nf_erase WM = nf_erase WN)
    by (rewrite !nf_erase_wk in EM, EN; eapply (proj1 nf_wk_inj); [ apply wk_left_inverse_shift | congruence ]).
  exact (soundness_erased HM HN HnM HnN Eerase).
Qed.

End Fixed_GCtx.
