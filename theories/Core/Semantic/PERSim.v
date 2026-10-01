(** * Simulated Values in the PER Model

    [vsim]-related values are interchangeable in [per_univ_elem] and in the
    element PERs it assigns: replacing the left value of a related pair by a
    simulated one keeps it related, at the same PER. *)

From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER Simulation Bridge.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  #[local] Notation vsim := (vsim gc_deps gc_stack).
  #[local] Notation nsim := (nsim gc_deps gc_stack).

  Lemma per_bot_sim : forall m n m2, Dom m ≈ n ∈ per_bot -> nsim m m2 -> Dom m2 ≈ n ∈ per_bot.
  Proof.
    intros * H Hs; unfold per_bot in *; intros s; destruct (H s) as (L & HL & HL'); exists L; split; [ eapply sim_read_ne; [ exact HL | exact Hs ] | exact HL' ].
  Qed.

  Lemma per_nat_sim : forall m n, Dom m ≈ n ∈ per_nat -> forall m2, vsim m m2 -> Dom m2 ≈ n ∈ per_nat.
  Proof.
    induction 1; intros * Hs.
    - apply vsim_zero_inv in Hs as ->; constructor.
    - destruct (vsim_succ_inv _ _ _ _ Hs) as (m' & -> & Hm); constructor; auto.
    - destruct (vsim_neut_inv _ _ _ _ _ Hs) as (a' & m' & -> & _ & Hm).
      constructor; eapply per_bot_sim; eassumption.
  Qed.

  Theorem per_univ_elem_sim : forall i R a b,
      DF a ≈ b ∈ per_univ_elem i ↘ R ->
      (forall a2, vsim a a2 -> DF a2 ≈ b ∈ per_univ_elem i ↘ R) /\
      (forall m n m2, Dom m ≈ n ∈ R -> vsim m m2 -> Dom m2 ≈ n ∈ R).
  Proof.
    intros * H; per_univ_elem_induction H; split.
    - intros * Hs; apply vsim_univ_inv in Hs as ->; subst.
      apply per_univ_elem_core_univ'; [ assumption |].
      etransitivity; [ eassumption | reflexivity ].
    - intros * Hmn Hs; apply_relation_equivalence.
      destruct Hmn as [R' HR']; exists R'.
      match goal with IH : forall A B R, per_univ_elem _ _ _ _ -> _ |- _ =>
        destruct (IH _ _ _ HR') as [IH1 _]; exact (IH1 _ Hs) end.
    - intros * Hs; apply vsim_nat_inv in Hs as ->.
      basic_per_univ_elem_econstructor; assumption.
    - intros * Hmn Hs; apply_relation_equivalence; eapply per_nat_sim; eassumption.
    - intros * Hs.
      destruct (vsim_pi_inv _ _ _ _ _ _ _ Hs) as (a2' & κ0 & ρ0 & B0 & -> & Ha & Hcs).
      eapply per_univ_elem_pi'; [ destruct IHH as [IH1 _]; exact (IH1 _ Ha) | | eassumption ].
      intros c c' equiv_c_c'.
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ _ _ _ _ _ _ _ |- _ =>
        destruct (HT _ _ equiv_c_c') as [b b' Hb Hb' [Hbb' [IHb1 _]]] end.
      destruct (sim_eval_csim _ _ _ _ _ _ _ _ _ _ _ Hcs (vs_refl _ _ _) Hb) as (b0 & Hb0 & Hsb).
      econstructor; [ exact Hb0 | exact Hb' | exact (IHb1 _ Hsb) ].
    - intros f g f2 Hfg Hs; apply_relation_equivalence.
      intros c c' equiv_c_c'.
      specialize (Hfg _ _ equiv_c_c'); destruct Hfg as [fc gc' Hfc Hgc Hr].
      destruct (sim_eval_app _ _ _ _ _ _ _ Hfc Hs (vs_refl _ _ _)) as (fc2 & Hfc2 & Hsfc).
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ _ _ _ _ _ _ _ |- _ =>
        destruct (HT _ _ equiv_c_c') as [b b' Hb Hb' [Hbb' [_ IHb2]]] end.
      econstructor; [ exact Hfc2 | exact Hgc | exact (IHb2 _ _ _ Hr Hsfc) ].
    - intros * Hs.
      destruct (vsim_neut_inv _ _ _ _ _ Hs) as (a2' & b0 & -> & _ & Hb).
      basic_per_univ_elem_econstructor; [ eapply per_bot_sim; eassumption | assumption ].
    - intros * Hmn Hs; apply_relation_equivalence.
      destruct Hmn as [? ? ? ? Hbot].
      destruct (vsim_neut_inv _ _ _ _ _ Hs) as (a2' & m0 & -> & _ & Hm).
      constructor; eapply per_bot_sim; eassumption.
  Qed.

  Corollary per_univ_elem_sim_l : forall i R a b a2,
      DF a ≈ b ∈ per_univ_elem i ↘ R -> vsim a a2 -> DF a2 ≈ b ∈ per_univ_elem i ↘ R.
  Proof. intros * H; exact (proj1 (per_univ_elem_sim _ _ _ _ H) _). Qed.

  Corollary per_univ_elem_sim_r : forall i R a b b2,
      DF a ≈ b ∈ per_univ_elem i ↘ R -> vsim b b2 -> DF a ≈ b2 ∈ per_univ_elem i ↘ R.
  Proof.
    intros * H Hs.
    apply (proj1 (per_univ_elem_sym _ _ _ _ (per_univ_elem_sim_l _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ H)) Hs))).
  Qed.

  Corollary per_elem_sim_l : forall i R a b m n m2,
      DF a ≈ b ∈ per_univ_elem i ↘ R -> Dom m ≈ n ∈ R -> vsim m m2 -> Dom m2 ≈ n ∈ R.
  Proof. intros * H; exact (proj2 (per_univ_elem_sim _ _ _ _ H) _ _ _). Qed.

  Corollary per_elem_sim_r : forall i R a b m n n2,
      DF a ≈ b ∈ per_univ_elem i ↘ R -> Dom m ≈ n ∈ R -> vsim n n2 -> Dom m ≈ n2 ∈ R.
  Proof.
    intros * H Hmn Hs.
    eapply per_elem_sym; [ eassumption |].
    eapply per_elem_sim_l; [ eassumption | eapply per_elem_sym; eassumption | eassumption ].
  Qed.
End Fixed_GCtx.

Section Tele.
  Context {GC : GCtx}.

  (** A value related to itself at the type of a telescope is related to any
      value that it is applicatively simulated by. *)
  Lemma per_tele_appsim : forall Δ A κ ρ0 t i R f g,
      eval_exp gc_deps gc_stack κ (ctx_pi Δ A) ρ0 t ->
      DF t ≈ t ∈ per_univ_elem i ↘ R ->
      Dom f ≈ f ∈ R ->
      appsim gc_deps gc_stack (List.length Δ) f g ->
      Dom f ≈ g ∈ R.
  Proof.
    induction Δ as [| T Δ IH] using List.rev_ind; intros * Ht Hper Hff Hs.
    - cbn in Ht.
      destruct Hs as [H1 _].
      destruct (H1 nil f eq_refl (apps_nil _ _ _)) as (v' & Hv' & Hfv).
      inversion Hv'; subst.
      eapply per_elem_sim_r; eassumption.
    - rewrite ctx_pi_snoc in Ht; inversion Ht; subst.
      rewrite List.length_app, Nat.add_comm in Hs; cbn in Hs.
      basic_invert_per_univ_elem Hper.
      apply_relation_equivalence.
      intros c c' equiv_c_c'.
      assert (equiv_c'_c' : in_rel c' c') by (etransitivity; [ symmetry |]; eassumption).
      destruct (Hff _ _ equiv_c_c') as [fc fc' Hfc Hfc' Hr].
      destruct (Hff _ _ equiv_c'_c') as [fc'2 fc'3 Hfc'2 Hfc'3 Hr'].
      pose proof (functional_eval_app _ _ _ _ Hfc' Hfc'2) as <-.
      pose proof (functional_eval_app _ _ _ _ Hfc' Hfc'3) as <-.
      destruct (appsim_head _ _ _ _ _ _ _ Hs Hfc') as [gc' Hgc'].
      pose proof (appsim_step _ _ _ _ _ _ _ _ Hs Hfc' Hgc') as Hs'.
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ _ _ _ _ _ _ _ |- _ =>
        destruct (HT _ _ equiv_c_c') as [b b' Hb Hb' Hbb'];
        destruct (HT _ _ equiv_c'_c') as [b2 b3 Hb2 Hb3 Hb23] end.
      pose proof (functional_eval_exp _ _ _ _ _ Hb' Hb2) as <-.
      pose proof (functional_eval_exp _ _ _ _ _ Hb' Hb3) as <-.
      pose proof (IH _ _ _ _ _ _ _ _ Hb' Hb23 Hr' Hs') as Hfg.
      pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hbb' Hb23) as Hirr.
      econstructor; [ exact Hfc | exact Hgc' |].
      assert (Hfg' : out_rel c c' equiv_c_c' fc' gc')
        by (unfold relation_equivalence, predicate_equivalence, pointwise_lifting in Hirr; apply Hirr; exact Hfg).
      eapply per_elem_trans; [ exact Hbb' | exact Hr | exact Hfg' ].
  Qed.
End Tele.
