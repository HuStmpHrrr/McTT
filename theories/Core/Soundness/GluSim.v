(** * Simulated Values in the Gluing Model

    A term glued to a value is glued to every value simulating it, and a type
    glued to a type value to every simulating one. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability Simulation PERSim.
From Mctt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  #[local] Notation vsim := (vsim gc_deps gc_stack).

  Lemma read_ne_sim_eq : forall m m2 s L L',
      nsim gc_deps gc_stack m m2 -> Rne m in s ↘ L -> Rne m2 in s ↘ L' -> L = L'.
  Proof.
    intros * Hs HL HL'.
    pose proof (sim_read_ne _ _ _ _ _ _ HL Hs) as HL2.
    eapply functional_read_ne; eassumption.
  Qed.

  Lemma glu_nat_sim : forall Γ M m, glu_nat Γ M m -> forall m2, vsim m m2 -> glu_nat Γ M m2.
  Proof.
    induction 1; intros * Hs.
    - apply vsim_zero_inv in Hs as ->; constructor; assumption.
    - destruct (vsim_succ_inv _ _ _ _ Hs) as (m2' & -> & Hm); econstructor; eauto.
    - destruct (vsim_neut_inv _ _ _ _ _ Hs) as (a2 & m3 & -> & _ & Hm).
      constructor.
      + eapply per_bot_sim; [| exact Hm ]; eapply per_bot_sym, per_bot_sim; [ exact H | exact Hm ].
      + intros * Hk HR.
        destruct (H (length Δ)) as (L & HL & _).
        pose proof (read_ne_sim_eq _ _ _ _ _ Hm HL HR) as <-.
        eauto.
  Qed.

  Lemma glu_univ_elem_trm_sim : forall i P El a,
      DG a ∈ glu_univ_elem i ↘ P ↘ El ->
      forall Γ A M m m2,
        Γ ⊢ M : A ® m ∈ El ->
        vsim m m2 ->
        Γ ⊢ M : A ® m2 ∈ El.
  Proof.
    simpl.
    glu_univ_elem_induction1; intros;
      simpl_glu_rel.
    - (* a universe *)
      repeat eexists; try split; eauto.
      match goal with H : glu_univ_elem _ ?P' ?El' m |- _ =>
        apply (glu_univ_elem_resp_per_univ _ m m2); [| exact H ] end.
      match goal with H : glu_univ_elem _ _ _ m |- _ =>
        destruct (glu_univ_elem_per_univ _ _ _ _ H) as [R HR] end.
      exists R; eapply per_univ_elem_sim_r; eassumption.
    - (* ℕ *)
      split; [ assumption | eapply glu_nat_sim; eassumption ].
    - (* Π *)
      econstructor; eauto.
      + eapply per_elem_sim_r; [ eassumption | | eassumption ].
        eapply per_elem_sim_l; eassumption.
      + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        intros.
        destruct_rel_mod_eval.
        match goal with
        | H : forall Δ φ N n, _ -> _ -> forall equiv_n, exists mn, _ /\ _ |- _ =>
            destruct (H _ _ _ _ ltac:(eassumption) ltac:(eassumption) equiv_n) as (mn & Hmn & Hglu)
        end.
        destruct (sim_eval_app _ _ _ _ _ _ _ Hmn ltac:(eassumption) (vs_refl _ _ _)) as (mn2 & Hmn2 & Hs).
        eexists; split; [ exact Hmn2 |].
        match goal with
        | IH : forall c equiv_c b, ⟦ _ ⟧ _ ⍮ _ ↘ b -> forall Γ A M m m2, _ -> _ -> _,
          Hb : ⟦ _ ⟧ _ ⍮ _ ↦ n ↘ ?b |- _ => eapply (IH _ equiv_n _ Hb); eassumption
        end.
    - (* a neutral type *)
      match goal with Hv : vsim (⇑ _ _) _ |- _ => destruct (vsim_neut_inv _ _ _ _ _ Hv) as (a2 & m2' & -> & _ & Hm) end.
      econstructor.
      + split; assumption.
      + assumption.
      + eapply per_bot_sim; [| exact Hm ]; eapply per_bot_sym, per_bot_sim; [ eassumption | exact Hm ].
      + intros * Hk HR.
        match goal with H : per_bot ?m ?m |- _ => destruct (H (length Δ)) as (L & HL & _) end.
        pose proof (read_ne_sim_eq _ _ _ _ _ Hm HL HR) as <-.
        eauto.
  Qed.

  Corollary glu_univ_elem_typ_sim : forall i P El a a2,
      DG a ∈ glu_univ_elem i ↘ P ↘ El -> vsim a a2 -> DG a2 ∈ glu_univ_elem i ↘ P ↘ El.
  Proof.
    intros * H Hs.
    apply (glu_univ_elem_resp_per_univ _ a a2); [| exact H ].
    destruct (glu_univ_elem_per_univ _ _ _ _ H) as [R HR].
    exists R; eapply per_univ_elem_sim_r; eassumption.
  Qed.
End Fixed_GCtx.
