(** * Simulated Values in the Gluing Model

    A term glued to a value is glued to every value simulating it, and a type
    glued to a type value to every simulating one. *)

From Stdlib Require Import PeanoNat List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability Simulation Bridge BridgeGlob PERSim.
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

Section Tele.
  Context {GC : GCtx}.

  (** Glued at a telescope type to a value, glued to whatever simulates it
      applicatively. *)
  Lemma glu_tele_appsim : forall Δ A κ ρ0 t i P El Γ M T f g,
      eval_exp gc_deps gc_stack κ (ctx_pi Δ A) ρ0 t ->
      DG t ∈ glu_univ_elem i ↘ P ↘ El ->
      Γ ⊢ M : T ® f ∈ El ->
      appsim gc_deps gc_stack (List.length Δ) f g ->
      Γ ⊢ M : T ® g ∈ El.
  Proof.
    induction Δ as [| T0 Δ IH] using List.rev_ind; intros * Ht Hglu Hf Hs.
    - destruct Hs as [H1 _].
      destruct (H1 nil f eq_refl (apps_nil _ _ _)) as (v' & Hv' & Hfv).
      inversion Hv'; subst.
      eapply glu_univ_elem_trm_sim; eassumption.
    - rewrite ctx_pi_snoc in Ht; inversion Ht; subst.
      rewrite List.length_app, Nat.add_comm in Hs; cbn in Hs.
      pose proof (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
      pose proof HR as HR'.
      basic_invert_per_univ_elem HR'.
      unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in Hglu; shelve_unifiable; [ eassumption |].
      destruct Hglu as (IP & IEl & OP & OEl & erel & HIP & HOP & Hel & HP & HEl).
      apply HEl in Hf; apply HEl.
      inversion Hf as [? ? ? ? IT OT HM Hff HT HIT HOT HITP Happ]; subst.
      pose proof (per_tele_appsim (Δ ++ T0 :: nil) A κ ρ0 _ i erel f g
                    ltac:(rewrite ctx_pi_snoc; exact Ht) Hel Hff
                    ltac:(rewrite List.length_app, Nat.add_comm; exact Hs)) as Hfg.
      econstructor; eauto.
      + eapply per_elem_trans; [ exact Hel | eapply per_elem_sym; [ exact Hel | exact Hfg ] | exact Hfg ].
      + intros * Hk HN equiv_n.
        destruct (Happ _ _ _ _ Hk HN equiv_n) as (fn & Hfn & HMN).
        destruct (appsim_head _ _ _ _ _ _ _ Hs Hfn) as [gn Hgn].
        pose proof (appsim_step _ _ _ _ _ _ _ _ Hs Hfn Hgn) as Hs'.
        exists gn; split; [ exact Hgn |].
        match goal with
        | H : forall c c' (e : in_rel c c'), rel_mod_eval _ _ _ _ _ _ _ _ |- _ =>
            destruct (H _ _ equiv_n) as [b b' Hb Hb' _]
        end.
        eapply IH; [ exact Hb | eapply HOP; exact Hb | exact HMN | exact Hs' ].
  Qed.
End Tele.
