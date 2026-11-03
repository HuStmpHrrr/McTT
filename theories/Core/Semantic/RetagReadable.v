(** * Context PERs Relate Retagged Environments

    The identity, and every substitution of variables, evaluates an
    environment to its retagging at the target context ([ctx_retag],
    [eval_sub_id]): each entry is stored at the context's type, as a
    closure over the retagged entries before it, and at the context's
    unit.  The retagged heads read back: their values are elements of the
    context's types, evaluated at the retagged tails, which the context
    PER relates to the original ones ([per_ctx_env_retag_readable]).  So
    a context PER relates the retagged environments as it relates the
    environments ([per_ctx_env_retag]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** A head retagged at a type closure reads back when its value is an
      element of the type the closure evaluates to; a module head reads
      back whatever its type, by its unit, whose free indices stay below
      [n]. *)
  Lemma retag_head_readable : forall {i A ρA a a' R} (n : nat) (U : gunit) (ρ : env) w,
      ⟦ A ⟧ ρA ↘ a -> DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom (ρ 0) ≈ w ∈ R ->
      (forall h U0, env_entry ρ 0 = de_mod h U0 -> gunit_free_bound U <= n) ->
      head_readable n (retag_entry (entry_type_closure A ρA) U (env_entry ρ 0)).
  Proof.
    intros * Ea HR Hv HU; unfold env_var in Hv.
    destruct (env_entry ρ 0) as [v t0 | h U0 | v t0 h U0] eqn:E; cbn [retag_entry]; split; cbn [entry_unit_bound]; try lia.
    - intros s; destruct (per_univ_then_per_top_typ HR s) as [T T' HT HT' _];
        destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _].
      eexists; eapply read_entry_term; solve [ eapply eval_entry_type_closure; eassumption | eassumption ].
    - apply mod_entry_readable.
    - exact (HU _ _ eq_refl).
    - intros s; destruct (per_univ_then_per_top_typ HR s) as [T T' HT HT' _];
        destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _].
      eexists; eapply read_entry_dm; solve [ eapply eval_entry_type_closure; eassumption | eassumption ].
  Qed.

  Lemma env_entry_head : forall ρ, List.hd absent_entry ρ = env_entry ρ 0.
  Proof. intros [| d ρ]; reflexivity. Qed.

  (** An environment agrees with its first [n] entries. *)
  Lemma env_agree_upto_env_upto : forall n ρ, env_agree_upto n ρ (env_upto n ρ).
  Proof. intros * x Hx; rewrite env_entry_env_upto by exact Hx; reflexivity. Qed.

  (** The environments of a context PER, retagged at the context, read
      back at every head. *)
  Lemma per_ctx_env_retag_readable : forall {Γ Δ R},
      EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
      forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> env_heads_readable Γ (ctx_retag Γ ρ).
  Proof.
    induction 1; intros ρ ρ' Hρ; apply_relation_equivalence.
    1: { intros x e Hx; destruct x; discriminate. }
    (* every case: the tail retagged reads back and is related to the
       other tail; its first entries are related to it too *)
    all: destruct Hρ as [Ht ?]; pose proof (IHper_ctx_env _ _ Ht) as Hr1.
    all: assert (Hl1 : Dom ctx_retag Γ ρ↯ ≈ ρ'↯ ∈ tail_rel)
           by exact (per_ctx_env_resp_retagged_left equiv_Γ_Γ' _ _ _ (env_agree_retagged_ctx_retag _ _ _) Hr1 Ht).
    all: assert (Hu1 : Dom env_upto (List.length Γ) (ctx_retag Γ ρ↯) ≈ ρ'↯ ∈ tail_rel)
           by exact (per_ctx_env_resp_agree equiv_Γ_Γ' _ _ _ _ (env_agree_upto_env_upto _ _) (reflexivity _) Hl1).
    all: intros [| x] e0 Hx; cbn [List.nth_error] in Hx;
      [ injection Hx as <- | cbn [ctx_retag skipn]; rewrite <- (env_entry_drop (_ :: _) x); exact (Hr1 x e0 Hx) ].
    all: cbn [ctx_retag skipn List.length centry_unit_room centry_tag centry_type centry_slot_unit centry_unit].
    all: change (env_entry (?d :: ?ρ0) 0) with d; rewrite env_entry_head.
    (* a slot: a module head, by its kind, stored at its unit, scoped by
       its tail *)
    3: { destruct per_ctx_env_mod_rel_left_kind as (U0 & Ek).
         rewrite Ek; cbn [retag_entry]; split; [ apply mod_entry_readable | cbn [entry_unit_bound]; assumption ]. }
    (* a type: the head is an element of the type at the retagged tail *)
    all: destruct (H0 _ _ Hu1) as [a1 a'1 Ea1 Ea'1 HR1]; destruct (H0 _ _ Ht) as [a a' Ea Ea' HR0].
    all: functional_eval_rewrite_clear.
    all: assert (Hirr : _ <~> _) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HR1))
                                                (proj1 (per_univ_elem_sym _ _ _ _ HR0))).
    all: eapply retag_head_readable with (ρ := ρ); [ exact Ea1 | exact HR1 | apply Hirr; eassumption | ].
    (* the stored unit matters only at a module head, which a definition
       with a module part has not *)
    all: intros h U0 Ek; try (cbn; lia).
    destruct per_ctx_env_dm_rel_left_kind as (t1 & U1 & Ek'); rewrite Ek in Ek'; discriminate.
  Qed.

  (** A context PER relates an environment as its retagging at the
      context, on either side. *)
  Corollary per_ctx_env_retag_left : forall {Γ Δ R},
      EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
      forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ctx_retag Γ ρ ≈ ρ' ∈ R.
  Proof.
    intros * H * Hρ.
    exact (per_ctx_env_resp_retagged_left H _ _ _ (env_agree_retagged_ctx_retag _ _ _) (per_ctx_env_retag_readable H _ _ Hρ) Hρ).
  Qed.

  Corollary per_ctx_env_retag_right : forall {Γ Δ R},
      EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
      forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ctx_retag Γ ρ' ∈ R.
  Proof.
    intros * H * Hρ.
    assert (HPER : PER R) by exact (per_env_PER H).
    assert (Hρ' : Dom ρ' ≈ ρ' ∈ R) by (etransitivity; [ symmetry |]; exact Hρ).
    exact (per_ctx_env_resp_retagged_right H _ _ _ (env_agree_retagged_ctx_retag _ _ _) (per_ctx_env_retag_readable H _ _ Hρ') Hρ).
  Qed.

  Corollary per_ctx_env_retag : forall {Γ Δ R},
      EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
      forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ctx_retag Γ ρ ≈ ctx_retag Γ ρ' ∈ R.
  Proof. intros * H * Hρ; exact (per_ctx_env_retag_right H _ _ (per_ctx_env_retag_left H _ _ Hρ)). Qed.
End Fixed_GCtx.
