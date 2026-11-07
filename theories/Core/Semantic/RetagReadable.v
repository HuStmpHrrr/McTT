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
      back whatever its type, by its unit, and a head with a module part
      by its term and its unit, whose free indices stay below [n]. *)
  Lemma retag_head_readable : forall {i A ρA a a' R} (n : nat) (U : gunit) (ρ : env) w,
      ⟦ A ⟧ ρA ↘ a -> DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom (ρ 0) ≈ w ∈ R ->
      (forall h U0, env_entry ρ 0 = de_mod h U0 -> gunit_free_bound U <= n) ->
      (forall v t h U0, env_entry ρ 0 = de_dm v t h U0 -> gunit_free_bound U <= n) ->
      head_readable n (retag_entry (entry_type_closure A ρA) U (env_entry ρ 0)).
  Proof.
    intros * Ea HR Hv HU HU'; unfold env_var in Hv.
    destruct (env_entry ρ 0) as [v t0 | h U0 | v t0 h U0] eqn:E; cbn [retag_entry]; split; cbn [entry_unit_bound]; try lia.
    - intros s; destruct (per_univ_then_per_top_typ HR s) as [T T' HT HT' _];
        destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _].
      eexists; eapply read_entry_term; solve [ eapply eval_entry_type_closure; eassumption | eassumption ].
    - apply mod_entry_readable.
    - exact (HU _ _ eq_refl).
    - intros s; destruct (per_univ_then_per_top_typ HR s) as [T T' HT HT' _];
        destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _].
      eexists; eapply read_entry_dm; solve [ eapply eval_entry_type_closure; eassumption | eassumption ].
    - exact (HU' _ _ _ _ eq_refl).
  Qed.

  Lemma env_entry_head : forall ρ, List.hd absent_entry ρ = env_entry ρ 0.
  Proof. intros [| d ρ]; reflexivity. Qed.

  (** The value of an entry of [ρ] moved to the head of another
      environment. *)
  Lemma env_var_head_entry : forall ρ x ρ1, env_var (env_entry ρ x :: ρ1) 0 = env_var ρ x.
  Proof. reflexivity. Qed.

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
    all: cbn [ctx_retag skipn List.length centry_tag centry_type centry_slot_unit centry_unit].
    all: change (env_entry (?d :: ?ρ0) 0) with d; rewrite env_entry_head.
    (* a slot: a module head, by its kind, stored at its unit, scoped by
       its tail *)
    3: { destruct per_ctx_env_mod_rel_left_kind as (U0 & Ek).
         rewrite Ek; cbn [retag_entry]; split; [ apply mod_entry_readable | cbn [entry_unit_bound]; assumption ]. }
    (* a type: the head is an element of the type at the retagged tail *)
    all: match goal with HT : forall ρ0 ρ'0 (e : _ ρ0 ρ'0), rel_typ _ _ _ _ _ _ |- _ =>
           destruct (HT _ _ Hu1) as [a1 a'1 Ea1 Ea'1 HR1]; destruct (HT _ _ Ht) as [a a' Ea Ea' HR0] end.
    all: functional_eval_rewrite_clear.
    all: assert (Hirr : _ <~> _) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HR1))
                                                (proj1 (per_univ_elem_sym _ _ _ _ HR0))).
    all: eapply retag_head_readable with (ρ := ρ); [ exact Ea1 | exact HR1 | apply Hirr; eassumption | | ].
    (* the stored unit is the entry's declared one: none at a term entry,
       and at a definition with a module part its unit, scoped by the
       tail *)
    all: intros * Ek; cbn; lia.
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

  (** The head PER of [A] at environments of [Δ] is included in the
      element PER of [A]'s values over their first [|Δ|] entries, the
      environment of the closure [centry_tag] stores. *)
  Lemma per_head_at_env_upto : forall {Δ κ A R S ρ ρ'},
      EF Δ ▹{κ} A ≈ Δ ▹{κ} A ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ S ->
      Dom ρ ≈ ρ' ∈ S ->
      exists i a a' Rh,
        ⟦ A ⟧ env_upto (List.length Δ) ρ ↘ a /\ ⟦ A ⟧ env_upto (List.length Δ) ρ' ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem i ↘ Rh /\
        (forall m m', Dom m ≈ m' ∈ per_head A A ρ ρ' -> Dom m ≈ m' ∈ Rh).
  Proof.
    intros * HΔA HΔ Hρ.
    inversion HΔA as [| ? ? ? ? ? ? tail_rel head_rel ? HΔt Htail HA | | | ]; subst.
    assert (ES : S <~> tail_rel) by (eapply per_ctx_env_right_irrel; eassumption).
    apply ES in Hρ.
    assert (Hu : Dom env_upto (List.length Δ) ρ ≈ env_upto (List.length Δ) ρ' ∈ tail_rel)
      by exact (per_ctx_env_resp_agree HΔt _ _ _ _ (env_agree_upto_env_upto _ _) (env_agree_upto_env_upto _ _) Hρ).
    assert (Hl : Dom env_upto (List.length Δ) ρ ≈ ρ' ∈ tail_rel)
      by exact (per_ctx_env_resp_agree HΔt _ _ _ _ (env_agree_upto_env_upto _ _) (reflexivity _) Hρ).
    destruct (HA _ _ Hu) as [a1 a1' Ea1 Ea1' HR1].
    destruct (HA _ _ Hl) as [b1 b' Eb1 Eb' HR2].
    destruct (HA _ _ Hρ) as [a a' Ea Ea' HR0].
    functional_eval_rewrite_clear.
    assert (E12 : _ <~> _) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR2).
    assert (E20 : _ <~> _) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR2 HR0).
    exists i, a1, a1', (head_rel _ _ Hu); do 3 (split; [ assumption |]).
    intros m m' Hm; apply E12, E20; exact (Hm _ _ _ _ Ea Eb' HR0).
  Qed.

  (** Values the head PER of [A] relates, at environments of [Δ], read
      back stored at the tag an extension of the environments by [A]
      gives them ([centry_tag]). *)
  Lemma per_head_closure_readable : forall {Δ κ A R S ρ ρ' m m'},
      EF Δ ▹{κ} A ≈ Δ ▹{κ} A ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ S ->
      Dom ρ ≈ ρ' ∈ S -> Dom m ≈ m' ∈ per_head A A ρ ρ' ->
      entry_readable (de_term m (centry_tag (ce_ass κ A) Δ ρ)) /\ entry_readable (de_term m' (centry_tag (ce_ass κ A) Δ ρ')).
  Proof.
    intros * HΔA HΔ Hρ Hm.
    destruct (per_head_at_env_upto HΔA HΔ Hρ) as (i & a & a' & Rh & Ea & Ea' & HR & Hincl).
    unfold centry_tag; cbn [centry_type].
    exact (entry_readable_of_elem_closure Ea Ea' HR (Hincl _ _ Hm)).
  Qed.

  (** Entries whose values the head PER of [A] relates, at environments of
      [Δ], read back retagged at [A] over the first [|Δ|] entries and at a
      unit [U], scoped by [n] when the entries store it: a module entry
      and a definition with a module part keep the unit. *)
  Lemma per_head_retag_readable_at : forall {Δ κ A R S ρ ρ' e e'} (n : nat) (U : gunit),
      EF Δ ▹{κ} A ≈ Δ ▹{κ} A ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ S ->
      Dom ρ ≈ ρ' ∈ S -> Dom (env_var (e :: ρ) 0) ≈ (env_var (e' :: ρ') 0) ∈ per_head A A ρ ρ' ->
      (forall h U0, e = de_mod h U0 -> gunit_free_bound U <= n) ->
      (forall h U0, e' = de_mod h U0 -> gunit_free_bound U <= n) ->
      (forall v t h U0, e = de_dm v t h U0 -> gunit_free_bound U <= n) ->
      (forall v t h U0, e' = de_dm v t h U0 -> gunit_free_bound U <= n) ->
      head_readable n (retag_entry (centry_tag (ce_ass κ A) Δ ρ) U e) /\
      head_readable n (retag_entry (centry_tag (ce_ass κ A) Δ ρ') U e').
  Proof.
    intros * HΔA HΔ Hρ Hm HU HU' HD HD'.
    destruct (per_head_at_env_upto HΔA HΔ Hρ) as (i & a & a' & Rh & Ea & Ea' & HR & Hincl).
    pose proof (Hincl _ _ Hm) as Hh.
    destruct (per_univ_elem_sym _ _ _ _ HR) as [HR' Hsym].
    unfold centry_tag; cbn [centry_type]; split.
    - exact (retag_head_readable n U (e :: ρ) _ Ea HR Hh HU HD).
    - exact (retag_head_readable n U (e' :: ρ') _ Ea' HR' (Hsym _ _ Hh) HU' HD').
  Qed.

  (** At the unit of an assumption, closed. *)
  Corollary per_head_retag_readable : forall {Δ κ A R S ρ ρ' e e'},
      EF Δ ▹{κ} A ≈ Δ ▹{κ} A ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ S ->
      Dom ρ ≈ ρ' ∈ S -> Dom (env_var (e :: ρ) 0) ≈ (env_var (e' :: ρ') 0) ∈ per_head A A ρ ρ' ->
      head_readable 0 (retag_entry (centry_tag (ce_ass κ A) Δ ρ) (centry_slot_unit (ce_ass κ A)) e) /\
      head_readable 0 (retag_entry (centry_tag (ce_ass κ A) Δ ρ') (centry_slot_unit (ce_ass κ A)) e').
  Proof.
    intros * HΔA HΔ Hρ Hm.
    exact (per_head_retag_readable_at 0 (centry_slot_unit (ce_ass κ A)) HΔA HΔ Hρ Hm
             (fun _ _ _ => ltac:(cbn; lia)) (fun _ _ _ => ltac:(cbn; lia))
             (fun _ _ _ _ _ => ltac:(cbn; lia)) (fun _ _ _ _ _ => ltac:(cbn; lia))).
  Qed.

  (** A definition with a module part, its term related in the head PER
      of [A] at environments of [Δ], reads back stored at [A] over the
      first [|Δ|] entries, its unit scoped by [n]. *)
  Corollary per_head_dm_readable : forall {Δ κ A R S ρ ρ' m m' h h' U} (n : nat),
      EF Δ ▹{κ} A ≈ Δ ▹{κ} A ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ S ->
      Dom ρ ≈ ρ' ∈ S -> Dom m ≈ m' ∈ per_head A A ρ ρ' ->
      gunit_free_bound U <= n ->
      head_readable n (de_dm m (centry_tag (ce_ass κ A) Δ ρ) h U) /\
      head_readable n (de_dm m' (centry_tag (ce_ass κ A) Δ ρ') h' U).
  Proof.
    intros * HΔA HΔ Hρ Hm HbU.
    exact (per_head_retag_readable_at (e := de_dm m (centry_tag (ce_ass κ A) Δ ρ) h U)
             (e' := de_dm m' (centry_tag (ce_ass κ A) Δ ρ') h' U) n U HΔA HΔ Hρ Hm
             (fun _ _ E => ltac:(discriminate E)) (fun _ _ E => ltac:(discriminate E))
             (fun _ _ _ _ _ => HbU) (fun _ _ _ _ _ => HbU)).
  Qed.

  (** [per_env_extend_intro'] for the extensions a substitution
      extension evaluates to ([eval_sub_extend]): the heads stored at
      [centry_tag], which read back ([per_head_closure_readable]). *)
  Corollary per_env_extend_intro_tagged : forall {Δ κ A R S ρ ρ' m m'},
      EF Δ ▹{κ} A ≈ Δ ▹{κ} A ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ S ->
      Dom ρ ≈ ρ' ∈ S -> Dom m ≈ m' ∈ per_head A A ρ ρ' ->
      Dom ρ ↦ m ⦂ centry_tag (ce_ass κ A) Δ ρ ≈ ρ' ↦ m' ⦂ centry_tag (ce_ass κ A) Δ ρ' ∈ per_env_extend A A (List.length Δ) S.
  Proof.
    intros * HΔA HΔ Hρ Hm.
    destruct (per_head_closure_readable HΔA HΔ Hρ Hm) as [Hr Hr'].
    exact (per_env_extend_intro' Hρ Hm Hr Hr').
  Qed.

  (** [per_env_extend_intro] for environments whose heads are retagged at
      the tag of an extension by [A] ([eval_sub_q]): their values are
      related in the head PER, and they read back as they are. *)
  Corollary per_env_extend_intro_retagged : forall {Δ κ A R S ρ ρ' e e'},
      EF Δ ▹{κ} A ≈ Δ ▹{κ} A ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ S ->
      Dom ρ ≈ ρ' ∈ S -> Dom (env_var (e :: ρ) 0) ≈ (env_var (e' :: ρ') 0) ∈ per_head A A ρ ρ' ->
      (rel_typ_propositional A ρ -> exists v t, e = de_term v t) ->
      (rel_typ_propositional A ρ' -> exists v t, e' = de_term v t) ->
      Dom retag_entry (centry_tag (ce_ass κ A) Δ ρ) (centry_slot_unit (ce_ass κ A)) e :: ρ
        ≈ retag_entry (centry_tag (ce_ass κ A) Δ ρ') (centry_slot_unit (ce_ass κ A)) e' :: ρ' ∈ per_env_extend A A (List.length Δ) S.
  Proof.
    intros * HΔA HΔ Hρ Hm Hp Hp'.
    destruct (per_head_retag_readable HΔA HΔ Hρ Hm) as [Hr Hr'].
    apply per_env_extend_intro; cbn [drop_env List.tl]; try assumption;
      try (eapply head_readable_mono; [ apply Nat.le_0_l | eassumption ]).
    - destruct e, e'; exact Hm.
    - intros Hq; destruct (Hp Hq) as (v & t & ->); eexists; reflexivity.
    - intros Hq; destruct (Hp' Hq) as (v & t & ->); eexists; reflexivity.
  Qed.
End Fixed_GCtx.

(** [solve_per_env_extend_chain] for a chain of extensions a substitution
    extension evaluates to, its heads stored at [centry_tag]: each link by
    [per_env_extend_intro_tagged], at the context PERs of [Δ ▹ A] and [Δ]
    in the hypotheses. *)
Ltac solve_per_env_extend_chain_tagged :=
  repeat
    match goal with
    | |- rel_chain _ (_ :: _ :: nil) => apply rel_chain_of_pair
    | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
    end;
  (eapply per_env_extend_intro_tagged; [ eassumption | eassumption | | ]);
    first [ pairwise | solve_per_head | assumption ].
