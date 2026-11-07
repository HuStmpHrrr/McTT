(** * PER Lemmas: Environments

    The last part of [Core.Semantic.PER.Lemmas]: extending related
    environments, agreement up to retagging, context PERs respecting
    agreement, environments holding their proofs, and the readability of
    kept proofs over related environments. *)
From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions PER.Tele.
From Mctt.Core.Semantic.PER.Lemmas Require Export CanonicalContexts.
Import Domain_Notations Fixed_Notations.
Import ListNotations.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_respects_length : forall {Γ Γ'},
    Exp Γ ≈ Γ' ∈ per_ctx ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.

(** A context below another has as many entries. *)
Lemma per_ctx_subtyp_length : forall Γ Δ, SubE Γ <: Δ -> length Γ = length Δ.
Proof. induction 1; cbn [length]; congruence. Qed.

Lemma per_ctx_subtyp_to_env : forall Γ Δ,
    SubE Γ <: Δ ->
    exists R R',
      EF Γ ≈ Γ ∈ per_ctx_env ↘ R /\
        EF Δ ≈ Δ ∈ per_ctx_env ↘ R'.
Proof.
  destruct 1; destruct_all.
  1: repeat eexists; econstructor; apply Equivalence_Reflexive.
  all: eauto.
Qed.

(** An inclusion of context PERs holds for any other names of them. *)
Lemma per_ctx_env_incl_irrel : forall Γ Δ R R1 R' R2 ρ ρ',
    (forall ρ ρ', R1 ρ ρ' -> R2 ρ ρ') ->
    R ρ ρ' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R1 ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R2 ->
    R' ρ ρ'.
Proof.
  intros * Hinc Hρ HR HR1 HR' HR2.
  apply (per_ctx_env_right_irrel _ _ _ _ _ HR' HR2), Hinc, (per_ctx_env_right_irrel _ _ _ _ _ HR HR1), Hρ.
Qed.

(** Subtyping relates types of one sort. *)
Lemma per_subtyp_kind : forall i a a', Sub a <: a' at i -> domain_kind a = domain_kind a'.
Proof.
  intros * H; destruct H; try reflexivity; try congruence.
  destruct H as [Hl Hr _]; congruence.
Qed.

(** A type below a proposition, at evaluated values, is one. *)
Lemma rel_typ_propositional_subtyp : forall {i A ρ A' ρ' a a'},
    ⟦ A ⟧ ρ ↘ a -> ⟦ A' ⟧ ρ' ↘ a' -> Sub a <: a' at i ->
    rel_typ_propositional A' ρ' -> rel_typ_propositional A ρ.
Proof.
  intros * Ea Ea' Hs (b & Eb & Hb).
  assert (b = a') as -> by (eapply functional_eval_exp; eassumption).
  exists a; split; [ exact Ea | rewrite (per_subtyp_kind _ _ _ Hs); exact Hb ].
Qed.

Lemma per_ctx_env_subtyping : forall Γ Δ,
    SubE Γ <: Δ ->
    forall R R' ρ ρ',
      EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
      R ρ ρ' ->
      R' ρ ρ'.
Proof.
  induction 1; intros;
    try solve [ eapply per_ctx_env_incl_irrel; eassumption ];
    handle_per_ctx_env_irrel;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    apply_relation_equivalence;
    trivial.

  destruct_all; destruct_cons_rels.
  assert (Ht : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition.
  assert (HPt : PER tail_rel) by (eapply per_env_PER; eassumption).
  assert (Htl : tail_rel ρ↯ ρ↯) by (etransitivity; [ eassumption | symmetry; eassumption ]).
  assert (Htr : tail_rel ρ'↯ ρ'↯) by (etransitivity; [ symmetry; eassumption | eassumption ]).
  apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht).
  4,5: (** The heads read back, as at [Γ]. *) assumption.
  2,3: (** A type below a proposition is one. *)
       intros (a' & Ea' & Hp);
       match goal with
       | Hl : rel_typ_propositional ?A0 ?t -> ?g |- ?g =>
           apply Hl;
           match goal with
           | Htt : ?T t t, HT : forall ρ ρ' (_ : ?T ρ ρ'), rel_typ _ A0 ρ A0 ρ' _ |- _ =>
               destruct (HT _ _ Htt) as [a a2 Ea Ea2 _];
               exact (rel_typ_propositional_subtyp Ea Ea' (H1 _ _ _ _ Htt Ea Ea') (ex_intro _ a' (conj Ea' Hp)))
           end
       end.
  destruct_rel_typ.
  eapply per_elem_subtyping with (i := max x (max i0 i)); try eassumption.
  - eauto using per_subtyp_cumu_right.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
Qed.

Lemma per_ctx_subtyp_trans : forall Γ1 Γ2,
    SubE Γ1 <: Γ2 ->
    forall Γ3,
      SubE Γ2 <: Γ3 ->
      SubE Γ1 <: Γ3.
Proof.
  induction 1; intros;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    mauto 1;
    clear_PER.

  1: handle_per_ctx_env_irrel.
  1: econstructor; try eassumption.
  - firstorder.
  - instantiate (1 := max i i0).
    intros.
    assert (Dom ρ ≈ ρ' ∈ tail_rel0) by (eapply per_ctx_env_subtyping; revgoals; eassumption).
    saturate_refl_for tail_rel.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    etransitivity.
    + intuition mauto using per_subtyp_cumu_left.
    + intuition mauto using per_subtyp_cumu_right.
  - econstructor; intuition.
    + typeclasses eauto.
    + solve_refl.
  - (** A definition: the inclusions of environments compose. *)
    match goal with HS : SubE (e :: Γ') <: ?Γ3 |- _ =>
      destruct (per_ctx_subtyp_to_env _ _ HS) as [R2 [R3 [HR2 HR3]]];
      destruct Γ3 as [| e3 Γ3']; [ inversion HS |];
      assert (SubE Γ' <: Γ3') by (inversion HS; assumption);
      eapply per_ctx_subtyp_def with (env_rel' := R3); [ eauto | eassumption | eassumption |];
      intros ρ ρ' Hρ;
      eapply per_ctx_env_subtyping; [ exact HS | eassumption | eassumption | ];
      handle_per_ctx_env_irrel; eauto
    end.
  - (** A slot: the inclusions compose. *)
    match goal with HS : SubE (?Γ'' ▹ₘ ?U'') <: ?Γ3 |- _ =>
      destruct (per_ctx_subtyp_to_env _ _ HS) as [R2 [R3 [HR2 HR3]]];
      inversion HS; subst;
      eapply per_ctx_subtyp_mod with (env_rel' := R3); [ eauto | eassumption | eassumption |];
      intros ρ ρ' Hρ;
      eapply per_ctx_env_subtyping; [ exact HS | eassumption | eassumption | ];
      handle_per_ctx_env_irrel; eauto
    end.
  - (** A definition with a module part: the inclusions compose. *)
    match goal with HS : SubE (?Γ'' ▸ₘ ?A'' ≔ ?M'' ‖ ?U'') <: ?Γ3 |- _ =>
      destruct (per_ctx_subtyp_to_env _ _ HS) as [R2 [R3 [HR2 HR3]]];
      inversion HS; subst;
      eapply per_ctx_subtyp_dm with (env_rel' := R3); [ eauto | eassumption | eassumption |];
      intros ρ ρ' Hρ;
      eapply per_ctx_env_subtyping; [ exact HS | eassumption | eassumption | ];
      handle_per_ctx_env_irrel; eauto
    end.
Qed.

Hint Resolve per_ctx_subtyp_trans : mctt.

#[local] Instance per_ctx_subtyp_trans_instance : Transitive per_ctx_subtyp.
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.

(** ** Agreement up to Retagging

    [env_agree_retagged n ρ1 ρ2]: below [n], each entry of [ρ2] is that of
    [ρ1] stored at some type and unit ([retag_entry]).  The values, the
    modules and the kinds of the entries are the same; only the stored types
    and units may differ.  Agreement ([env_agree_upto]) is an instance, and
    so is an environment against its retagging at a context
    ([ctx_retag]), as the evaluation of [Id] yields ([eval_sub_id]). *)
Definition env_agree_retagged (n : nat) (ρ1 ρ2 : env) : Prop :=
  forall x, x < n -> exists t U, env_entry ρ2 x = retag_entry t U (env_entry ρ1 x).

(** Every entry is a retagging of itself. *)
Lemma retag_entry_self : forall e, exists t U, e = retag_entry t U e.
Proof.
  intros [v t | h U | v t h U]; [ exists t, gunit_default | exists entry_type_none, U | exists t, U ]; reflexivity.
Qed.

Lemma env_agree_upto_retagged : forall n ρ1 ρ2, env_agree_upto n ρ1 ρ2 -> env_agree_retagged n ρ1 ρ2.
Proof.
  intros * H x Hx; rewrite <- (H x Hx).
  destruct (retag_entry_self (env_entry ρ1 x)) as (t & U & E); exists t, U; exact E.
Qed.

#[export]
Instance env_agree_retagged_Reflexive n : Reflexive (env_agree_retagged n).
Proof. intros ρ; apply env_agree_upto_retagged; reflexivity. Qed.

(** An environment against its retagging at a context. *)
Lemma env_agree_retagged_ctx_retag : forall Δ n ρ, env_agree_retagged n ρ (ctx_retag Δ ρ).
Proof.
  intros * x _; destruct (Compare_dec.le_lt_dec (List.length Δ) x) as [Hx | Hx].
  - rewrite env_entry_ctx_retag_ge by exact Hx.
    destruct (retag_entry_self (env_entry ρ x)) as (t & U & E); exists t, U; exact E.
  - rewrite env_entry_ctx_retag by exact Hx; eexists; eexists; reflexivity.
Qed.

(** An environment agreeing with the retagging of [ρ], as an evaluation
    of [Id] at [ρ] is ([eval_sub_id], [functional_eval_sub]). *)
Lemma env_agree_retagged_of_upto : forall Δ n ρ e, env_agree_upto n e (ctx_retag Δ ρ) -> env_agree_retagged n ρ e.
Proof.
  intros * H x Hx; rewrite (H x Hx); exact (env_agree_retagged_ctx_retag Δ n ρ x Hx).
Qed.

(** An environment against its head retagged, as [q σ] keeps it
    ([eval_sub_q]). *)
Lemma env_agree_retagged_head : forall n t U e ρ, env_agree_retagged n (e :: ρ) (retag_entry t U e :: ρ).
Proof.
  intros n t U e ρ [| x] _; [ exists t, U; reflexivity |].
  destruct (retag_entry_self (env_entry ρ x)) as (t' & U' & E); exists t', U'; exact E.
Qed.

Lemma env_agree_retagged_drop : forall n ρ1 ρ2, env_agree_retagged (S n) ρ1 ρ2 -> env_agree_retagged n ρ1↯ ρ2↯.
Proof. intros * H x Hx; rewrite !env_entry_drop; apply H; lia. Qed.

Lemma env_agree_retagged_var : forall n ρ1 ρ2, env_agree_retagged n ρ1 ρ2 -> forall x, x < n -> env_var ρ1 x = env_var ρ2 x.
Proof. intros * H x Hx; unfold env_var; destruct (H x Hx) as (t & U & E); rewrite E; destruct (env_entry ρ1 x); reflexivity. Qed.

Lemma env_agree_retagged_mod : forall n ρ1 ρ2, env_agree_retagged n ρ1 ρ2 -> forall x, x < n -> env_mod ρ1 x = env_mod ρ2 x.
Proof. intros * H x Hx; unfold env_mod; destruct (H x Hx) as (t & U & E); rewrite E; destruct (env_entry ρ1 x); reflexivity. Qed.

(** A head that is a term entry is one after retagging. *)
Lemma env_agree_retagged_term_head : forall n ρ1 ρ2, env_agree_retagged (S n) ρ1 ρ2 ->
    (exists t, env_entry ρ1 0 = de_term (ρ1 0) t) -> exists t, env_entry ρ2 0 = de_term (ρ2 0) t.
Proof.
  intros * H [t0 Ht]; destruct (H 0 ltac:(lia)) as (t & U & E); exists t.
  rewrite <- (env_agree_retagged_var _ _ _ H 0 ltac:(lia)), E, Ht; reflexivity.
Qed.

(** A head that is a definition with a module part, or a module slot, is
    one after retagging: the kind fields of the context PERs' records. *)
Lemma env_agree_retagged_dm_kind_from : forall n ρ1 ρ2, env_agree_retagged (S n) ρ1 ρ2 ->
    forall t1 U1, env_entry ρ1 0 = de_dm (ρ1 0) t1 (env_mod ρ1 0) U1 ->
    exists t U0, env_entry ρ2 0 = de_dm (ρ1 0) t (env_mod ρ1 0) U0.
Proof.
  intros * H t1 U1 E1; destruct (H 0 ltac:(lia)) as (t & U & E).
  rewrite E, E1; exists t, U; reflexivity.
Qed.

Lemma env_agree_retagged_dm_kind : forall n ρ1 ρ2, env_agree_retagged (S n) ρ1 ρ2 ->
    forall t1 U1, env_entry ρ1 0 = de_dm (ρ1 0) t1 (env_mod ρ1 0) U1 ->
    exists t U0, env_entry ρ2 0 = de_dm (ρ2 0) t (env_mod ρ2 0) U0.
Proof.
  intros * H t1 U1 E1.
  rewrite <- (env_agree_retagged_var _ _ _ H 0 ltac:(lia)), <- (env_agree_retagged_mod _ _ _ H 0 ltac:(lia)).
  exact (env_agree_retagged_dm_kind_from _ _ _ H _ _ E1).
Qed.

Lemma env_agree_retagged_mod_kind_from : forall n ρ1 ρ2, env_agree_retagged (S n) ρ1 ρ2 ->
    forall U1, env_entry ρ1 0 = de_mod (env_mod ρ1 0) U1 ->
    exists U0, env_entry ρ2 0 = de_mod (env_mod ρ1 0) U0.
Proof.
  intros * H U1 E1; destruct (H 0 ltac:(lia)) as (t & U & E).
  rewrite E, E1; exists U; reflexivity.
Qed.

Lemma env_agree_retagged_mod_kind : forall n ρ1 ρ2, env_agree_retagged (S n) ρ1 ρ2 ->
    forall U1, env_entry ρ1 0 = de_mod (env_mod ρ1 0) U1 ->
    exists U0, env_entry ρ2 0 = de_mod (env_mod ρ2 0) U0.
Proof.
  intros * H U1 E1; rewrite <- (env_agree_retagged_mod _ _ _ H 0 ltac:(lia)).
  exact (env_agree_retagged_mod_kind_from _ _ _ H _ E1).
Qed.

(** The kind of a retagged head, from the kind of the head it retags,
    whether the goal reads the head's value and module on the new side or,
    rewritten, on the old one. *)
Ltac solve_retagged_kind :=
  let close Heq Hk :=
    first [ exact (env_agree_retagged_dm_kind _ _ _ Heq _ _ Hk) | exact (env_agree_retagged_dm_kind_from _ _ _ Heq _ _ Hk)
          | exact (env_agree_retagged_mod_kind _ _ _ Heq _ Hk) | exact (env_agree_retagged_mod_kind_from _ _ _ Heq _ Hk) ] in
  match goal with
  | |- context [ env_entry ?ρ2 0 ] =>
      match goal with
      | Heq : env_agree_retagged _ ?ρ1 ρ2, Hk : env_entry ?ρ1 0 = _ |- _ => close Heq Hk
      | Heq : env_agree_retagged _ ?ρ1 ρ2, Hk : exists t U0, env_entry ?ρ1 0 = _ |- _ =>
          let t1 := fresh "t" in let U1 := fresh "U" in let Hk1 := fresh "Hk" in
          destruct Hk as (t1 & U1 & Hk1); close Heq Hk1
      | Heq : env_agree_retagged _ ?ρ1 ρ2, Hk : exists U0, env_entry ?ρ1 0 = _ |- _ =>
          let U1 := fresh "U" in let Hk1 := fresh "Hk" in
          destruct Hk as (U1 & Hk1); close Heq Hk1
      end
  end.

(** How far the unit an environment of [Γ] stores at an entry [e] after
    [n] entries may reach: [n] at a module slot and at a definition with
    a module part, which store their units over their tails; nothing at
    any other entry, which stores no unit the readback of a proof would
    bind. *)
Definition centry_unit_bound (e : centry) (n : nat) : nat :=
  match e with
  | ce_mod _ | ce_dm _ _ _ => n
  | _ => 0
  end.

(** The entries of an environment of [Γ] read back, at the room their
    context entry leaves them: what a context PER asks of every head
    ([per_ctx_env_heads_readable]). *)
Definition env_heads_readable (Γ : ctx) (ρ : env) : Prop :=
  forall x e, List.nth_error Γ x = Some e ->
    head_readable (centry_unit_bound e (List.length (List.skipn (S x) Γ))) (env_entry ρ x).

Lemma env_heads_readable_drop : forall e Γ ρ, env_heads_readable (e :: Γ) ρ -> env_heads_readable Γ ρ↯.
Proof. intros * H x e' Hx; rewrite env_entry_drop; exact (H (S x) e' Hx). Qed.

Lemma env_heads_readable_resp_agree : forall Γ ρ1 ρ2,
    env_agree_upto (List.length Γ) ρ1 ρ2 -> env_heads_readable Γ ρ1 -> env_heads_readable Γ ρ2.
Proof.
  intros * Ha H x e Hx; rewrite <- (Ha x); [ exact (H x e Hx) |].
  apply List.nth_error_Some; congruence.
Qed.

(** The heads of the environments a context PER relates read back. *)
Lemma per_ctx_env_heads_readable : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> env_heads_readable Γ ρ /\ env_heads_readable Γ ρ'.
Proof.
  intros * H; induction H; intros ρ ρ' HR; apply_relation_equivalence;
    [ split; intros [] ? ?; discriminate | .. ];
    destruct HR; destruct (IHper_ctx_env _ _ ltac:(eassumption)) as [IHl IHr];
    split; intros [| x] e Hx; cbn [List.nth_error] in Hx;
    first [ injection Hx as <-; assumption | rewrite <- env_entry_drop; first [ exact (IHl x e Hx) | exact (IHr x e Hx) ] ].
Qed.

(** The readability of a head of an environment of [Γ] that reads back. *)
Ltac readable_head :=
  match goal with
  | Hr : env_heads_readable _ ?ρ |- head_readable _ (env_entry ?ρ 0) => exact (Hr 0 _ eq_refl)
  end.

(** * Context PERs Respect Agreement of Environments

    Evaluating a substitution determines its result only on the entries of
    its target ([functional_eval_sub]), so every use of a context PER in the
    completeness proof needs this lemma.  It does not follow from evaluation
    respecting [env_eq], which is false because a closure captures its
    environment.  It holds because a context PER inspects an environment
    only pointwise, on the entries of its context, and its head relations at
    agreeing environments coincide up to [<~>] by irrelevance.  The types
    and units stored in the entries may be retagged: the PER reads an
    entry's value, module and kind, and its readability, which the new
    environments are asked for. *)
Lemma per_ctx_env_resp_retagged : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ1 ρ2 ρ1' ρ2',
      env_agree_retagged (List.length Γ) ρ1 ρ2 ->
      env_agree_retagged (List.length Γ) ρ1' ρ2' ->
      env_heads_readable Γ ρ2 ->
      env_heads_readable Γ ρ2' ->
      Dom ρ1 ≈ ρ1' ∈ R ->
      Dom ρ2 ≈ ρ2' ∈ R.
Proof.
  intros * H.
  induction H; intros * Heq Heq' Hr2 Hr2' HR; apply_relation_equivalence; [ trivial | | | | ].
  all: pose proof (env_heads_readable_drop _ _ _ Hr2) as Hr2d; pose proof (env_heads_readable_drop _ _ _ Hr2') as Hr2d'.
  4: { (** A definition with a module part: the term part as a definition,
         the unit as a slot. *)
    destruct HR as [Dtail1 Hh Hterms T1 T2 T3 T4].
    destruct (per_ctx_env_heads_readable equiv_Γ_Γ' _ _ Dtail1) as [Hr1d Hr1d'].
    assert (Hd : env_agree_retagged (List.length Γ) ρ1↯ ρ2↯) by exact (env_agree_retagged_drop _ _ _ Heq).
    assert (Hd' : env_agree_retagged (List.length Γ) ρ1'↯ ρ2'↯) by exact (env_agree_retagged_drop _ _ _ Heq').
    assert (Dmix : Dom ρ1↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption .. ]).
    assert (Dtail2 : Dom ρ2↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; eassumption).
    assert (D11 : Dom ρ1↯ ≈ ρ1↯ ∈ tail_rel) by solve_per.
    assert (D11' : Dom ρ1'↯ ≈ ρ1'↯ ∈ tail_rel) by solve_per.
    assert (D12 : Dom ρ1↯ ≈ ρ2↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | eassumption | eassumption | exact D11 ]).
    assert (D12' : Dom ρ1'↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | eassumption | eassumption | exact D11' ]).
    match goal with HU : forall ρ ρ', tail_rel ρ ρ' -> rel_modexp_evals _ _ _ _ |- _ =>
      destruct (rel_modexp_evals_move _ _ _ _ _ _ D12 HU) as (M1 & M2 & M3 & M4);
      destruct (rel_modexp_evals_move _ _ _ _ _ _ D12' HU) as (M1' & M2' & M3' & M4') end.
    assert (Dom ρ2↯ ≈ ρ2↯ ∈ tail_rel) by solve_per.
    assert (Dom ρ2'↯ ≈ ρ2'↯ ∈ tail_rel) by solve_per.
    (** The heads are read at the old pair, the new one and the mixed one;
        the bodies at each old side against its new one and at each new
        side against itself.  The self-relations of the old sides are not
        needed, and would only enlarge the saturation. *)
    clear D11 D11'.
    destruct r; cbn [def_heads_at def_bodies_at] in *; [ destruct Hterms; destruct_conjs | | destruct Hterms; destruct_conjs ].
    all: solve_def_heads_pre.
    all: apply (mk_per_ctx_env_dm_rel _ _ _ _ _ _ _ _ _ _ Dtail2);
      try (match goal with |- def_heads_at _ _ _ _ _ _ => cbn [def_heads_at]; constructor end);
      try rewrite <- (env_agree_retagged_var _ _ _ Heq 0 ltac:(cbn; lia)); try rewrite <- (env_agree_retagged_var _ _ _ Heq' 0 ltac:(cbn; lia));
      try rewrite <- (env_agree_retagged_mod _ _ _ Heq 0 ltac:(cbn; lia)); try rewrite <- (env_agree_retagged_mod _ _ _ Heq' 0 ltac:(cbn; lia));
      try solve [ readable_head ]; try solve [ solve_retagged_kind ];
      try solve [ solve_tie ]; solve_def_heads_post. }
  3: { (** A slot: the heads are the same, and the closures over the new
         tails are related to those over the old ones. *)
    destruct HR as [Dtail1 T1 T2 T3 T4 Hrl Hrr].
    destruct (per_ctx_env_heads_readable equiv_Γ_Γ' _ _ Dtail1) as [Hr1d Hr1d'].
    assert (Hd : env_agree_retagged (List.length Γ) ρ1↯ ρ2↯) by exact (env_agree_retagged_drop _ _ _ Heq).
    assert (Hd' : env_agree_retagged (List.length Γ) ρ1'↯ ρ2'↯) by exact (env_agree_retagged_drop _ _ _ Heq').
    assert (Dtail2 : Dom ρ2↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; eassumption).
    assert (D11 : Dom ρ1↯ ≈ ρ1↯ ∈ tail_rel) by solve_per.
    assert (D11' : Dom ρ1'↯ ≈ ρ1'↯ ∈ tail_rel) by solve_per.
    assert (D12 : Dom ρ1↯ ≈ ρ2↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | eassumption | eassumption | exact D11 ]).
    assert (D12' : Dom ρ1'↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | eassumption | eassumption | exact D11' ]).
    destruct (rel_modexp_evals_move _ _ _ _ _ _ D12 H2) as (M1 & M2 & M3 & M4).
    destruct (rel_modexp_evals_move _ _ _ _ _ _ D12' H2) as (M1' & M2' & M3' & M4').
    constructor; [ exact Dtail2 | .. ];
      try rewrite <- (env_agree_retagged_mod _ _ _ Heq 0 ltac:(cbn; lia)); try rewrite <- (env_agree_retagged_mod _ _ _ Heq' 0 ltac:(cbn; lia));
      try solve [ readable_head ]; try solve [ solve_retagged_kind ]; solve_tie. }
  all: destruct HR as [Dtail1 Hhead1];
    destruct (per_ctx_env_heads_readable equiv_Γ_Γ' _ _ Dtail1) as [Hr1d Hr1d'];
    assert (Hd : env_agree_retagged (List.length Γ) ρ1↯ ρ2↯) by exact (env_agree_retagged_drop _ _ _ Heq);
    assert (Hd' : env_agree_retagged (List.length Γ) ρ1'↯ ρ2'↯) by exact (env_agree_retagged_drop _ _ _ Heq');
    assert (Dmix : Dom ρ1↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption .. ]);
    assert (Dtail2 : Dom ρ2↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; eassumption);
    first [ apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Dtail2) | apply (mk_per_ctx_env_def_rel' _ _ _ _ _ _ _ _ _ Dtail2) ];
    (** The term-head fields: the new tails' types are propositions exactly
        when the old ones' are, through the mixed pair. *)
    try (let Hp := fresh "Hp" in intros Hp; apply (env_agree_retagged_term_head _ _ _ Heq); revert Hp; solve_prop_head);
    try (let Hp := fresh "Hp" in intros Hp; apply (env_agree_retagged_term_head _ _ _ Heq'); revert Hp; solve_prop_head);
    try solve [ readable_head ];
    rewrite <- (env_agree_retagged_var _ _ _ Heq 0 ltac:(cbn; lia)), <- (env_agree_retagged_var _ _ _ Heq' 0 ltac:(cbn; lia)).
  - pose proof (H0 _ _ Dtail1).
    pose proof (H0 _ _ Dmix).
    pose proof (H0 _ _ Dtail2).
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    first [ eassumption | use_relation_equivalence; eassumption ].
  - (** A definition: the bodies at the new tails are related to the old
        heads through the other side's body; nothing at a proposition. *)
    destruct_conjs.
    assert (Dom ρ2↯ ≈ ρ2↯ ∈ tail_rel) by solve_per.
    assert (Dom ρ2'↯ ≈ ρ2'↯ ∈ tail_rel) by solve_per.
    assert (Dom ρ1'↯ ≈ ρ2'↯ ∈ tail_rel) by solve_per.
    destruct r; cbn [def_heads_at def_bodies_at] in *;
      repeat match goal with H : def_heads _ _ _ _ _ |- _ => destruct H end; destruct_conjs;
      [| split; [ solve_def_heads | exact I ] |].
    all: solve_def_heads_pre.
    all: split; [ solve_def_heads_post |].
    all: constructor; try rewrite <- (env_agree_retagged_var _ _ _ Heq 0 ltac:(cbn; lia)); try rewrite <- (env_agree_retagged_var _ _ _ Heq' 0 ltac:(cbn; lia));
      solve_def_heads_post.
Qed.

(** In particular, context PERs respect agreement: an environment agreeing
    with a related one reads back as it does. *)
Corollary per_ctx_env_resp_agree : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ1 ρ2 ρ1' ρ2',
      env_agree_upto (List.length Γ) ρ1 ρ2 ->
      env_agree_upto (List.length Γ) ρ1' ρ2' ->
      Dom ρ1 ≈ ρ1' ∈ R ->
      Dom ρ2 ≈ ρ2' ∈ R.
Proof.
  intros * H * Heq Heq' Hρ.
  destruct (per_ctx_env_heads_readable H _ _ Hρ) as [Hr Hr'].
  apply (per_ctx_env_resp_retagged H ρ1 ρ2 ρ1' ρ2'); try (apply env_agree_upto_retagged; assumption);
    [ exact (env_heads_readable_resp_agree _ _ _ Heq Hr) | exact (env_heads_readable_resp_agree _ _ _ Heq' Hr') | exact Hρ ].
Qed.

(** One side retagged, at heads that read back. *)
Corollary per_ctx_env_resp_retagged_left : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ1 ρ2 ρ', env_agree_retagged (List.length Γ) ρ1 ρ2 -> env_heads_readable Γ ρ2 ->
      Dom ρ1 ≈ ρ' ∈ R -> Dom ρ2 ≈ ρ' ∈ R.
Proof.
  intros * H * Heq Hr Hρ.
  exact (per_ctx_env_resp_retagged H _ _ _ _ Heq (reflexivity _) Hr (proj2 (per_ctx_env_heads_readable H _ _ Hρ)) Hρ).
Qed.

Corollary per_ctx_env_resp_retagged_right : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ ρ1' ρ2', env_agree_retagged (List.length Γ) ρ1' ρ2' -> env_heads_readable Γ ρ2' ->
      Dom ρ ≈ ρ1' ∈ R -> Dom ρ ≈ ρ2' ∈ R.
Proof.
  intros * H * Heq Hr Hρ.
  exact (per_ctx_env_resp_retagged H _ _ _ _ (reflexivity _) Heq (proj1 (per_ctx_env_heads_readable H _ _ Hρ)) Hr Hρ).
Qed.

(** In particular, context PERs respect pointwise equality. *)
Corollary per_ctx_env_resp_env_eq : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ1 ρ2 ρ1' ρ2',
      env_eq ρ1 ρ2 ->
      env_eq ρ1' ρ2' ->
      Dom ρ1 ≈ ρ1' ∈ R ->
      Dom ρ2 ≈ ρ2' ∈ R.
Proof.
  intros * H * Heq Heq'; apply (per_ctx_env_resp_agree H); apply env_eq_agree_upto; assumption.
Qed.

#[local] Instance per_ctx_env_Proper {Γ Δ R} (H : EF Γ ≈ Δ ∈ per_ctx_env ↘ R) :
  Proper (env_eq ==> env_eq ==> iff) R.
Proof.
  intros ρ1 ρ2 Heq ρ1' ρ2' Heq'.
  split; intros; eapply per_ctx_env_resp_env_eq;
    try eassumption; symmetry; eassumption.
Qed.

(** Cumulativity on [per_univ], along the order of indices. *)
Corollary per_univ_cumu_universe_index : forall {u v a a'},
    universe_index_le u v ->
    Dom a ≈ a' ∈ per_univ u ->
    Dom a ≈ a' ∈ per_univ v.
Proof. intros * ? [R ?]; eexists; eapply per_univ_elem_cumu_universe_index; eassumption. Qed.

(** The universe at an index is in every universe above it, at either tier,
    with its own relevant elements as the relation. *)
Lemma per_univ_elem_universe_index_value : forall u i,
    universe_index_lt u i ->
    DF universe_index_value u ≈ universe_index_value u ∈ per_univ_elem i ↘ per_universe_elements (per_univ u).
Proof.
  intros [n | n] * Hlt; cbn.
  - (** The small universe at [n] is the one at the literal level [n], whose
        realiser is [n]. *)
    assert (Hr : domain_level_real (d_lvl n nil) = n) by apply domain_level_real_lit.
    apply per_univ_elem_core_suniv'; rewrite ?Hr;
      [ apply per_lvl_lit | assumption | reflexivity ].
  - apply per_univ_elem_core_univ'; solve [ assumption | reflexivity ].
Qed.

(** * Context PERs Relate Environments Holding Their Proofs

    The environments a context PER relates hold the proof [⋆ᵈ], as a term
    entry, at each entry whose type is a proposition ([env_proofs]): the
    condition under which the identity and the weakenings evaluate, at the
    context, to the environment itself ([eval_sub_id], [eval_sub_of_wk]). *)

(** A proposition's elements are the proof alone. *)
Lemma per_univ_elem_propositional : forall i R a a',
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    domain_kind a = ak_propositional ->
    R <~> per_proof.
Proof.
  intros * H Hr.
  basic_invert_per_univ_elem H; try assumption.
  all: try solve [ cbn in Hr; discriminate Hr ].
  all: congruence.
Qed.

(** The head relation of an extension at a type whose value at a tail
    pointwise equal to the left one is a proposition is the proof's, and
    so it is at the right one. *)
Lemma per_ctx_head_propositional_left : forall Γ Γ' tail_rel i A A'
    (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain) ρ ρ' (Ht : Dom ρ ≈ ρ' ∈ tail_rel) E a,
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel ->
    (forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    env_agree_upto (List.length Γ) E ρ -> ⟦ A ⟧ E ↘ a -> domain_kind a = ak_propositional ->
    head_rel Ht <~> per_proof.
Proof.
  intros * HΓ HT HE Ea Hp.
  assert (HE' : Dom E ≈ ρ' ∈ tail_rel) by (eapply per_ctx_env_resp_agree; [ exact HΓ | symmetry; exact HE | reflexivity | exact Ht ]).
  destruct (HT _ _ HE') as [a1 b1 Ea1 Eb1 R1].
  destruct (HT _ _ Ht) as [a0 b0 Ea0 Eb0 R0].
  functional_eval_rewrite_clear.
  pose proof (per_univ_elem_kind _ _ _ _ R1) as Hr1.
  pose proof (per_univ_elem_kind _ _ _ _ R0) as Hr0.
  eapply per_univ_elem_propositional; [ exact R0 | congruence ].
Qed.

Lemma per_ctx_head_propositional_right : forall Γ Γ' tail_rel i A A'
    (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain) ρ ρ' (Ht : Dom ρ ≈ ρ' ∈ tail_rel) E a',
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel ->
    (forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    env_agree_upto (List.length Γ') E ρ' -> ⟦ A' ⟧ E ↘ a' -> domain_kind a' = ak_propositional ->
    head_rel Ht <~> per_proof.
Proof.
  intros * HΓ HT HE Ea Hp.
  assert (HE' : Dom ρ ≈ E ∈ tail_rel)
    by (eapply per_ctx_env_resp_agree; [ exact HΓ | reflexivity | rewrite (per_ctx_env_length HΓ); symmetry; exact HE | exact Ht ]).
  destruct (HT _ _ HE') as [a1 b1 Ea1 Eb1 R1].
  destruct (HT _ _ Ht) as [a0 b0 Ea0 Eb0 R0].
  functional_eval_rewrite_clear.
  pose proof (per_univ_elem_kind _ _ _ _ R1) as Hr1.
  eapply per_univ_elem_propositional; [ exact R0 | congruence ].
Qed.

(** A type of an extension is a proposition at a tail when it is one at a
    pointwise equal environment, on either side. *)
Lemma rel_typ_propositional_env_eq_left : forall Γ Γ' tail_rel i A A'
    (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain) ρ ρ' E a,
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel ->
    (forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    Dom ρ ≈ ρ' ∈ tail_rel ->
    env_agree_upto (List.length Γ) E ρ -> ⟦ A ⟧ E ↘ a -> domain_kind a = ak_propositional ->
    rel_typ_propositional A ρ.
Proof.
  intros * HΓ HT Ht HE Ea Hp.
  assert (HE' : Dom E ≈ ρ' ∈ tail_rel) by (eapply per_ctx_env_resp_agree; [ exact HΓ | symmetry; exact HE | reflexivity | exact Ht ]).
  exact (rel_typ_propositional_left (HT _ _ Ht) (rel_typ_propositional_right (HT _ _ HE') (ex_intro _ a (conj Ea Hp)))).
Qed.

Lemma rel_typ_propositional_env_eq_right : forall Γ Γ' tail_rel i A A'
    (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain) ρ ρ' E a',
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel ->
    (forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    Dom ρ ≈ ρ' ∈ tail_rel ->
    env_agree_upto (List.length Γ') E ρ' -> ⟦ A' ⟧ E ↘ a' -> domain_kind a' = ak_propositional ->
    rel_typ_propositional A' ρ'.
Proof.
  intros * HΓ HT Ht HE Ea Hp.
  assert (HE' : Dom ρ ≈ E ∈ tail_rel)
    by (eapply per_ctx_env_resp_agree; [ exact HΓ | reflexivity | rewrite (per_ctx_env_length HΓ); symmetry; exact HE | exact Ht ]).
  exact (rel_typ_propositional_right (HT _ _ Ht) (rel_typ_propositional_left (HT _ _ HE') (ex_intro _ a' (conj Ea Hp)))).
Qed.

(** The tail after the head is the drop. *)
Lemma skipn_one_drop : forall ρ : env, List.skipn 1 ρ = ρ↯.
Proof. intros [| d ρ]; reflexivity. Qed.

(** Two contexts a context PER relates have the same propositional
    entries, read at related environments: the types at each entry are
    related, so of one sort. *)
Lemma per_ctx_env_props_cross : forall Γ Γ' R,
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R ->
      forall x, entry_propositional gc_deps gc_stack Γ ρ x -> entry_propositional gc_deps gc_stack Γ' ρ' x.
Proof.
  induction 1; intros ρ ρ' Hρ x Hx; apply_relation_equivalence.
  (** At an entry with a type, the head is read off the type's relation
      and the deeper entries off the tails'. *)
  2-3,5: match goal with
         | Hρ : per_ctx_env_cons_rel _ _ _ _ _ _ |- _ => destruct Hρ as [Ht _ _ _]
         | Hρ : per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ |- _ => destruct Hρ as [Ht _ _ _ _]
         | Hρ : per_ctx_env_dm_rel _ _ _ _ _ _ _ _ _ _ |- _ => destruct Hρ as [Ht _ _ _ _ _ _]
         end;
         (destruct x as [| x];
          [ destruct Hx as [T HT E HE a Ea Hp]; cbn in HT; injection HT as <-; rewrite skipn_one_drop in HE;
            pose proof (per_ctx_env_resp_agree equiv_Γ_Γ' _ _ _ _ (symmetry HE) (reflexivity _) Ht) as HE';
            match goal with
            | HT0 : forall ρ ρ' (e : _), rel_typ _ _ ρ _ ρ' _ |- _ =>
                destruct (rel_typ_propositional_right (HT0 _ _ HE') (ex_intro _ a (conj Ea Hp))) as (a' & Ea' & Hp')
            end;
            eapply mk_entry_propositional with (entry_propositional_env := ρ'↯);
              [ reflexivity | intros y _; rewrite ?skipn_one_drop; reflexivity | exact Ea' | exact Hp' ]
          | apply (proj2 (entry_propositional_succ _ _ _ _));
            exact (IHper_ctx_env _ _ Ht x (proj1 (entry_propositional_succ _ _ _ _) Hx)) ]).
  - destruct Hx as [T HT]; unfold ctx_entry_type in HT; destruct x; discriminate.
  - destruct Hρ as [Ht _].
    destruct x as [| x]; [ destruct Hx as [T HT]; discriminate HT |].
    apply (proj2 (entry_propositional_succ _ _ _ _)).
    exact (IHper_ctx_env _ _ Ht x (proj1 (entry_propositional_succ _ _ _ _) Hx)).
Qed.

(** * Readability of Kept Proofs over Related Environments *)

(** The entries of the environments a context PER relates read back, on
    the context's entries: each head does ([head_readable] fields). *)
Lemma per_ctx_env_entries_readable : forall Γ Γ' R, EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> forall x, x < List.length Γ ->
      entry_readable (env_entry ρ x) /\ entry_readable (env_entry ρ' x).
Proof.
  induction 1; intros ρ ρ' Hρ x Hx; cbn [List.length] in Hx; [ lia | .. ].
  all: apply_relation_equivalence; destruct Hρ; unfold head_readable in *; destruct_all;
    destruct x as [| x]; [ split; assumption |].
  all: change (env_entry ρ (S x)) with (env_entry ρ↯ x); change (env_entry ρ' (S x)) with (env_entry ρ'↯ x).
  all: apply IHper_ctx_env; [ assumption | lia ].
Qed.

(** The lets of an environment whose entries below [k] read back, at [k]
    positions and any length. *)
Lemma read_lets_of_entries_readable : forall ρ k, (forall x, x < k -> entry_readable (env_entry ρ x)) ->
    forall s, exists bs, Rlets ρ at k in gc_deps ⍮ gc_stack ⍮ s ↘ bs.
Proof.
  intros ρ k; induction k as [| k IH]; intros H s; [ eexists; constructor |].
  destruct (H k ltac:(lia) s) as [b Hb]; destruct (IH ltac:(intros x Hx; apply H; lia) (S s)) as [bs Hbs].
  eexists; econstructor; eassumption.
Qed.

(** The scope of a kept proof over an environment a context PER relates
    stays inside the context when the proof's free bound does: the stored
    units of the heads are scoped by their tails ([head_readable] fields).
    Stated from the position [j] on, for the recursion of
    [proof_scope_from]. *)
Lemma per_ctx_env_proof_scope_from : forall Γ Γ' R, EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> forall j n, n <= j + List.length Γ ->
      proof_scope_from ρ j n <= j + List.length Γ /\ proof_scope_from ρ' j n <= j + List.length Γ.
Proof.
  induction 1; intros ρ ρ' Hρ j n Hn; cbn [List.length] in *.
  1: split; [ destruct ρ | destruct ρ' ]; cbn [proof_scope_from]; try lia;
      destruct (Nat.ltb_spec j n); lia.
  all: apply_relation_equivalence.
  all: destruct Hρ;
    match goal with
    | Ht : Dom (drop_env ?r) ≈ (drop_env ?r') ∈ _ |- _ => rename Ht into Htail
    end.
  all: unfold head_readable in *; destruct_all.
  all: split; [ destruct ρ as [| e ρ0] | destruct ρ' as [| e ρ0] ]; cbn [proof_scope_from]; try lia;
    destruct (Nat.ltb_spec j n); try lia;
    cbn [drop_env List.tl] in *; rewrite ?env_entry_nth in *; cbn [List.nth] in *.
  (** The head widens the scope by its stored unit, scoped by the tail. *)
  all: match goal with
    | IH : forall ρ ρ', _ -> forall j n, _ -> _ /\ _ |- _ =>
        destruct (IH _ _ Htail (S j) (Nat.max n (S j + entry_unit_bound e)) ltac:(lia)) as [IH1 IH2]; lia
    end.
Qed.

(** A proof kept over an environment a context PER relates, with a free
    bound inside the context, reads back. *)
Lemma per_ctx_env_kept_proof_readable : forall Γ Γ' R M, EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    exp_free_bound M <= List.length Γ ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> proof_readable ⋆ᵈ⟨M, ρ⟩ /\ proof_readable ⋆ᵈ⟨M, ρ'⟩.
Proof.
  intros * HΓ HM ρ ρ' Hρ.
  destruct (per_ctx_env_proof_scope_from _ _ _ HΓ _ _ Hρ 0 (exp_free_bound M) HM) as [S1 S2].
  split; intros s; unfold proof_scope.
  - destruct (read_lets_of_entries_readable ρ (proof_scope_from ρ 0 (exp_free_bound M))
                (fun x Hx => proj1 (per_ctx_env_entries_readable _ _ _ HΓ _ _ Hρ x ltac:(lia))) s) as [bs Hbs].
    eexists; constructor; exact Hbs.
  - destruct (read_lets_of_entries_readable ρ' (proof_scope_from ρ' 0 (exp_free_bound M))
                (fun x Hx => proj2 (per_ctx_env_entries_readable _ _ _ HΓ _ _ Hρ x ltac:(lia))) s) as [bs Hbs].
    eexists; constructor; exact Hbs.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_ctx_subtyp_trans : mctt.
#[export] Existing Instance per_ctx_subtyp_trans_instance.
#[export] Existing Instance per_ctx_env_Proper.

#[export]
Hint Resolve per_univ_elem_universe_index_value : mctt.
