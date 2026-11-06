From Stdlib Require Import List Morphisms Morphisms_Relations RelationClasses Relation_Definitions.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Semantic Require Import RetagReadable.
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions Tactics.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

(** Context PERs are only ever determined up to [<~>] ([per_ctx_env_right_irrel]),
    so every judgment must be transportable along it.  For [rel_wk] both
    arguments are relations on environments; for the other two layers only the
    result PER is. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Add Parametric Morphism φ : (rel_wk φ)
    with signature (@relation_equivalence env) ==> (@relation_equivalence env) ==> iff as rel_wk_morphism.
Proof.
  intros R1 R1' H1 R2 R2' H2.
  split; intros [Hm H]; split; auto; intros ρ ρ' Hρ; apply H2; apply H; now apply H1.
Qed.

Add Parametric Morphism M σ ρ ρσ M' σ' ρ' ρ'σ' : (rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ')
    with signature (@relation_equivalence domain) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; try eassumption;
    (eapply rel_chain_mono; [| eassumption]); intros; now apply HRR'.
Qed.

Add Parametric Morphism Δ σ φ ρ σ' ρ' : (rel_sub Δ σ φ ρ σ' ρ')
    with signature (@relation_equivalence env) ==> iff as rel_sub_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; try eassumption;
    (eapply rel_chain_mono; [| eassumption]); intros; now apply HRR'.
Qed.

(** The four values of a type chain in [per_univ i] each come with their own
    element PER; irrelevance identifies them, giving a single [R] for the term
    chain to live in. *)
Lemma rel_exp_implies_rel_typ : forall {i : nat} {A σ ρ ρσ A' σ' ρ' ρ'σ'},
    rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i) ->
    exists R, rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R.
Proof.
  intros * H.
  destruct H as [aσ a a' a'σ' ? ? ? ? Hchain].
  simpl in Hchain.
  destruct Hchain as [[? ?] [[? ?] [? ?]]].
  handle_per_univ_elem_irrel.
  eexists; econstructor; try eassumption.
  simpl; repeat split; eassumption.
Qed.

Hint Resolve rel_exp_implies_rel_typ : mctt.

Lemma rel_typ_implies_rel_exp : forall {i : nat} {A σ ρ ρσ A' σ' ρ' ρ'σ' R},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i).
Proof.
  intros * H.
  destruct H as [aσ a a' a'σ' ? ? ? ? Hchain].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption].
  intros; eexists; eassumption.
Qed.

Hint Resolve rel_typ_implies_rel_exp : mctt.

(** The element PER of a type chain is a PER, which is the precondition of every
    [rel_chain] lemma applied to the term chain. *)
Lemma rel_typ_elem_PER : forall {i : nat} {A σ ρ ρσ A' σ' ρ' ρ'σ' R},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    PER R.
Proof.
  intros * H.
  destruct H as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain.
  destruct Hchain as [? [? ?]].
  eauto using per_elem_PER.
Qed.

Hint Resolve rel_typ_elem_PER : mctt.

(** * Semantic Weakenings

    All three lemmas concern the bare [rel_wk], the form the proofs use: the two
    context witnesses of [rel_wk_under_ctx] are carried by whatever produced them.
    Each holds because [eval_wk] is a function and the corresponding equation for
    [⟪_⟫] ([eval_wk_id], [eval_wk_shift], [eval_wk_compose]) holds by
    [reflexivity], which is what fails for substitutions. *)

(** [⟪wk_id⟫ ρ] is [ρ], so this is the identity. *)
Lemma rel_wk_id : forall R, rel_wk wk_id R R.
Proof.
  intros R; split; [ apply wk_mono_id |]; intros ρ ρ' H; rewrite !eval_wk_id; exact H.
Qed.

Hint Resolve rel_wk_id : mctt.

(** A weakening acts contravariantly on environments, so the
    composite [φ ⊙ ψ] — [ψ] after [φ] on variables — is [φ] after [ψ] here. *)
Lemma rel_wk_compose : forall {φ ψ R R' R''},
    rel_wk ψ R R' ->
    rel_wk φ R' R'' ->
    rel_wk (φ ⊙ ψ) R R''.
Proof.
  intros * [Hψm Hψ] [Hφm Hφ]; split; [ apply wk_mono_compose; assumption |].
  intros ρ ρ' H; rewrite !eval_wk_compose by assumption.
  exact (Hφ _ _ (Hψ _ _ H)).
Qed.

(** [⟪↑⟫ ρ] is [ρ↯], and the Ctx-Ext biconditional says precisely
    that an environment of an extended context has a related tail.  This holds
    for an assumption entry and a definition entry alike. *)
Lemma rel_wk_shift : forall {Γ e R R'},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R' ->
    rel_wk ↑ R' R.
Proof.
  intros * HΓ HΓA; split; [ apply wk_mono_shift |]; intros ρ ρ' H; rewrite !eval_wk_shift.
  inversion HΓA; subst; handle_per_ctx_env_irrel;
    apply_relation_equivalence; destruct_conjs; destruct_cons_rels; destruct_def_rels; destruct_dm_rels; destruct_mod_rels;
    eassumption.
Qed.

(** The tail of an extended context, with [rel_wk_shift] for it.  Inverting
    the extension rule produces the tail PER, so unlike [rel_wk_shift] this needs
    no externally supplied witness for [Γ]; this is what allows
    [rel_sub_under_ctx_shift] its premise. *)
Corollary rel_wk_shift_tail : forall {Γ e R},
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    exists R', EF Γ ≈ Γ ∈ per_ctx_env ↘ R' /\ rel_wk ↑ R R'.
Proof.
  intros * H.
  inversion H; subst;
    (eexists; split; [ eassumption | eapply rel_wk_shift; eassumption ]).
Qed.

(** The introduction rule of [Γ ⊨ʷ φ : Δ], packaging its components.
    Kripke-style premises provide a [rel_wk] together with the two context PERs
    it connects, not the judgment itself, so each substitution case needs this
    step. *)
Lemma rel_wk_under_ctx_intro : forall {Γ Δ φ R R'},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
    rel_wk φ R R' ->
    (forall x, x < List.length Δ -> φ x < List.length Γ) ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> forall x, x < List.length Δ ->
        entry_propositional gc_deps gc_stack Γ ρ (φ x) <-> entry_propositional gc_deps gc_stack Δ (⟪φ⟫ ρ) x) ->
    Γ ⊨ʷ φ : Δ.
Proof.
  intros * ? ? ? ? ?.
  eexists_rel_wk; eassumption.
Qed.

(** Semantic weakenings compose. *)
Lemma rel_wk_under_ctx_compose : forall Γ Δ Θ' φ ψ,
    Γ ⊨ʷ ψ : Δ -> Δ ⊨ʷ φ : Θ' -> Γ ⊨ʷ (wk_compose φ ψ) : Θ'.
Proof.
  intros * [R1 H1 R2 H2 Hψ Bψ Pψ] [R3 H3 R4 H4 Hφ Bφ Pφ].
  assert (E : R2 <~> R3) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hφ' : rel_wk φ R2 R4) by (destruct Hφ as [Hm Hφ]; split; [ exact Hm | intros; apply Hφ, E; assumption ]).
  eapply rel_wk_under_ctx_intro; [ exact H1 | exact H4 | eapply rel_wk_compose; [ exact Hψ | exact Hφ' ]
                                 | intros x Hx; exact (Bψ _ (Bφ x Hx)) |].
  (** [Γ] at [ψ (φ x)] is propositional exactly when [Δ] is at [φ x], and
      so exactly when [Θ'] is at [x]. *)
  intros ρ ρ' Hρ x Hx.
  pose proof Hψ as [Hψm Hψr]; pose proof Hφ' as [Hφm _].
  pose proof (Hψr _ _ Hρ) as Hρψ.
  rewrite eval_wk_compose by (first [ exact Hψm | exact Hφm ]).
  exact (iff_trans (Pψ _ _ Hρ (φ x) (Bφ x Hx)) (Pφ _ _ (proj1 (E _ _) Hρψ) x Hx)).
Qed.

(** The propositional entries of an extended context's tail are those of
    the context, one index up: [↑] and [wk_id] take them along. *)
Lemma entry_propositional_shift_wk : forall e Γ ρ x,
    entry_propositional gc_deps gc_stack (e :: Γ) ρ (↑ x) <-> entry_propositional gc_deps gc_stack Γ (⟪↑⟫ ρ) x.
Proof. intros *; rewrite eval_wk_shift; exact (entry_propositional_succ _ _ _ _). Qed.

Lemma entry_propositional_id_wk : forall Γ ρ x,
    entry_propositional gc_deps gc_stack Γ ρ (wk_id x) <-> entry_propositional gc_deps gc_stack Γ (⟪wk_id⟫ ρ) x.
Proof. intros *; rewrite eval_wk_id; reflexivity. Qed.

(** ** Evaluating the Identity and the Weakenings at a Context

    The identity evaluates to the environment retagged at the context,
    and a weakening to its image retagged ([ctx_retag]): each entry is the
    corresponding entry of the environment, stored at the context's type
    and unit.  A context PER relates the retagged environments as it
    relates the environments ([per_ctx_env_retag]). *)

Lemma eval_sub_id_rel : forall {Γ R ρ ρ'},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ' ∈ R ->
    ⟦ Id : Γ ⟧s ρ ↘ ctx_retag Γ ρ /\ ⟦ Id : Γ ⟧s ρ' ↘ ctx_retag Γ ρ'.
Proof.
  intros * HΓ Hρ; split; apply eval_sub_id.
Qed.

Lemma eval_sub_of_wk_rel : forall {Γ R φ ρ ρ'} `{Hφ : WkMono φ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Dom ⟪φ⟫ ρ ≈ ρ' ∈ R ->
    ⟦ ι φ : Γ ⟧s ρ ↘ ctx_retag Γ (⟪φ⟫ ρ).
Proof.
  intros Γ R φ ρ ρ' Hφ HΓ Hρ; exact (eval_sub_of_wk _ _ _ (Hφ := Hφ)).
Qed.

(** A semantic weakening at both environments of a pair its source
    relation relates. *)
Lemma eval_sub_of_wk_pair : forall {Γ φ R R' ρ ρ'},
    rel_wk φ R R' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R' ->
    Dom ρ ≈ ρ' ∈ R ->
    ⟦ ι φ : Γ ⟧s ρ ↘ ctx_retag Γ (⟪φ⟫ ρ) /\ ⟦ ι φ : Γ ⟧s ρ' ↘ ctx_retag Γ (⟪φ⟫ ρ').
Proof.
  intros * Hφ HΓ Hρ; pose proof (rel_wk_mono _ _ _ Hφ) as Hm.
  split; exact (eval_sub_of_wk _ _ _ (Hφ := Hm)).
Qed.

(** The weakening [Wk] at both environments of a pair an extended context's
    PER relates. *)
Lemma eval_sub_shift_rel : forall {e Γ R ρ ρ'},
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ' ∈ R ->
    ⟦ Wk : Γ ⟧s ρ ↘ ctx_retag Γ ρ↯ /\ ⟦ Wk : Γ ⟧s ρ' ↘ ctx_retag Γ ρ'↯.
Proof.
  intros * HΓ Hρ; split; apply eval_sub_shift.
Qed.

(** [eval_sub_of_wk_rel] at the relation of a given relatedness [H] of the
    weakened environment. *)
Ltac eval_wk_at H :=
  let T := type of H in
  match T with ?R _ _ => eapply (eval_sub_of_wk_rel (R := R)); [ eassumption | exact H ] end.

#[local] Transparent eval_sub.

(** A weakened extension at a propositional head: the head is the proof,
    weakened, kept over [ρ]. *)
Lemma eval_sub_wk_extend_proof : forall e Δ σ M φ ρ ρσ,
    ⟦ sb_wk σ φ : Δ ⟧s ρ ↘ ρσ ->
    head_propositional gc_deps gc_stack e Δ ρσ ->
    ⟦ sb_wk (σ,,M) φ : e :: Δ ⟧s ρ ↘ ρσ ↦ ⋆ᵈ⟨M[φ]ʷ, ρ⟩ ⦂ centry_tag e Δ ρσ.
Proof.
  intros * H Hp [| x] Hx.
  - split; [ intros _; cbn; rewrite ctx_entry_tag_head; reflexivity
           | intros Hn; exfalso; exact (Hn (proj2 (entry_propositional_head _ _ _ _) Hp)) ].
  - cbn [List.length] in Hx.
    split; [ intros Hp'; apply (H x ltac:(lia)); exact (entry_propositional_extend_inv _ _ _ _ _ Hp')
           | intros Hn; apply (H x ltac:(lia)); intros Hp'; exact (Hn (entry_propositional_extend_intro _ _ _ _ _ Hp')) ].
Qed.

(** An evaluated extension: its tail is the tail's evaluation, and at a
    head that is no proposition the head is the term's value. *)
Lemma eval_sub_extend_inv : forall e Δ σ M ρ ρτ,
    ⟦ σ,,M : e :: Δ ⟧s ρ ↘ ρτ ->
    ⟦ σ : Δ ⟧s ρ ↘ ρτ↯ /\
      (~ entry_propositional gc_deps gc_stack (e :: Δ)%list ρτ 0 -> ⟦ M ⟧ ρ ↘ ρτ 0).
Proof.
  intros * H; split.
  - intros x Hx; rewrite env_entry_drop, (ctx_entry_tag_drop e); change (ctx_entry_unit Δ x) with (ctx_entry_unit (e :: Δ) (S x)); split.
    + intros Hp; apply (H (S x) ltac:(cbn; lia)); exact (proj2 (entry_propositional_succ _ _ _ _) Hp).
    + intros Hn; apply (H (S x) ltac:(cbn; lia)); intros Hp; exact (Hn (proj1 (entry_propositional_succ _ _ _ _) Hp)).
  - intros Hn; destruct (proj2 (H 0 ltac:(cbn; lia)) Hn) as (m0 & Hm0 & Hx); unfold env_var; rewrite Hm0; exact Hx.
Qed.

(** Evaluation at a target reads its entries' types and units only. *)
Lemma eval_sub_same_types : forall {Δ1 Δ2 σ ρ ρσ},
    (forall x, ctx_entry_type Δ1 x = ctx_entry_type Δ2 x) ->
    List.length Δ1 = List.length Δ2 ->
    (forall x, ctx_entry_unit Δ1 x = ctx_entry_unit Δ2 x) ->
    ⟦ σ : Δ1 ⟧s ρ ↘ ρσ ->
    ⟦ σ : Δ2 ⟧s ρ ↘ ρσ.
Proof.
  intros * Ht Hl Hu H x Hx.
  assert (Etag : ctx_entry_tag Δ1 x ρσ = ctx_entry_tag Δ2 x ρσ)
    by (unfold ctx_entry_tag; rewrite Ht, !List.length_skipn, Hl; reflexivity).
  rewrite <- Etag, <- (Hu x).
  assert (Hsk : forall n, List.length (List.skipn n Δ1) = List.length (List.skipn n Δ2))
    by (intros n; rewrite !List.length_skipn, Hl; reflexivity).
  assert (I : entry_propositional gc_deps gc_stack Δ2 ρσ x <-> entry_propositional gc_deps gc_stack Δ1 ρσ x).
  { split; intros [T HT E HE a Ea Hp]; econstructor; try eassumption;
      first [ rewrite Ht; eassumption | rewrite <- Ht; eassumption | rewrite Hsk; eassumption | rewrite <- Hsk; eassumption ]. }
  rewrite I; exact (H x ltac:(rewrite Hl; exact Hx)).
Qed.

(** An evaluated lifting: its tail is that of the weakened substitution,
    and at a head that is no proposition the head is the environment's. *)
Lemma eval_sub_q_inv : forall e Δ σ ρ ρq,
    ⟦ q σ : e :: Δ ⟧s ρ ↘ ρq ->
    ⟦ sb_wk σ ↑ : Δ ⟧s ρ ↘ ρq↯ /\
      (~ entry_propositional gc_deps gc_stack (e :: Δ)%list ρq 0 ->
         env_entry ρq 0 = retag_entry (ctx_entry_tag (e :: Δ) 0 ρq) (ctx_entry_unit (e :: Δ) 0) (env_entry ρ 0)).
Proof.
  intros * H; split.
  - intros x Hx; rewrite env_entry_drop, (ctx_entry_tag_drop e); change (ctx_entry_unit Δ x) with (ctx_entry_unit (e :: Δ) (S x)); split.
    + intros Hp; apply (H (S x) ltac:(cbn; lia)); exact (proj2 (entry_propositional_succ _ _ _ _) Hp).
    + intros Hn; apply (H (S x) ltac:(cbn; lia)); intros Hp; exact (Hn (proj1 (entry_propositional_succ _ _ _ _) Hp)).
  - intros Hn; exact (proj2 (H 0 ltac:(cbn; lia)) Hn).
Qed.
#[local] Opaque eval_sub.

(** The head relation of a type whose value is a proposition relates any
    two proofs that read back. *)
Lemma per_head_proof : forall {S S' ρ ρ' a v v'},
    ⟦ S ⟧ ρ ↘ a ->
    domain_kind a = ak_propositional ->
    proof_readable v -> proof_readable v' ->
    Dom v ≈ v' ∈ per_head S S' ρ ρ'.
Proof.
  intros * Ha Hr Hv Hv'; hnf; intros i R a0 a0' Ha0 Ha0' HR.
  functional_eval_rewrite_clear.
  apply (per_univ_elem_propositional _ _ _ _ HR Hr); split; assumption.
Qed.

(** At an environment a context PER relates, an entry of a type whose
    values the PER's pairs relate is a proposition exactly when its value
    there is.  The entry reads its type up to pointwise equality of
    environments, which the context PER respects. *)
Lemma head_propositional_iff : forall {Δ R e A i ρ ρ' a},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R ->
    ctx_entry_type (e :: nil) 0 = Some A ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    Dom ρ ≈ ρ' ∈ R ->
    ⟦ A ⟧ ρ ↘ a ->
    head_propositional gc_deps gc_stack e Δ ρ <-> domain_kind a = ak_propositional.
Proof.
  intros * HΔ He HA Hρ Ha.
  assert (He' : ctx_entry_type (e :: Δ) 0 = Some A) by exact He.
  split.
  - intros [T HT E HE v Ev Hv]; rewrite He' in HT; injection HT as <-.
    cbn [List.skipn] in HE.
    assert (HE' : Dom E ≈ ρ' ∈ R)
      by (eapply per_ctx_env_resp_agree; [ exact HΔ | symmetry; exact HE | reflexivity | exact Hρ ]).
    destruct (HA _ _ HE') as (a1 & a1' & Ea1 & Ea1' & [R1 H1]).
    destruct (HA _ _ Hρ) as (a2 & a2' & Ea2 & Ea2' & [R2 H2]).
    functional_eval_rewrite_clear.
    pose proof (per_univ_elem_kind _ _ _ _ H1).
    pose proof (per_univ_elem_kind _ _ _ _ H2).
    congruence.
  - intros Hr; econstructor; [ exact He' | intros y _; reflexivity | exact Ha | exact Hr ].
Qed.

(** The same, negated, for a value of an evaluated kind. *)
Corollary head_not_propositional : forall {Δ R e A i ρ ρ' a},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R ->
    ctx_entry_type (e :: nil) 0 = Some A ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    Dom ρ ≈ ρ' ∈ R ->
    ⟦ A ⟧ ρ ↘ a ->
    evaluated_kind (domain_kind a) ->
    ~ head_propositional gc_deps gc_stack e Δ ρ.
Proof.
  intros * HΔ He HA Hρ Ha Hr Hp.
  apply (head_propositional_iff HΔ He HA Hρ Ha) in Hp; exact (evaluated_kind_not_propositional _ Hr Hp).
Qed.

(** The same at the right environment of the pair. *)
Corollary head_propositional_iff_right : forall {Δ R e A i ρ ρ' a'},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R ->
    ctx_entry_type (e :: nil) 0 = Some A ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    Dom ρ ≈ ρ' ∈ R ->
    ⟦ A ⟧ ρ' ↘ a' ->
    head_propositional gc_deps gc_stack e Δ ρ' <-> domain_kind a' = ak_propositional.
Proof.
  intros * HΔ He HA Hρ Ha.
  assert (PER R) by (eapply per_env_PER; eassumption).
  assert (Hρ' : Dom ρ' ≈ ρ' ∈ R) by (etransitivity; [ symmetry |]; exact Hρ).
  exact (head_propositional_iff HΔ He HA Hρ' Ha).
Qed.

(** Related environments agree on whether such an entry is a
    proposition. *)
Corollary head_propositional_pair : forall {Δ R e A i ρ ρ'},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R ->
    ctx_entry_type (e :: nil) 0 = Some A ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    Dom ρ ≈ ρ' ∈ R ->
    head_propositional gc_deps gc_stack e Δ ρ <-> head_propositional gc_deps gc_stack e Δ ρ'.
Proof.
  intros * HΔ He HA Hρ.
  destruct (HA _ _ Hρ) as (a & a' & Ea & Ea' & [R0 H0]).
  pose proof (head_propositional_iff HΔ He HA Hρ Ea) as I1.
  pose proof (head_propositional_iff_right HΔ He HA Hρ Ea') as I2.
  pose proof (per_univ_elem_kind _ _ _ _ H0) as E.
  rewrite I1, I2, E; reflexivity.
Qed.

(** The first entry of [e :: Δ] is a proposition in [ρ] exactly when [e]
    is one in the tail. *)
Lemma entry_propositional_zero_head : forall e Δ ρ,
    entry_propositional gc_deps gc_stack (e :: Δ)%list ρ 0 <-> head_propositional gc_deps gc_stack e Δ ρ↯.
Proof.
  intros; split; intros [T HT E HE v Ev Hv]; econstructor; try eassumption;
    intros y Hy; rewrite (HE y Hy); cbn [List.skipn]; rewrite ?skipn_one_drop; reflexivity.
Qed.

(** A head of a type that a context PER's type premise relates is a
    proposition exactly when the type's value in the tail is one. *)
Lemma head_propositional_of_rel_typ : forall {Δ R e A i} (hr : forall ρ ρ', R ρ ρ' -> relation domain) ρ ρ',
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R -> ctx_entry_type (e :: nil) 0 = Some A ->
    (forall ρ0 ρ'0 (H0 : R ρ0 ρ'0), PER.Definitions.rel_typ i A ρ0 A ρ'0 (hr ρ0 ρ'0 H0)) ->
    R ρ ρ' ->
    head_propositional gc_deps gc_stack e Δ ρ <-> rel_typ_propositional A ρ.
Proof.
  intros * HΔ He Hrt Hρ.
  assert (HAs : forall ρ0 ρ'0, R ρ0 ρ'0 ->
            exists a a', ⟦ A ⟧ ρ0 ↘ a /\ ⟦ A ⟧ ρ'0 ↘ a' /\ Dom a ≈ a' ∈ per_univ i)
    by (intros ρ0 ρ'0 H0; destruct (Hrt _ _ H0) as [b b' Eb Eb' Hb];
        exists b, b'; repeat split; [ exact Eb | exact Eb' | eexists; exact Hb ]).
  destruct (Hrt _ _ Hρ) as [a a' Ea Ea' Ha].
  rewrite (head_propositional_iff HΔ He HAs Hρ Ea).
  split; [ intros Hp; exists a; split; assumption | intros (a0 & Ea0 & Hp); functional_eval_rewrite_clear; exact Hp ].
Qed.

(** At an environment a context PER relates, an entry is a proposition
    exactly when its type is one in the environment's tail after it: the
    entry reads its type up to pointwise equality of environments, which
    the context PER respects. *)
Lemma entry_propositional_local : forall Γ R ρ ρ' x T,
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R -> ctx_entry_type Γ x = Some T ->
    entry_propositional gc_deps gc_stack Γ ρ x <-> rel_typ_propositional T (List.skipn (S x) ρ).
Proof.
  induction Γ as [| e Γ IH]; intros * HΓ Hρ HT; [ destruct x; discriminate HT |].
  inversion HΓ; subst; handle_per_ctx_env_irrel; apply_relation_equivalence; destruct_conjs;
    destruct_cons_rels; destruct_def_rels; destruct_dm_rels; destruct_mod_rels.
  all: destruct x as [| y].
  all: try (cbn in HT; discriminate HT).
  all: try (rewrite entry_propositional_succ; cbn [ctx_entry_type List.nth_error] in HT;
            replace (List.skipn (S (S y)) ρ) with (List.skipn (S y) ρ↯) by (destruct ρ; reflexivity);
            eapply IH; eassumption).
  all: cbn in HT; injection HT as <-; rewrite entry_propositional_zero_head.
  all: change (List.skipn 1 ρ) with ρ↯.
  all: eapply head_propositional_of_rel_typ; [ eassumption | reflexivity | eassumption | eassumption ].
Qed.

(** Environments a context PER relates agree on which entries are
    propositions: the entries' types are related at their tails. *)
Lemma entry_propositional_rel : forall Γ R ρ ρ' x,
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R ->
    entry_propositional gc_deps gc_stack Γ ρ x <-> entry_propositional gc_deps gc_stack Γ ρ' x.
Proof.
  induction Γ as [| e Γ IH]; intros * HΓ Hρ.
  { split; intros [T HT]; destruct x; discriminate HT. }
  inversion HΓ; subst; handle_per_ctx_env_irrel; apply_relation_equivalence; destruct_conjs;
    destruct_cons_rels; destruct_def_rels; destruct_dm_rels; destruct_mod_rels.
  all: destruct x as [| y]; [| rewrite !entry_propositional_succ; eapply IH; eassumption ].
  all: rewrite !entry_propositional_zero_head.
  all: try solve [ split; intros [T HT]; discriminate HT ].
  all: eapply head_propositional_pair; [ eassumption | reflexivity | | eassumption ].
  all: intros ρ0 ρ0' H0'; match goal with Hrt : forall ρ ρ' (_ : _ ρ ρ'), PER.Definitions.rel_typ _ _ _ _ _ _ |- _ =>
         destruct (Hrt _ _ H0') as [b b' Eb Eb' Hb]; exists b, b'; repeat split; [ exact Eb | exact Eb' | eexists; exact Hb ] end.
Qed.

(** An entry of the retagging of an environment a context PER relates is
    a proposition exactly when the entry of the environment is. *)
Corollary entry_propositional_ctx_retag : forall Γ R ρ ρ' x,
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R ->
    entry_propositional gc_deps gc_stack Γ (ctx_retag Γ ρ) x <-> entry_propositional gc_deps gc_stack Γ ρ x.
Proof.
  intros * HΓ Hρ.
  assert (PER R) by (eapply per_env_PER; eassumption).
  assert (Hρρ : Dom ρ ≈ ρ ∈ R) by (etransitivity; [| symmetry ]; exact Hρ).
  exact (entry_propositional_rel _ _ _ _ x HΓ (per_ctx_env_retag_left HΓ _ _ Hρρ)).
Qed.

(** The same at a semantic weakening, at an environment its source PER
    relates. *)
Lemma eval_sub_wk_pre_rel : forall {Δ Δ' φ σ ρ ρσ ρσ'},
    Δ ⊨ʷ φ : Δ' ->
    forall R, EF Δ ≈ Δ ∈ per_ctx_env ↘ R ->
    Dom ρσ ≈ ρσ' ∈ R ->
    ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
    ⟦ (ι φ) ⨟ σ : Δ' ⟧s ρ ↘ ctx_retag Δ' (⟪φ⟫ ρσ).
Proof.
  intros * [R1 HΔ R2 HΔ' Hφ Hl Hc] R HR Hρ H.
  assert (E : R <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E in Hρ.
  pose proof (rel_wk_mono _ _ _ Hφ) as Hm.
  apply (eval_sub_wk_pre _ _ _ _ _ _ H Hl); intros x Hx.
  rewrite (entry_propositional_ctx_retag _ _ _ _ x HΔ' (Hφ _ _ Hρ)); symmetry; exact (Hc _ _ Hρ x Hx).
Qed.

(** * Reading a Context PER off [⊨ Γ]

    [rel_ctx_wf] stores the witness in the extension rule, so there is nothing to
    reconstruct. *)

Lemma rel_ctx_wf_per_ctx_env : forall {Γ},
    ⊨ Γ ->
    exists R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R.
Proof.
  induction 1; [| eexists; eassumption .. ].
  eexists; econstructor; apply Equivalence_Reflexive.
Qed.

Hint Resolve rel_ctx_wf_per_ctx_env : mctt.

Corollary rel_ctx_wf_per_ctx : forall {Γ},
    ⊨ Γ ->
    ⊨ Γ ≈ Γ.
Proof.
  intros * H. apply rel_ctx_wf_per_ctx_env in H. exact H.
Qed.

Hint Resolve rel_ctx_wf_per_ctx : mctt.

(** * Semantic Weakenings are Semantic Substitutions

    The degenerate four-value pattern.  Both commutation obligations are
    discharged by [eval_sub_of_wk] alone, because [sb_wk (ι ψ) φ] is
    [ι (ψ ⊙ φ)] and [⟪ψ ⊙ φ⟫ ρ] is [⟪ψ⟫ (⟪φ⟫ ρ)] by conversion: a weakening
    substitutes only variables, and a variable carries no environment into a
    closure.  So the four values are the same two, and [rel_chain_4_of_2]
    finishes. *)

(** Only the weakening's two context PERs, its relation and its bound are
    used: the weakening evaluates at any environment ([eval_sub_of_wk]). *)
Lemma rel_sub_of_wk_rel : forall {Δ ψ Γ env_relΔ env_relΓ},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    rel_wk ψ env_relΔ env_relΓ ->
    (forall x, x < List.length Γ -> ψ x < List.length Δ) ->
    Δ ⊨ˢ (ι ψ) ≈ (ι ψ) : Γ.
Proof.
  intros * HΔ HΓ [Hψm Hψ] Hψb.
  eexists_rel_sub; [| intros x Hx; cbn; split; apply Hψb; exact Hx ].
  intros Γ' env_rel' HΓ' φ [Hφm Hφ] Hφb ρ ρ' Hρ.
  assert (Hc : WkMono (ψ ⊙ φ)) by (apply wk_mono_compose; assumption).
  assert (Hψ' : WkMono ψ) by exact Hψm.
  assert (H1 : Dom ⟪ψ⟫ (⟪φ⟫ ρ) ≈ ⟪ψ⟫ (⟪φ⟫ ρ') ∈ env_relΓ) by exact (Hψ _ _ (Hφ _ _ Hρ)).
  assert (H2 : Dom ⟪ψ⟫ (⟪φ⟫ ρ') ≈ ⟪ψ⟫ (⟪φ⟫ ρ) ∈ env_relΓ) by (symmetry; exact H1).
  apply mk_rel_sub with (ρσφ := ctx_retag Γ (⟪ψ ⊙ φ⟫ ρ)) (ρσ := ctx_retag Γ (⟪ψ⟫ (⟪φ⟫ ρ)))
                        (ρ'σ' := ctx_retag Γ (⟪ψ⟫ (⟪φ⟫ ρ'))) (ρ'σ'φ := ctx_retag Γ (⟪ψ ⊙ φ⟫ ρ')).
  - eapply (eval_sub_of_wk_rel (φ := ψ ⊙ φ)); [ exact HΓ | rewrite eval_wk_compose by assumption; exact H1 ].
  - eapply eval_sub_of_wk_rel; [ exact HΓ | exact H1 ].
  - eapply eval_sub_of_wk_rel; [ exact HΓ | exact H2 ].
  - eapply (eval_sub_of_wk_rel (φ := ψ ⊙ φ)); [ exact HΓ | rewrite eval_wk_compose by assumption; exact H2 ].
  - rewrite !eval_wk_compose by assumption.
    apply rel_chain_4_of_2; [ solve_chain_PER |].
    exact (per_ctx_env_retag HΓ _ _ H1).
Qed.

Corollary rel_sub_of_wk : forall {Δ ψ Γ},
    Δ ⊨ʷ ψ : Γ ->
    Δ ⊨ˢ (ι ψ) ≈ (ι ψ) : Γ.
Proof. intros * [env_relΔ HΔ env_relΓ HΓ Hψ Hb _]; exact (rel_sub_of_wk_rel HΔ HΓ Hψ Hb). Qed.

Corollary rel_sub_id : forall {Γ},
    ⊨ Γ ≈ Γ ->
    Γ ⊨ˢ Id ≈ Id : Γ.
Proof.
  intros * [env_relΓ HΓ].
  exact (rel_sub_of_wk_rel (ψ := wk_id) HΓ HΓ (rel_wk_id _) (fun x Hx => Hx)).
Qed.

Hint Resolve rel_sub_id : mctt.

(** The tail of a semantically well-formed context is semantically
    well-formed. *)
Lemma rel_ctx_wf_tail : forall {Γ e},
    ⊨ (e :: Γ)%list ->
    ⊨ Γ.
Proof.
  intros * H; inversion H; assumption.
Qed.

(** A context with valid slots is semantically well formed, and so is its
    tail, with valid slots. *)
Lemma valid_ctx_rel_ctx_wf : forall {Θm Ξm Γ}, valid_ctx Θm Ξm Γ -> ⊨ Γ.
Proof. intros * H; destruct H; [ constructor | assumption .. ]. Qed.

Lemma valid_ctx_tail : forall {Θm Ξm Γ e}, valid_ctx Θm Ξm (e :: Γ)%list -> valid_ctx Θm Ξm Γ.
Proof. intros * H; inversion H; assumption. Qed.

(** [⇑] as a weakening judgment — the form the weakening lemmas below, and
    soundness through them, are instantiated at. *)
Corollary rel_wk_under_ctx_shift : forall {Γ e},
    ⊨ (e :: Γ)%list ->
    (e :: Γ)%list ⊨ʷ ↑ : Γ.
Proof.
  intros * H.
  pose proof (rel_ctx_wf_per_ctx_env H) as [env_relΓA HΓA].
  pose proof (rel_ctx_wf_per_ctx_env (rel_ctx_wf_tail H)) as [env_relΓ HΓ'].
  eapply rel_wk_under_ctx_intro; try eassumption.
  - eapply rel_wk_shift; eassumption.
  - intros x Hx; cbn; lia.
  - intros ρ ρ' _ x _; apply entry_propositional_shift_wk.
Qed.

Hint Resolve rel_wk_under_ctx_shift : mctt.

(** The same, from the two context PERs. *)
Lemma rel_wk_under_ctx_shift_per : forall {Γ e R R'},
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R' ->
    (e :: Γ)%list ⊨ʷ ↑ : Γ.
Proof.
  intros * HR HR'.
  eapply rel_wk_under_ctx_intro; [ exact HR | exact HR' | eapply rel_wk_shift; eassumption | |].
  - intros x Hx; cbn; lia.
  - intros ρ ρ' _ x _; apply entry_propositional_shift_wk.
Qed.

Corollary rel_sub_shift : forall {Γ e},
    ⊨ (e :: Γ)%list ->
    (e :: Γ)%list ⊨ˢ Wk : Γ.
Proof.
  intros * H.
  apply (rel_sub_of_wk (rel_wk_under_ctx_shift H)).
Qed.

Hint Resolve rel_sub_shift : mctt.

(** * Instantiation at the Identity

    A semantic judgment quantifies over semantic substitutions; instantiating it
    at [Id] gives a two-value statement.  The Kripke quantification is
    instantiated at [wk_id] via [rel_wk_id], and [Id] evaluates to the environment
    itself ([eval_sub_id]), which the universal form of [rel_exp_under_ctx] allows
    naming as the substituted environment.  Since [M[Id]] is syntactically [M]
    ([exp_sub_id]), both commutation obligations of each chain compare a value
    with itself, and only the middle link remains.  The case files and
    [Core/Completeness.v] use these forms. *)

Lemma rel_sub_under_ctx_simple : forall {Γ Δ σ σ'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ)
       env_relΔ (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists ρσ ρ'σ',
        ⟦ σ : Δ ⟧s ρ ↘ ρσ /\
        ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' /\
        Dom ρσ ≈ ρ'σ' ∈ env_relΔ.
Proof.
  intros * [env_relΓ HΓ env_relΔ HΔ Hσ _].
  eexists_rel_sub.
  intros ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ wk_id (rel_wk_id _) (fun x Hx => Hx) _ _ Hρ) as [? ρσ ρ'σ' ? ? ? ? ? Hchain].
  rewrite !eval_wk_id in *.
  exists ρσ, ρ'σ'.
  repeat split; try eassumption.
  pairwise.
Qed.

(** The companion of [rel_exp_under_ctx_simple] for substitutions.
    [rel_sub_under_ctx] keeps the two substituted environments existential, since
    their existence is real content there, but a caller with its own evaluations
    needs to relate those.  Both forms are needed, and reconciling them is easy at
    this layer, because a context PER, unlike evaluation, respects [env_eq]
    ([per_ctx_env_Proper]). *)
(** A context PER relates any two evaluations of the substitutions at it
    when it relates one pair: evaluations of a substitution agree on the
    entries of its target ([functional_eval_sub]), which is all a context
    PER reads ([per_ctx_env_resp_agree]). *)
Lemma per_ctx_env_resp_eval_sub : forall {Δ R σ σ' ρ ρ' ρσ ρσ0 ρ'σ' ρ'σ'0},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R ->
    ⟦ σ : Δ ⟧s ρ ↘ ρσ0 -> ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
    ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ'0 -> ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
    Dom ρσ0 ≈ ρ'σ'0 ∈ R -> Dom ρσ ≈ ρ'σ' ∈ R.
Proof.
  intros * HΔ H0 H H0' H' Hr.
  exact (per_ctx_env_resp_agree HΔ _ _ _ _ (functional_eval_sub _ _ _ _ _ H0 H) (functional_eval_sub _ _ _ _ _ H0' H') Hr).
Qed.

(** Two evaluations of one substitution are related when either is related
    to itself. *)
Corollary per_ctx_env_eval_sub_link : forall {Δ R σ ρ ρσ1 ρσ2},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R ->
    ⟦ σ : Δ ⟧s ρ ↘ ρσ1 -> ⟦ σ : Δ ⟧s ρ ↘ ρσ2 ->
    Dom ρσ2 ≈ ρσ2 ∈ R -> Dom ρσ1 ≈ ρσ2 ∈ R.
Proof. intros * HΔ H1 H2 Hr; exact (per_ctx_env_resp_eval_sub HΔ H2 H1 H2 H2 Hr). Qed.

Lemma rel_sub_under_ctx_at : forall {Γ Δ σ σ'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ)
       env_relΔ (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ),
    forall ρ ρ' ρσ ρ'σ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      Dom ρσ ≈ ρ'σ' ∈ env_relΔ.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_simple H) as [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  eexists_rel_sub.
  intros ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (Hσ _ _ Hρ) as [ρσ0 [ρ'σ'0 [Hev0 [Hev'0 Hrel]]]].
  exact (per_ctx_env_resp_eval_sub HΔ Hev0 Hev Hev'0 Hev' Hrel).
Qed.

(** The same at the caller's own context PERs, the form every case file uses.
    Taking the two witnesses as arguments confines [handle_per_ctx_env_irrel],
    which renames hypotheses and so breaks proof scripts that mention them later,
    to this proof. *)
Corollary rel_sub_under_ctx_at' : forall {Γ Δ σ σ' env_relΓ env_relΔ},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    forall ρ ρ' ρσ ρ'σ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      Dom ρσ ≈ ρ'σ' ∈ env_relΔ.
Proof.
  intros * H ? ? * ? ? ?.
  pose proof (rel_sub_under_ctx_at H) as [? [? [? [? Hat]]]].
  handle_per_ctx_env_irrel.
  eapply Hat; eassumption.
Qed.

Lemma rel_exp_under_ctx_simple : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) (i : nat),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a' R,
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A ⟧ ρ' ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem i ↘ R /\
        (domain_kind a = ak_propositional \/
         exists m m',
           ⟦ M ⟧ ρ ↘ m /\
           ⟦ M' ⟧ ρ' ↘ m' /\
           Dom m ≈ m' ∈ R).
Proof.
  intros * [env_relΓ HΓ i HM].
  eexists_rel_exp_with i.
  intros ρ ρ' Hρ.
  destruct (eval_sub_id_rel HΓ Hρ) as [Hid Hid'].
  destruct (HM _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ Hid Hid')
    as [R [Htyp Hexp]].
  (** The outer values: [A[Id]] is [A], at the environments themselves.
      The inner ones are at their retaggings. *)
  destruct Htyp as [aσ a a' a'σ' Haσ ? ? Ha'σ' Htychain].
  rewrite exp_sub_id in Haσ, Ha'σ'.
  exists aσ, a'σ', R.
  assert (DF aσ ≈ a'σ' ∈ per_univ_elem i ↘ R) by pairwise.
  repeat split; try eassumption.
  destruct Hexp as [(a0 & Ha0 & Hp) | [mσ m m' m'σ' Hmσ ? ? Hm'σ' Hmchain]].
  - left.
    rewrite exp_sub_id in Ha0.
    assert (a0 = aσ) as -> by (eapply functional_eval_exp; eassumption).
    exact Hp.
  - right; exists mσ, m'σ'.
    rewrite exp_sub_id in Hmσ, Hm'σ'.
    repeat split; try eassumption.
    pairwise.
Qed.

(** ** Instances at Retagged Environments

    A substitution of variables ([Id], a weakening, [Wk]) evaluates to the
    environment it reads retagged at its target ([eval_sub_id],
    [ctx_retag]): an instance of a judgment along it has its inner values
    at the retaggings.  The [Id] instance at the environments themselves
    has the same inner values, and its outer values are at the
    environments, so the two chains merge there.  These two lemmas read a
    judgment's body at a substitution whose results are retaggings, with
    the inner values at the environments retagged, for example [⟪φ⟫ ρ]
    for [ι φ] at [ρ]. *)
Lemma rel_exp_body_of_retagged : forall {Γ T M M' RΓ} {i : nat},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    (forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ R' -> ⟦ σ : Γ ⟧s ρ ↘ ρσ -> ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          exists R, rel_typ i T σ ρ ρσ T σ' ρ' ρ'σ' R /\
            (type_propositional T σ ρ \/ rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' R)) ->
    forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ R' ->
        ⟦ σ : Γ ⟧s ρ ↘ ctx_retag Γ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ctx_retag Γ ρ'σ' ->
        Dom ρσ ≈ ρ'σ' ∈ RΓ ->
        exists R, rel_typ i T σ ρ ρσ T σ' ρ' ρ'σ' R /\
          (type_propositional T σ ρ \/ rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' R).
Proof.
  intros * HΓ HM * HΓ' * Hσ * Hρ Hev Hev' Hρσ.
  destruct (HM _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R1 [Ht1 He1]].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid Hid'].
  destruct (HM _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρσ Hid Hid') as [R2 [Ht2 He2]].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hac].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbc].
  rewrite exp_sub_id in Hb1, Hb4.
  assert (b2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hmid1 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hmid2 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  assert (Hty : rel_chain (per_univ_elem i R1) ([a1; b1; b4; a4])) by merge_rel_chain Hac Hbc a2.
  exists R1; split; [ apply (mk_rel_exp a1 b1 b4 a4); assumption |].
  destruct He1 as [Hp | [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hc1]]; [ left; exact Hp |].
  destruct He2 as [(c & Hc & Hp) | [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hc2]].
  { left; exists a1; split; [ exact Ha1 |].
    rewrite exp_sub_id in Hc.
    assert (c = b1) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hab : DF a1 ≈ b1 ∈ per_univ_elem i ↘ R1) by pairwise.
    rewrite (per_univ_elem_kind _ _ _ _ Hab); exact Hp. }
  rewrite exp_sub_id in Hw1, Hw4.
  assert (w2 = v2) as -> by (eapply functional_eval_exp; eassumption).
  assert (w3 = v3) as -> by (eapply functional_eval_exp; eassumption).
  right; apply (mk_rel_exp v1 w1 w4 v4); try eassumption.
  merge_rel_chain Hc1 Hc2 v2.
Qed.

(** For type judgments, at any PER of type values ([per_univ i], or the
    elements of a universe). *)
Lemma rel_type_body_of_retagged : forall {Γ T T' RΓ} {P : relation domain} `{HP : PER domain P},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    (forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ R' -> ⟦ σ : Γ ⟧s ρ ↘ ρσ -> ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          rel_exp T σ ρ ρσ T' σ' ρ' ρ'σ' P) ->
    forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ R' ->
        ⟦ σ : Γ ⟧s ρ ↘ ctx_retag Γ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ctx_retag Γ ρ'σ' ->
        Dom ρσ ≈ ρ'σ' ∈ RΓ ->
        rel_exp T σ ρ ρσ T' σ' ρ' ρ'σ' P.
Proof.
  intros * HP HΓ HT * HΓ' * Hσ * Hρ Hev Hev' Hρσ.
  destruct (HT _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hac].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid Hid'].
  destruct (HT _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρσ Hid Hid') as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbc].
  rewrite exp_sub_id in Hb1, Hb4.
  assert (b2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  apply (mk_rel_exp a1 b1 b4 a4); try eassumption.
  merge_rel_chain Hac Hbc a2.
Qed.

(** The same with the element PER replaced by the canonical head PER of the
    type, at any context PER of [Γ].  Taking the context PER as an argument
    lets several such instances be read at one relation. *)
Corollary rel_exp_under_ctx_simple_at : forall {Γ A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      rel_typ_propositional A ρ \/
      exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A A ρ ρ'.
Proof.
  intros * HΓ H.
  pose proof (rel_exp_under_ctx_simple H) as [env_relΓ' [HΓ' [i HM]]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E.
  destruct (HM _ _ Hρ) as [a [a' [R [Ha [Ha' [HR [Hp | [m [m' [Hm [Hm' Hmm']]]]]]]]]]].
  - left; exists a; split; assumption.
  - right; exists m, m'; repeat split; try eassumption.
    eapply per_head_of; eassumption.
Qed.

(** The value of the type [A] in [ρ] is of an evaluated kind: a type of a
    universe or a type of levels, not a proposition. *)
Definition rel_typ_evaluated (A : exp) (ρ : env) : Prop :=
  exists a, ⟦ A ⟧ ρ ↘ a /\ evaluated_kind (domain_kind a).

(** A type of an evaluated kind is of an evaluated kind. *)
Lemma rel_typ_evaluated_of_kind : forall {A ρ κ}, rel_typ_kind A ρ κ -> evaluated_kind κ -> rel_typ_evaluated A ρ.
Proof. intros * (a & Ea & <-) Hκ; exists a; split; assumption. Qed.

(** A valid term at related environments where its type is of an
    evaluated kind: its values, related at the type's head. *)
Corollary rel_exp_under_ctx_simple_at_evaluated : forall {Γ A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ -> Γ ⊨ M ≈ M' : A ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_evaluated A ρ ->
      exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A A ρ ρ'.
Proof.
  intros * HΓ HM ρ ρ' Hρ (a & Ea & Hr).
  destruct (rel_exp_under_ctx_simple_at HΓ HM _ _ Hρ) as [(a0 & Ea0 & Hp) | H]; [| exact H ].
  exfalso; assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  exact (evaluated_kind_not_propositional _ Hr Hp).
Qed.

Lemma rel_subtyp_under_ctx_simple : forall {Γ A A'},
    Γ ⊨ A ⊆ A' ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) (i : nat),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a',
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ρ' ↘ a' /\
        Sub a <: a' at i.
Proof.
  intros * [env_relΓ HΓ i HA].
  eexists_subtyp_with i.
  intros ρ ρ' Hρ.
  destruct (eval_sub_id_rel HΓ Hρ) as [Hid Hid'].
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ Hid Hid')
    as [aσ a a'σ' a' HaσI ? Ha'σ'I ? Hl Hr Hsub].
  (** The inner values are at the retagged environments; the subtyping is
    transported to the outer ones, the values of [A[Id]] and [A'[Id]] at
    the environments themselves. *)
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists aσ, a'σ'.
  destruct Hl as [Rl Hl], Hr as [Rr Hr].
  repeat split; try eassumption.
  eapply per_subtyp_transp; [ exact Hsub | symmetry; exact Hl | symmetry; exact Hr ].
Qed.

(** * Precomposition with a Weakening

    Two instantiations of the same hypothesis at two weakenings.  Given
    [Γ' ⊨ʷ φ : Γ] and [ρ ≈ ρ' ∈ R_Γ'], instantiate [Δ ⊨ˢ σ ≈ σ' : Δ']:

    - at [Γ'] with the composite [ψ ⊙ φ] ([rel_wk_compose]), whose outer values
      are the outer values wanted, because [σ[ψ][φ]] is [σ[ψ ⊙ φ]] ([sb_wk_wk]);
    - at [Δ] with [ψ] and the weakened pair [⟪φ⟫ ρ ≈ ⟪φ⟫ ρ'], whose outer values
      are the inner values wanted.

    Their inner values coincide, since [⟪ψ ⊙ φ⟫ ρ] and [⟪ψ⟫ (⟪φ⟫ ρ)] are
    convertible, so both chains contain the value of [σ] at that environment.  The
    chains then merge, up to [env_eq] as in transitivity, because
    [functional_eval_sub] is all that identifies two evaluations of [σ]. *)

(** Only the weakening's two context PERs, its relation and its bound are
    used. *)
Lemma rel_sub_under_ctx_wk_rel : forall {Γ ψ Δ σ σ' Δ' env_relΓ env_relΔ2},
    Δ ⊨ˢ σ ≈ σ' : Δ' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ2 ->
    rel_wk ψ env_relΓ env_relΔ2 ->
    (forall x, x < List.length Δ -> ψ x < List.length Γ) ->
    Γ ⊨ˢ (sb_wk σ ψ) ≈ (sb_wk σ' ψ) : Δ'.
Proof.
  intros * [env_relΔ HΔ env_relΔ' HΔ' Hσ Hσs] HΓ HΔ2 Hψ Hψb.
  handle_per_ctx_env_irrel.
  eexists_rel_sub;
    [| intros x Hx; destruct (Hσs x Hx); cbn; split; eapply sentry_scoped_wk; eassumption ].
  intros Γ' env_rel' HΓ' φ Hφ Hφb ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ (rel_wk_compose Hφ Hψ) (fun x Hx => Hφb _ (Hψb x Hx)) _ _ Hρ)
    as [a1 a2 ? a4 Ha1 Ha2 ? Ha4 Ha].
  rewrite eval_wk_compose in Ha2 by (eapply rel_wk_mono; eassumption).
  destruct (Hσ _ _ HΓ _ Hψ Hψb _ _ (Hφ _ _ Hρ)) as [b1 b2 ? b4 Hb1 Hb2 ? Hb4 Hb].
  apply (mk_rel_sub a1 b1 b4 a4);
    [ rewrite sb_wk_wk; exact Ha1 | exact Hb1 | exact Hb4 | rewrite sb_wk_wk; exact Ha4 |].
  assert (Hlink : Dom a2 ≈ b2 ∈ env_relΔ').
  { assert (Hbb : Dom b2 ≈ b2 ∈ env_relΔ') by pairwise.
    exact (per_ctx_env_resp_agree HΔ' _ _ _ _ (functional_eval_sub _ _ _ _ _ Hb2 Ha2) (reflexivity _) Hbb). }
  assert (Hb' : rel_chain env_relΔ' ([b2; b1; b4])) by solve_rel_chain.
  assert (Hc : rel_chain env_relΔ' ([a2; b2; b1; b4]))
    by (apply rel_chain_cons; assumption).
  merge_rel_chain Hc Ha a2.
Qed.

Corollary rel_sub_under_ctx_wk : forall {Γ ψ Δ σ σ' Δ'},
    Δ ⊨ˢ σ ≈ σ' : Δ' ->
    Γ ⊨ʷ ψ : Δ ->
    Γ ⊨ˢ (sb_wk σ ψ) ≈ (sb_wk σ' ψ) : Δ'.
Proof.
  intros * Hσ [env_relΓ HΓ env_relΔ2 HΔ2 Hψ Hψb _].
  exact (rel_sub_under_ctx_wk_rel Hσ HΓ HΔ2 Hψ Hψb).
Qed.

(** Precomposition by a weakening, which, unlike general composition of two
    semantic substitutions, is semantic.  Nothing is instantiated twice: the four
    environments wanted are the [⟪φ⟫]-images of the four the hypothesis supplies,
    by [eval_sub_wk_pre] on the inner two and by the same lemma after
    [sb_wk_wk_pre] on the outer two.  The chain is transported member by member by
    [rel_chain_map], whose hypothesis is [rel_wk φ].

    The general case fails because [Γ'' ⊨ˢ σ ⨟ τ : Γ] would need the value of
    [(σ x)[τ]] for every index [x], a statement about terms that the substitution
    judgment does not make.  This is why the [ℕ]-elimination [β]-rule goes
    through the generic recursor. *)

Lemma rel_sub_under_ctx_wk_pre : forall {Γ Δ Δ' φ σ σ'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ʷ φ : Δ' ->
    Γ ⊨ˢ (ι φ) ⨟ σ ≈ (ι φ) ⨟ σ' : Δ'.
Proof.
  intros * [env_relΓ HΓ env_relΔ HΔ Hσ Hσs] Hφj.
  pose proof Hφj as [env_relΔ2 HΔ2 env_relΔ' HΔ' Hφ Hφb _].
  handle_per_ctx_env_irrel.
  eexists_rel_sub; [| intros x Hx; cbn; exact (Hσs _ (Hφb x Hx)) ].
  intros Γ' env_rel' HΓ' ψ Hψ Hψb ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hψ Hψb _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  pose proof (rel_chain_map _ _ (eval_wk φ) (rel_wk_app _ _ _ Hφ) _ Hchain) as Hchain'.
  simpl in Hchain'.
  (** Each of the four is an environment of [Δ], related to itself. *)
  apply (mk_rel_sub (ctx_retag Δ' (⟪φ⟫ v1)) (ctx_retag Δ' (⟪φ⟫ v2))
                    (ctx_retag Δ' (⟪φ⟫ v3)) (ctx_retag Δ' (⟪φ⟫ v4)));
    [ rewrite sb_wk_wk_pre | | | rewrite sb_wk_wk_pre | ];
    [ ..| destruct Hchain' as (C1 & C2 & C3); cbn; repeat split; apply (per_ctx_env_retag HΔ'); assumption ];
    (eapply (eval_sub_wk_pre_rel Hφj); [ eassumption | | eassumption ]); pairwise.
Qed.

(** * Semantic Weakening of a Term Judgment

    A term judgment may be weakened along [Γ ⊨ʷ φ : Δ].  The equation
    [⟦M[φ]ʷ⟧(ρ) = ⟦M⟧(⟪φ⟫ ρ)] fails (in the [λ] case the two sides are different
    closures), so the two values must be related instead, by the judgment about
    [M] instantiated twice:

    - along [ι φ ⨟ τ] at [(ρ, ρ')], whose outer values are the goal's outer ones
      ([exp_sub_wk]: [M[φ]ʷ[τ]] is [M[ι φ ⨟ τ]]);
    - along [ι φ] at [(ρτ, ρ'τ')], whose outer values are the goal's inner ones
      ([exp_sub_of_wk]: [M[ι φ]] is [M[φ]ʷ]).

    Both are read at the same pair of inner environments, [⟪φ⟫ ρτ] and
    [⟪φ⟫ ρ'τ'] (named by [eval_sub_wk_pre] and [eval_sub_of_wk] respectively), so
    their inner values coincide and the two chains merge.  This relies on the
    universal form of [rel_exp_under_ctx]: with existential environments the two
    instantiations would concern merely pointwise-equal environments, hence
    unrelated closures. *)

Lemma rel_exp_under_ctx_wk : forall {Γ Δ φ A M M'},
    Γ ⊨ʷ φ : Δ ->
    Δ ⊨ M ≈ M' : A ->
    Γ ⊨ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ.
Proof.
  intros * Hφj HM.
  pose proof Hφj as [env_relΓ HΓ env_relΔ HΔ Hφ _].
  pose proof HM as [env_relΔ2 HΔ2 i HMgen].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' τ τ' Hτj ρ ρ' ρτ ρ'τ' Hρ Hev Hev'.
  assert (Hρτ : Dom ρτ ≈ ρ'τ' ∈ env_relΓ)
    by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρτ' : Dom ρ'τ' ≈ ρτ ∈ env_relΓ) by (symmetry; exact Hρτ).
  assert (Hρτl : Dom ρτ ≈ ρτ ∈ env_relΓ) by (etransitivity; [ exact Hρτ | exact Hρτ' ]).
  assert (Hρτr : Dom ρ'τ' ≈ ρ'τ' ∈ env_relΓ) by (etransitivity; [ exact Hρτ' | exact Hρτ ]).
  pose proof (rel_wk_mono _ _ _ Hφ) as Hφm.
  (** The first instantiation is read at the retaggings of the inner
      environments, which the second one names ([eval_sub_wk_pre_rel]). *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_wk_pre Hτj Hφj) _ _ _ _ Hρ
              (eval_sub_wk_pre_rel Hφj _ HΓ Hρτl Hev)
              (eval_sub_wk_pre_rel Hφj _ HΓ Hρτr Hev'))
    as [R1 [Htyp1 Hexp1]].
  destruct (HMgen _ _ HΓ _ _ (rel_sub_of_wk Hφj) _ _ _ _ Hρτ
              ltac:(eval_wk_at (Hφ _ _ Hρτ)) ltac:(eval_wk_at (Hφ _ _ Hρτ')))
    as [R2 [Htyp2 Hexp2]].
  destruct Htyp1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Htyp2 as [b1 b2 b3 b4 Hb1 ? ? Hb4 Hty2].
  (** The two commutation obligations of each chain, read as rewritings of the
      substitution that produced it. *)
  rewrite <- exp_sub_wk in Ha1, Ha4.
  rewrite exp_sub_of_wk in Hb1, Hb4.
  functional_eval_rewrite_clear.
  (** The middle link of each type chain, which is where the two element PERs
      overlap: both are read at the same pair of inner environments. *)
  assert (Hmid1 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hmid2 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  assert (Hty : rel_chain (per_univ_elem i R1) ([a1; b1; b4; a4])) by merge_rel_chain Hty1 Hty2 a2.
  exists R1.
  split.
  - apply (mk_rel_exp a1 b1 b4 a4); try eassumption.
  - (** At a proposition, either instance says so. *)
    destruct Hexp1 as [(c & Hc & Hp) | [v1 v2 v3 v4 Hv1 ? ? Hv4 Hc1]].
    { left; exists c; split; [ rewrite exp_sub_wk; exact Hc | exact Hp ]. }
    destruct Hexp2 as [(c & Hc & Hp) | [w1 w2 w3 w4 Hw1 ? ? Hw4 Hc2]].
    { left; exists a1; split; [ exact Ha1 |].
      rewrite exp_sub_of_wk in Hc.
      assert (c = b1) as -> by (eapply functional_eval_exp; eassumption).
      assert (Hab : DF a1 ≈ b1 ∈ per_univ_elem i ↘ R1) by pairwise.
      rewrite (per_univ_elem_kind _ _ _ _ Hab); exact Hp. }
    rewrite <- exp_sub_wk in Hv1, Hv4.
    rewrite exp_sub_of_wk in Hw1, Hw4.
    functional_eval_rewrite_clear.
    right; apply (mk_rel_exp v1 w1 w4 v4); try eassumption.
    merge_rel_chain Hc1 Hc2 v2.
Qed.

(** The form the variable case of soundness uses: the failing equation
    [⟦M[φ]ʷ⟧(ρ) = ⟦M⟧(⟪φ⟫ ρ)] as a relatedness.  This is [rel_exp_under_ctx] at
    [ι φ], where both commutation obligations vanish ([exp_sub_of_wk]) and
    [eval_sub_of_wk] names both inner environments, so the wanted pair (an outer
    value against the opposite inner one) is one [pairwise] away. *)
Lemma rel_exp_under_ctx_wk_simple : forall {Γ Δ φ A M M'},
    Γ ⊨ʷ φ : Δ ->
    Δ ⊨ M ≈ M' : A ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) (i : nat),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a' R,
        ⟦ A[φ]ʷ ⟧ ρ ↘ a /\
        ⟦ A ⟧ ⟪φ⟫ ρ' ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem i ↘ R /\
        (domain_kind a = ak_propositional \/
         exists m m',
           ⟦ M[φ]ʷ ⟧ ρ ↘ m /\
           ⟦ M' ⟧ ⟪φ⟫ ρ' ↘ m' /\
           Dom m ≈ m' ∈ R).
Proof.
  intros * Hφj HM.
  pose proof Hφj as [env_relΓ HΓ env_relΔ HΔ Hφ _].
  pose proof HM as [env_relΔ2 HΔ2 i HMgen].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros ρ ρ' Hρ.
  pose proof (rel_wk_mono _ _ _ Hφ) as Hφm.
  assert (Hρ' : Dom ρ' ≈ ρ ∈ env_relΓ) by (symmetry; exact Hρ).
  destruct (HMgen _ _ HΓ _ _ (rel_sub_of_wk Hφj) _ _ _ _ Hρ
              ltac:(eval_wk_at (Hφ _ _ Hρ)) ltac:(eval_wk_at (Hφ _ _ Hρ'))) as [R [Htyp Hexp]].
  destruct Htyp as [a1 a2 a3 a4 Ha1 ? Ha3 ? Hty].
  rewrite exp_sub_of_wk in Ha1.
  (** The type pair first: it puts [per_univ_elem i R] in context, which is what
      resolves the [PER R] obligation of the element pair. *)
  assert (Hmid : DF a1 ≈ a3 ∈ per_univ_elem i ↘ R) by pairwise.
  (** The inner values are at the retaggings of [⟪φ⟫ ρ] and [⟪φ⟫ ρ'].
      The judgment read at the retagging of [⟪φ⟫ ρ] against [⟪φ⟫ ρ']
      itself, related by [per_ctx_env_retag_left], bridges the first
      inner values to the values wanted. *)
  assert (HΔk : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ) by eassumption.
  pose proof (per_ctx_env_retag_left HΔk _ _ (Hφ _ _ Hρ)) as Hrφρ.
  destruct (rel_exp_under_ctx_simple HM) as [env_relΔ3 [HΔ3 [i3 HMs]]].
  assert (E3 : env_relΔ <~> env_relΔ3) by (eapply per_ctx_env_right_irrel; [ exact HΔk | exact HΔ3 ]).
  destruct (HMs _ _ (proj1 (E3 _ _) Hrφρ)) as (b & b' & R3 & Hb & Hb' & HR3 & Hbr).
  assert (b = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (H12 : DF a1 ≈ a2 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (H22 : DF a2 ≈ a2 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (E : R3 <~> R) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR3 H22).
  exists a1, b', R.
  assert (Hab' : DF a1 ≈ b' ∈ per_univ_elem i ↘ R).
  { eapply per_univ_trans; [ exact H12 | eapply per_univ_elem_resp_iff; [ exact HR3 | exact E ] ]. }
  repeat split; try eassumption.
  destruct Hexp as [(c & Hc & Hp) | [v1 v2 v3 v4 Hv1 Hv2 Hv3 ? Hc]].
  - left; rewrite exp_sub_of_wk in Hc.
    assert (c = a1) as -> by (eapply functional_eval_exp; eassumption).
    exact Hp.
  - rewrite exp_sub_of_wk in Hv1.
    destruct Hbr as [Hp | (w & w' & Hw & Hw' & Hww')].
    { left; rewrite (per_univ_elem_kind _ _ _ _ H12); exact Hp. }
    right.
    assert (w = v2) as -> by (eapply functional_eval_exp; eassumption).
    exists v1, w'.
    repeat split; try eassumption.
    assert (PER R) by (eapply per_elem_PER; exact Hmid).
    apply E in Hww'.
    assert (Hv12 : Dom v1 ≈ v2 ∈ R) by pairwise.
    etransitivity; eassumption.
Qed.

(** * Precomposition by [⇑]

    Nothing is instantiated twice: once dropped, the four values of the hypothesis
    are the four values wanted.  Two facts do the work, each the [⇑] case of
    something that fails in general:

    - [eval_sub_shift_pre]: [⟦⇑ ⨟ σ⟧(ρ)] is [⟦σ⟧(ρ)↯], because [⇑] substitutes
      only variables (and [sb_wk_shift_pre] says postcomposition by [φ] slides
      past, so the same holds of the two [φ]-weakened values);
    - [rel_wk_shift_tail]: the Ctx-Ext biconditional, which says that dropping
      takes [R_{Δ ▹ A}] to [R_Δ].

    The second is a [rel_wk], the hypothesis of [rel_chain_map], so the chain is
    transported along the drop member by member. *)

Lemma rel_sub_under_ctx_shift : forall {Γ Δ e σ σ'},
    Γ ⊨ˢ σ ≈ σ' : (e :: Δ)%list ->
    Γ ⊨ˢ Wk ⨟ σ ≈ Wk ⨟ σ' : Δ.
Proof.
  intros * [env_relΓ HΓ env_relΔA HΔA Hσ Hσs].
  pose proof (rel_wk_shift_tail HΔA) as [env_relΔ [HΔ Hdrop]].
  eexists_rel_sub; [| intros x Hx; cbn; apply Hσs; cbn; lia ].
  intros Γ' env_rel' HΓ' φ Hφ Hφb ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hφ Hφb _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  assert (Hdrop' : forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔA -> Dom ρ↯ ≈ ρ'↯ ∈ env_relΔ)
    by (intros; rewrite <- !eval_wk_shift; apply Hdrop; assumption).
  pose proof (rel_chain_map _ _ drop_env Hdrop' _ Hchain) as Hchain'.
  simpl in Hchain'.
  apply (mk_rel_sub v1↯ v2↯ v3↯ v4↯);
    [ rewrite sb_wk_shift_pre | | | rewrite sb_wk_shift_pre |];
    try (eapply eval_sub_shift_pre; eassumption).
  exact Hchain'.
Qed.

(** * Symmetry

    The four values of the symmetric judgment are the same four in the opposite
    order, so symmetry is [rel_chain_4_sym]. *)

Lemma rel_exp_sym : forall {M σ ρ ρσ M' σ' ρ' ρ'σ' R},
    PER R ->
    rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' R ->
    rel_exp M' σ' ρ' ρ'σ' M σ ρ ρσ R.
Proof.
  intros * ? [].
  econstructor; try eassumption.
  now apply rel_chain_4_sym.
Qed.

(** The four values of a type chain are of one sort: if one is a
    proposition, all are. *)
Lemma rel_typ_prop_any : forall {i A σ ρ ρσ A' σ' ρ' ρ'σ' R},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    (rel_typ_propositional A[σ] ρ \/ rel_typ_propositional A ρσ \/
       rel_typ_propositional A' ρ'σ' \/ rel_typ_propositional A'[σ'] ρ') ->
    rel_typ_propositional A[σ] ρ /\ rel_typ_propositional A ρσ /\
      rel_typ_propositional A' ρ'σ' /\ rel_typ_propositional A'[σ'] ρ'.
Proof.
  intros * [a1 a2 a3 a4 E1 E2 E3 E4 Hc] Hp.
  assert (H12 : DF a1 ≈ a2 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (H23 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R) by pairwise.
  assert (H34 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ R) by pairwise.
  pose proof (per_univ_elem_kind _ _ _ _ H12).
  pose proof (per_univ_elem_kind _ _ _ _ H23).
  pose proof (per_univ_elem_kind _ _ _ _ H34).
  assert (Hr : domain_kind a1 = ak_propositional).
  { destruct Hp as [(c & Ec & Hp) | [(c & Ec & Hp) | [(c & Ec & Hp) | (c & Ec & Hp)]]];
      functional_eval_rewrite_clear; congruence. }
  repeat split; eexists; (split; [ eassumption | congruence ]).
Qed.

(** A term judgment's disjunct, symmetric: the propositional case moves
    along the type chain. *)
Lemma rel_exp_or_prop_sym : forall {i A σ ρ ρσ σ' ρ' ρ'σ' R M M'},
    rel_typ i A σ ρ ρσ A σ' ρ' ρ'σ' R ->
    type_propositional A σ ρ \/ rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' R ->
    type_propositional A σ' ρ' \/ rel_exp M' σ' ρ' ρ'σ' M σ ρ ρσ R.
Proof.
  intros * HT [Hp | HM].
  - left; exact (proj2 (proj2 (proj2 (rel_typ_prop_any HT (or_introl Hp))))).
  - right; apply rel_exp_sym; [ eauto using rel_typ_elem_PER | exact HM ].
Qed.

(** At a type of an evaluated kind at the inner left environment, a term
    judgment's disjunct is its relation. *)
Lemma rel_exp_or_prop_evaluated : forall {i A σ ρ ρσ A' σ' ρ' ρ'σ' R} {P : Prop},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    rel_typ_evaluated A ρσ ->
    type_propositional A σ ρ \/ P ->
    P.
Proof.
  intros * HT (a & Ea & Hr) [Hp | HP]; [| exact HP ].
  destruct (proj1 (proj2 (rel_typ_prop_any HT (or_introl Hp)))) as (a' & Ea' & Hp').
  functional_eval_rewrite_clear; exfalso; exact (evaluated_kind_not_propositional _ Hr Hp').
Qed.

Lemma rel_sub_sym : forall {Δ σ φ ρ σ' ρ' R},
    PER R ->
    rel_sub Δ σ φ ρ σ' ρ' R ->
    rel_sub Δ σ' φ ρ' σ ρ R.
Proof.
  intros * ? [].
  econstructor; try eassumption.
  now apply rel_chain_4_sym.
Qed.

Lemma rel_sub_under_ctx_sym : forall {Γ Δ σ σ'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Γ ⊨ˢ σ' ≈ σ : Δ.
Proof.
  intros * [env_relΓ HΓ env_relΔ HΔ Hσ Hσs].
  eexists_rel_sub; [| intros x Hx; destruct (Hσs x Hx); split; assumption ].
  intros Γ' env_rel' HΓ' φ Hφ Hφb ρ ρ' Hρ.
  apply rel_sub_sym; [ solve_chain_PER |].
  apply (Hσ _ _ HΓ' _ Hφ Hφb).
  symmetry; eassumption.
Qed.

(** Instantiate the hypothesis at the swapped substitution pair and the swapped
    environment pair; both chains come out reversed, and reversing them again is
    [rel_exp_sym].  The universal form of [rel_exp_under_ctx] makes the swap
    possible: the caller's two evaluations serve, read in the other order. *)
Lemma rel_exp_under_ctx_sym : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ M' ≈ M : A.
Proof.
  intros * [env_relΓ HΓ i HM].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρ' : Dom ρ' ≈ ρ ∈ env_rel') by (symmetry; eassumption).
  destruct (HM _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ _ _ _ Hρ' Hev' Hev)
    as [R [Htyp Hexp]].
  exists R.
  split; [ apply rel_exp_sym; first [ eassumption | solve_chain_PER ] | exact (rel_exp_or_prop_sym Htyp Hexp) ].
Qed.

(** * Transitivity

    Two four-value chains, sharing the value both sides evaluate [σ2[φ]] to.  It
    is shared only up to [env_eq] ([functional_eval_sub] determines an evaluated
    substitution no further), hence [per_ctx_env_resp_env_eq]; with that link
    prefixed the two chains overlap, [rel_chain_merge] joins them, and
    [rel_chain_incl] selects the four values wanted. *)

Lemma rel_sub_under_ctx_trans : forall {Γ Δ σ1 σ2 σ3},
    Γ ⊨ˢ σ1 ≈ σ2 : Δ ->
    Γ ⊨ˢ σ2 ≈ σ3 : Δ ->
    Γ ⊨ˢ σ1 ≈ σ3 : Δ.
Proof.
  intros * [env_relΓ HΓ env_relΔ HΔ H12 H12s] H23'.
  pose proof H23' as [env_relΓ2 HΓ2 env_relΔ2 HΔ2 H23 H23s].
  handle_per_ctx_env_irrel.
  eexists_rel_sub; [| intros x Hx; destruct (H12s x Hx), (H23s x Hx); split; assumption ].
  intros Γ' env_rel' HΓ' φ Hφ Hφb ρ ρ' Hρ.
  assert (Hρ' : Dom ρ' ≈ ρ' ∈ env_rel')
    by (etransitivity; [ symmetry | ]; eassumption).
  destruct (H12 _ _ HΓ' _ Hφ Hφb _ _ Hρ) as [ρσ1φ ρσ1 ρ'σ2 ρ'σ2φ ? ? ? Hev2 Ha].
  destruct (H23 _ _ HΓ' _ Hφ Hφb _ _ Hρ') as [ρ'σ2φb ρ'σ2b ρ'σ3 ρ'σ3φ Hev2b ? ? ? Hb].
  econstructor; try eassumption.
  assert (Hlink : Dom ρ'σ2φ ≈ ρ'σ2φb ∈ env_relΔ)
    by (eapply per_ctx_env_eval_sub_link; [ eassumption | eassumption | eassumption | pairwise ]).
  assert (Hc : rel_chain env_relΔ ([ρ'σ2φ; ρ'σ2φb; ρ'σ2b; ρ'σ3; ρ'σ3φ]))
    by (apply rel_chain_cons; assumption).
  merge_rel_chain Ha Hc ρ'σ2φ.
Qed.

(** The reflexive instances of a substitution judgment.  The substitution
    cases and [rel_exp_under_ctx_trans] instantiate a second judgment at one side
    of a given substitution pair; symmetry and transitivity supply these. *)

Corollary rel_sub_under_ctx_refl_left : forall {Γ Δ σ σ'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Γ ⊨ˢ σ : Δ.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_sym H).
  eapply rel_sub_under_ctx_trans; eassumption.
Qed.

Corollary rel_sub_under_ctx_refl_right : forall {Γ Δ σ σ'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Γ ⊨ˢ σ' : Δ.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_sym H).
  eapply rel_sub_under_ctx_trans; eassumption.
Qed.

(** Two four-value chains, this time sharing values exactly.  The second
    judgment is instantiated at the reflexive right-hand substitution [σ'] and the
    reflexive right-hand environment pair [ρ' ≈ ρ'], with the caller's [ρ'σ']
    named on both sides, so its first two values are [⟦M2[σ']⟧(ρ')] and
    [⟦M2⟧(ρ'σ')], the last two of the first chain.  With existential environments
    they would only be values of [M2] at [env_eq]-related environments, and the
    chains would not join.

    The two element PERs are identified through the type chains, which overlap in
    [⟦A⟧(ρ'σ')]; irrelevance is cross-level, so the two judgments' universe levels
    need not agree. *)

Lemma rel_exp_under_ctx_trans : forall {Γ A M1 M2 M3},
    Γ ⊨ M1 ≈ M2 : A ->
    Γ ⊨ M2 ≈ M3 : A ->
    Γ ⊨ M1 ≈ M3 : A.
Proof.
  intros * [env_relΓ HΓ i H12] H23'.
  pose proof H23' as [env_relΓ2 HΓ2 j H23].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρ' : Dom ρ' ≈ ρ' ∈ env_rel')
    by (etransitivity; [ symmetry | ]; eassumption).
  destruct (H12 _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R1 [Htyp1 Hexp1]].
  destruct (H23 _ _ HΓ' _ _ (rel_sub_under_ctx_refl_right Hσ) _ _ _ _ Hρ' Hev' Hev')
    as [R2 [Htyp2 Hexp2]].
  (** At a proposition, the first judgment says so, or the second does at
      the right-hand side, which the first's type chain carries back. *)
  assert (Hprop : type_propositional A σ' ρ' -> type_propositional A σ ρ)
    by (intros Hp; exact (proj1 (rel_typ_prop_any Htyp1 (or_intror (or_intror (or_intror Hp)))))).
  destruct Htyp1 as [aσ a a' a'σ' ? ? ? ? Hty1].
  destruct Htyp2 as [b'σ' b' b'' b''σ' ? ? ? ? Hty2].
  functional_eval_rewrite_clear.
  simpl in Hty1, Hty2.
  destruct Hty1 as [? [? ?]], Hty2 as [? [? ?]].
  handle_per_univ_elem_irrel.
  exists R1.
  split.
  - econstructor; try eassumption.
    simpl; repeat split; eassumption.
  - destruct Hexp1 as [Hp | [v1 v2 v3 v4 ? ? ? ? Hc1]]; [ left; exact Hp |].
    destruct Hexp2 as [Hp | [w1 w2 w3 w4 ? ? ? ? Hc2]]; [ left; exact (Hprop Hp) |].
    functional_eval_rewrite_clear.
    right; econstructor; try eassumption.
    merge_rel_chain Hc1 Hc2 v3.
Qed.

(** The term-level reflexive instances.  The substitution cases use one to
    bridge the values of a term at two different environments. *)

Corollary rel_exp_under_ctx_refl_left : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ M : A.
Proof.
  intros * H.
  pose proof (rel_exp_under_ctx_sym H).
  eapply rel_exp_under_ctx_trans; eassumption.
Qed.

Corollary rel_exp_under_ctx_refl_right : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ M' : A.
Proof.
  intros * H.
  pose proof (rel_exp_under_ctx_sym H).
  eapply rel_exp_under_ctx_trans; eassumption.
Qed.

(** * Changing the Context PER

    A substitution judgment may be read with a smaller domain relation or a
    larger codomain relation, and a term judgment in any context whose
    relation is included in that of its own context.  This is how a judgment
    about [Γ ▹ A] serves for [Γ ▸ A ≔ M], and a judgment about [Γ ▸ A ≔ M] for
    [Γ ▸ A ≔ M'] when [M] and [M'] are related.  As evaluation is directed by
    the target, the larger codomain and the smaller one are to agree on
    which of the smaller one's entries are propositional
    ([ctx_props_agree]): each is, in practice, a context of the same entry
    types, or a prefix of it. *)

(** The entries of [Δ2], at the environments [S] relates, are propositional
    entries of [Δ1] exactly when they are of [Δ2]: an evaluation at [Δ1]
    holds a kept proof at the one and a value at the other, as an
    evaluation at [Δ2] asks. *)
Definition ctx_props_agree (S : relation env) (Δ1 Δ2 : ctx) : Prop :=
  forall ρ ρ', Dom ρ ≈ ρ' ∈ S -> forall x, x < List.length Δ2 ->
    entry_propositional gc_deps gc_stack Δ1 ρ x <-> entry_propositional gc_deps gc_stack Δ2 ρ x.

(** Contexts of the same entry types have the same propositional entries. *)
Lemma ctx_props_agree_same_types : forall S Δ1 Δ2,
    List.length Δ1 = List.length Δ2 ->
    (forall x, ctx_entry_type Δ1 x = ctx_entry_type Δ2 x) -> ctx_props_agree S Δ1 Δ2.
Proof.
  intros * Hl Ht ρ ρ' _ x _; split; intros [T HT E HE a Ea Hp].
  - econstructor; [ rewrite <- Ht; exact HT | | exact Ea | exact Hp ].
    rewrite List.length_skipn, <- Hl, <- List.length_skipn; exact HE.
  - econstructor; [ rewrite Ht; exact HT | | exact Ea | exact Hp ].
    rewrite List.length_skipn, Hl, <- List.length_skipn; exact HE.
Qed.

(** A context's propositional entries among the first ones are those of the
    prefix, at the environments both context PERs relate: each reads its
    type at the environment's tail ([entry_propositional_local]). *)
Lemma ctx_props_agree_app : forall S S' Δ Γ,
    EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ S -> EF Δ ≈ Δ ∈ per_ctx_env ↘ S' ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ S -> Dom ρ ≈ ρ' ∈ S') -> ctx_props_agree S (Δ ++ Γ) Δ.
Proof.
  intros * HS HS' Hsub ρ ρ' Hρ x Hx.
  assert (Hlk : ctx_entry_type (Δ ++ Γ) x = ctx_entry_type Δ x)
    by (unfold ctx_entry_type; rewrite List.nth_error_app1 by exact Hx; reflexivity).
  destruct (ctx_entry_type Δ x) as [T |] eqn:HT.
  - rewrite (entry_propositional_local _ _ _ _ _ _ HS Hρ Hlk), (entry_propositional_local _ _ _ _ _ _ HS' (Hsub _ _ Hρ) HT).
    reflexivity.
  - split; intros [T' HT' _ _ _ _ _]; congruence.
Qed.

(** Two contexts a context PER relates have the same propositional
    entries at the environments it relates. *)
Lemma ctx_props_agree_of_per : forall Γ1 Γ2 R, EF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R -> ctx_props_agree R Γ1 Γ2.
Proof.
  intros * HR ρ ρ' Hρ x _.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : Dom ρ ≈ ρ ∈ R) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (per_ctx_env_sym _ _ _ HR) as [HR' _].
  split; [ exact (per_ctx_env_props_cross _ _ _ HR _ _ Hρρ x) | exact (per_ctx_env_props_cross _ _ _ HR' _ _ Hρρ x) ].
Qed.

(** The identity from a context to a prefix of it, when the context's
    relation is included in the prefix's: past the prefix nothing is asked
    of the environments. *)
Lemma rel_wk_under_ctx_drop : forall {Γ Δ R R'},
    EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R') ->
    Δ ++ Γ ⊨ʷ wk_id : Δ.
Proof.
  intros * HR HR' Hsub.
  eapply rel_wk_under_ctx_intro;
    [ exact HR | exact HR' | split; [ typeclasses eauto | intros ρ ρ' Hρ; rewrite !eval_wk_id; exact (Hsub _ _ Hρ) ] | |].
  - intros x Hx; rewrite List.length_app; unfold wk_id; lia.
  - intros ρ ρ' Hρ x Hx; rewrite eval_wk_id; exact (ctx_props_agree_app _ _ Δ Γ HR HR' Hsub ρ ρ' Hρ x Hx).
Qed.

(** An evaluation at [Δ1] gives one at [Δ2], to the environment retagged
    at [Δ2], when the entries of [Δ2] are propositional in [Δ1] exactly
    when they are in [Δ2] at the retagging. *)
#[local] Transparent eval_sub.
Lemma eval_sub_change_target : forall {Δ1 Δ2 σ ρ ρσ},
    ⟦ σ : Δ1 ⟧s ρ ↘ ρσ ->
    List.length Δ2 <= List.length Δ1 ->
    (forall x, x < List.length Δ2 ->
       entry_propositional gc_deps gc_stack Δ1 ρσ x <-> entry_propositional gc_deps gc_stack Δ2 (ctx_retag Δ2 ρσ) x) ->
    ⟦ σ : Δ2 ⟧s ρ ↘ ctx_retag Δ2 ρσ.
Proof.
  intros * H Hl Hc x Hx; rewrite (env_entry_ctx_retag _ _ _ Hx); split.
  - intros Hp; apply eval_sentry_proof_retag with (t := ctx_entry_tag Δ1 x ρσ) (U := ctx_entry_unit Δ1 x).
    apply (H x ltac:(lia)); exact (proj2 (Hc _ Hx) Hp).
  - intros Hn; apply eval_sentry_retag with (t := ctx_entry_tag Δ1 x ρσ) (U := ctx_entry_unit Δ1 x).
    apply (H x ltac:(lia)); intros Hp'; exact (Hn (proj1 (Hc _ Hx) Hp')).
Qed.
#[local] Opaque eval_sub.

(** The same, at an environment the context PERs of [Δ1] and [Δ2] relate,
    from [ctx_props_agree]. *)
Corollary eval_sub_change_target_rel : forall {Δ1 Δ2 S1 S2 σ ρ ρσ ρσ'},
    EF Δ2 ≈ Δ2 ∈ per_ctx_env ↘ S2 ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ S1 -> Dom ρ ≈ ρ' ∈ S2) ->
    List.length Δ2 <= List.length Δ1 ->
    ctx_props_agree S1 Δ1 Δ2 ->
    Dom ρσ ≈ ρσ' ∈ S1 ->
    ⟦ σ : Δ1 ⟧s ρ ↘ ρσ ->
    ⟦ σ : Δ2 ⟧s ρ ↘ ctx_retag Δ2 ρσ.
Proof.
  intros * HΔ2 HS Hl Hc Hv Hτ.
  apply (eval_sub_change_target Hτ Hl); intros x Hx.
  rewrite (entry_propositional_ctx_retag _ _ _ _ x HΔ2 (HS _ _ Hv)); exact (Hc _ _ Hv x Hx).
Qed.

Lemma rel_sub_under_ctx_restrict : forall {Γ1 Γ2 Δ1 Δ2 σ σ' R1 R2 S1 S2},
    EF Γ1 ≈ Γ1 ∈ per_ctx_env ↘ R1 ->
    EF Γ2 ≈ Γ2 ∈ per_ctx_env ↘ R2 ->
    EF Δ1 ≈ Δ1 ∈ per_ctx_env ↘ S1 ->
    EF Δ2 ≈ Δ2 ∈ per_ctx_env ↘ S2 ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R1 -> Dom ρ ≈ ρ' ∈ R2) ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ S1 -> Dom ρ ≈ ρ' ∈ S2) ->
    List.length Δ2 <= List.length Δ1 ->
    List.length Γ2 <= List.length Γ1 ->
    ctx_props_agree S1 Δ1 Δ2 ->
    Γ2 ⊨ˢ σ ≈ σ' : Δ1 ->
    Γ1 ⊨ˢ σ ≈ σ' : Δ2.
Proof.
  intros * HΓ1 HΓ2 HΔ1 HΔ2 HR HS Hl HlΓ Hc [R2' HΓ2' S1' HΔ1' Hσ Hσs].
  assert (ER : R2' <~> R2) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (ES : S1' <~> S1) by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_sub_under_ctx _ _ _ _ R1 HΓ1 S2 HΔ2 _ _);
    [| intros x Hx; destruct (Hσs x ltac:(lia)); split; eapply sentry_scoped_mono; eassumption ].
  intros Γ' env_rel' HΓ' φ [Hφm Hφ] Hφb ρ ρ' Hρ.
  assert (Hφ' : rel_wk φ env_rel' R2')
    by (split; [ assumption | intros; apply ER, HR, Hφ; assumption ]).
  destruct (Hσ _ _ HΓ' _ Hφ' (fun x Hx => Hφb x ltac:(lia)) _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  (** Each of the four is an environment of [Δ1]; retagged, of [Δ2]. *)
  assert (Hch : rel_chain S1 ([v1; v2; v3; v4]))
    by (eapply rel_chain_mono; [| eassumption ]; intros; apply ES; assumption).
  assert (Hch2 : rel_chain S2 ([v1; v2; v3; v4]))
    by (eapply rel_chain_mono; [| exact Hch ]; intros; apply HS; assumption).
  apply (mk_rel_sub (ctx_retag Δ2 v1) (ctx_retag Δ2 v2) (ctx_retag Δ2 v3) (ctx_retag Δ2 v4));
    [ ..| destruct Hch2 as (C1 & C2 & C3); cbn; repeat split; apply (per_ctx_env_retag HΔ2); assumption ];
    (eapply (eval_sub_change_target_rel HΔ2 HS Hl Hc); [| eassumption ]); pairwise.
Qed.

(** A term judgment at [Γ2] is one at a [Γ1] whose relation is included
    in [Γ2]'s: its instance at the environments retagged at [Γ2] is read
    at the environments themselves ([rel_exp_body_of_retagged]). *)

Lemma rel_exp_under_ctx_restrict : forall {Γ1 Γ2 R1 R2 A M M'},
    EF Γ1 ≈ Γ1 ∈ per_ctx_env ↘ R1 ->
    EF Γ2 ≈ Γ2 ∈ per_ctx_env ↘ R2 ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R1 -> Dom ρ ≈ ρ' ∈ R2) ->
    List.length Γ2 <= List.length Γ1 ->
    ctx_props_agree R1 Γ1 Γ2 ->
    Γ2 ⊨ M ≈ M' : A ->
    Γ1 ⊨ M ≈ M' : A.
Proof.
  intros * HΓ1 HΓ2 HR Hl Hc [R2' HΓ2' i HM].
  assert (ER : R2' <~> R2) by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_exp_under_ctx _ _ _ _ R1 HΓ1 i _).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ R1) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρσ' : Dom ρ'σ' ≈ ρσ ∈ R1) by (symmetry; exact Hρσ).
  apply (rel_exp_body_of_retagged HΓ2' HM _ _ HΓ').
  - eapply rel_sub_under_ctx_restrict; [ eassumption | eassumption | exact HΓ1 | exact HΓ2 | | exact HR | exact Hl | exact (le_n _) | exact Hc | exact Hσ ].
    auto.
  - exact Hρ.
  - exact (eval_sub_change_target_rel HΓ2 HR Hl Hc Hρσ Hev).
  - exact (eval_sub_change_target_rel HΓ2 HR Hl Hc Hρσ' Hev').
  - apply ER, HR; exact Hρσ.
Qed.

(** Type judgments likewise. *)
Lemma rel_type_under_ctx_restrict : forall {Γ1 Γ2 R1 R2 A A'} {i : nat},
    EF Γ1 ≈ Γ1 ∈ per_ctx_env ↘ R1 ->
    EF Γ2 ≈ Γ2 ∈ per_ctx_env ↘ R2 ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R1 -> Dom ρ ≈ ρ' ∈ R2) ->
    List.length Γ2 <= List.length Γ1 ->
    ctx_props_agree R1 Γ1 Γ2 ->
    Γ2 ⊨ᵗ A ≈ A' at i ->
    Γ1 ⊨ᵗ A ≈ A' at i.
Proof.
  intros * HΓ1 HΓ2 HR Hl Hc [R2' HΓ2' HA HAn].
  assert (ER : R2' <~> R2) by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_type_under_ctx _ _ _ _ R1 HΓ1 _ _);
    [| (** The environments of [Γ1] are environments of [Γ2]. *)
       intros R HR0 ρ ρ' Hρ;
       assert (E1 : R <~> R1) by (eapply per_ctx_env_right_irrel; eassumption);
       exact (HAn _ HΓ2 ρ ρ' (HR _ _ (proj1 (E1 _ _) Hρ))) ].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ R1) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρσ' : Dom ρ'σ' ≈ ρσ ∈ R1) by (symmetry; exact Hρσ).
  apply (rel_type_body_of_retagged HΓ2' HA _ _ HΓ').
  - eapply rel_sub_under_ctx_restrict; [ eassumption | eassumption | exact HΓ1 | exact HΓ2 | | exact HR | exact Hl | exact (le_n _) | exact Hc | exact Hσ ].
    auto.
  - exact Hρ.
  - exact (eval_sub_change_target_rel HΓ2 HR Hl Hc Hρσ Hev).
  - exact (eval_sub_change_target_rel HΓ2 HR Hl Hc Hρσ' Hev').
  - apply ER, HR; exact Hρσ.
Qed.

(** * Equality from Pointwise Relatedness

    Two valid terms of [T] are equal when their values at related environments
    are related.  The commutation obligations come from the two validity
    judgments, and the relatedness obligation from the pointwise premise read
    at the substituted environments. *)
Lemma rel_exp_under_ctx_of_simple : forall {Γ T N N' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ N : T ->
    Γ ⊨ N' : T ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΓ ->
        rel_typ_propositional T ρ \/
        exists n n', ⟦ N ⟧ ρ ↘ n /\ ⟦ N' ⟧ ρ' ↘ n' /\ Dom n ≈ n' ∈ per_head T T ρ ρ') ->
    Γ ⊨ N ≈ N' : T.
Proof.
  intros * HΓ [R1' HΓ1 i HN] [R2' HΓ2 j HN'] Hpt.
  refine (mk_rel_exp_under_ctx _ _ _ _ env_relΓ HΓ i _).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HN _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R1 [Ht1 He1]].
  destruct (HN' _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R2 [Ht2 He2]].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  destruct (Hpt _ _ Hρσ) as [Hp | [n [n' [Hn [Hn' Hnn']]]]].
  { exists R1; split; [ exact Ht1 | left ].
    exact (proj1 (rel_typ_prop_any Ht1 (or_intror (or_introl Hp)))). }
  destruct He1 as [Hp | [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hc1]]; [ exists R1; split; [ exact Ht1 | left; exact Hp ] |].
  destruct He2 as [Hp | [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hc2]].
  { exists R1; split; [ exact Ht1 | left ].
    destruct (rel_typ_prop_any Ht2 (or_introl Hp)) as (_ & Hp2 & _).
    exact (proj1 (rel_typ_prop_any Ht1 (or_intror (or_introl Hp2)))). }
  destruct Ht1 as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hty2].
  functional_eval_rewrite_clear.
  assert (Hmid1 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hmid2 : DF a2 ≈ a3 ∈ per_univ_elem j ↘ R2) by pairwise.
  assert (HPER : PER R1) by (eapply per_elem_PER; eassumption).
  apply (per_head_iff Ha2 Ha3 Hmid1) in Hnn'.
  assert (E : R2 <~> R1) by (eapply per_univ_elem_right_irrel; eassumption).
  exists R1; split.
  - econstructor; eassumption.
  - right; apply (mk_rel_exp v1 v2 w3 w4); try eassumption.
    apply rel_chain_4; [ pairwise | eassumption | apply E; pairwise ].
Qed.

(** Two valid types, of either sort, are equal when their values at related
    environments are related. *)
Lemma rel_type_under_ctx_of_simple : forall {Γ A A' env_relΓ} {i : nat},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ᵗ A' ≈ A' at i ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ ->
        exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * HΓ [R1' HΓ1 HA HAn] [R2' HΓ2 HA' _] Hpt.
  refine (mk_rel_type_under_ctx _ _ _ _ env_relΓ HΓ _ HAn).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hc1].
  destruct (HA' _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hc2].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  destruct (Hpt _ _ Hρσ) as (a & a' & Ha & Ha' & Haa).
  functional_eval_rewrite_clear.
  destruct Hc1 as (H12 & _); destruct Hc2 as (_ & _ & H34).
  apply (mk_rel_exp v1 v2 w3 w4); try eassumption.
  apply rel_chain_4; assumption.
Qed.

End Fixed_GCtx.

(** [eval_wk_at] for the files that follow (the one above is the
    section's). *)
Ltac eval_wk_at H :=
  let T := type of H in
  match T with ?R _ _ => eapply (eval_sub_of_wk_rel (R := R)); [ eassumption | exact H ] end.

#[export] Existing Instance rel_wk_morphism_Proper.
#[export] Existing Instance rel_exp_morphism_Proper.
#[export] Existing Instance rel_sub_morphism_Proper.
#[export]
Hint Resolve rel_exp_implies_rel_typ : mctt.
#[export]
Hint Resolve rel_typ_implies_rel_exp : mctt.
#[export]
Hint Resolve rel_typ_elem_PER : mctt.
#[export]
Hint Resolve rel_wk_id : mctt.
#[export]
Hint Resolve rel_ctx_wf_per_ctx_env : mctt.
#[export]
Hint Resolve rel_ctx_wf_per_ctx : mctt.
#[export]
Hint Resolve rel_sub_id : mctt.
#[export]
Hint Resolve rel_wk_under_ctx_shift : mctt.
#[export]
Hint Resolve rel_sub_shift : mctt.
