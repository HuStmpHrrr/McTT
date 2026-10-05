From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Soundness.
From Mctt.Core.Completeness.Consequences Require Export Types.
From Mctt.Core.Semantic Require Export Transparency Stuck.
From Mctt.Core.Syntactic Require Export Unseal.
From Mctt.Core.Syntactic.System Require Import Command.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma idempotent_nbe_ty : forall {Γ i A B C},
    Γ ⊢ A : Type@i ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B C ->
    B = C.
Proof.
  intros.
  assert (Γ ⊢ A ≈ B : Type@i) as [? []]%completeness_ty by mauto 2 using soundness_ty'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.
Hint Resolve idempotent_nbe_ty : mctt.

Lemma adjust_exp_eq_level : forall {Γ A A' i j},
    Γ ⊢ A ≈ A' : Type@i ->
    Γ ⊢ A : Type@j ->
    Γ ⊢ A' : Type@j ->
    Γ ⊢ A ≈ A' : Type@j.
Proof.
  intros * ?%completeness_ty ?%soundness ?%soundness.
  destruct_conjs.
  dir_inversion_by_head nbe; dir_inversion_by_head nbe_ty; subst.
  match_by_head eval_exp ltac:(fun H => progressive_invert H).
  match_by_head read_nf ltac:(fun H => progressive_invert H).
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  etransitivity; [| symmetry]; eauto.
Qed.

Lemma exp_eq_pi_inversion : forall {Γ A B A' B' i},
    Γ ⊢ Π A B ≈ Π A' B' : Type@i ->
    Γ ⊢ A ≈ A' : Type@i /\ Γ ▹ A ⊢ B ≈ B' : Type@i.
Proof.
  intros * H.
  gen_presups.
  (on_all_hyp: fun H => apply wf_pi_inversion' in H; destruct H).
  (on_all_hyp: fun H => apply completeness_ty in H).
  (on_all_hyp: fun H => pose proof (soundness H)).
  destruct_conjs.
  dir_inversion_clear_by_head nbe.
  dir_inversion_clear_by_head nbe_ty.
  dir_inversion_by_head initial_env; subst.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_clear_by_head read_nf.
  dir_inversion_by_head read_typ; subst.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  autoinjections.
  assert (Γ ⊢ A' ≈ A : Type@i) by mauto 3.
  (** [Γ ▹ A] refines [Γ ▹ A'] because the two heads are equal, and
      [ctxsub_exp_eq] moves the codomain's normal form across. *)
  assert (Γ ▹ A ⊢s Id : Γ ▹ A') by mauto 3.
  split; [mauto 3 |].
  etransitivity; [| symmetry]; mauto 3.
Qed.

Lemma nf_of_pi : forall {Γ M A B},
    Γ ⊢ M : Π A B ->
    exists W1 W2, nbe_f Γ M (Π A B) λⁿ W1 W2.
Proof.
  intros * [? []]%soundness.
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  dir_inversion_clear_by_head read_nf.
  do 2 eexists; mauto 4.
Qed.
Hint Resolve nf_of_pi : mctt.

Theorem canonical_form_of_pi : forall {M A B},
    ⋅ ⊢ M : Π A B ->
    exists W1 W2, nbe_f ⋅ M (Π A B) λⁿ W1 W2.
Proof. mauto 3. Qed.
Hint Resolve canonical_form_of_pi : mctt.

Lemma subtyp_spec : forall {Γ A B},
    Γ ⊢ A ⊆ B ->
    (exists k, Γ ⊢ A ≈ B : Type@k) \/
      (exists i j, (exists k, Γ ⊢ A ≈ Type@i : Type@k) /\ (exists k, Γ ⊢ Type@j ≈ B : Type@k) /\ i <= j) \/
      (exists A1 A2 B1 B2, (exists k, Γ ⊢ A ≈ Π A1 A2 : Type@k) /\ (exists k, Γ ⊢ Π B1 B2 ≈ B : Type@k) /\ (exists k, Γ ⊢ A1 ≈ B1 : Type@k) /\ Γ ▹ B1 ⊢ A2 ⊆ B2).
Proof.
  (** The global context is an index of [wf_subtyp], so fix it for the induction. *)
  intros * H.
  remember gc_ctx as Θ0 eqn:HΘ.
  induction H; subst;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
    mauto 3.
  - destruct_all; firstorder (mauto 3);
      try (right; right; do 4 eexists; firstorder mautosolve 3).
    + match goal with
      | _: (Γ ⊢ M' ≈ Type@?i : Type@_),
          _: Γ ⊢ Type@?j ≈ M' : Type@_ |- _ =>
          assert (Γ ⊢ Type@j ≈ Type@i : Type@_) by mauto 3;
          assert (j = i) as -> by mauto 3
      end; (congruence + firstorder (mautosolve 4 + lia)).
    + assert (Γ ⊢ Π _ _ ≈ Type@_ : Type@_) by mauto 3.
      assert (Π _ _ = Type@_) by mauto 3; (congruence + firstorder (mautosolve 4 + lia)).
    + assert (Γ ⊢ Π _ _ ≈ Type@_ : Type@_) by mauto 3.
      assert (Π _ _ = Type@_) by mauto 3; (congruence + firstorder (mautosolve 4 + lia)).
    + match goal with
      | _: (Γ ⊢ M' ≈ Π ?A1 ?A2 : Type@_),
          _: Γ ⊢ Π ?B1 ?B2 ≈ M' : Type@_ |- _ =>
          assert (Γ ⊢ Π A1 A2 ≈ Π B1 B2 : Type@_) by mauto 3;
          assert (Γ ⊢ A1 ≈ B1 : Type@_ /\ Γ ▹ A1 ⊢ A2 ≈ B2 : Type@_) as [] by mauto 3 using exp_eq_pi_inversion
      end.
      right; right.
      do 4 eexists; repeat split; mauto 3.
      * eexists; eapply exp_eq_trans_typ_max; (congruence + firstorder (mautosolve 4 + lia)).
      * (** The two codomain refinements live in contexts extended by the three
            equal domains, so [ctxsub_subtyp] moves both into the one we chose. *)
        etransitivity; [| eassumption].
        etransitivity; eapply ctxsub_subtyp; [| eassumption | | mauto 3]; [| mauto 3].
        eapply wf_sub_id_extend_eq', exp_eq_trans_typ_max; [symmetry |]; eassumption.
  - right; left.
    do 2 eexists; (congruence + firstorder (mautosolve 4 + lia)).
  - right; right.
    do 4 eexists; (congruence + firstorder (mautosolve 4 + lia)).
Qed.

Hint Resolve subtyp_spec : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve idempotent_nbe_ty : mctt.
#[export]
Hint Resolve nf_of_pi : mctt.
#[export]
Hint Resolve canonical_form_of_pi : mctt.
#[export]
Hint Resolve subtyp_spec : mctt.

(** Stated at explicit [Θ] so that the induction need not generalize the
    instance. *)
Lemma consistency_ne_helper : forall {Θ i A A'} {W : ne},
    gc_transparent Θ ->
    ne_clean W ->
    is_typ_constr A' ->
    (forall j, A' <> Type@j) ->
    Θ ⍮ ⋅ ▹ Type@i ⊢ A ⊆ A' ->
    ~ (Θ ⍮ ⋅ ▹ Type@i ⊢ W : A).
Proof.
  intros * Htr HWc HA' HA'eq Heq HW. gen A'.
  dependent induction HW; intros; mauto 3; try directed dependent destruction HA';
    try (destruct W; simpl in *; congruence).
  (* a global: not the head of a neutral at a transparent context *)
  all: try solve [ destruct W; simpl in *; try congruence; contradiction ].
  - destruct W; simpl in *; try contradiction; autoinjections; destruct_all.
    eapply IHHW4; [ eassumption | idtac .. | mauto 4 ]; (congruence + mautosolve 3).
  - destruct W; simpl in *; try contradiction; autoinjections; destruct_all.
    (** The scrutinee of [efq] is a neutral of type [⊥]. *)
    eapply (IHHW2 Htr W ltac:(eassumption) i eq_refl eq_refl ⊥);
      [ constructor | congruence | gen_presups; mauto 3 ].
  - destruct W; simpl in *; try contradiction; autoinjections; destruct_all.
    eapply IHHW3; [ eassumption | idtac .. | mauto 4 ]; (congruence + mautosolve 3).
  - destruct W; simpl in *; try contradiction; autoinjections.
    pose (GC := gc_mk Θ).
    do 2 match_by_head ctx_lookup ltac:(fun H => dependent destruction H).
    assert (⋅ ▹ Type@i ⊢ Type@i[↑]ʷ ≈ Type@i : Type@(S i)) by mauto 3.
    assert (rigid_typ (⋅ ▹ Type@i) A').
    { assert (exists k, ⋅ ▹ Type@i ⊢ A' : Type@k) as [k ?] by (gen_presups; eauto).
      eapply rigid_typ_of_is_typ_constr; [ eapply ctx_ass_of_lookup_typ | eassumption | eassumption ]. }
    eapply (@subtyp_spec GC) in Heq as [| []]; destruct_conjs;
      try (eapply HA'eq; mautosolve 4).
    assert (⋅ ▹ Type@i ⊢ Type@i ≈ Π _ _ : Type@_) by mauto 3.
    assert (Π _ _ = Type@i) by mauto 3; (congruence + mautosolve 3).
Qed.

(** In the empty context, a neutral without a global head has no type: its
    head would be a variable. *)
Lemma no_closed_neutral : forall {Θ A} {W : ne},
    ne_clean W ->
    ~ (Θ ⍮ ⋅ ⊢ W : A).
Proof.
  intros * HWc HW.
  dependent induction HW; try (destruct W; simpl in *; congruence);
    try solve [ eauto ].
  all: destruct W; simpl in *; try congruence; autoinjections; destruct_all;
    try contradiction; eauto.
  match_by_head ctx_lookup ltac:(fun H => inversion H).
Qed.

(** ** Canonical Forms and Consistency

    These hold only at a transparent global context: otherwise an axiom
    [c : ℕ] is a closed neutral, and an axiom of type [Π Type@i #0] refutes
    consistency.  At a transparent context a normal form has no global head
    ([nbe_clean]), and a neutral without one has no head in the empty local
    context ([no_closed_neutral]). *)

Inductive canonical_nat : nf -> Prop :=
| canonical_nat_zero : canonical_nat zeroⁿ
| canonical_nat_succ : forall W, canonical_nat W -> canonical_nat succⁿ W
.
#[export]
Hint Constructors canonical_nat : mctt.

Section Transparent_GCtx.
  Context {GC : GCtx}.
  Hypothesis Htr : gc_transparent gc_ctx.

Theorem canonical_form_of_nat : forall {M},
    ⋅ ⊢ M : ℕ ->
    exists W, nbe_f ⋅ M ℕ W /\ canonical_nat W.
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_clean _ Htr _ _ _ _ H) as Hc).
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  match_by_head1 read_nf ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; mauto 3;
    gen_presups.
  - eassert (⋅ ⊢ _ : ℕ /\ ⋅ ⊢ ℕ ⊆ ℕ) as [? _]; mautosolve 4.
  - match_by_head1 (wf_exp gc_ctx ⋅ ℕ) ltac:(fun H => contradict H); mautosolve 4.
Qed.
Hint Resolve canonical_form_of_nat : mctt.

Theorem canonical_form_of_typ : forall {i M},
    ⋅ ⊢ M : Type@i ->
    exists W, nbe_f ⋅ M Type@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_clean _ Htr _ _ _ _ H) as Hc).
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  dir_inversion_clear_by_head read_nf.
  match_by_head1 read_typ ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; split; intros; mauto 3; try congruence;
    gen_presups;
    match_by_head1 (wf_exp gc_ctx ⋅ Type@i) ltac:(fun H => contradict H); mautosolve 4.
Qed.
Hint Resolve canonical_form_of_typ : mctt.

Theorem consistency : forall {i} M,
    ~ ⋅ ⊢ M : Π Type@i #0.
Proof.
  intros * HW.
  assert (exists W1 W2, nbe_f ⋅ M (Π Type@i #0) λⁿ W1 W2) as [W1 [W2 Hnbe]] by mauto 3.
  assert (exists W, nbe_f ⋅ M (Π Type@i #0) W /\ ⋅ ⊢ M ≈ W : Π Type@i #0) as [? []] by mauto 3 using soundness.
  gen_presups.
  functional_nbe_rewrite_clear.
  pose proof (nbe_clean _ Htr _ _ _ _ Hnbe) as Hc; cbn in Hc; destruct_all.
  dependent destruction Hnbe.
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  match_by_head read_typ ltac:(fun H => directed dependent destruction H).
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  simpl in *.
  assert (exists B, ⋅ ▹ Type@i ⊢ M0 : B /\ ⋅ ⊢ Π Type@i B ⊆ Π Type@i #0) as [B [? [| [|]]%subtyp_spec]] by mauto 3;
    destruct_conjs;
    try assert (Π _ _ = Type@_) by mauto 3;
    try congruence.
  - assert (_ /\ _ ⊢ B ≈ #0 : _) as [_ ?] by mauto 3 using exp_eq_pi_inversion.
    eapply consistency_ne_helper; (congruence + mautosolve 3).
  - assert (_ /\ _ ⊢ B ≈ _ : _) as [_ ?] by mauto 3 using exp_eq_pi_inversion.
    assert (_ /\ _ ⊢ _ ≈ #0 : _) as [? ?] by mauto 3 using exp_eq_pi_inversion.
    (** The middle refinement and the right-hand equation live in the context
        extended by the other domain, so both move across the refinement
        [⋅ ▹ Type@i ⊢s Id : ⋅ ▹ _] given by the domain equation. *)
    assert (⋅ ▹ Type@i ⊢ B ⊆ #0) by
      (match goal with Hs : _ ▹ _ ⊢ ?X ⊆ ?Y |- _ =>
         transitivity X; [mauto 3 |]; transitivity Y;
         [eapply ctxsub_subtyp; [| exact Hs] | eapply wf_subtyp_refl', ctxsub_exp_eq; [| eassumption]]
       end;
       mauto 3).
    eapply consistency_ne_helper; (congruence + mautosolve 3).
Qed.

(** There is no closed proof of [⊥]: its normal form would be a closed
    neutral. *)
Theorem consistency_False : forall M,
    ~ ⋅ ⊢ M : ⊥.
Proof.
  intros * [W [Hnbe HMW]]%soundness.
  pose proof (nbe_clean _ Htr _ _ _ _ Hnbe) as Hc.
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  simpl in *.
  gen_presups.
  eapply no_closed_neutral; eassumption.
Qed.

End Transparent_GCtx.

#[export]
Hint Resolve canonical_form_of_nat : mctt.
#[export]
Hint Resolve canonical_form_of_typ : mctt.

(** The theorems above, with the global context explicit. *)
Corollary canonical_form_of_nat_gctx : forall Θ M,
    gc_transparent Θ ->
    Θ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ ⋅ M ℕ W /\ canonical_nat W.
Proof. intros * Htr HM; exact (@canonical_form_of_nat (gc_mk Θ) Htr M HM). Qed.

Corollary canonical_form_of_typ_gctx : forall Θ i M,
    gc_transparent Θ ->
    Θ ⍮ ⋅ ⊢ M : Type@i ->
    exists W, nbe Θ ⋅ M Type@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof. intros * Htr HM; exact (@canonical_form_of_typ (gc_mk Θ) Htr i M HM). Qed.

Corollary consistency_gctx : forall Θ i M,
    gc_transparent Θ ->
    ~ (Θ ⍮ ⋅ ⊢ M : Π Type@i #0).
Proof. intros * Htr; exact (@consistency (gc_mk Θ) Htr i M). Qed.

Corollary consistency_False_gctx : forall Θ M,
    gc_transparent Θ ->
    ~ (Θ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Htr; exact (@consistency_False (gc_mk Θ) Htr M). Qed.

(** ** Sealed Constants and Axioms

    With [abstract] definitions and axioms, a closed normal form of type [ℕ]
    can be stuck: a sealed constant or an axiom applied to arguments, as [c]
    is in [abstract c : ℕ := 3].  What survives is:

    - at the global context itself, every closed normal form of type [ℕ] is a
      numeral or a numeral wrapped around a neutral headed by a constant that
      does not unfold ([canonical_form_of_nat_stuck]), with no hypothesis at
      all;
    - without axioms that constant is sealed and has a body, and after
      unsealing every constant the term computes to a numeral, equal in the
      unsealed context to the sealed normal form
      ([canonical_form_of_nat_no_axioms]);
    - without axioms there is no closed proof of [⊥]
      ([consistency_False_no_axioms]): unsealing preserves typing
      ([unseal_exp]) and produces a transparent context
      ([gc_unseal_transparent]). *)

(** The global at the head of a neutral, if any. *)
Fixpoint ne_head (W : ne) : option qname :=
  match W with
  | ne_natrec _ _ _ W | ne_exfalso _ W | ne_app W _ => ne_head W
  | ne_var _ => None
  | ne_glob p => Some p
  end.

Lemma ne_stuck_head : forall G W p, ne_stuck G W -> ne_head W = Some p -> G p.
Proof.
  induction W; intros * HW Hh; cbn in *; destruct_all; try discriminate;
    [ eauto .. | congruence ].
Qed.

(** In the empty context, a neutral is headed by a global. *)
Lemma no_closed_neutral_head : forall {Θ A} {W : ne},
    ne_head W = None ->
    ~ (Θ ⍮ ⋅ ⊢ W : A).
Proof.
  intros * HWc HW.
  dependent induction HW; try (destruct W; simpl in *; congruence);
    try solve [ eauto ].
  all: destruct W; simpl in *; try congruence; autoinjections; destruct_all;
    try contradiction; eauto.
  match_by_head ctx_lookup ltac:(fun H => inversion H).
Qed.

Lemma closed_neutral_head : forall {Θ A} {W : ne},
    Θ ⍮ ⋅ ⊢ W : A ->
    exists p, ne_head W = Some p.
Proof.
  intros * HW; destruct (ne_head W) as [p |] eqn:Hh; [ eauto |].
  exfalso; exact (no_closed_neutral_head Hh HW).
Qed.

(** A numeral, possibly around a neutral whose globals satisfy [G], headed by
    one. *)
Inductive canonical_nat_stuck (G : qname -> Prop) : nf -> Prop :=
| canonical_nat_stuck_zero : canonical_nat_stuck G zeroⁿ
| canonical_nat_stuck_succ : forall W, canonical_nat_stuck G W -> canonical_nat_stuck G succⁿ W
| canonical_nat_stuck_neut : forall W p,
    ne_head W = Some p -> ne_stuck G W -> canonical_nat_stuck G ⇑ⁿ W
.
#[export]
Hint Constructors canonical_nat_stuck : mctt.

Lemma canonical_nat_stuck_of_canonical_nat : forall G W, canonical_nat W -> canonical_nat_stuck G W.
Proof. induction 1; mauto. Qed.

(** A constant that is sealed and has a body. *)
Definition gopaque (Θ : gctx) (p : qname) : Prop :=
  exists A M, gc_const Θ p = Some (A, Some M, false).

Lemma gstuck_gopaque : forall Θ p, gc_no_axioms Θ -> gstuck Θ p -> gopaque Θ p.
Proof.
  intros * Hna (A & oM & b & Hr & Hb).
  pose proof (Hna _ _ _ _ Hr) as HB.
  destruct oM as [M |]; [| congruence ].
  destruct Hb as [-> | ?]; [| discriminate ].
  unfold gopaque; eauto.
Qed.

Lemma nf_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall W, nf_stuck G W -> nf_stuck G' W
with ne_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall W, ne_stuck G W -> ne_stuck G' W.
Proof.
  all: intros G G' HG [] H; cbn in *; destruct_all;
    repeat split; eauto using nf_stuck_mono, ne_stuck_mono.
Qed.

Lemma canonical_nat_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall W, canonical_nat_stuck G W -> canonical_nat_stuck G' W.
Proof.
  intros * HG; induction 1; econstructor; eauto using ne_stuck_mono.
Qed.

Section Stuck_GCtx.
  Context {GC : GCtx}.

Theorem canonical_form_of_nat_stuck : forall {M},
    ⋅ ⊢ M : ℕ ->
    exists W, nbe_f ⋅ M ℕ W /\ canonical_nat_stuck (gstuck gc_ctx) W.
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_stuck _ _ _ _ _ H) as Hc).
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  match_by_head1 read_nf ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; mauto 3;
    gen_presups.
  - eassert (⋅ ⊢ _ : ℕ /\ ⋅ ⊢ ℕ ⊆ ℕ) as [? _]; mautosolve 4.
  - match_by_head1 (wf_exp gc_ctx ⋅ ℕ) ltac:(fun H => destruct (closed_neutral_head H)).
    mauto 3.
Qed.

Theorem canonical_form_of_typ_stuck : forall {i M},
    ⋅ ⊢ M : Type@i ->
    exists W, nbe_f ⋅ M Type@i W /\ nf_stuck (gstuck gc_ctx) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_stuck _ _ _ _ _ H) as Hc).
  split; [ exact Hc |].
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  dir_inversion_clear_by_head read_nf.
  match_by_head1 read_typ ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; try (left; split; intros; mauto 3; congruence);
    gen_presups.
  match goal with H : wf_exp _ ⋅ _ (ne_to_exp _) |- _ => destruct (closed_neutral_head H) end.
  right; eauto.
Qed.

End Stuck_GCtx.

Corollary canonical_form_of_nat_stuck_gctx : forall Θ M,
    Θ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ ⋅ M ℕ W /\ canonical_nat_stuck (gstuck Θ) W.
Proof. intros * HM; exact (@canonical_form_of_nat_stuck (gc_mk Θ) M HM). Qed.

Corollary canonical_form_of_typ_stuck_gctx : forall Θ i M,
    Θ ⍮ ⋅ ⊢ M : Type@i ->
    exists W, nbe Θ ⋅ M Type@i W /\ nf_stuck (gstuck Θ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_typ_stuck (gc_mk Θ) i M HM). Qed.

(** *** Without Axioms *)

Theorem consistency_no_axioms : forall Θ i M,
    gc_no_axioms Θ ->
    ~ (Θ ⍮ ⋅ ⊢ M : Π Type@i #0).
Proof.
  intros * Hna HM.
  exact (consistency_gctx _ _ _ (gc_unseal_transparent _ Hna) (unseal_exp _ _ _ _ HM)).
Qed.

Theorem consistency_False_no_axioms : forall Θ M,
    gc_no_axioms Θ ->
    ~ (Θ ⍮ ⋅ ⊢ M : ⊥).
Proof.
  intros * Hna HM.
  exact (consistency_False_gctx _ _ (gc_unseal_transparent _ Hna) (unseal_exp _ _ _ _ HM)).
Qed.

(** The sealed normal form is a numeral around a neutral headed by a sealed
    constant with a body; unsealed, the term computes to a numeral, which is
    equal to the sealed normal form once the constants unfold. *)
Theorem canonical_form_of_nat_no_axioms : forall Θ M,
    gc_no_axioms Θ ->
    Θ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ ⋅ M ℕ W /\ canonical_nat_stuck (gopaque Θ) W /\
      exists V, nbe (gc_unseal Θ) ⋅ M ℕ V /\ canonical_nat V /\
        gc_unseal Θ ⍮ ⋅ ⊢ W ≈ V : ℕ.
Proof.
  intros * Hna HM.
  pose proof (gc_unseal_transparent _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_nat_stuck_gctx _ _ HM) as (W & HW & Hc).
  destruct (canonical_form_of_nat_gctx _ _ Htr HM') as (V & HV & HcV).
  exists W; split; [ exact HW | split ].
  - eapply canonical_nat_stuck_mono; [| exact Hc ]; intros; apply gstuck_gopaque; assumption.
  - exists V; repeat split; [ exact HV | exact HcV |].
    pose proof (unseal_exp_eq _ _ _ _ _ (soundness_gctx' _ _ _ _ _ HM HW)).
    pose proof (soundness_gctx' _ _ _ _ _ HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

Theorem canonical_form_of_typ_no_axioms : forall Θ i M,
    gc_no_axioms Θ ->
    Θ ⍮ ⋅ ⊢ M : Type@i ->
    exists W, nbe Θ ⋅ M Type@i W /\ nf_stuck (gopaque Θ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gc_unseal Θ) ⋅ M Type@i V /\ is_typ_constr V /\ (forall V', V <> ⇑ⁿ V') /\
        gc_unseal Θ ⍮ ⋅ ⊢ W ≈ V : Type@i.
Proof.
  intros * Hna HM.
  pose proof (gc_unseal_transparent _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_typ_stuck_gctx _ _ _ HM) as (W & HW & Hs & Hc).
  destruct (canonical_form_of_typ_gctx _ _ _ Htr HM') as (V & HV & HcV & HnV).
  exists W; split; [ exact HW | split; [| split; [ exact Hc |] ] ].
  - apply (nf_stuck_mono (gstuck Θ)); [ intros; apply gstuck_gopaque; assumption | exact Hs ].
  - exists V; repeat split; [ exact HV | exact HcV | exact HnV |].
    pose proof (unseal_exp_eq _ _ _ _ _ (soundness_gctx' _ _ _ _ _ HM HW)).
    pose proof (soundness_gctx' _ _ _ _ _ HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

(** *** Every Program Without Axioms

    A run of commands without a body-less definition, in units without one,
    files no axiom ([run_no_axioms]), so the theorems above hold at every
    global context such a run reaches, and at what such a program files. *)

Section Programs.
  Variables (load_path : path -> option String.string) (read : String.string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  Hypothesis Hall : forall fq src prg u,
      load_path fq = Some src -> read src = Some prg -> to_core prg = Some u -> unit_no_axioms u.

Corollary consistency_False_run : forall ch fp Γimp F cs Θ F' M,
    run_cmds load_path read to_core ch fp Γimp nil F cs Θ F' ->
    cmds_no_axioms cs ->
    ~ (Θ ⍮ ⋅ ⊢ M : ⊥).
Proof.
  intros * Hr Hc; apply consistency_False_no_axioms.
  exact (run_cmds_no_axioms _ _ _ Hall _ _ _ _ _ _ _ _ Hr Hc gc_no_axioms_nil).
Qed.

Corollary consistency_False_prog : forall prg Θ U M,
    (forall u, to_core prg = Some u -> unit_no_axioms u) ->
    prog_sem load_path read to_core prg Θ U ->
    ~ (gd_unit (prog_path prg) U :: Θ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Hp Hs; apply consistency_False_no_axioms; eapply prog_sem_no_axioms; eassumption. Qed.

Corollary canonical_form_of_nat_prog : forall prg Θ U M,
    (forall u, to_core prg = Some u -> unit_no_axioms u) ->
    prog_sem load_path read to_core prg Θ U ->
    let Θ' := gd_unit (prog_path prg) U :: Θ in
    Θ' ⍮ ⋅ ⊢ M : ℕ ->
    exists V, nbe (gc_unseal Θ') ⋅ M ℕ V /\ canonical_nat V.
Proof.
  intros * Hp Hs Θ' HM.
  pose proof (prog_sem_no_axioms _ _ _ Hall _ _ _ Hp Hs) as Hna.
  destruct (canonical_form_of_nat_no_axioms _ _ Hna HM) as (_ & _ & _ & V & HV & HcV & _).
  eauto.
Qed.

End Programs.
