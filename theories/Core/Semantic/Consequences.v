From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Soundness.
From Mctt.Core.Completeness.Consequences Require Export Types.
From Mctt.Core.Semantic Require Export Transparency Stuck.
From Mctt.Core.Syntactic Require Export Unseal.
Require Import Mctt.Core.Syntactic.Command.
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

(** The three universe rules are one disjunct, at an index: inside a tier it
    is the order on levels, and from the small tier to the large one it is
    [wf_subtyp_small_large]. *)
Lemma subtyp_spec : forall {Γ A B},
    Γ ⊢ A ⊆ B ->
    (exists k, Γ ⊢ A ≈ B : Type@k) \/
      (exists (u v : uidx), (exists k, Γ ⊢ A ≈ univ_tm u : Type@k) /\ (exists k, Γ ⊢ univ_tm v ≈ B : Type@k) /\ uidx_le u v) \/
      (exists A1 A2 B1 B2, (exists k, Γ ⊢ A ≈ Π A1 A2 : Type@k) /\ (exists k, Γ ⊢ Π B1 B2 ≈ B : Type@k) /\ (exists k, Γ ⊢ A1 ≈ B1 : Type@k) /\ Γ ▹ B1 ⊢ A2 ⊆ B2).
Proof.
  (** The global context is an index of [wf_subtyp], so fix it for the induction. *)
  intros * H.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  induction H; subst;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
    mauto 3.
  - (** Transitivity: nine combinations of the two cases, of which the mixed
        universe/[Π] ones are impossible. *)
    destruct IHwf_subtyp1 as [[? Heq1] | [[u [v [[? Hu] [[? Hv] Huv]]]] | (A1 & A2 & B1 & B2 & [? Ha1] & [? Hb1] & [? Hab1] & Hsub1)]],
             IHwf_subtyp2 as [[? Heq2] | [[u' [v' [[? Hu'] [[? Hv'] Hu'v']]]] | (C1 & C2 & D1 & D2 & [? Hc2] & [? Hd2] & [? Hcd2] & Hsub2)]].
    (** [≈] then [≈]. *)
    + left; eexists; eapply exp_eq_trans_typ_max; eassumption.
    (** [≈] then a universe, and a universe then [≈]. *)
    + right; left; exists u', v'; repeat split; [| | exact Hu'v' ];
        eexists; [ eapply exp_eq_trans_typ_max; eassumption | eassumption ].
    (** [≈] then a [Π]. *)
    + right; right; exists C1, C2, D1, D2; repeat split; [| | | exact Hsub2 ];
        eexists; [ eapply exp_eq_trans_typ_max; eassumption | eassumption | eassumption ].
    + right; left; exists u, v; repeat split; [| | exact Huv ];
        eexists; [ eassumption | eapply exp_eq_trans_typ_max; eassumption ].
    (** A universe then a universe: the two middle universes are equal, so
        their indices are. *)
    + assert (Γ ⊢ univ_tm v ≈ univ_tm u' : Type@(max _ _))
        by (eapply exp_eq_trans_typ_max; [ exact Hv | exact Hu' ]).
      assert (v = u') as -> by mauto 3 using exp_eq_univ_tm_implies_eq.
      right; left; exists u, v'; repeat split;
        [ eexists; eassumption | eexists; eassumption | eapply uidx_le_trans; eassumption ].
    (** A universe then a [Π], and a [Π] then a universe: impossible. *)
    + exfalso; eapply pi_univ_tm_absurd, exp_eq_trans_typ_max; [ symmetry; exact Hc2 | symmetry; exact Hv ].
    + right; right; exists A1, A2, B1, B2; repeat split; [| | | exact Hsub1 ];
        eexists; [ eassumption | eapply exp_eq_trans_typ_max; eassumption | eassumption ].
    + exfalso; eapply pi_univ_tm_absurd, exp_eq_trans_typ_max; [ exact Hb1 | exact Hu' ].
    (** A [Π] then a [Π]: the two middle [Π]s are equal, so the development
        continues with the domain and codomain of the one we keep. *)
    + assert (Γ ⊢ Π B1 B2 ≈ Π C1 C2 : Type@(max _ _))
        by (eapply exp_eq_trans_typ_max; [ exact Hb1 | exact Hc2 ]).
      assert (Γ ⊢ B1 ≈ C1 : Type@_ /\ Γ ▹ B1 ⊢ B2 ≈ C2 : Type@_) as []
          by mauto 3 using exp_eq_pi_inversion.
      right; right.
      exists A1, A2, D1, D2; repeat split; [ eexists; eassumption | eexists; eassumption | |].
      * eexists; eapply exp_eq_trans_typ_max; [ exact Hab1 |].
        eapply exp_eq_trans_typ_max; [ eassumption | exact Hcd2 ].
      * (** The two codomain refinements live in contexts extended by the three
            equal domains, so [ctxsub_subtyp] moves both into the one we chose. *)
        etransitivity; [| exact Hsub2 ].
        etransitivity; eapply ctxsub_subtyp; [| exact Hsub1 | | mauto 3 ]; [| mauto 3 ].
        all: eapply wf_sub_id_extend_eq'; eapply exp_eq_trans_typ_max; [ eassumption | exact Hcd2 ].
  (** The three universe rules, at their own indices. *)
  - right; left; exists (ul i), (ul j); cbn [univ_tm];
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | cbn; lia ].
  - right; left; exists (us n), (us m); cbn [univ_tm];
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | cbn; lia ].
  - right; left; exists (us n), (ul i); cbn [univ_tm];
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | exact I ].
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

(** Stated at explicit [Θ Ξ] so that the induction need not generalize the
    instance. *)
Lemma consistency_ne_helper : forall {Θ Ξ i A A'} {W : ne},
    gc_transparent Θ Ξ ->
    ne_clean W ->
    is_typ_constr A' ->
    (forall (u : uidx), A' <> univ_tm u) ->
    Θ ⍮ Ξ ⍮ ⋅ ▹ Type@i ⊢ A ⊆ A' ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ▹ Type@i ⊢ W : A).
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
      [ apply False_is_typ_constr | intros []; discriminate | gen_presups; mauto 3 ].
  - destruct W; simpl in *; try contradiction; autoinjections; destruct_all.
    eapply IHHW3; [ eassumption | idtac .. | mauto 4 ]; (congruence + mautosolve 3).
  - destruct W; simpl in *; try contradiction; autoinjections.
    pose (GC := gc_mk Θ Ξ).
    do 2 match_by_head ctx_lookup ltac:(fun H => dependent destruction H).
    assert (⋅ ▹ Type@i ⊢ Type@i[↑]ʷ ≈ Type@i : Type@(S i)) by mauto 3.
    assert (rigid_typ (⋅ ▹ Type@i) A').
    { assert (exists k, ⋅ ▹ Type@i ⊢ A' : Type@k) as [k ?] by (gen_presups; eauto).
      eapply rigid_typ_of_is_typ_constr; [ eapply ctx_ass_of_lookup_typ | eassumption | eassumption ]. }
    eapply (@subtyp_spec GC) in Heq as [| []]; destruct_conjs;
      (** [A'] is rigid, so an equation with a universe makes it that
          universe, which [HA'eq] excludes. *)
      try (eapply (HA'eq (ul i)); eapply rigid_typ_eq_univ_tm;
           [ eassumption | cbn [univ_tm]; symmetry; eassumption ]);
      try (eapply HA'eq, rigid_typ_eq_univ_tm; [ eassumption | symmetry; mautosolve 3 ]).
    assert (⋅ ▹ Type@i ⊢ Type@i ≈ Π _ _ : Type@_) by mauto 3.
    assert (Π _ _ = Type@i) by mauto 3; (congruence + mautosolve 3).
Qed.

(** In the empty context, a neutral without a global head has no type: its
    head would be a variable. *)
Lemma no_closed_neutral : forall {Θ Ξ A} {W : ne},
    ne_clean W ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A).
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
  Hypothesis Htr : gc_transparent gc_deps gc_stack.

Theorem canonical_form_of_nat : forall {M},
    ⋅ ⊢ M : ℕ ->
    exists W, nbe_f ⋅ M ℕ W /\ canonical_nat W.
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_clean _ _ Htr _ _ _ _ H) as Hc).
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  match_by_head1 read_nf ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; mauto 3;
    gen_presups.
  - eassert (⋅ ⊢ _ : ℕ /\ ⋅ ⊢ ℕ ⊆ ℕ) as [? _]; mautosolve 4.
  - match_by_head1 (wf_exp gc_deps gc_stack ⋅ ℕ) ltac:(fun H => contradict H); mautosolve 4.
Qed.
Hint Resolve canonical_form_of_nat : mctt.

Theorem canonical_form_of_typ : forall {i M},
    ⋅ ⊢ M : Type@i ->
    exists W, nbe_f ⋅ M Type@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_clean _ _ Htr _ _ _ _ H) as Hc).
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  dir_inversion_clear_by_head read_nf.
  match_by_head1 read_typ ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; split; intros; mauto 3; try congruence;
    gen_presups;
    match_by_head1 (wf_exp gc_deps gc_stack ⋅ Type@i) ltac:(fun H => contradict H); mautosolve 4.
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
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hnbe) as Hc; cbn in Hc; destruct_all.
  dependent destruction Hnbe.
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  match_by_head read_typ ltac:(fun H => directed dependent destruction H).
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  simpl in *.
  assert (exists B, ⋅ ▹ Type@i ⊢ M0 : B /\ ⋅ ⊢ Π Type@i B ⊆ Π Type@i #0) as [B [? [| [|]]%subtyp_spec]] by mauto 3;
    destruct_conjs;
    (** A [Π] is never a universe, so the universe case is impossible. *)
    try (exfalso; eapply pi_univ_tm_absurd; eassumption);
    try assert (Π _ _ = Type@_) by mauto 3;
    try congruence.
  - assert (_ /\ _ ⊢ B ≈ #0 : _) as [_ ?] by mauto 3 using exp_eq_pi_inversion.
    eapply consistency_ne_helper; (apply var_neq_univ_tm + congruence + mautosolve 3).
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
    eapply consistency_ne_helper; (apply var_neq_univ_tm + congruence + mautosolve 3).
Qed.

(** There is no closed proof of [⊥]: its normal form would be a closed
    neutral. *)
Theorem consistency_False : forall M,
    ~ ⋅ ⊢ M : ⊥.
Proof.
  intros * [W [Hnbe HMW]]%soundness.
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hnbe) as Hc.
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
Corollary canonical_form_of_nat_gctx : forall Θ Ξ M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ Ξ ⋅ M ℕ W /\ canonical_nat W.
Proof. intros * Htr HM; exact (@canonical_form_of_nat (gc_mk Θ Ξ) Htr M HM). Qed.

Corollary canonical_form_of_typ_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@i ->
    exists W, nbe Θ Ξ ⋅ M Type@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof. intros * Htr HM; exact (@canonical_form_of_typ (gc_mk Θ Ξ) Htr i M HM). Qed.

Corollary consistency_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@i #0).
Proof. intros * Htr; exact (@consistency (gc_mk Θ Ξ) Htr i M). Qed.

Corollary consistency_False_gctx : forall Θ Ξ M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Htr; exact (@consistency_False (gc_mk Θ Ξ) Htr M). Qed.

(** ** Opaque Definitions

    With [abstract] definitions allowed, a closed normal form of type [ℕ] can
    be stuck: an opaque global applied to arguments, as [c] is in
    [abstract c : ℕ := 3].  What survives is:

    - at the global context itself, every closed normal form of type [ℕ] is a
      numeral or a numeral wrapped around a neutral headed by a global that
      does not unfold ([canonical_form_of_nat_stuck]), with no hypothesis at
      all;
    - without axioms that global is an opaque definition with a body, and
      after unsealing every definition the term computes to a numeral, equal
      in the unsealed context to the sealed normal form
      ([canonical_form_of_nat_no_axioms]);
    - without axioms there is no closed proof of [⊥]
      ([consistency_False_no_axioms]): unsealing preserves typing
      ([unseal_exp]) and produces a transparent context
      ([gc_no_axioms_unseal_transparent]). *)

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
Lemma no_closed_neutral_head : forall {Θ Ξ A} {W : ne},
    ne_head W = None ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A).
Proof.
  intros * HWc HW.
  dependent induction HW; try (destruct W; simpl in *; congruence);
    try solve [ eauto ].
  all: destruct W; simpl in *; try congruence; autoinjections; destruct_all;
    try contradiction; eauto.
  match_by_head ctx_lookup ltac:(fun H => inversion H).
Qed.

Lemma closed_neutral_head : forall {Θ Ξ A} {W : ne},
    Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A ->
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

(** A global that is an opaque definition with a body. *)
Definition gopaque (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop :=
  exists pv A M, gc_resolve Θ Ξ p = Some (ge_def false pv A (Some M)).

Lemma gstuck_gopaque : forall Θ Ξ p, gc_no_axioms Θ Ξ -> gstuck Θ Ξ p -> gopaque Θ Ξ p.
Proof.
  intros * Hna (b & pv & A & B & Hr & Hb).
  pose proof (gc_no_axioms_resolve _ _ _ _ _ _ _ Hna Hr) as HB.
  destruct B as [M |]; [| congruence ].
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
    exists W, nbe_f ⋅ M ℕ W /\ canonical_nat_stuck (gstuck gc_deps gc_stack) W.
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_stuck _ _ _ _ _ _ H) as Hc).
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  match_by_head1 read_nf ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; mauto 3;
    gen_presups.
  - eassert (⋅ ⊢ _ : ℕ /\ ⋅ ⊢ ℕ ⊆ ℕ) as [? _]; mautosolve 4.
  - match_by_head1 (wf_exp gc_deps gc_stack ⋅ ℕ) ltac:(fun H => destruct (closed_neutral_head H)).
    mauto 3.
Qed.

Theorem canonical_form_of_typ_stuck : forall {i M},
    ⋅ ⊢ M : Type@i ->
    exists W, nbe_f ⋅ M Type@i W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  match_by_head1 nbe ltac:(fun H => pose proof (nbe_stuck _ _ _ _ _ _ H) as Hc).
  split; [ exact Hc |].
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M; revert Hc.
  dir_inversion_clear_by_head read_nf.
  match_by_head1 read_typ ltac:(fun H => dependent induction H);
    intros; cbn in *; destruct_all; try (left; split; intros; mauto 3; congruence);
    gen_presups.
  match goal with H : wf_exp _ _ ⋅ _ (ne_to_exp _) |- _ => destruct (closed_neutral_head H) end.
  right; eauto.
Qed.

End Stuck_GCtx.

Corollary canonical_form_of_nat_stuck_gctx : forall Θ Ξ M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ Ξ ⋅ M ℕ W /\ canonical_nat_stuck (gstuck Θ Ξ) W.
Proof. intros * HM; exact (@canonical_form_of_nat_stuck (gc_mk Θ Ξ) M HM). Qed.

Corollary canonical_form_of_typ_stuck_gctx : forall Θ Ξ i M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@i ->
    exists W, nbe Θ Ξ ⋅ M Type@i W /\ nf_stuck (gstuck Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_typ_stuck (gc_mk Θ Ξ) i M HM). Qed.

(** *** Without Axioms *)

Theorem consistency_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@i #0).
Proof.
  intros * Hna HM.
  exact (consistency_gctx _ _ _ _ (gc_no_axioms_unseal_transparent _ _ Hna) (unseal_exp _ _ _ _ _ HM)).
Qed.

Theorem consistency_False_no_axioms : forall Θ Ξ M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof.
  intros * Hna HM.
  exact (consistency_False_gctx _ _ _ (gc_no_axioms_unseal_transparent _ _ Hna) (unseal_exp _ _ _ _ _ HM)).
Qed.

(** The sealed normal form is a numeral around a neutral headed by an opaque
    definition; unsealed, the term computes to a numeral, which is equal to
    the sealed normal form once the definitions unfold. *)
Theorem canonical_form_of_nat_no_axioms : forall Θ Ξ M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ Ξ ⋅ M ℕ W /\ canonical_nat_stuck (gopaque Θ Ξ) W /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M ℕ V /\ canonical_nat V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : ℕ.
Proof.
  intros * Hna HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_nat_stuck_gctx _ _ _ HM) as (W & HW & Hc).
  destruct (canonical_form_of_nat_gctx _ _ _ Htr HM') as (V & HV & HcV).
  exists W; split; [ exact HW | split ].
  - eapply canonical_nat_stuck_mono; [| exact Hc ]; intros; apply gstuck_gopaque; assumption.
  - exists V; repeat split; [ exact HV | exact HcV |].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness_gctx' _ _ _ _ _ _ HM HW)).
    pose proof (soundness_gctx' _ _ _ _ _ _ HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

Theorem canonical_form_of_typ_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@i ->
    exists W, nbe Θ Ξ ⋅ M Type@i W /\ nf_stuck (gopaque Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Type@i V /\ is_typ_constr V /\ (forall V', V <> ⇑ⁿ V') /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Type@i.
Proof.
  intros * Hna HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_typ_stuck_gctx _ _ _ _ HM) as (W & HW & Hs & Hc).
  destruct (canonical_form_of_typ_gctx _ _ _ _ Htr HM') as (V & HV & HcV & HnV).
  exists W; split; [ exact HW | split; [| split; [ exact Hc |] ] ].
  - apply (nf_stuck_mono (gstuck Θ Ξ)); [ intros; apply gstuck_gopaque; assumption | exact Hs ].
  - exists V; repeat split; [ exact HV | exact HcV | exact HnV |].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness_gctx' _ _ _ _ _ _ HM HW)).
    pose proof (soundness_gctx' _ _ _ _ _ _ HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

(** *** Every Program

    A run of commands that declare no axiom, loading units that declare
    none, files no axiom ([run_no_axioms]), so the theorems above hold at
    every global context it reaches, and at what such a program files. *)

Section Programs.
  Variables (load_path : path -> option String.string) (read : String.string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  Hypothesis Hload : forall prg u, to_core prg = Some u -> unit_no_axioms u.

Corollary consistency_False_run : forall ch cs Θ Ξ M,
    Mctt.Core.Syntactic.System.Command.run_cmds load_path read to_core ch nil nil cs Θ Ξ ->
    cmds_no_axioms cs ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Hr Hc; apply consistency_False_no_axioms; eapply run_cmds_no_axioms; [ exact Hload | exact Hr | exact Hc ]. Qed.

Corollary consistency_False_prog : forall prg Θ U M,
    Mctt.Core.Syntactic.System.Command.prog_sem load_path read to_core prg Θ U ->
    ~ (((prog_path prg, U) :: Θ) ⍮ nil ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Hp; apply consistency_False_no_axioms; eapply prog_sem_no_axioms; [ exact Hload | exact Hp ]. Qed.

Corollary canonical_form_of_nat_prog : forall prg Θ U M,
    Mctt.Core.Syntactic.System.Command.prog_sem load_path read to_core prg Θ U ->
    let Θ' := ((prog_path prg, U) :: Θ) in
    Θ' ⍮ nil ⍮ ⋅ ⊢ M : ℕ ->
    exists V, nbe (gds_unseal Θ') nil ⋅ M ℕ V /\ canonical_nat V.
Proof.
  intros * Hp Θ' HM.
  pose proof (prog_sem_no_axioms _ _ _ Hload _ _ _ Hp) as Hna.
  destruct (canonical_form_of_nat_no_axioms _ _ _ Hna HM) as (_ & _ & _ & V & HV & HcV & _).
  eauto.
Qed.

End Programs.
