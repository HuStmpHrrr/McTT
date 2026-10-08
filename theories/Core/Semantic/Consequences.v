From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Soundness.
From Mctt.Core.Completeness.Consequences Require Export Types.
From Mctt.Core.Semantic Require Export Transparency Stuck.
From Mctt.Core.Syntactic Require Export Unseal.
From Mctt.Core.Syntactic Require Import CoreInversions LevelEq.
From Mctt.Core.Semantic Require Import Realizability Levels.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
Require Import Mctt.Core.Syntactic.Command.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma idempotent_nbe_ty : forall {Γ i A B C},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B C ->
    B = C.
Proof.
  intros.
  assert (Γ ⊢ A ≈ B : Typeω@i) as [? []]%completeness_ty by mauto 2 using soundness_ty'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.
Hint Resolve idempotent_nbe_ty : mctt.

Lemma adjust_exp_eq_level : forall {Γ A A' i j},
    Γ ⊢ A ≈ A' : Typeω@i ->
    Γ ⊢ A : Typeω@j ->
    Γ ⊢ A' : Typeω@j ->
    Γ ⊢ A ≈ A' : Typeω@j.
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
    Γ ⊢ Π A B ≈ Π A' B' : Typeω@i ->
    Γ ⊢ A ≈ A' : Typeω@i /\ Γ ▹ A ⊢ B ≈ B' : Typeω@i.
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
  assert (Γ ⊢ A' ≈ A : Typeω@i) by mauto 3.
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

(** ** Small Universes Are Injective

    Two small universes are equal only at equal levels: their values are
    related, so their levels are ([per_univ_elem_core_suniv]), so the two
    level terms have the same normal form, and soundness turns that into an
    equation. *)
Lemma exp_eq_suniv_tm_inj : forall {Γ t t' k},
    Γ ⊢ Type⟨t⟩ ≈ Type⟨t'⟩ : Typeω@k ->
    Γ ⊢ t ≈ t' : Level.
Proof.
  intros * H.
  assert (Γ ⊢ t : Level) by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  assert (Γ ⊢ t' : Level) by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  match goal with Hl : per_lvl ?l ?l' |- _ => destruct (Hl (length Γ)) as [W [HW HW']] end.
  assert (Γ ⊢ t ≈ W : Level) by (eapply soundness'; [ eassumption | econstructor; mauto 3 ]).
  assert (Γ ⊢ t' ≈ W : Level) by (eapply soundness'; [ eassumption | econstructor; mauto 3 ]).
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

(** ** Subtyping of Universe Terms

    The three universe rules, as a relation on universe terms: large below
    large by the order on levels, small below small by the order on level
    terms, and small below large. *)
Inductive univ_sub (Γ : ctx) : exp -> exp -> Prop :=
| usub_large : forall i j, i <= j -> univ_sub Γ Typeω@i Typeω@j
| usub_small : forall t t',
    Γ ⊢ t : Level ->
    Γ ⊢ t' : Level ->
    Γ ⊢ maxl t t' ≈ t' : Level ->
    univ_sub Γ Type⟨t⟩ Type⟨t'⟩
| usub_small_large : forall t j,
    Γ ⊢ t : Level ->
    univ_sub Γ Type⟨t⟩ Typeω@j.
Hint Constructors univ_sub : mctt.

Lemma univ_sub_univ_term : forall {Γ U V},
    univ_sub Γ U V -> univ_term U /\ univ_term V.
Proof. intros * []; split; constructor. Qed.

(** Two universe subtypings compose through an equation between the middle
    universes: the two tiers are distinct, the large one is injective on
    levels and the small one on level terms. *)
Lemma univ_sub_trans_eq : forall {Γ U V U' W k},
    univ_sub Γ U V ->
    Γ ⊢ V ≈ U' : Typeω@k ->
    univ_sub Γ U' W ->
    univ_sub Γ U W.
Proof.
  intros * H1 Heq H2.
  destruct H1 as [i j Hij | t1 t2 Ht1 Ht2 H12 | t1 j Ht1],
           H2 as [i' j' Hij' | t3 t4 Ht3 Ht4 H34 | t3 j' Ht3].
  - assert (j = i') as -> by mauto 3; constructor; lia.
  - exfalso; eapply exp_eq_typ_suniv_absurd; exact Heq.
  - exfalso; eapply exp_eq_typ_suniv_absurd; exact Heq.
  - exfalso; eapply exp_eq_typ_suniv_absurd; symmetry; exact Heq.
  - (** The order on level terms through the equation of the middle ones:
        [t1 ≤ t2 ≈ t3 ≤ t4]. *)
    assert (Heqt : Γ ⊢ t2 ≈ t3 : Level) by (eapply exp_eq_suniv_tm_inj; exact Heq).
    assert (H23 : @lvl_sub gc_deps gc_stack Γ t2 t3).
    { unfold lvl_sub.
      transitivity (maxl t3 t3);
        [ apply wf_exp_eq_maxl_cong; [ exact Heqt | apply wf_exp_eq_refl; exact Ht3 ]
        | apply wf_exp_eq_maxl_idem; exact Ht3 ]. }
    constructor; [ assumption | assumption |].
    change (@lvl_sub gc_deps gc_stack Γ t1 t4).
    eapply (lvl_sub_trans Ht1 Ht3 Ht4); [| exact H34 ].
    eapply (lvl_sub_trans Ht1 Ht2 Ht3); [ exact H12 | exact H23 ].
  - constructor; assumption.
  - constructor; assumption.
  - exfalso; eapply exp_eq_typ_suniv_absurd; exact Heq.
  - exfalso; eapply exp_eq_typ_suniv_absurd; exact Heq.
Qed.

(** The three universe rules are one disjunct, on universe terms: inside a
    tier it is the order on levels or on level terms, and from the small tier
    to the large one it is [wf_subtyp_small_large]. *)
Lemma subtyp_spec : forall {Γ A B},
    Γ ⊢ A ⊆ B ->
    (exists k, Γ ⊢ A ≈ B : Typeω@k) \/
      (exists U V, (exists k, Γ ⊢ A ≈ U : Typeω@k) /\ (exists k, Γ ⊢ V ≈ B : Typeω@k) /\ univ_sub Γ U V) \/
      (exists A1 A2 B1 B2, (exists k, Γ ⊢ A ≈ Π A1 A2 : Typeω@k) /\ (exists k, Γ ⊢ Π B1 B2 ≈ B : Typeω@k) /\ (exists k, Γ ⊢ A1 ≈ B1 : Typeω@k) /\ Γ ▹ B1 ⊢ A2 ⊆ B2).
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
             IHwf_subtyp2 as [[? Heq2] | [[u' [v' [[? Hu'] [[? Hv'] Hu'v']]]] | (C1 & C2 & D1 & D2 & [? Hc2] & [? Hd2] & [? Hcd2] & Hsub2)]];
      try pose proof (univ_sub_univ_term Huv) as [Hut Hvt];
      try pose proof (univ_sub_univ_term Hu'v') as [Hu't Hv't].
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
        the two subtypings compose. *)
    + assert (Γ ⊢ v ≈ u' : Typeω@(max _ _))
        by (eapply exp_eq_trans_typ_max; [ exact Hv | exact Hu' ]).
      right; left; exists u, v'; repeat split;
        [ eexists; eassumption | eexists; eassumption | eapply univ_sub_trans_eq; eassumption ].
    (** A universe then a [Π], and a [Π] then a universe: impossible. *)
    + exfalso; eapply (pi_univ_term_absurd _ _ _ _ _ Hvt), exp_eq_trans_typ_max;
        [ symmetry; exact Hc2 | symmetry; exact Hv ].
    + right; right; exists A1, A2, B1, B2; repeat split; [| | | exact Hsub1 ];
        eexists; [ eassumption | eapply exp_eq_trans_typ_max; eassumption | eassumption ].
    + exfalso; eapply (pi_univ_term_absurd _ _ _ _ _ Hu't), exp_eq_trans_typ_max; [ exact Hb1 | exact Hu' ].
    (** A [Π] then a [Π]: the two middle [Π]s are equal, so the development
        continues with the domain and codomain of the one we keep. *)
    + assert (Γ ⊢ Π B1 B2 ≈ Π C1 C2 : Typeω@(max _ _))
        by (eapply exp_eq_trans_typ_max; [ exact Hb1 | exact Hc2 ]).
      assert (Γ ⊢ B1 ≈ C1 : Typeω@_ /\ Γ ▹ B1 ⊢ B2 ≈ C2 : Typeω@_) as []
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
  (** The three universe rules, at their own universe terms. *)
  - right; left; exists Typeω@i, Typeω@j;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; lia ].
  - right; left; exists Type⟨M⟩, Type⟨M'⟩;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; assumption ].
  - right; left; exists Type⟨M⟩, Typeω@i;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; assumption ].
  - right; right.
    do 4 eexists; (congruence + firstorder (mautosolve 4 + lia)).
Qed.

Hint Resolve subtyp_spec : mctt.

(** The large tier is never below the small one. *)
Lemma subtyp_large_small_absurd : forall {Γ i t},
    Γ ⊢ Typeω@i ⊆ Type⟨t⟩ ->
    False.
Proof.
  intros * H.
  apply subtyp_spec in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]].
  - eapply exp_eq_typ_suniv_absurd; exact Heq.
  - destruct Hs; eapply exp_eq_typ_suniv_absurd; eassumption.
  - eapply pi_univ_term_absurd; [ apply univ_term_typ | symmetry; exact HA ].
Qed.

End Fixed_GCtx.

(** ** The Normal Forms of Small Types

    A small type's normal form is a type constructor of the small tier: [ℕ],
    [⊤], [⊥], [Level], a [Π], or a small universe at a literal level below the
    one the type lives in.  It is never a large universe (the large tier is
    not below the small one), and never a small universe at a level with an
    atom: such a universe is in no small universe at a literal level, since an
    atom is unbounded under some assignment. *)
Inductive small_typ_nf (n : nat) : nf -> Prop :=
| small_typ_nf_nat : small_typ_nf n ℕⁿ
| small_typ_nf_True : small_typ_nf n ⊤ⁿ
| small_typ_nf_False : small_typ_nf n ⊥ⁿ
| small_typ_nf_level : small_typ_nf n Levelⁿ
| small_typ_nf_pi : forall A B, small_typ_nf n (Πⁿ A B)
| small_typ_nf_univ : forall m, m < n -> small_typ_nf n Typeⁿ@m.
#[export]
Hint Constructors small_typ_nf : mctt.

Section Small_Typ.
  Context {GC : GCtx}.

(** A small universe below a literal one: the canonical level of its level
    term is below the literal.  Read off the semantic subtyping at the
    initial environment, where [per_subtyp_suniv] orders the readbacks. *)
Lemma subtyp_suniv_lit_bound : forall {Γ M n L},
    Γ ⊢ Type⟨M⟩ ⊆ Type@n ->
    nbe_f Γ M Level (nf_lvl_of L) ->
    lvl_le L (lvl_lit (ofin n)).
Proof.
  intros * Hs Hn.
  apply completeness_fundamental_subtyp in Hs as [R [HR [i Hg]]].
  destruct (per_ctx_then_per_env_initial_env HR) as (ρ & ρ' & Hρ & Hρ' & Hrel).
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (⊨ Γ ≈ Γ) as HsΓ by (eexists; exact HR).
  destruct (Hg _ _ HR _ _ (rel_sub_id HsΓ) _ _ _ _ Hrel (eval_sub_id _) (eval_sub_id _))
    as (aσ & a & a'σ' & a' & Ha1 & Ha2 & Ha3 & Ha4 & _ & _ & Hsub).
  inversion Hn; subst.
  dir_inversion_by_head eval_exp; subst.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  inversion Hsub; subst.
  match goal with Hl : per_sublvl _ _ |- _ =>
    destruct (Hl (length Γ)) as (L0 & L1 & HL0 & HL1 & Hle) end.
  functional_read_rewrite_clear.
  assert (Hlit : Rnf ⇓ Levelᵈ (dlvl_lit (ofin n)) in length Γ ↘ nf_lvl_of (lvl_lit (ofin n))) by mauto 3.
  functional_read_rewrite_clear.
  repeat match goal with H : nf_lvl_of _ = nf_lvl_of _ |- _ => apply nf_lvl_of_inj in H; subst end.
  exact Hle.
Qed.

(** The normal form of a small universe is the universe at the normal form of
    its level. *)
Lemma nbe_ty_univ_level : forall {Γ t L},
    nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L) ->
    nbe_f Γ t Level (nf_lvl_of L).
Proof.
  intros * Hn.
  inversion Hn; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  match goal with H1 : fst ?L0 = fst L, H2 : snd ?L0 = snd L |- _ =>
    assert (L0 = L) as -> by (destruct L0, L; cbn in *; congruence) end.
  econstructor; [ eassumption | apply eval_exp_level | eassumption | eassumption ].
Qed.

(** A small universe in normal form inside a small universe at a literal level
    has no atom, and its constant is below the literal. *)
Lemma univ_nf_below_lit : forall {Γ c xs n},
    Γ ⊢ nf_to_exp (univⁿ c xs) : Type@n ->
    nbe_ty_f Γ (nf_to_exp (univⁿ c xs)) (univⁿ c xs) ->
    xs = la_nil /\ olt c (ofin n).
Proof.
  intros * HW Hn.
  cbn [nf_to_exp] in HW, Hn.
  set (T := lvl_exp_of c (la_to_list xs)) in *.
  apply wf_univ_inversion in HW.
  assert (HL : nbe_f Γ T Level (nf_lvl_of (c, xs)))
    by (apply (nbe_ty_univ_level (L := (c, xs))); exact Hn).
  inversion HL; subst.
  dir_inversion_by_head eval_exp; subst.
  match goal with Hr : Rnf ⇓ Levelᵈ ?l in _ ↘ _, HT : ⟦ T ⟧ _ ↘ ?l |- _ =>
    destruct (dlvl_canon_of_read _ _ _ Hr) as [Hsh [L' [HL' Hc]]] end.
  apply nf_lvl_of_inj in HL'; subst L'.
  pose proof (dlvl_canon_suc _ _ _ Hc) as Hc'.
  (** The universe above has the successor level, whose canonical form is the
      canonical successor of [(c, xs)]. *)
  assert (Hn' : nbe_f Γ (succl T) Level (nf_lvl_of (lvl_canon (lvl_suc (c, xs))))).
  { econstructor; [ eassumption | eassumption | apply eval_exp_succl; eassumption
                  | apply dlvl_canon_read; [ apply dlvl_shape_suc | exact Hc' ] ]. }
  pose proof (subtyp_suniv_lit_bound HW Hn') as Hle.
  rewrite lvl_le_correct in Hle.
  assert (Hev : forall ν, ole (osuc (lvl_ev ν (c, xs))) (ofin n)).
  { intros ν; specialize (Hle ν); rewrite lvl_canon_ev, lvl_ev_suc, lvl_ev_lit in Hle; exact Hle. }
  (** An atom is unbounded: assign it [ω]. *)
  destruct xs as [| k a r].
  - split; [ reflexivity |]. specialize (Hev (fun _ => oz)); unfold lvl_ev in Hev; cbn in Hev; ord.
  - exfalso; specialize (Hev (fun _ => (1, 0))); unfold lvl_ev in Hev; cbn in Hev.
    revert Hev; generalize (la_ev (fun _ => (1, 0)) r); intros; ord.
Qed.

(** NbE at a small universe reads the term back as a type. *)
Lemma nbe_suniv_to_nbe_ty : forall {Γ M t W},
    nbe_f Γ M Type⟨t⟩ W ->
    nbe_ty_f Γ M W.
Proof.
  intros * Hn.
  inversion Hn; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_nf; subst.
  econstructor; eassumption.
Qed.

(** The shape of a small type's normal form, when it is not neutral. *)
Lemma small_typ_nf_of_nbe : forall {Γ M n W},
    Γ ⊢ M : Type@n ->
    nbe_f Γ M Type@n W ->
    (forall V, W <> ⇑ⁿ V) ->
    small_typ_nf n W.
Proof.
  intros * HM Hn Hne.
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (HMW : Γ ⊢ M ≈ W : Type@n) by (eapply soundness'; eassumption).
  assert (HW : Γ ⊢ W : Type@n) by (gen_presups; assumption).
  assert (HMl : Γ ⊢ M : Typeω@0)
    by (eapply wf_exp_subtyp'; [ exact HM | apply wf_subtyp_small_large_lit; assumption ]).
  assert (HWl : Γ ⊢ W : Typeω@0)
    by (eapply wf_exp_subtyp'; [ exact HW | apply wf_subtyp_small_large_lit; assumption ]).
  pose proof (nbe_suniv_to_nbe_ty Hn) as Hty.
  (** A normal form is its own normal form. *)
  assert (HWW : nbe_ty_f Γ W W).
  { destruct (soundness_ty HWl) as (C & HC & _).
    assert (W = C) as <- by (exact (idempotent_nbe_ty HMl Hty HC)).
    exact HC. }
  inversion Hty; subst.
  match goal with Hr : Rtyp _ in _ ↘ W |- _ => inversion Hr; subst end.
  - exfalso; cbn in HW; apply wf_typ_inversion in HW; eapply subtyp_large_small_absurd; exact HW.
  - destruct L as [c xs]; unfold nf_univ_of in *; cbn [fst snd] in *.
    destruct (univ_nf_below_lit HW HWW) as [-> Hc].
    destruct c as [a m]; assert (a = 0) as -> by (unfold olt in Hc; cbn in Hc; lia).
    constructor; unfold olt in Hc; cbn in Hc; lia.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - exfalso; eapply Hne; reflexivity.
Qed.

End Small_Typ.

#[export]
Hint Resolve idempotent_nbe_ty : mctt.
#[export]
Hint Resolve nf_of_pi : mctt.
#[export]
Hint Resolve canonical_form_of_pi : mctt.
#[export]
Hint Resolve subtyp_spec : mctt.

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
    [c : ℕ] is a closed neutral, and an axiom of type [Π Typeω@i #0] refutes
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

Theorem canonical_form_of_large_typ : forall {i M},
    ⋅ ⊢ M : Typeω@i ->
    exists W, nbe_f ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
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
    intros; cbn in *; destruct_all; split; intros; mauto 3; try congruence.
  (** A small universe, at whatever level its readback has, is a type
      constructor. *)
  all: try solve [ unfold nf_univ_of; discriminate | constructor ].
  all: gen_presups;
    match_by_head1 (wf_exp gc_deps gc_stack ⋅ Typeω@i) ltac:(fun H => contradict H); mautosolve 4.
Qed.
Hint Resolve canonical_form_of_large_typ : mctt.



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

Theorem consistency : forall {n} M,
    ~ ⋅ ⊢ M : Π Type@n #0.
Proof.
  intros * HM.
  assert (⊢ ⋅) by (gen_presups; assumption).
  assert (⋅ ⊢ ⊥ : Type@n)
    by (eapply wf_exp_subtyp'; [ apply wf_False; assumption | apply wf_subtyp_suniv_le; [ assumption | lia ] ]).
  assert (⋅ ⊢ Type@n : Typeω@0) by (apply wf_univ_large_tm; mauto 3).
  assert (⋅ ▹ Type@n ⊢ #0 : Typeω@0)
    by (eapply wf_exp_subtyp'; [ apply wf_vlookup; [ mauto 3 | constructor ]
                               | apply wf_subtyp_small_large_lit; mauto 3 ]).
  apply (consistency_False (M $ ⊥)).
  change (⋅ ⊢ M $ ⊥ : #0[Id,,⊥]).
  eapply wf_app; eassumption.
Qed.

(** The large tier's statement follows by η: [λ (A : Type@0). M A] inhabits
    [Π Type@0 #0], since [A : Type@0 ⊆ Typeω@i]. *)
Theorem consistency_large : forall {i} M,
    ~ ⋅ ⊢ M : Π Typeω@i #0.
Proof.
  intros * HM.
  assert (⊢ ⋅) by (gen_presups; assumption).
  assert (⋅ ⊢ Type@0 : Typeω@0) by (apply wf_univ_large_tm; mauto 3).
  assert (⊢ ⋅ ▹ Type@0) by mauto 3.
  assert (Hv : ⋅ ▹ Type@0 ⊢ #0 : Typeω@i)
    by (eapply wf_exp_subtyp'; [ apply wf_vlookup; [ assumption | constructor ]
                               | apply wf_subtyp_small_large_lit; assumption ]).
  assert (HMw : ⋅ ▹ Type@0 ⊢ M[↑]ʷ : Π Typeω@i #0).
  { change (⋅ ▹ Type@0 ⊢ M[↑]ʷ : (Π Typeω@i #0)[↑]ʷ).
    eapply wk_preserves_exp; [ eassumption | apply wf_wk_shift; assumption ]. }
  apply (consistency (n := 0) (λ Type@0 (M[↑]ʷ $ #0))).
  eapply wf_fn; [ eassumption |].
  change (⋅ ▹ Type@0 ⊢ M[↑]ʷ $ #0 : #0[Id,,#0]).
  eapply wf_app with (A := Typeω@i) (B := #0) (i := S i);
    [ mauto 3 | apply wf_cumu; eapply wf_vlookup; [ mauto 3 | exact (here Typeω@i (⋅ ▹ Type@0)) ] | exact HMw | exact Hv ].
Qed.

(** Canonicity and consistency at the small tier.  A closed small type has a
    normal form of the precise shape [small_typ_nf]; and there is no closed
    inhabitant of [Π Type@n #0], a corollary of [consistency_False]: [⊥] is a
    small type, so [M $ ⊥ : ⊥].  The large-tier statements are
    [canonical_form_of_large_typ] and [consistency_large]. *)
Theorem canonical_form_of_typ : forall {n M},
    ⋅ ⊢ M : Type@n ->
    exists W, nbe_f ⋅ M Type@n W /\ small_typ_nf n W.
Proof.
  intros * HM.
  assert (⊢ ⋅) by (gen_presups; assumption).
  assert (HMl : ⋅ ⊢ M : Typeω@0)
    by (eapply wf_exp_subtyp'; [ exact HM | apply wf_subtyp_small_large_lit; assumption ]).
  destruct (canonical_form_of_large_typ HMl) as (W & Hnbe & _ & Hne).
  destruct (soundness HM) as (W' & Hnbe' & _).
  assert (W' = W) as ->
    by (eapply functional_nbe_ty;
        [ eapply nbe_suniv_to_nbe_ty; exact Hnbe' | eapply nbe_type_to_nbe_ty; exact Hnbe ]).
  exists W; split; [ exact Hnbe' | eapply small_typ_nf_of_nbe; eassumption ].
Qed.



End Transparent_GCtx.

#[export]
Hint Resolve canonical_form_of_nat : mctt.
#[export]
Hint Resolve canonical_form_of_large_typ : mctt.

(** The theorems above, with the global context explicit. *)
Corollary canonical_form_of_nat_gctx : forall Θ Ξ M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ Ξ ⋅ M ℕ W /\ canonical_nat W.
Proof. intros * Htr HM; exact (@canonical_form_of_nat (gc_mk Θ Ξ) Htr M HM). Qed.

Corollary canonical_form_of_large_typ_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof. intros * Htr HM; exact (@canonical_form_of_large_typ (gc_mk Θ Ξ) Htr i M HM). Qed.

Corollary canonical_form_of_typ_gctx : forall Θ Ξ n M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ small_typ_nf n W.
Proof. intros * Htr HM; exact (@canonical_form_of_typ (gc_mk Θ Ξ) Htr n M HM). Qed.

Corollary consistency_gctx : forall Θ Ξ n M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@n #0).
Proof. intros * Htr; exact (@consistency (gc_mk Θ Ξ) Htr n M). Qed.

Corollary consistency_large_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Typeω@i #0).
Proof. intros * Htr; exact (@consistency_large (gc_mk Θ Ξ) Htr i M). Qed.

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
    forall W, ne_stuck G W -> ne_stuck G' W
with la_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall xs, la_stuck G xs -> la_stuck G' xs.
Proof.
  all: intros G G' HG [] H; cbn in *; destruct_all;
    repeat split; eauto using nf_stuck_mono, ne_stuck_mono, la_stuck_mono.
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

Theorem canonical_form_of_large_typ_stuck : forall {i M},
    ⋅ ⊢ M : Typeω@i ->
    exists W, nbe_f ⋅ M Typeω@i W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
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
    intros; cbn in *; destruct_all;
    try (left; split; [ constructor | intros; unfold nf_univ_of; discriminate ]);
    try (left; split; intros; mauto 3; congruence);
    gen_presups.
  match goal with H : wf_exp _ _ ⋅ _ (ne_to_exp _) |- _ => destruct (closed_neutral_head H) end.
  right; eauto.
Qed.

Theorem canonical_form_of_typ_stuck : forall {n M},
    ⋅ ⊢ M : Type@n ->
    exists W, nbe_f ⋅ M Type@n W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * HM.
  assert (⊢ ⋅) by (gen_presups; assumption).
  assert (HMl : ⋅ ⊢ M : Typeω@0)
    by (eapply wf_exp_subtyp'; [ exact HM | apply wf_subtyp_small_large_lit; assumption ]).
  destruct (canonical_form_of_large_typ_stuck HMl) as (W & Hnbe & Hs & Hc).
  destruct (soundness HM) as (W' & Hnbe' & _).
  assert (W' = W) as ->
    by (eapply functional_nbe_ty;
        [ eapply nbe_suniv_to_nbe_ty; exact Hnbe' | eapply nbe_type_to_nbe_ty; exact Hnbe ]).
  exists W; split; [ exact Hnbe' | split; [ exact Hs |] ].
  destruct Hc as [[_ Hne] | Hneu]; [ left; eapply small_typ_nf_of_nbe; eassumption | right; exact Hneu ].
Qed.

End Stuck_GCtx.

Corollary canonical_form_of_nat_stuck_gctx : forall Θ Ξ M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ Ξ ⋅ M ℕ W /\ canonical_nat_stuck (gstuck Θ Ξ) W.
Proof. intros * HM; exact (@canonical_form_of_nat_stuck (gc_mk Θ Ξ) M HM). Qed.

Corollary canonical_form_of_large_typ_stuck_gctx : forall Θ Ξ i M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ nf_stuck (gstuck Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_large_typ_stuck (gc_mk Θ Ξ) i M HM). Qed.

Corollary canonical_form_of_typ_stuck_gctx : forall Θ Ξ n M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ nf_stuck (gstuck Θ Ξ) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_typ_stuck (gc_mk Θ Ξ) n M HM). Qed.

(** *** Without Axioms *)

Theorem consistency_large_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Typeω@i #0).
Proof.
  intros * Hna HM.
  exact (consistency_large_gctx _ _ _ _ (gc_no_axioms_unseal_transparent _ _ Hna) (unseal_exp _ _ _ _ _ HM)).
Qed.

Theorem consistency_no_axioms : forall Θ Ξ n M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@n #0).
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

Theorem canonical_form_of_large_typ_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ nf_stuck (gopaque Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Typeω@i V /\ is_typ_constr V /\ (forall V', V <> ⇑ⁿ V') /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Typeω@i.
Proof.
  intros * Hna HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_large_typ_stuck_gctx _ _ _ _ HM) as (W & HW & Hs & Hc).
  destruct (canonical_form_of_large_typ_gctx _ _ _ _ Htr HM') as (V & HV & HcV & HnV).
  exists W; split; [ exact HW | split; [| split; [ exact Hc |] ] ].
  - apply (nf_stuck_mono (gstuck Θ Ξ)); [ intros; apply gstuck_gopaque; assumption | exact Hs ].
  - exists V; repeat split; [ exact HV | exact HcV | exact HnV |].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness_gctx' _ _ _ _ _ _ HM HW)).
    pose proof (soundness_gctx' _ _ _ _ _ _ HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

Theorem canonical_form_of_typ_no_axioms : forall Θ Ξ n M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ nf_stuck (gopaque Θ Ξ) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Type@n V /\ small_typ_nf n V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Type@n.
Proof.
  intros * Hna HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_typ_stuck_gctx _ _ _ _ HM) as (W & HW & Hs & Hc).
  destruct (canonical_form_of_typ_gctx _ _ _ _ Htr HM') as (V & HV & HcV).
  exists W; split; [ exact HW | split; [| split; [ exact Hc |] ] ].
  - apply (nf_stuck_mono (gstuck Θ Ξ)); [ intros; apply gstuck_gopaque; assumption | exact Hs ].
  - exists V; repeat split; [ exact HV | exact HcV |].
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
