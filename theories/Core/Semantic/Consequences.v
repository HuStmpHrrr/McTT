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
    exists n, Γ ⊢ t ≈ t' : Level@n.
Proof.
  intros * H.
  assert (exists n, Γ ⊢ t : Level@n) as [n1 Ht] by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  assert (exists n, Γ ⊢ t' : Level@n) as [n2 Ht'] by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  (** Both level terms move to the larger of their two sorts, where the
      equation is stated. *)
  assert (Γ ⊢ t : Level@(Nat.max n1 n2))
    by (eapply wf_exp_subtyp'; [ exact Ht | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
  assert (Γ ⊢ t' : Level@(Nat.max n1 n2))
    by (eapply wf_exp_subtyp'; [ exact Ht' | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
  exists (Nat.max n1 n2).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  match goal with Hl : per_lvl ?l ?l' |- _ => destruct (Hl (length Γ)) as [W [HW HW']] end.
  assert (Γ ⊢ t ≈ W : Level@(Nat.max n1 n2))
    by (eapply soundness';
        [ eassumption
        | econstructor; [ eassumption | apply eval_exp_level | eassumption
                        | eapply read_nf_level_sort; eassumption ] ]).
  assert (Γ ⊢ t' ≈ W : Level@(Nat.max n1 n2))
    by (eapply soundness';
        [ eassumption
        | econstructor; [ eassumption | apply eval_exp_level | eassumption
                        | eapply read_nf_level_sort; eassumption ] ]).
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

(** ** Subtyping of Universe Terms and Level Types

    The three universe rules and the rule for the types of levels, as a
    relation on universe terms and level types: large below large by the
    order on levels, small below small by the order on level terms, small
    below large, and [Level@m] below [Level@n] by the order on sorts. *)
Inductive univ_sub (Γ : ctx) : exp -> exp -> Prop :=
| usub_large : forall i j, i <= j -> univ_sub Γ Typeω@i Typeω@j
| usub_small : forall t t' n,
    Γ ⊢ t : Level@n ->
    Γ ⊢ t' : Level@n ->
    Γ ⊢ maxl t t' ≈ t' : Level@n ->
    univ_sub Γ Type⟨t⟩ Type⟨t'⟩
| usub_small_large : forall t j n,
    Γ ⊢ t : Level@n ->
    univ_sub Γ Type⟨t⟩ Typeω@j
| usub_level : forall m n, m <= n -> univ_sub Γ Level@m Level@n.
Hint Constructors univ_sub : mctt.

(** The two sides of [univ_sub]: a universe term or a type of levels. *)
Inductive sort_term : exp -> Prop :=
| sort_term_univ : forall U, univ_term U -> sort_term U
| sort_term_level : forall n, sort_term Level@n.
Hint Constructors sort_term : mctt.

Lemma univ_sub_sort_term : forall {Γ U V},
    univ_sub Γ U V -> sort_term U /\ sort_term V.
Proof. intros * []; split; first [ apply sort_term_level | apply sort_term_univ; constructor ]. Qed.

(** The types of levels are distinct from the universes and from [Π], and
    [Level@n] determines its sort: in each case the two values are related
    by [per_univ_elem] at the initial environment, which only relates values
    with the same head and, for the types of levels, the same sort. *)
Lemma exp_eq_level_typ_absurd : forall {Γ m i k},
    Γ ⊢ Level@m ≈ Typeω@i : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_suniv_absurd : forall {Γ m t k},
    Γ ⊢ Level@m ≈ Type⟨t⟩ : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_pi_absurd : forall {Γ m A B k},
    Γ ⊢ Level@m ≈ Π A B : Typeω@k ->
    False.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_inj : forall {Γ m n k},
    Γ ⊢ Level@m ≈ Level@n : Typeω@k ->
    m = n.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  reflexivity.
Qed.

(** A [Π] is neither a universe term nor a type of levels. *)
Lemma pi_sort_term_absurd : forall {Γ A B U k},
    sort_term U ->
    Γ ⊢ Π A B ≈ U : Typeω@k ->
    False.
Proof.
  intros * [U' HU | n] H.
  - eapply pi_univ_term_absurd; eassumption.
  - eapply exp_eq_level_pi_absurd; symmetry; exact H.
Qed.

(** Two universe or level-type subtypings compose through an equation
    between the middle ones: the two tiers and the types of levels are
    distinct, the large tier is injective on levels, the small one on level
    terms and the types of levels on sorts. *)
Lemma univ_sub_trans_eq : forall {Γ U V U' W k},
    univ_sub Γ U V ->
    Γ ⊢ V ≈ U' : Typeω@k ->
    univ_sub Γ U' W ->
    univ_sub Γ U W.
Proof.
  intros * H1 Heq H2.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct H1 as [i j Hij | t1 t2 n Ht1 Ht2 H12 | t1 j n Ht1 | m1 m2 Hm12],
           H2 as [i' j' Hij' | t3 t4 n' Ht3 Ht4 H34 | t3 j' n' Ht3 | m3 m4 Hm34].
  (** The middle universes or level types have different heads: impossible. *)
  all: try solve [ exfalso;
                   (eapply exp_eq_typ_suniv_absurd + eapply exp_eq_level_typ_absurd
                    + eapply exp_eq_level_suniv_absurd);
                   (exact Heq + (symmetry; exact Heq)) ].
  - assert (j = i') as -> by mauto 3; constructor; lia.
  - (** The order on level terms through the equation of the middle ones:
        [t1 ≤ t2 ≈ t3 ≤ t4]. *)
    (** The two orders and the equation of the middle terms are at three
        sorts; all four terms move to the largest, where they compose. *)
    destruct (exp_eq_suniv_tm_inj Heq) as [m Heqt].
    set (N := Nat.max (Nat.max n n') m).
    assert (Hup : forall k M, k <= N -> Γ ⊢ M : Level@k -> Γ ⊢ M : Level@N)
      by (intros * ? ?; eapply wf_exp_subtyp'; [ eassumption | apply wf_subtyp_level; assumption ]).
    assert (HupE : forall k M M', k <= N -> Γ ⊢ M ≈ M' : Level@k -> Γ ⊢ M ≈ M' : Level@N)
      by (intros * ? ?; eapply wf_exp_eq_subtyp'; [ eassumption | apply wf_subtyp_level; assumption ]).
    assert (Ht1N : Γ ⊢ t1 : Level@N) by (apply (Hup n); [ subst N; lia | exact Ht1 ]).
    assert (Ht2N : Γ ⊢ t2 : Level@N) by (apply (Hup n); [ subst N; lia | exact Ht2 ]).
    assert (Ht3N : Γ ⊢ t3 : Level@N) by (apply (Hup n'); [ subst N; lia | exact Ht3 ]).
    assert (Ht4N : Γ ⊢ t4 : Level@N) by (apply (Hup n'); [ subst N; lia | exact Ht4 ]).
    assert (H12N : @lvl_sub gc_deps gc_stack N Γ t1 t2)
      by (apply (HupE n); [ subst N; lia | exact H12 ]).
    assert (H34N : @lvl_sub gc_deps gc_stack N Γ t3 t4)
      by (apply (HupE n'); [ subst N; lia | exact H34 ]).
    assert (HeqtN : Γ ⊢ t2 ≈ t3 : Level@N) by (apply (HupE m); [ subst N; lia | exact Heqt ]).
    assert (H23 : @lvl_sub gc_deps gc_stack N Γ t2 t3).
    { unfold lvl_sub.
      transitivity (maxl t3 t3);
        [ apply wf_exp_eq_maxl_cong; [ exact HeqtN | apply wf_exp_eq_refl; exact Ht3N ]
        | apply wf_exp_eq_maxl_idem; exact Ht3N ]. }
    econstructor; [ exact Ht1N | exact Ht4N |].
    change (@lvl_sub gc_deps gc_stack N Γ t1 t4).
    eapply (lvl_sub_trans Ht1N Ht3N Ht4N); [| exact H34N ].
    eapply (lvl_sub_trans Ht1N Ht2N Ht3N); [ exact H12N | exact H23 ].
  - econstructor; eassumption.
  - econstructor; eassumption.
  - assert (m2 = m3) as -> by (eapply exp_eq_level_inj; exact Heq); constructor; lia.
Qed.

(** The three universe rules and the level rule are one disjunct, on
    universe terms and level types: inside a tier it is the order on levels
    or on level terms, from the small tier to the large one it is
    [wf_subtyp_small_large], and between the types of levels it is the order
    on sorts. *)
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
      try pose proof (univ_sub_sort_term Huv) as [Hut Hvt];
      try pose proof (univ_sub_sort_term Hu'v') as [Hu't Hv't].
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
    + exfalso; eapply (pi_sort_term_absurd Hvt), exp_eq_trans_typ_max;
        [ symmetry; exact Hc2 | symmetry; exact Hv ].
    + right; right; exists A1, A2, B1, B2; repeat split; [| | | exact Hsub1 ];
        eexists; [ eassumption | eapply exp_eq_trans_typ_max; eassumption | eassumption ].
    + exfalso; eapply (pi_sort_term_absurd Hu't), exp_eq_trans_typ_max; [ exact Hb1 | exact Hu' ].
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
  (** The three universe rules and the level rule, at their own terms. *)
  - right; left; exists Typeω@i, Typeω@j;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; lia ].
  - right; left; exists Type⟨M⟩, Type⟨M'⟩;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | econstructor; eassumption ].
  - right; left; exists Level@m, Level@n;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; lia ].
  - right; left; exists Type⟨M⟩, Typeω@i;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | econstructor; eassumption ].
  - right; right.
    do 4 eexists; (congruence + firstorder (mautosolve 4 + lia)).
Qed.

Hint Resolve subtyp_spec : mctt.

(** The types of levels are ordered by their sorts. *)
Lemma subtyp_level_inv : forall {Γ m n},
    Γ ⊢ Level@m ⊆ Level@n ->
    m <= n.
Proof.
  intros * H.
  apply subtyp_spec in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]].
  - apply exp_eq_level_inj in Heq; lia.
  - destruct Hs as [i j | t t' ? | t j ? | m' n' Hmn'];
      try solve [ exfalso;
                  (eapply exp_eq_level_typ_absurd + eapply exp_eq_level_suniv_absurd);
                  (exact HU + exact HV + (symmetry; exact HV)) ].
    apply exp_eq_level_inj in HU; symmetry in HV; apply exp_eq_level_inj in HV; lia.
  - exfalso; eapply exp_eq_level_pi_absurd; exact HA.
Qed.

(** A literal of type [Level@n] is of a tier at most [n], and so is the
    constant of a level of type [Level@n]. *)
Lemma wf_llit_sort : forall {Γ o n},
    Γ ⊢ 𝕃ᵒ o : Level@n ->
    fst o <= n.
Proof.
  intros * H; destruct (wf_llit_inversion_sort _ _ _ _ _ H) as (m & Hm & Hs).
  apply subtyp_level_inv in Hs; lia.
Qed.

Lemma lvl_fold_hd_sort : forall {Γ} (l : list (nat * exp)) hd n,
    Γ ⊢ lvl_fold hd l : Level@n ->
    Γ ⊢ hd : Level@n.
Proof.
  intros Γ l; induction l as [| [k a] r IH]; cbn; intros hd n H; [ exact H |].
  apply IH in H; apply wf_maxl_inversion in H as (m & Hhd & _ & Hs).
  eapply wf_exp_subtyp'; [ exact Hhd | exact Hs ].
Qed.

Lemma lvl_exp_of_cst_sort : forall {Γ c} {l : list (nat * exp)} {n},
    Γ ⊢ lvl_exp_of c l : Level@n ->
    fst c <= n.
Proof.
  intros * H.
  destruct l as [| [k a] r]; cbn in H; [ exact (wf_llit_sort H) |].
  destruct c as [[| c1] [| c2]]; try (cbn; lia);
    apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m & Hc & _ & Hs);
    apply subtyp_level_inv in Hs; apply wf_llit_sort in Hc; cbn in *; lia.
Qed.

(** The large tier is never below the small one. *)
Lemma subtyp_large_small_absurd : forall {Γ i t},
    Γ ⊢ Typeω@i ⊆ Type⟨t⟩ ->
    False.
Proof.
  intros * H.
  apply subtyp_spec in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]].
  - eapply exp_eq_typ_suniv_absurd; exact Heq.
  - destruct Hs; solve [ eapply exp_eq_typ_suniv_absurd; eassumption | eapply exp_eq_level_suniv_absurd; eassumption ].
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
| small_typ_nf_level : forall m, small_typ_nf n Levelⁿ@m
| small_typ_nf_pi : forall A B, small_typ_nf n (Πⁿ A B)
| small_typ_nf_univ : forall m, m < n -> small_typ_nf n Typeⁿ@m.
#[export]
Hint Constructors small_typ_nf : mctt.

(** ** The Normal Forms of the Types of a Universe

    The normal forms of the types of a universe [u], when they are not
    neutral: the base types, the types of levels, the [Π]s, the small
    universes whose successor level is below [u] (every small universe when
    [u] is large), and the large universes below [u].  A literal small
    universe's instance is [small_typ_nf] ([typ_nf_below_lit]); a large one's
    gives the type constructors ([typ_nf_below_large]). *)
Inductive typ_nf_below : unf -> nf -> Prop :=
| typ_nf_below_nat : forall u, typ_nf_below u ℕⁿ
| typ_nf_below_True : forall u, typ_nf_below u ⊤ⁿ
| typ_nf_below_False : forall u, typ_nf_below u ⊥ⁿ
| typ_nf_below_level : forall u m, typ_nf_below u Levelⁿ@m
| typ_nf_below_pi : forall u A B, typ_nf_below u (Πⁿ A B)
| typ_nf_below_univ : forall u c xs,
    unf_le (uns (lvl_suc (c, xs))) u ->
    typ_nf_below u (univⁿ c xs)
| typ_nf_below_typ : forall i j, j < i -> typ_nf_below (unl i) Typeωⁿ@j.
#[export]
Hint Constructors typ_nf_below : mctt.

(** Below the literal [Type@n], a universe has no atom (an atom is
    unbounded below a finite literal, [lvl_le_lit_closed]) and a finite
    level below [n]. *)
Lemma typ_nf_below_lit : forall n W,
    typ_nf_below (uns (lvl_lit (ofin n))) W ->
    small_typ_nf n W.
Proof.
  intros * H; inversion H as [| | | | | ? c xs Hle |]; subst; try constructor.
  cbn [unf_le] in Hle.
  pose proof (lvl_le_lit_closed _ _ Hle) as Hxs.
  destruct xs as [| k s a r]; cbn in Hxs; [| discriminate ].
  rewrite lvl_le_correct in Hle; specialize (Hle _ lvl_adm_zero).
  rewrite lvl_ev_suc in Hle; unfold lvl_ev, lvl_lit in Hle; cbn in Hle.
  destruct c as [a m]; assert (a = 0) as -> by ord.
  constructor; ord.
Qed.

(** Below a large universe, a type constructor that is not neutral. *)
Lemma typ_nf_below_large : forall i W,
    typ_nf_below (unl i) W ->
    is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof.
  intros * H; inversion H; subst; (split; [ cbn; constructor | intros ? Heq; discriminate Heq ]).
Qed.

Section Small_Typ.
  Context {GC : GCtx}.

(** A small universe below another: the canonical level of its level term
    is below the other's.  Read off the semantic subtyping at the initial
    environment, where [per_subtyp_suniv] orders the readbacks. *)
Lemma subtyp_suniv_bound : forall {Γ M N L L'},
    Γ ⊢ Type⟨M⟩ ⊆ Type⟨N⟩ ->
    nbe_f Γ M Level (nf_lvl_of L) ->
    nbe_f Γ N Level (nf_lvl_of L') ->
    lvl_le L L'.
Proof.
  intros * Hs Hn Hn'.
  apply completeness_fundamental_subtyp in Hs as [R [HR [i Hg]]].
  destruct (per_ctx_then_per_env_initial_env HR) as (ρ & ρ' & Hρ & Hρ' & Hrel).
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (⊨ Γ ≈ Γ) as HsΓ by (eexists; exact HR).
  destruct (Hg _ _ HR _ _ (rel_sub_id HsΓ) _ _ _ _ Hrel (eval_sub_id _) (eval_sub_id _))
    as (aσ & a & a'σ' & a' & Ha1 & Ha2 & Ha3 & Ha4 & _ & _ & Hsub).
  inversion Hn; subst.
  inversion Hn'; subst.
  dir_inversion_by_head eval_exp; subst.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  inversion Hsub; subst.
  match goal with Hl : per_sublvl _ _ |- _ =>
    destruct (Hl (length Γ)) as (L0 & L1 & HL0 & HL1 & Hle) end.
  functional_read_rewrite_clear.
  repeat match goal with H : nf_lvl_of _ = nf_lvl_of _ |- _ => apply nf_lvl_of_inj in H; subst end.
  exact Hle.
Qed.

(** The instance at a literal. *)
Corollary subtyp_suniv_lit_bound : forall {Γ M n L},
    Γ ⊢ Type⟨M⟩ ⊆ Type@n ->
    nbe_f Γ M Level (nf_lvl_of L) ->
    lvl_le L (lvl_lit (ofin n)).
Proof.
  intros * Hs Hn; eapply subtyp_suniv_bound; [ exact Hs | exact Hn |].
  inversion Hn; subst.
  econstructor; [ eassumption | eassumption | apply eval_exp_llit |].
  dir_inversion_by_head eval_exp; subst; mauto 3.
Qed.

(** The normal form of a small universe is the universe at the normal form of
    its level. *)
Lemma nbe_ty_univ_level : forall {Γ t L n},
    nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L) ->
    nbe_f Γ t Level@n (nf_lvl_of L).
Proof.
  intros * Hn.
  inversion Hn; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  match goal with H1 : fst ?L0 = fst L, H2 : snd ?L0 = snd L |- _ =>
    assert (L0 = L) as -> by (destruct L0, L; cbn in *; congruence) end.
  econstructor; [ eassumption | apply eval_exp_level | eassumption | eapply read_nf_level_sort; eassumption ].
Qed.

(** The level of a small universe in normal form is a canonical level of a
    sort its level term has: its constant is of a tier at most that sort, and
    each atom is a level of its own sort ([soundness_lvl_ws]). *)
Lemma univ_nf_ws : forall {Γ c xs A},
    Γ ⊢ Type⟨lvl_exp_of c (la_to_list xs)⟩ : A ->
    nbe_ty_f Γ Type⟨lvl_exp_of c (la_to_list xs)⟩ (univⁿ c xs) ->
    exists n, Γ ⊢ lvl_exp_of c (la_to_list xs) : Level@n /\ fst c <= n /\ @la_ws gc_deps gc_stack n Γ xs.
Proof.
  intros * HA Hn.
  destruct (wf_univ_lvl_inversion HA) as [n Ht].
  pose proof (nbe_ty_univ_level (L := (c, xs)) (n := n) Hn) as Hl.
  pose proof (soundness_lvl_ws Ht Hl) as Hws; cbn in Hws.
  exists n; split; [ exact Ht | exact Hws ].
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

(** A small universe at a literal level reads back as itself. *)
Lemma nbe_ty_suniv_lit : forall {Γ n W},
    nbe_ty_f Γ Type⟨𝕃ᵒ n⟩ W ->
    W = nf_univ n la_nil.
Proof.
  intros * Hn.
  dir_inversion_clear_by_head nbe_ty; dir_inversion_by_head eval_exp; subst.
  match goal with H : eval_exp _ _ (a_llit _) _ _ |- _ => inversion H; subst end.
  dir_inversion_by_head read_typ; subst.
  match goal with H : Rnf ⇓ Levelᵈ (dlvl_lit n) in _ ↘ _ |- _ =>
    pose proof (read_nf_dlvl_lit n (length Γ)) as Hk;
    assert (L = lvl_lit n) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption) end.
  reflexivity.
Qed.

(** The large universes are ordered by their indices. *)
Lemma subtyp_large_inv : forall {Γ i j},
    Γ ⊢ Typeω@i ⊆ Typeω@j ->
    i <= j.
Proof.
  intros * H.
  apply subtyp_spec in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (A1 & A2 & B1 & B2 & [k1 HA] & _)]].
  - apply exp_eq_typ_implies_eq_level in Heq; lia.
  - destruct Hs as [i' j' Hij | t t' ? | t j' ? | m' n' Hmn'].
    + apply exp_eq_typ_implies_eq_level in HU; symmetry in HV; apply exp_eq_typ_implies_eq_level in HV; lia.
    + exfalso; eapply exp_eq_typ_suniv_absurd; exact HU.
    + exfalso; eapply exp_eq_typ_suniv_absurd; exact HU.
    + exfalso; eapply exp_eq_level_typ_absurd; symmetry; exact HU.
  - exfalso; eapply pi_univ_term_absurd; [ apply univ_term_typ | symmetry; exact HA ].
Qed.

(** The normal form of a universe term is a universe normal form: [Typeω@i]
    is its own, and [Type⟨t⟩]'s is the universe at the normal form of [t]. *)
Lemma nbe_ty_univ_term : forall {Γ T W},
    univ_term T ->
    nbe_ty_f Γ T W ->
    exists u, W = univ_nf u.
Proof.
  intros * HT Hn; inversion HT; subst;
    dir_inversion_clear_by_head nbe_ty; dir_inversion_by_head eval_exp; subst;
    dir_inversion_by_head read_typ; subst.
  - exists (unl i); reflexivity.
  - exists (uns L); reflexivity.
Qed.

Lemma nbe_ty_typ_univ_nf : forall {Γ i u},
    nbe_ty_f Γ Typeω@i (univ_nf u) ->
    u = unl i.
Proof.
  intros * Hn; dir_inversion_clear_by_head nbe_ty; dir_inversion_by_head eval_exp; subst.
  destruct u; cbn in *; match goal with H : Rtyp _ in _ ↘ _ |- _ => inversion H; subst end; congruence.
Qed.

Lemma nbe_ty_suniv_univ_nf : forall {Γ t u},
    nbe_ty_f Γ Type⟨t⟩ (univ_nf u) ->
    exists L, u = uns L /\ nbe_f Γ t Level (nf_lvl_of L).
Proof.
  intros * Hn; destruct u as [L | i].
  - exists L; split; [ reflexivity | exact (nbe_ty_univ_level Hn) ].
  - exfalso; dir_inversion_clear_by_head nbe_ty; dir_inversion_by_head eval_exp; subst.
    cbn in *; match goal with H : Rtyp _ in _ ↘ _ |- _ => inversion H end.
Qed.

Lemma nbe_ty_lit_univ_nf : forall {Γ n u},
    nbe_ty_f Γ Type@n (univ_nf u) ->
    u = uns (lvl_lit (ofin n)).
Proof.
  intros * Hn; apply nbe_ty_suniv_lit in Hn.
  destruct u as [[c xs] | i]; cbn in Hn; inversion Hn; reflexivity.
Qed.

(** NbE at a universe term reads the term back as a type. *)
Lemma nbe_univ_term_to_nbe_ty : forall {Γ T M W},
    univ_term T ->
    nbe_f Γ M T W ->
    nbe_ty_f Γ M W.
Proof. intros * [] Hn; [ eapply nbe_type_to_nbe_ty; exact Hn | eapply nbe_suniv_to_nbe_ty; exact Hn ]. Qed.

(** A type of a universe term is a type of a large universe. *)
Lemma univ_term_large : forall {Γ T M},
    univ_term T ->
    Γ ⊢ M : T ->
    exists k, Γ ⊢ M : Typeω@k.
Proof.
  intros * [i | t] HM; [ eauto |].
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (exists k, Γ ⊢ Type⟨t⟩ : Typeω@k) as [k Hk] by (gen_presups; eauto).
  destruct (wf_univ_lvl_inversion Hk) as [n Ht].
  exists 0; eapply wf_exp_subtyp'; [ exact HM | eapply wf_subtyp_small_large; eassumption ].
Qed.

(** [⊥] is a type of every universe. *)
Lemma wf_False_univ_term : forall {Γ T i},
    univ_term T ->
    Γ ⊢ T : Typeω@i ->
    Γ ⊢ ⊥ : T.
Proof.
  intros * [j | t] HT; assert (⊢ Γ) by (gen_presups; assumption).
  - apply wf_False_large; assumption.
  - destruct (wf_univ_lvl_inversion HT) as [n Ht].
    eapply wf_exp_subtyp'; [ apply wf_False; assumption |].
    eapply wf_subtyp_suniv; [ assumption | apply wf_llit; [ cbn; lia | assumption ] | exact Ht
                            | apply wf_exp_eq_maxl_zero; exact Ht ].
Qed.

(** The shape of the normal form of a type of a universe term, when it is
    not neutral.  A large universe [Typeω@j] in [Typeω@i] has [j < i], and is
    in no small universe; a small universe [Type⟨l⟩] in [Type⟨t⟩] has the
    successor of [l] below the normal form of [t] ([subtyp_suniv_bound]). *)
Lemma typ_nf_below_of_nbe : forall {Γ M T u W},
    univ_term T ->
    Γ ⊢ M : T ->
    nbe_ty_f Γ T (univ_nf u) ->
    nbe_f Γ M T W ->
    (forall V, W <> ⇑ⁿ V) ->
    typ_nf_below u W.
Proof.
  intros * HT HM HnT Hn Hne.
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (HMW : Γ ⊢ M ≈ W : T) by (eapply soundness'; eassumption).
  assert (HW : Γ ⊢ W : T) by (gen_presups; assumption).
  destruct (univ_term_large HT HM) as [k HMl].
  destruct (univ_term_large HT HW) as [k' HWl].
  pose proof (nbe_univ_term_to_nbe_ty HT Hn) as Hty.
  (** A normal form is its own normal form. *)
  assert (HWW : nbe_ty_f Γ W W).
  { destruct (soundness_ty HWl) as (C & HC & _).
    assert (W = C) as <- by (exact (idempotent_nbe_ty HMl Hty HC)).
    exact HC. }
  inversion Hty; subst.
  match goal with Hr : Rtyp _ in _ ↘ W |- _ => inversion Hr; subst end.
  all: try solve [ constructor | exfalso; eapply Hne; reflexivity ].
  - destruct HT as [i0 | t].
    + apply nbe_ty_typ_univ_nf in HnT as ->.
      cbn in HW; apply wf_typ_inversion, subtyp_large_inv in HW.
      constructor; lia.
    + exfalso; cbn in HW; apply wf_typ_inversion in HW; eapply subtyp_large_small_absurd; exact HW.
  - destruct L as [c xs]; unfold nf_univ_of in *; cbn [fst snd] in *.
    constructor.
    destruct HT as [i | t].
    + apply nbe_ty_typ_univ_nf in HnT as ->; exact I.
    + destruct (nbe_ty_suniv_univ_nf HnT) as (L' & -> & HL').
      cbn [unf_le nf_to_exp] in *.
      set (E := lvl_exp_of c (la_to_list xs)) in *.
      apply wf_univ_inversion in HW.
      assert (HL : nbe_f Γ E Level (nf_lvl_of (c, xs))) by (apply (nbe_ty_univ_level (L := (c, xs))); exact HWW).
      inversion HL; subst.
      dir_inversion_by_head eval_exp; subst.
      match goal with Hr : Rnf ⇓ Levelᵈ ?l in _ ↘ _, HE : ⟦ E ⟧ _ ↘ ?l |- _ =>
        destruct (dlvl_canon_of_read _ _ _ Hr) as [Hsh [L0 [HL0 Hc]]] end.
      apply nf_lvl_of_inj in HL0; subst L0.
      (** The universe above has the successor level, whose canonical form
          is the canonical successor of [(c, xs)]. *)
      pose proof (dlvl_canon_suc _ _ _ Hc) as Hc'.
      assert (Hn' : nbe_f Γ (succl E) Level (nf_lvl_of (lvl_canon (lvl_suc (c, xs))))).
      { econstructor; [ eassumption | eassumption | apply eval_exp_succl; eassumption
                      | apply dlvl_canon_read; [ apply dlvl_shape_suc | exact Hc' ] ]. }
      pose proof (subtyp_suniv_bound HW Hn' HL') as Hle.
      rewrite lvl_le_correct in *; intros ν Hν; specialize (Hle ν Hν).
      rewrite lvl_canon_ev in Hle by exact Hν; exact Hle.
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

(** Canonicity at a universe.  A closed type of a universe term [T] has a
    normal form of the shape [typ_nf_below u], where [u] is the normal form
    of [T] ([typ_nf_below_of_nbe]): it is not neutral, since at a
    transparent context a closed neutral has no type.  At [Typeω@i] this is
    [canonical_form_of_large_typ], at [Type@n] [canonical_form_of_typ_lit]. *)
Theorem canonical_form_of_typ : forall {T M},
    univ_term T ->
    ⋅ ⊢ M : T ->
    exists u W, nbe_ty_f ⋅ T (univ_nf u) /\ nbe_f ⋅ M T W /\ typ_nf_below u W.
Proof.
  intros * HT HM.
  destruct (soundness HM) as (W & Hn & HMW).
  assert (exists k, ⋅ ⊢ T : Typeω@k) as [k Hk] by (gen_presups; eauto).
  destruct (soundness_ty Hk) as (U & HU & _).
  destruct (nbe_ty_univ_term HT HU) as [u ->].
  exists u, W; split; [ exact HU | split; [ exact Hn |] ].
  eapply typ_nf_below_of_nbe; [ exact HT | exact HM | exact HU | exact Hn |].
  intros V ->.
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hn) as Hc; cbn in Hc.
  assert (⋅ ⊢ V : T) by (gen_presups; assumption).
  eapply no_closed_neutral; eassumption.
Qed.

Corollary canonical_form_of_large_typ : forall {i M},
    ⋅ ⊢ M : Typeω@i ->
    exists W, nbe_f ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof.
  intros * HM; destruct (canonical_form_of_typ (univ_term_typ i) HM) as (u & W & Hu & Hn & Hb).
  apply nbe_ty_typ_univ_nf in Hu as ->; exists W; split; [ exact Hn | exact (typ_nf_below_large _ _ Hb) ].
Qed.
Hint Resolve canonical_form_of_large_typ : mctt.

Corollary canonical_form_of_typ_lit : forall {n M},
    ⋅ ⊢ M : Type@n ->
    exists W, nbe_f ⋅ M Type@n W /\ small_typ_nf n W.
Proof.
  intros * HM; destruct (canonical_form_of_typ (univ_term_suniv _) HM) as (u & W & Hu & Hn & Hb).
  apply nbe_ty_lit_univ_nf in Hu as ->; exists W; split; [ exact Hn | exact (typ_nf_below_lit _ _ Hb) ].
Qed.

(** Consistency at a universe: there is no closed inhabitant of [Π T #0]
    for a universe term [T], a corollary of [consistency_False]: [⊥] is a
    type of every universe ([wf_False_univ_term]), so [M $ ⊥ : ⊥].  At
    [Typeω@i] this is [consistency_large], at [Type@n] [consistency_lit]. *)
Theorem consistency : forall T M,
    univ_term T ->
    ~ ⋅ ⊢ M : Π T #0.
Proof.
  intros * HT HM.
  assert (exists i, ⋅ ⊢ Π T #0 : Typeω@i) as [i Hpi] by (gen_presups; eauto).
  destruct (wf_pi_inversion' Hpi) as [HTi Hv].
  assert (⋅ ⊢ ⊥ : T) by (eapply wf_False_univ_term; eassumption).
  apply (consistency_False (M $ ⊥)).
  change (⋅ ⊢ M $ ⊥ : #0[Id,,⊥]).
  eapply wf_app; eassumption.
Qed.

Corollary consistency_large : forall {i} M,
    ~ ⋅ ⊢ M : Π Typeω@i #0.
Proof. intros; apply consistency, univ_term_typ. Qed.

Corollary consistency_lit : forall {n} M,
    ~ ⋅ ⊢ M : Π Type@n #0.
Proof. intros; apply consistency, univ_term_suniv. Qed.

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

Corollary canonical_form_of_typ_gctx : forall Θ Ξ T M,
    gc_transparent Θ Ξ ->
    univ_term T ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : T ->
    exists u W, nbe_ty Θ Ξ ⋅ T (univ_nf u) /\ nbe Θ Ξ ⋅ M T W /\ typ_nf_below u W.
Proof. intros * Htr HT HM; exact (@canonical_form_of_typ (gc_mk Θ Ξ) Htr T M HT HM). Qed.

Corollary canonical_form_of_large_typ_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall V, W <> ⇑ⁿ V).
Proof. intros * Htr HM; exact (@canonical_form_of_large_typ (gc_mk Θ Ξ) Htr i M HM). Qed.

Corollary canonical_form_of_typ_lit_gctx : forall Θ Ξ n M,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ small_typ_nf n W.
Proof. intros * Htr HM; exact (@canonical_form_of_typ_lit (gc_mk Θ Ξ) Htr n M HM). Qed.

Corollary consistency_gctx : forall Θ Ξ T M,
    gc_transparent Θ Ξ ->
    univ_term T ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π T #0).
Proof. intros * Htr; exact (@consistency (gc_mk Θ Ξ) Htr T M). Qed.

Corollary consistency_large_gctx : forall Θ Ξ i M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Typeω@i #0).
Proof. intros * Htr; exact (@consistency_large (gc_mk Θ Ξ) Htr i M). Qed.

Corollary consistency_lit_gctx : forall Θ Ξ n M,
    gc_transparent Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@n #0).
Proof. intros * Htr; exact (@consistency_lit (gc_mk Θ Ξ) Htr n M). Qed.

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

(** Canonicity at a universe, at any global context: the normal form is of
    the shape [typ_nf_below u], or a neutral headed by a stuck global. *)
Theorem canonical_form_of_typ_stuck : forall {T M},
    univ_term T ->
    ⋅ ⊢ M : T ->
    exists u W, nbe_ty_f ⋅ T (univ_nf u) /\ nbe_f ⋅ M T W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      (typ_nf_below u W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * HT HM.
  destruct (soundness HM) as (W & Hn & HMW).
  assert (exists k, ⋅ ⊢ T : Typeω@k) as [k Hk] by (gen_presups; eauto).
  destruct (soundness_ty Hk) as (U & HU & _).
  destruct (nbe_ty_univ_term HT HU) as [u ->].
  exists u, W; split; [ exact HU | split; [ exact Hn | split; [ exact (nbe_stuck _ _ _ _ _ _ Hn) |] ] ].
  assert (Hd : (exists V, W = ⇑ⁿ V) \/ (forall V, W <> ⇑ⁿ V))
    by (destruct W; try (right; intros ? Heq; discriminate Heq); left; eexists; reflexivity).
  destruct Hd as [[V ->] | Hne].
  - right; assert (HV : ⋅ ⊢ V : T) by (gen_presups; assumption).
    destruct (closed_neutral_head HV) as [p Hp]; eauto.
  - left; eapply typ_nf_below_of_nbe; eassumption.
Qed.

Corollary canonical_form_of_large_typ_stuck : forall {i M},
    ⋅ ⊢ M : Typeω@i ->
    exists W, nbe_f ⋅ M Typeω@i W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * HM; destruct (canonical_form_of_typ_stuck (univ_term_typ i) HM) as (u & W & Hu & Hn & Hs & Hc).
  apply nbe_ty_typ_univ_nf in Hu as ->; exists W; split; [ exact Hn | split; [ exact Hs |] ].
  destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_large _ _ Hb) | right; exact Hneu ].
Qed.

Corollary canonical_form_of_typ_lit_stuck : forall {n M},
    ⋅ ⊢ M : Type@n ->
    exists W, nbe_f ⋅ M Type@n W /\ nf_stuck (gstuck gc_deps gc_stack) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof.
  intros * HM; destruct (canonical_form_of_typ_stuck (univ_term_suniv _) HM) as (u & W & Hu & Hn & Hs & Hc).
  apply nbe_ty_lit_univ_nf in Hu as ->; exists W; split; [ exact Hn | split; [ exact Hs |] ].
  destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_lit _ _ Hb) | right; exact Hneu ].
Qed.

End Stuck_GCtx.

Corollary canonical_form_of_nat_stuck_gctx : forall Θ Ξ M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ℕ ->
    exists W, nbe Θ Ξ ⋅ M ℕ W /\ canonical_nat_stuck (gstuck Θ Ξ) W.
Proof. intros * HM; exact (@canonical_form_of_nat_stuck (gc_mk Θ Ξ) M HM). Qed.

Corollary canonical_form_of_typ_stuck_gctx : forall Θ Ξ T M,
    univ_term T ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : T ->
    exists u W, nbe_ty Θ Ξ ⋅ T (univ_nf u) /\ nbe Θ Ξ ⋅ M T W /\ nf_stuck (gstuck Θ Ξ) W /\
      (typ_nf_below u W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HT HM; exact (@canonical_form_of_typ_stuck (gc_mk Θ Ξ) T M HT HM). Qed.

Corollary canonical_form_of_large_typ_stuck_gctx : forall Θ Ξ i M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ nf_stuck (gstuck Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_large_typ_stuck (gc_mk Θ Ξ) i M HM). Qed.

Corollary canonical_form_of_typ_lit_stuck_gctx : forall Θ Ξ n M,
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ nf_stuck (gstuck Θ Ξ) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)).
Proof. intros * HM; exact (@canonical_form_of_typ_lit_stuck (gc_mk Θ Ξ) n M HM). Qed.

(** *** Without Axioms *)

Theorem consistency_no_axioms : forall Θ Ξ T M,
    gc_no_axioms Θ Ξ ->
    univ_term T ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π T #0).
Proof.
  intros * Hna HT HM.
  exact (consistency_gctx _ _ _ _ (gc_no_axioms_unseal_transparent _ _ Hna) HT (unseal_exp _ _ _ _ _ HM)).
Qed.

Corollary consistency_large_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Typeω@i #0).
Proof. intros * Hna; apply consistency_no_axioms; [ exact Hna | apply univ_term_typ ]. Qed.

Corollary consistency_lit_no_axioms : forall Θ Ξ n M,
    gc_no_axioms Θ Ξ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π Type@n #0).
Proof. intros * Hna; apply consistency_no_axioms; [ exact Hna | apply univ_term_suniv ]. Qed.

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

(** At a universe term [T]: sealed, the normal form is of the shape
    [typ_nf_below u] or a neutral headed by an opaque definition; unsealed,
    it is of the shape [typ_nf_below u'], where [u] and [u'] are the normal
    forms of [T] sealed and unsealed; and the two normal forms are equal once
    the definitions unfold. *)
Theorem canonical_form_of_typ_no_axioms : forall Θ Ξ T M,
    gc_no_axioms Θ Ξ ->
    univ_term T ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : T ->
    exists u W, nbe_ty Θ Ξ ⋅ T (univ_nf u) /\ nbe Θ Ξ ⋅ M T W /\ nf_stuck (gopaque Θ Ξ) W /\
      (typ_nf_below u W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists u' V, nbe_ty (gds_unseal Θ) (gs_unseal Ξ) ⋅ T (univ_nf u') /\
        nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M T V /\ typ_nf_below u' V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : T.
Proof.
  intros * Hna HT HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (canonical_form_of_typ_stuck_gctx _ _ _ _ HT HM) as (u & W & Hu & HW & Hs & Hc).
  destruct (canonical_form_of_typ_gctx _ _ _ _ Htr HT HM') as (u' & V & Hu' & HV & HcV).
  exists u, W; split; [ exact Hu | split; [ exact HW | split; [| split; [ exact Hc |] ] ] ].
  - apply (nf_stuck_mono (gstuck Θ Ξ)); [ intros; apply gstuck_gopaque; assumption | exact Hs ].
  - exists u', V; split; [ exact Hu' | split; [ exact HV | split; [ exact HcV |] ] ].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness_gctx' _ _ _ _ _ _ HM HW)).
    pose proof (soundness_gctx' _ _ _ _ _ _ HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

Corollary canonical_form_of_large_typ_no_axioms : forall Θ Ξ i M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ nf_stuck (gopaque Θ Ξ) W /\
      ((is_typ_constr W /\ (forall V, W <> ⇑ⁿ V)) \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Typeω@i V /\ is_typ_constr V /\ (forall V', V <> ⇑ⁿ V') /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Typeω@i.
Proof.
  intros * Hna HM.
  destruct (canonical_form_of_typ_no_axioms _ _ _ _ Hna (univ_term_typ i) HM)
    as (u & W & Hu & HW & Hs & Hc & u' & V & Hu' & HV & HcV & HWV).
  apply (@nbe_ty_typ_univ_nf (gc_mk Θ Ξ)) in Hu as ->.
  apply (@nbe_ty_typ_univ_nf (gc_mk (gds_unseal Θ) (gs_unseal Ξ))) in Hu' as ->.
  exists W; split; [ exact HW | split; [ exact Hs | split ] ].
  - destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_large _ _ Hb) | right; exact Hneu ].
  - destruct (typ_nf_below_large _ _ HcV) as [HcV' HnV].
    exists V; split; [ exact HV | split; [ exact HcV' | split; [ exact HnV | exact HWV ] ] ].
Qed.

Corollary canonical_form_of_typ_lit_no_axioms : forall Θ Ξ n M,
    gc_no_axioms Θ Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ nf_stuck (gopaque Θ Ξ) W /\
      (small_typ_nf n W \/ (exists V p, W = ⇑ⁿ V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Type@n V /\ small_typ_nf n V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Type@n.
Proof.
  intros * Hna HM.
  destruct (canonical_form_of_typ_no_axioms _ _ _ _ Hna (univ_term_suniv _) HM)
    as (u & W & Hu & HW & Hs & Hc & u' & V & Hu' & HV & HcV & HWV).
  apply (@nbe_ty_lit_univ_nf (gc_mk Θ Ξ)) in Hu as ->.
  apply (@nbe_ty_lit_univ_nf (gc_mk (gds_unseal Θ) (gs_unseal Ξ))) in Hu' as ->.
  exists W; split; [ exact HW | split; [ exact Hs | split ] ].
  - destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_lit _ _ Hb) | right; exact Hneu ].
  - exists V; split; [ exact HV | split; [ exact (typ_nf_below_lit _ _ HcV) | exact HWV ] ].
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
