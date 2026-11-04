(** * Presupposition

    Presupposition for term equality, refinement and substitution
    equivalence: the context is well formed, both sides are well typed, and
    the type is a type.  Presupposition for typing is [presup_exp] in
    [Core.Syntactic.System.Lemmas], derived from the mutual theorem
    [presup_global].

    These statements come after [sub_eq_preserves_exp], because the
    congruences whose type depends on a left premise, such as application's
    [B[Id ,, N]], type their right-hand side at the type built from the right
    premises, and [sub_eq_preserves_exp] bridges the two.  That lemma is
    about typing derivations only, so it is proved by induction on [wf_exp]
    without presupposition.

    The type of a term is a type of some sort, a universe or [Prop]
    ([⊢ᵗ]), and so is each side of a refinement, each at its own sort.

    None of the three statements needs a mutual induction:

    - the [wf_exp_eq_subtyp] case of [presup_exp_eq] gets
      [Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i] from a premise rather than from
      [presup_subtyp];
    - the [wf_subtyp_refl] case of [presup_subtyp] uses the finished
      [presup_exp_eq].

    Both rely on extra premises that [Definitions] carries on those two rules
    for this purpose.

    A few of the term-equality rules need an argument of their own, all for
    the same reason: a congruence rule states its equation at the type built
    from the left premises, so the right-hand side is typed by its own rule,
    at its own type, and then moved to the type of the equation by
    [wf_conv].  The congruence rule for [let module] premises its right-hand
    side instead, and only its left-hand side needs the body's type to be a
    type.  The remaining rules, including [η] (whose right-hand side is
    [wf_fn_eta_expand]), are hints. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Tactics.
From Mctt.Core.Syntactic.System.Global Require Import LookupSound.
Import Syntax_Notations Wk_Notations.

(** ** The Two Sides of a Term Equation *)

(** A [Π] typed, and equal to a [Π] of equal parts, at one sort. *)
#[warnings="-cannot-define-projection"]
Record pi_typed_and_congruent (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (κd κc : abs_kind) (A B A' B' : typ) : Prop :=
  mk_pi_typed_and_congruent
  { (** The sort both are at *)
    pi_typed_and_congruent_sort : exp
    (** It is a sort of types *)
  ; pi_typed_and_congruent_sort_is_type : type_sort pi_typed_and_congruent_sort
    (** The [Π] is of it *)
  ; pi_typed_and_congruent_typed : Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κd κc A B : pi_typed_and_congruent_sort
    (** The two [Π]s are equal at it *)
  ; pi_typed_and_congruent_congruent : Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κd κc A B ≈ a_pi κd κc A' B' : pi_typed_and_congruent_sort }.

(** A [Π] at the kinds [pi_kinds κd κc], at the premises of [wf_fn]: a
    type of the sort of [κc]; between types of levels, [LevelSort]. *)
Lemma wf_pi_cong_at_kinds : forall Θ Ξ Γ κd κc A A' B B' Srt i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    sort_kind Srt κd ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B ≈ B' : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc ->
    pi_typed_and_congruent Θ Ξ Γ κd κc A B A' B'.
Proof.
  intros * HA HS HAA HB HBB Hk.
  destruct (abs_kind_eq_dec κc ak_level) as [-> | Hl].
  - (* between types of levels: [LevelSort] *)
    inversion Hk; subst; inversion HS; subst.
    assert (HU : Θ ⍮ Ξ ⍮ Γ ⊢ᵤ Typeω@0) by (apply wf_is_univ_large; eapply presup_exp_ctx, HA).
    exists LevelSort; [ constructor | |].
    + eapply wf_pi with (U := Typeω@0) (κd := ak_level) (κc := ak_level); [ exact HU | exact HA | exact HB | constructor ].
    + eapply wf_exp_eq_pi_cong with (U := Typeω@0) (κd := ak_level) (κc := ak_level);
        [ exact HU | exact HA | exact HAA | exact HBB | constructor ].
  - destruct (wf_pi_sort_at _ _ _ _ _ _ _ _ _ HA HS HB Hl) as [j Hj].
    destruct (wf_exp_eq_pi_sort_at _ _ _ _ _ _ _ _ _ _ _ HA HS HAA HBB Hl) as [k Hk'].
    exists (abs_kind_sort κc Typeω@(max j k));
      [ apply type_sort_abs_kind; constructor | exact (lift_rel_max_left _ _ _ _ _ _ _ Hj)
      | exact (lift_rel_eq_max_right _ _ _ _ _ _ _ _ Hk') ].
Qed.

Lemma presup_exp_eq_sides : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ M' : A.
Proof.
  induction 1; assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2; destruct_conjs; split; mauto 3.

  (** Members: the left-hand side by [wf_mem], at the type the lookup reads,
      which is a type; a δ-reduct is of that type. *)
  all: try solve [
    match goal with HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ _, Hm : mdenote _ _ _ (me_mem ?H _) ?R, Ht : mdesc_type ?R = Some ?A |- _ =>
      let Hv := fresh "Hv" in
      pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hv;
      destruct (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht) as [[? HS HA] HM];
      first [ eapply wf_mem; [ eapply wf_modexp_eq_refl_left; exact HH | exact Hm | exact Ht | exact HA | exact HS | exact HM ]
            | apply HM; assumption ]
    end ].

  (** The universe congruence is stated at [Type⟨succl M⟩], so its
      right-hand side has to be moved there from [Type⟨succl M'⟩].  Its goal
      is the only one of that shape. *)
  all: try solve [ eapply wf_univ_cong_right; mauto 2 ].

  (** The left-hand side of absorption is at the sort above the one its
      level is typed at, and the right-hand side of the distributivity
      equation of levels is one level operation deeper than [mauto 3]
      reaches. *)
  1:{ apply wf_maxl;
      [ eapply wf_exp_subtyp'; [ eassumption | apply wf_subtyp_level; [ lia | assumption ] ]
      | apply wf_llit; [ cbn; lia | assumption ] ]. }
  1: mauto 4.

  (** The eliminator of an inductive type, congruence, [ι] and the
      eliminator at a view: each side by the lemmas of
      [System/Inductives/Typing.v].  The positional premises of the
      congruence on the motives and the branches give those of either side,
      one component of their induction hypotheses each.  The lemmas are
      stated at the motives' sort, [relevance_sort r Typeω@i], so they
      cover both tags. *)
  all: try solve [ eapply wf_iota_lhs; eassumption | eapply wf_iota_rhs; eassumption ].
  all: try solve [ eapply wf_elim; eassumption | eapply wf_elim_view_rhs; eassumption ].
  all: try solve [ (eapply wf_elim_cong_lhs + eapply wf_elim_cong_rhs); try eassumption;
                   intros; match goal with
                   | H : forall _ _ _ _ _ _ _ _ _ _, _ -> _ -> _ -> _ -> _ -> _ -> _ /\ _ |- _ =>
                       edestruct H as [HL HR]; [ eassumption .. | first [ exact HL | exact HR ] ]
                   | H : forall _ _ _ _, _ -> _ -> _ -> _ /\ _ |- _ =>
                       edestruct H as [HL HR]; [ eassumption .. | first [ exact HR | exact HL ] ]
                   end ].

  (** [efq], right: at its own type [C'], moved to [C] along [C' ≈ C]. *)
  all: try solve [ eapply wf_conv_sort;
                   [ eapply wf_absurd; eassumption | eassumption | eassumption | apply wf_exp_eq_sym; eassumption ] ].

  (** [Π], right.  Only the codomain has to move, and it moves by context
      conversion: [Γ ▹{κd} A'] refines [Γ ▹{κd} A], at a sort of the
      domain's kind the domain's sort lifts to ([pi_domain_eq_sort]). *)
  all: try solve [
    match goal with
    | HU : _ ⍮ _ ⍮ ?G ⊢ᵤ ?U, HA : _ ⍮ _ ⍮ ?G ⊢ ?A : abs_kind_sort ?kd ?U, HA' : _ ⍮ _ ⍮ ?G ⊢ ?A' : abs_kind_sort ?kd ?U,
      HAA : _ ⍮ _ ⍮ ?G ⊢ ?A ≈ ?A' : abs_kind_sort ?kd ?U, HB' : _ ⍮ _ ⍮ ?G ▹{?kd} ?A ⊢ ?B' : _,
      Hk : pi_kinds ?kd ?kc
      |- _ ⍮ _ ⍮ ?G ⊢ a_pi ?kd ?kc ?A' ?B' : _ =>
        destruct (pi_domain_eq_sort HU HA HA' HAA) as (S0 & HS0 & HA0 & HA0' & HAA0);
        let HI := fresh "HI" in let HB'' := fresh "HB''" in
        assert (HI : _ ⍮ _ ⍮ G ▹{kd} A' ⊢ˢ Id : G ▹{kd} A) by (eapply wf_sub_id_extend_eq; eassumption);
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB' HI) as HB''; rewrite !exp_sub_id in HB'';
        eapply wf_pi; [ exact HU | exact HA' | exact HB'' | exact Hk ]
    end ].

  (** [λ], right.  The codomain moves by context conversion; the bridging
      equation [a_pi κd κc A B ≈ a_pi κd κc A' B] is at a sort the [Π] is
      of ([wf_pi_cong_at_kinds]). *)
  all: try solve [
    match goal with
    | HA : _ ⍮ _ ⍮ ?G ⊢ ?A : ?S, HS : sort_kind ?S ?kd, HA' : _ ⍮ _ ⍮ ?G ⊢ ?A' : ?S,
      HAA : _ ⍮ _ ⍮ ?G ⊢ ?A ≈ ?A' : ?S, HB : _ ⍮ _ ⍮ ?G ▹{?kd} ?A ⊢ ?B : abs_kind_sort ?kc Typeω@?i,
      Hk : pi_kinds ?kd ?kc, HM' : _ ⍮ _ ⍮ ?G ▹{?kd} ?A ⊢ ?M' : ?B
      |- _ ⍮ _ ⍮ ?G ⊢ λ ?A' ?M' : a_pi ?kd ?kc ?A ?B =>
        let HI := fresh "HI" in
        assert (HI : _ ⍮ _ ⍮ G ▹{kd} A' ⊢ˢ Id : G ▹{kd} A) by (eapply wf_sub_id_extend_eq; eassumption);
        let HBi := fresh "HBi" in let HMi := fresh "HMi" in
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB HI) as HBi; rewrite !exp_sub_id in HBi;
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM' HI) as HMi; rewrite !exp_sub_id in HMi;
        let HF := fresh "HF" in
        assert (HF : _ ⍮ _ ⍮ G ⊢ λ A' M' : a_pi kd kc A' B)
          by (eapply wf_fn with (i := i); [ exact HA' | exact HS | exact HBi | exact Hk | exact HMi ]);
        let S0 := fresh "S0" in let HS0 := fresh "HS0" in let HP := fresh "HP" in let HPP := fresh "HPP" in
        destruct (wf_pi_cong_at_kinds _ _ _ _ _ _ _ _ _ _ _ HA HS HAA HB ltac:(apply wf_exp_eq_refl; exact HB) Hk)
          as [S0 HS0 HP HPP];
        eapply wf_conv_sort; [ exact HF | exact HP | exact HS0 | apply wf_exp_eq_sym; exact HPP ]
    end ].

  (** Application, right: the type is the codomain at the argument, and
      the arguments are equal. *)
  all: try solve [
    match goal with
    | HA : _ ⍮ _ ⍮ ?G ⊢ ?A : ?S, HS : sort_kind ?S ?kd, HB : _ ⍮ _ ⍮ ?G ▹{?kd} ?A ⊢ ?B : abs_kind_sort ?kc Typeω@?i,
      Hk : pi_kinds ?kd ?kc,
      HM' : _ ⍮ _ ⍮ ?G ⊢ ?M' : a_pi ?kd ?kc ?A ?B, HN : _ ⍮ _ ⍮ ?G ⊢ ?N : ?A, HN' : _ ⍮ _ ⍮ ?G ⊢ ?N' : ?A,
      HNN : _ ⍮ _ ⍮ ?G ⊢ ?N ≈ ?N' : ?A
      |- _ ⍮ _ ⍮ ?G ⊢ ?M' $ ?N' : ?B[Id,,?N] =>
        let HSr := fresh "HSr" in
        assert (HSr : type_sort (abs_kind_sort kc Typeω@i)) by (apply type_sort_abs_kind; constructor);
        let Hs := fresh "Hs" in let Hss := fresh "Hss" in
        assert (Hs : _ ⍮ _ ⍮ G ⊢ˢ Id,,N : G ▹{kd} A) by (eapply wf_sub_single; [ exact HA | exact HS | exact HN ]);
        assert (Hss : _ ⍮ _ ⍮ G ⊢ˢ Id,,N' ≈ Id,,N : G ▹{kd} A)
          by (eapply wf_sub_eq_id_extend; [ exact HA | exact HS | exact HN' | exact HN | apply wf_exp_eq_sym; exact HNN ]);
        eapply wf_conv_sort;
          [ eapply wf_app with (i := i); [ exact HA | exact HS | exact HB | exact Hk | exact HM' | exact HN' ]
          | exact (sub_preserves_sort _ _ _ _ _ _ _ HB HSr Hs) | exact HSr
          | exact (sub_eq_preserves_sort _ _ _ _ _ _ _ _ HB HSr Hss) ]
    end ].

  (** η: the expansion at the codomain's sort ([wf_fn_eta_expand]). *)
  all: try solve [ eapply wf_fn_eta_expand; eassumption ].

  (** [Σₚ], right: the family moves by context conversion. *)
  - assert (Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P' ⊢ˢ Id : Γ ▹{ak_propositional} P) by mauto 3.
    eapply wf_and; [ eassumption | mauto 3 ].

  (** [let], right: as for [λ], the body moves by context conversion, and the
      type moves along the equal bodies. *)
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ M' : A') by (eapply wf_conv_sort; eassumption).
    assert (Θ ⍮ Ξ ⍮ Γ ▸ A' ≔ M' ⊢ˢ Id : Γ ▸ A ≔ M) by mauto 3.
    match goal with HB : _ ⍮ _ ⍮ _ ▸ A ≔ M ⊢ B : C |- _ => destruct (presup_exp_typ HB) as [SC HSC HC] end.
    assert (Θ ⍮ Ξ ⍮ Γ ▸ A' ≔ M' ⊢ B' : C) by mauto 2.
    match goal with HCS : _ ⍮ _ ⍮ _ ▸ A ≔ M ⊢ C : ?SrtC, Hlc : level_closed_sort _ ?SrtC |- _ =>
      assert (Θ ⍮ Ξ ⍮ Γ ▸ A' ≔ M' ⊢ C : SrtC) by mauto 2;
      assert (Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def A' M') B' : C[Id,,M'])
        by (eapply wf_let; [ | | | eassumption | exact Hlc | ]; eassumption) end.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M ≈ Id,,M' : Γ ▸ A ≔ M) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ≈ C[Id,,M'] : SC) by (eapply sub_eq_preserves_sort; eassumption).
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] : SC) by (eapply sub_preserves_sort; [ eassumption | eassumption | mauto 3 ]).
    eapply wf_conv_sort; [ eassumption | eassumption | eassumption | apply wf_exp_eq_sym; eassumption ].

  (** [let module], left: the body's type is a type, by presupposition. *)
  - eapply wf_let_mod; eauto using wf_unit_eq_refl_left, module_body_sort_type_sort.

Qed.

Theorem presup_exp_eq : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ M' : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A.
Proof.
  intros * H; destruct (presup_exp_eq_sides H) as [HM HM'].
  repeat split; eauto using presup_exp_ctx, presup_exp_typ.
Qed.

Corollary presup_exp_eq_left : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * H; apply presup_exp_eq in H; destruct_conjs; assumption.
Qed.

Corollary presup_exp_eq_right : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A.
Proof.
  intros * H; apply presup_exp_eq in H; destruct_conjs; assumption.
Qed.

#[export]
Hint Resolve presup_exp_eq_left presup_exp_eq_right : mctt.

(** ** The Two Sides of a Refinement

    Each side of a refinement is a type, each of its own sort: that the two
    sorts agree is the same-sort theorem, which needs completeness.
    ([wf_subtyp_refl]'s case is where [presup_exp_eq] is used, and the only
    place it is needed.) *)

Corollary presup_subtyp_left : forall {Θ Ξ Γ A A'},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A.
Proof.
  induction 1; try assumption.
  (** Reflexivity: at the sort of the equation. *)
  1: exact (mk_wf_type _ H0 (presup_exp_eq_left H1)).
  (** The others are between types of universes. *)
  all: try (match goal with |- ?Θ ⍮ ?Ξ ⍮ ?Γ ⊢ᵗ ?A =>
              assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) as (k & Hk) by (eexists; mauto 3);
              exact (mk_wf_type _ (type_sort_universe k) Hk) end).
  (** The types of levels of a sort: types of levels. *)
  all: try solve [ apply (mk_wf_type _ type_sort_level); mauto 3 ].
  (** [Π] at its kinds, at the sort of the codomain's kind next to the
      universe of its parts. *)
  all: assert (Θ ⍮ Ξ ⍮ Γ ⊢ᵤ Typeω@i) by mauto 3.
  all: apply (mk_wf_type (abs_kind_sort κc Typeω@i)); [ apply type_sort_abs_kind; constructor |].
  all: eapply wf_pi; [ eassumption | eassumption | rewrite abs_kind_sort_wk; eassumption | eassumption ].
Qed.

Theorem presup_subtyp : forall {Θ Ξ Γ A A'},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A'.
Proof.
  intros * H; exact (conj (presup_subtyp_ctx H) (conj (presup_subtyp_left H) (presup_subtyp_right H))).
Qed.

#[export]
Hint Resolve presup_subtyp_left : mctt.

(** ** Substitution Equivalence *)

Theorem presup_sub_eq : forall {Θ Ξ Γ Δ σ σ'},
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ /\ Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ' : Δ /\ ⊢ Θ ⍮ Ξ ⍮ Δ.
Proof.
  intros * [Hσ Hσ' _].
  exact (conj (wf_sub_dom _ _ _ _ _ Hσ) (conj Hσ (conj Hσ' (wf_sub_cod _ _ _ _ _ Hσ)))).
Qed.

(** ** Saturating the Context, with Equality

    [gen_presup] extends [gen_core_presup] with the two statements above.  The
    equality case calls [gen_core_presup] on the left-hand typing it has just
    produced, so that [⊢ Θ ⍮ Ξ ⍮ Γ] and the type of the equation are added as
    well. *)

Ltac gen_presup1 H :=
  match type of H with
  | ?Θ ⍮ ?Ξ ⍮ ?Γ ⊢ ?M ≈ ?M' : ?A =>
      let HM := fresh "HM" in
      let HM' := fresh "HM'" in
      pose proof presup_exp_eq_sides H as [HM HM'];
      try gen_core_presup HM
  | ?Θ ⍮ ?Ξ ⍮ ?Γ ⊢ ?A ⊆ ?A' =>
      let S := fresh "S" in
      let HS := fresh "HS" in
      let HA := fresh "HA" in
      let S' := fresh "S'" in
      let HS' := fresh "HS'" in
      let HA' := fresh "HA'" in
      pose proof presup_subtyp_left H as [S HS HA];
      pose proof presup_subtyp_right H as [S' HS' HA'];
      try gen_core_presup HA
  | wf_sub_eq _ _ _ _ _ _ =>
      (** The two projections of [wf_sub_eq]; see [saturate_sub_eq]. *)
      let Hσ := fresh "Hσ" in
      let Hσ' := fresh "Hσ'" in
      pose proof (wf_sub_eq_left _ _ _ _ _ _ H) as Hσ;
      pose proof (wf_sub_eq_right _ _ _ _ _ _ H) as Hσ'
  end.

Ltac gen_presup H := first [ gen_presup1 H | gen_core_presup H ].

Ltac gen_presups :=
  (on_all_hyp: fun H => gen_presup H);
  invert_wf_ctx;
  (on_all_hyp: fun H => gen_lookup_presup H);
  saturate_wk;
  saturate_sub;
  clear_dups.
