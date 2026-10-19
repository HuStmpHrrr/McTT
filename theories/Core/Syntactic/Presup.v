(** * Presupposition

    Presupposition for term equality, refinement and substitution
    equivalence: the context is well formed, both sides are well typed, and
    the type is a type.  Presupposition for typing is [presup_exp] in
    [Core.Syntactic.System.Lemmas], derived from the mutual theorem
    [presup_global].

    These statements come after [sub_eq_preserves_exp], because
    [wf_exp_eq_exfalso_cong] lets the motive vary: the equation is at
    [A[Id ,, M]], while the right-hand side is naturally typed at
    [A'[Id ,, M']], and [sub_eq_preserves_exp] bridges the two.  That lemma is
    about typing derivations only, so it is proved by induction on [wf_exp]
    without presupposition.

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

Lemma presup_exp_eq_sides : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ M' : A.
Proof.
  induction 1; assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2; destruct_conjs; split; mauto 3.

  (** Members: the left-hand side by [wf_mem], at the type the lookup reads,
      which is a type; a δ-reduct is of that type. *)
  all: try solve [
    match goal with HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ _, Hm : mdenote _ _ _ (me_mem ?H _) ?R, Ht : ds_ty _ _ ?R = Some ?A |- _ =>
      let Hv := fresh "Hv" in
      pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hv;
      destruct (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht) as [[? HA] HM];
      first [ eapply wf_mem; [ eapply wf_modexp_eq_refl_left; exact HH | exact Hm | exact Ht | exact HA | exact HM ]
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
      one component of their induction hypotheses each. *)
  all: try solve [ eapply wf_iota_lhs; eassumption | eapply wf_iota_rhs; eassumption ].
  all: try solve [ eapply wf_elim; eassumption | eapply wf_elim_view_rhs; eassumption ].
  all: try solve [ (eapply wf_elim_cong_lhs + eapply wf_elim_cong_rhs); try eassumption;
                   intros; match goal with
                   | H : forall _ _ _ _ _ _ _ _ _ _, _ -> _ -> _ -> _ -> _ -> _ -> _ /\ _ |- _ =>
                       edestruct H as [HL HR]; [ eassumption .. | first [ exact HL | exact HR ] ]
                   | H : forall _ _ _ _, _ -> _ -> _ -> _ /\ _ |- _ =>
                       edestruct H as [HL HR]; [ eassumption .. | first [ exact HR | exact HL ] ]
                   end ].

  (** [efq], right.  The motive varies, so the eliminator has to be built at
      [A'[Id ,, M']] and then transported twice: along [Id ,, M' ≈ Id ,, M] by
      [sub_eq_preserves_exp], and along [A' ≈ A] by [sub_preserves_wf]. *)
  - assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ ⊥) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M : Γ ▹ ⊥) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M' : Γ ▹ ⊥) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ efq M' return A' : A'[Id,,M']) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ M' ≈ M : ⊥) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M' ≈ Id,,M : Γ ▹ ⊥) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A'[Id,,M'] ≈ A'[Id,,M] : Typeω@i) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A'[Id,,M] ≈ A[Id,,M] : Typeω@i) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[Id,,M] : Typeω@i) by mauto 2.
    eapply wf_conv; [ eassumption | eassumption | mauto 2 ].

  (** [Π], right.  Only the codomain has to move, and it moves by context
      conversion: [Γ ▹ A'] refines [Γ ▹ A].  In a small universe, the domain
      is moved to a large one for context conversion first. *)
  - match goal with Hu : _ ⍮ _ ⍮ _ ⊢ᵤ _ |- _ => inversion Hu; subst end.
    + assert (Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ˢ Id : Γ ▹ A) by mauto 3.
      eapply wf_pi; [ eassumption | eassumption | cbn in *; mauto 3 ].
    + match goal with HL : _ ⍮ _ ⍮ _ ⊢ _ : Level@?n |- _ => rename HL into HL0 end.
      assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@0) by (eapply wf_exp_eq_suniv_large; eassumption).
      assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@0) by (eapply wf_exp_suniv_large; eassumption).
      assert (Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@0) by mauto 3.
      assert (Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ˢ Id : Γ ▹ A) by mauto 3.
      eapply wf_pi; [ eassumption | eassumption | mauto 3 ].

  (** [λ], right.  The codomain [B] is not the type of any premise, so its
      level is unrelated to [i] and the bridging equation [Π A' B ≈ Π A B] has
      to be assembled at the maximum of the two. *)
  - assert (Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ˢ Id : Γ ▹ A) by mauto 3.
    assert (exists j, Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@j) as [j] by mauto 2 using presup_exp_typ.
    assert (Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B : Typeω@j) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ λ A' M' : Π A' B) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B : Typeω@(max i j)) by mauto 2 using lift_exp_max_right.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A' ≈ A : Typeω@(max i j)) by mauto 3 using lift_exp_eq_max_left.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@(max i j)) by mauto 2 using lift_exp_max_right.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Typeω@(max i j)) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ Π A' B ≈ Π A B : Typeω@(max i j)) by mauto 3.
    eapply wf_conv; eassumption.

  (** application, right: the type is the codomain at the argument, and the
      arguments are equal. *)
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,N : Γ ▹ A) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ M' $ N' : B[Id,,N']) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ N' ≈ N : A) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,N' ≈ Id,,N : Γ ▹ A) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ B[Id,,N'] ≈ B[Id,,N] : Typeω@i) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ B[Id,,N] : Typeω@i) by mauto 2.
    eapply wf_conv; eassumption.

  (** [let], right: as for [λ], the body moves by context conversion, and the
      type moves along the equal bodies. *)
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ M' : A') by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ▸ A' ≔ M' ⊢ˢ Id : Γ ▸ A ≔ M) by mauto 3.
    assert (exists j, Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ C : Typeω@j) as [j] by mauto 2 using presup_exp_typ.
    assert (Θ ⍮ Ξ ⍮ Γ ▸ A' ≔ M' ⊢ B' : C) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA' M') B' : C[Id,,M']) by (eapply wf_let; cycle 3; [ eassumption | eassumption .. ]).
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M ≈ Id,,M' : Γ ▸ A ≔ M) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ≈ C[Id,,M'] : Typeω@j) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] : Typeω@j) by mauto 3.
    eapply wf_conv; [ eassumption | eassumption | mauto 2 ].

  (** [let module], left: the body's type is a type, by presupposition. *)
  - assert (exists j, Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Typeω@j) as [j] by mauto 2 using presup_exp_typ.
    eapply wf_let_mod; eauto using wf_unit_eq_refl_left.

Qed.

Theorem presup_exp_eq : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ M' : A /\ exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
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

    A refinement holds between types at a common universe level, which is what
    makes the statement existential and its cases uniform: in each of them the
    two sides are types at levels that need not agree, and [lift_exp_common]
    raises both.  ([wf_subtyp_refl]'s case is where [presup_exp_eq] is used, and
    the only place it is needed.) *)

Lemma presup_subtyp_types : forall {Θ Ξ Γ A A'},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i.
Proof.
  induction 1; destruct_conjs; eapply lift_exp_common; mauto 2.
Qed.

Theorem presup_subtyp : forall {Θ Ξ Γ A A'},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i.
Proof.
  intros * H; split; [ eapply presup_subtyp_ctx; eassumption | apply presup_subtyp_types, H ].
Qed.

Corollary presup_subtyp_left : forall {Θ Ξ Γ A A'},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * H; apply presup_subtyp in H; destruct_conjs; eexists; eassumption.
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
      let i := fresh "i" in
      let HA := fresh "HA" in
      let HA' := fresh "HA'" in
      pose proof presup_subtyp_types H as [i [HA HA']];
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
