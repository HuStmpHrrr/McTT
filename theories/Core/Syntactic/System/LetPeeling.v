(** * Peeling the Local Definitions of a Kept Proof

    The readback of a kept proof [⋆ᵈ⟨M, ρ⟩] is [M] copied under local
    definitions of the positions of [ρ] it reads ([read_proof_kept]): a let
    chain [lets_exp bs M].  An implementation may instead move the local
    definitions in front of [M] into the environment first ("peeling"),
    and read back a different chain over the body.  The two chains differ
    in length and in their definitions, and this file shows the peeled one
    is typed and convertible to the original
    ([lets_chain_replacement_typed], [lets_peeling_typed]), when a
    substitution relates the two chains' contexts and their
    ζ-substitutions agree through it.  Those two premises collect every
    entry's equation; the normal forms of the peeled definitions meet
    them by soundness.

    With [q : ℕ → P] in context, the wrapped readback
    [ℓ q' : ℕ → P ≔ #0 in ℓ y : ℕ ≔ f q' in h y] and the peeled one
    [ℓ y : ℕ ≔ W in h y], with [W] the normal form of [f q], are related
    by the substitution [#0 ↦ #0, #1 ↦ #1, #(k+2) ↦ #(k+1)]. *)

From Stdlib Require Import Lia List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import CoreInversions SystemOpt.
Import Syntax_Notations Wk_Notations ListNotations.

(** ** Let Chains *)

(** [ctx_lets Γ bs]: [Γ] extended by the definitions of the let chain
    [bs], outermost first: a term definition as a defined variable, a local
    module as a module slot, a definition with a module part as both. *)
Fixpoint ctx_lets (Γ : ctx) (bs : list binding) : ctx :=
  match bs with
  | nil => Γ
  | b_def A M :: bs => ctx_lets (Γ ▸ A ≔ M) bs
  | b_mod U :: bs => ctx_lets (Γ ▹ₘ U) bs
  | b_def_mod A M U :: bs => ctx_lets (Γ ▸ₘ A ≔ M ‖ U) bs
  end.

(** The substitution a binding is ζ-reduced by: its definition, its unit
    as a literal module, or both. *)
Definition binding_zeta_sub (b : binding) : sub :=
  match b with
  | b_def _ M => Id,,M
  | b_mod U => Id ,,ₘ me_lit U
  | b_def_mod _ M U => Id ,,ᵈ M ‖ me_lit U
  end.

(** [lets_sub bs]: the ζ-substitution of the let chain [bs], from
    [ctx_lets Γ bs] back to [Γ]: the innermost definitions first, each
    reduced by the ones outside it. *)
Fixpoint lets_sub (bs : list binding) : sub :=
  match bs with
  | nil => Id
  | b :: bs => lets_sub bs ⨟ binding_zeta_sub b
  end.

(** A chain over a chain is one chain. *)
Lemma lets_exp_app : forall bs bs' M, lets_exp (bs ++ bs') M = lets_exp bs (lets_exp bs' M).
Proof. intros; unfold lets_exp; apply List.fold_right_app. Qed.

(** ** ζ Along a Chain *)

(** ζ under an equation of the body: a typed local definition whose body
    equals [Y'] at every type the body has is its ζ-reduct at [Y']. *)
Lemma let_body_zeta : forall {Θ Ξ Γ A M Y Y' T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in Y : T ->
    (forall C, Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ Y : C -> Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ Y ≈ Y' : C) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in Y ≈ Y'[Id,,M] : T.
Proof.
  intros * H HY; dependent induction H.
  - pose proof (HY _ ltac:(eassumption)) as E.
    assert (Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ Y' : C) by (gen_presups; assumption).
    etransitivity; [ eapply wf_exp_eq_let_cong; try eassumption; mauto 3 |].
    eapply wf_exp_eq_let_zeta; eassumption.
  - eapply wf_exp_eq_subtyp; [ eapply IHwf_exp1; eauto | eassumption | eassumption | eassumption ].
Qed.

(** The same for a local module. *)
Lemma let_mod_body_zeta : forall {Θ Ξ Γ U Y Y' T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in Y : T ->
    (forall C, Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ Y : C -> Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ Y ≈ Y' : C) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in Y ≈ Y'[Id ,,ₘ me_lit U] : T.
Proof.
  intros * H HY; dependent induction H.
  - pose proof (HY _ ltac:(eassumption)) as E.
    assert (Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ Y' : C) by (gen_presups; assumption).
    etransitivity; [ eapply wf_exp_eq_let_mod_cong; try eassumption; eapply wf_let_mod; eassumption |].
    eapply wf_exp_eq_let_mod_zeta; eassumption.
  - eapply wf_exp_eq_subtyp; [ eapply IHwf_exp1; eauto | eassumption | eassumption | eassumption ].
Qed.

(** The same for a definition with a module part. *)
Lemma let_dm_body_zeta : forall {Θ Ξ Γ A M U Y Y' T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓᵈ A ≔ M ‖ U in Y : T ->
    (forall C, Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊢ Y : C -> Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊢ Y ≈ Y' : C) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓᵈ A ≔ M ‖ U in Y ≈ Y'[Id ,,ᵈ M ‖ me_lit U] : T.
Proof.
  intros * H HY; dependent induction H.
  - pose proof (HY _ ltac:(eassumption)) as HE.
    assert (Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊢ Y' : C) by (gen_presups; assumption).
    etransitivity; [ eapply wf_exp_eq_let_dm_cong; try eassumption; mauto 3; eapply wf_let_dm; eassumption |].
    eapply wf_exp_eq_let_dm_zeta; eassumption.
  - eapply wf_exp_eq_subtyp; [ eapply IHwf_exp1; eauto | eassumption | eassumption | eassumption ].
Qed.

(** ζ for a whole chain: a typed let chain is its body under the chain's
    ζ-substitution. *)
Lemma lets_exp_zeta : forall bs {Θ Ξ Γ X T},
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp bs X : T ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp bs X ≈ X[lets_sub bs] : T.
Proof.
  induction bs as [| [A M | U | A M U] bs IH]; intros * H; cbn [lets_exp List.fold_right lets_sub binding_zeta_sub] in *.
  - rewrite exp_sub_id; apply wf_exp_eq_refl; exact H.
  - rewrite <- exp_sub_sub; apply (let_body_zeta H); intros C HC; exact (IH _ _ _ _ _ HC).
  - rewrite <- exp_sub_sub; apply (let_mod_body_zeta H); intros C HC; exact (IH _ _ _ _ _ HC).
  - rewrite <- exp_sub_sub; apply (let_dm_body_zeta H); intros C HC; exact (IH _ _ _ _ _ HC).
Qed.

(** ** Typing a Chain *)

(** A typed chain types its body in the chain's context, at a type whose
    ζ-instance is the chain's or below it: the empty chain's body may be a
    type of levels, of the sort [LevelSort], which is outside subtyping. *)
Lemma lets_exp_inversion : forall bs {Θ Ξ Γ X T},
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp bs X : T ->
    exists C, Θ ⍮ Ξ ⍮ ctx_lets Γ bs ⊢ X : C /\ (C[lets_sub bs] = T \/ Θ ⍮ Ξ ⍮ Γ ⊢ C[lets_sub bs] ⊆ T).
Proof.
  induction bs as [| [A M | U | A M U] bs IH]; intros * H; cbn [lets_exp List.fold_right lets_sub binding_zeta_sub ctx_lets] in *.
  - exists T; split; [ exact H |]; rewrite exp_sub_id; left; reflexivity.
  - destruct (wf_let_ann_inversion H) as [S Y HS HA HM HB Hs].
    destruct (IH _ _ _ _ _ HB) as (C & HX & [HC | HC]); exists C; split; [ exact HX | | exact HX |];
      right; rewrite <- exp_sub_sub.
    + rewrite HC; exact Hs.
    + eapply wf_subtyp_trans; [| exact Hs ].
      eapply sub_preserves_subtyp; [ exact HC | eapply wf_sub_single_def; eassumption ].
  - destruct (wf_let_mod_inversion H) as (Y & HU & HB & Hs).
    destruct (IH _ _ _ _ _ HB) as (C & HX & [HC | HC]); exists C; split; [ exact HX | | exact HX |];
      right; rewrite <- exp_sub_sub.
    + rewrite HC; exact Hs.
    + eapply wf_subtyp_trans; [| exact Hs ].
      eapply sub_preserves_subtyp; [ exact HC | eapply wf_sub_single_mod; eassumption ].
  - destruct (wf_let_dm_inversion H) as [i Y E0 -> HA HM HU HB Hs].
    destruct (IH _ _ _ _ _ HB) as (C & HX & [HC | HC]); exists C; split; [ exact HX | | exact HX |];
      right; rewrite <- exp_sub_sub.
    + rewrite HC; exact Hs.
    + eapply wf_subtyp_trans; [| exact Hs ].
      eapply sub_preserves_subtyp; [ exact HC | eapply wf_sub_single_dm; eassumption ].
Qed.

(** The weakening past a chain: [ctx_lets Γ bs] over [Γ]. *)
Lemma ctx_lets_wk_shiftn : forall bs {Θ Ξ Γ},
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets Γ bs -> Θ ⍮ Ξ ⍮ ctx_lets Γ bs ⊢ʷ wk_shiftn (List.length bs) : Γ.
Proof.
  induction bs as [| b bs IH]; intros * H; cbn [List.length] in *.
  - rewrite wk_shiftn_zero; apply wf_wk_id; exact H.
  - assert (E : wk_eq (↑ ⊙ wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) by (intros x; cbn; lia).
    rewrite <- E.
    destruct b as [A M | U | A M U]; cbn [ctx_lets] in *;
      pose proof (IH _ _ _ H) as Hw; apply (wf_wk_compose _ _ _ _ _ _ _ Hw), wf_wk_shift, (wf_wk_cod _ _ _ _ _ Hw).
Qed.

(** A definition of [Γ] is one of [ctx_lets Γ bs], past the chain. *)
Lemma ctx_lets_lookup_def : forall bs Γ x A M,
    Γ ∋ #x ≔ M : A ->
    ctx_lets Γ bs ∋ #(x + List.length bs) ≔ M[wk_shiftn (List.length bs)]ʷ : A[wk_shiftn (List.length bs)]ʷ.
Proof.
  induction bs as [| b bs IH]; intros * H; cbn [List.length].
  - rewrite Nat.add_0_r, <- (exp_wk_wk_ext M wk_id wk_id (wk_shiftn 0)), <- (exp_wk_wk_ext A wk_id wk_id (wk_shiftn 0)),
      !exp_wk_id by (intros y; cbn; lia); exact H.
  - rewrite <- (exp_wk_wk_ext M ↑ (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))),
      <- (exp_wk_wk_ext A ↑ (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) by (intros y; cbn; lia).
    replace (x + S (List.length bs)) with (S x + List.length bs) by lia.
    destruct b as [A' M' | U' | A' M' U']; cbn [ctx_lets]; apply IH; constructor; exact H.
Qed.

(** A module slot of [Γ] is one of [ctx_lets Γ bs], past the chain. *)
Lemma ctx_lets_lookup_mod : forall bs Γ x U,
    Γ ∋ #x ≔ₘ U ->
    ctx_lets Γ bs ∋ #(x + List.length bs) ≔ₘ gunit_wk U (wk_shiftn (List.length bs)).
Proof.
  induction bs as [| b bs IH]; intros * H; cbn [List.length].
  - rewrite Nat.add_0_r, (gunit_wk_id_ext U (wk_shiftn 0)) by (intros y; cbn; lia); exact H.
  - rewrite <- (gunit_wk_wk_ext U ↑ (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) by (intros y; cbn; lia).
    replace (x + S (List.length bs)) with (S x + List.length bs) by lia.
    destruct b as [A' M' | U' | A' M' U']; cbn [ctx_lets]; apply IH; constructor; exact H.
Qed.

(** The ζ-substitution of a chain is typed, from the chain's context back
    to [Γ]. *)
Lemma lets_sub_wf : forall bs {Θ Ξ Γ},
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets Γ bs -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ lets_sub bs : ctx_lets Γ bs.
Proof.
  induction bs as [| b bs IH]; intros * H; cbn [lets_sub].
  - apply wf_sub_id; exact H.
  - destruct b as [A M | U | A M U]; cbn [ctx_lets binding_zeta_sub] in *;
      pose proof (wf_wk_cod _ _ _ _ _ (ctx_lets_wk_shiftn bs H)) as Hb; inversion Hb; subst;
      (eapply wf_sub_compose; [ exact (IH _ _ _ H) |]).
    + eapply wf_sub_single_def; eassumption.
    + apply wf_sub_single_mod; assumption.
    + eapply wf_sub_single_dm; eassumption.
Qed.

(** An equation of substitutions moves along a pointwise equality of its
    right side. *)
Lemma wf_sub_eq_respects_sb_eq : forall {Θ Ξ Γ Δ σ τ τ'},
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ τ : Δ -> sb_eq τ τ' -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ τ' : Δ.
Proof.
  intros * [Hl Hr Ha Hm] E; constructor; [ exact Hl | rewrite <- E; exact Hr | |].
  - intros x A HA; rewrite <- (exp_sub_sb_eq (a_var x) _ _ E); exact (Ha _ _ HA).
  - intros x U HU; rewrite <- (E x); exact (Hm _ _ HU).
Qed.

(** Past a chain over a definition, the definition's variable is its body
    ([wf_exp_eq_var_delta]): the weakening past the chain equals the
    definition's ζ-substitution followed by the weakening past the
    definition too. *)
Lemma ctx_lets_shift_def_unfold : forall bs {Θ Ξ Γ A M},
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets (Γ ▸ A ≔ M) bs ->
    Θ ⍮ Ξ ⍮ ctx_lets (Γ ▸ A ≔ M) bs ⊢ˢ ι (wk_shiftn (List.length bs)) ≈ (Id,,M) ⨟ ι (wk_shiftn (S (List.length bs)))
      : Γ ▸ A ≔ M.
Proof.
  intros * H.
  pose proof (ctx_lets_wk_shiftn bs H) as Hw.
  pose proof (ctx_lets_wk_shiftn (b_def A M :: bs) H) as Hw'; cbn [ctx_lets List.length] in Hw'.
  pose proof (wf_wk_cod _ _ _ _ _ Hw) as Hb; inversion Hb; subst.
  assert (Hs : Θ ⍮ Ξ ⍮ ctx_lets (Γ ▸ A ≔ M) bs ⊢ˢ (Id,,M) ⨟ ι (wk_shiftn (S (List.length bs))) : Γ ▸ A ≔ M)
    by (eapply wf_sub_compose; [ eapply wf_sub_single_def; eassumption | apply wf_sub_of_wk, Hw' ]).
  constructor; [ apply wf_sub_of_wk, Hw | exact Hs | |].
  - intros x B HL; inversion HL; subst; cbn.
    + (** The definition's variable: its body, by [δ] *)
      assert (HD0 : Γ ▸ A ≔ M ∋ #0 ≔ M[↑]ʷ : A[↑]ʷ) by constructor.
      pose proof (ctx_lets_lookup_def bs _ 0 _ _ HD0) as HD; cbn [Nat.add] in HD.
      pose proof (wf_exp_eq_var_delta _ _ _ _ _ _ H HD) as E.
      rewrite !exp_sub_of_wk.
      rewrite (exp_wk_wk_ext M ↑ (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) in E
        by (intros y; cbn; lia).
      exact E.
    + (** A variable below it: the same variable on both sides *)
      replace (n + S (List.length bs)) with (S (n + List.length bs)) by lia.
      apply wf_exp_eq_refl; exact (wf_sub_apply _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hw) _ _ HL).
  - intros x U HL; inversion HL; subst.
    pose proof (wf_sub_mod_image _ _ _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hw) HL) as E; cbn in E |- *.
    replace (n + S (List.length bs)) with (S (n + List.length bs)) by lia; exact E.
Qed.

(** The same over a module slot: the slot's variable is its unit
    ([wf_me_delta_slot]). *)
Lemma ctx_lets_shift_mod_unfold : forall bs {Θ Ξ Γ U},
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets (Γ ▹ₘ U) bs ->
    Θ ⍮ Ξ ⍮ ctx_lets (Γ ▹ₘ U) bs ⊢ˢ ι (wk_shiftn (List.length bs)) ≈ (Id ,,ₘ me_lit U) ⨟ ι (wk_shiftn (S (List.length bs)))
      : Γ ▹ₘ U.
Proof.
  intros * H.
  pose proof (ctx_lets_wk_shiftn bs H) as Hw.
  pose proof (ctx_lets_wk_shiftn (b_mod U :: bs) H) as Hw'; cbn [ctx_lets List.length] in Hw'.
  pose proof (wf_wk_cod _ _ _ _ _ Hw) as Hb; inversion Hb; subst.
  assert (Hs : Θ ⍮ Ξ ⍮ ctx_lets (Γ ▹ₘ U) bs ⊢ˢ (Id ,,ₘ me_lit U) ⨟ ι (wk_shiftn (S (List.length bs))) : Γ ▹ₘ U)
    by (eapply wf_sub_compose; [ apply wf_sub_single_mod; assumption | apply wf_sub_of_wk, Hw' ]).
  constructor; [ apply wf_sub_of_wk, Hw | exact Hs | |].
  - intros x B HL; inversion HL; subst; cbn.
    replace (n + S (List.length bs)) with (S (n + List.length bs)) by lia.
    apply wf_exp_eq_refl; exact (wf_sub_apply _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hw) _ _ HL).
  - intros x U' HL; inversion HL; subst; cbn.
    + (** The slot's variable: its unit, by [δ] *)
      assert (HM0 : Γ ▹ₘ U ∋ #0 ≔ₘ gunit_wk U wk_shift) by constructor.
      pose proof (ctx_lets_lookup_mod bs _ 0 _ HM0) as HM; cbn [Nat.add] in HM.
      pose proof (wf_me_delta_slot _ _ _ _ _ H HM) as E.
      rewrite (gunit_wk_wk_ext U wk_shift (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) in E
        by (intros y; cbn; lia).
      rewrite <- gunit_sub_of_wk in E; exact E.
    + (** A slot below it: the same slot on both sides *)
      pose proof (wf_sub_mod_image _ _ _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hw) HL) as E; cbn in E |- *.
      replace (n + S (List.length bs)) with (S (n + List.length bs)) by lia; exact E.
Qed.

(** The same over a definition with a module part: its variable is its
    body and its slot its unit. *)
Lemma ctx_lets_shift_dm_unfold : forall bs {Θ Ξ Γ A M U},
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets (Γ ▸ₘ A ≔ M ‖ U) bs ->
    Θ ⍮ Ξ ⍮ ctx_lets (Γ ▸ₘ A ≔ M ‖ U) bs ⊢ˢ ι (wk_shiftn (List.length bs))
      ≈ (Id ,,ᵈ M ‖ me_lit U) ⨟ ι (wk_shiftn (S (List.length bs))) : Γ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * H.
  pose proof (ctx_lets_wk_shiftn bs H) as Hw.
  pose proof (ctx_lets_wk_shiftn (b_def_mod A M U :: bs) H) as Hw'; cbn [ctx_lets List.length] in Hw'.
  pose proof (wf_wk_cod _ _ _ _ _ Hw) as Hb; inversion Hb; subst.
  assert (Hs : Θ ⍮ Ξ ⍮ ctx_lets (Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)) bs
                 ⊢ˢ (Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))) ⨟ ι (wk_shiftn (S (List.length bs)))
                 : Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E))
    by (eapply wf_sub_compose; [ eapply wf_sub_single_dm; eassumption | apply wf_sub_of_wk, Hw' ]).
  constructor; [ apply wf_sub_of_wk, Hw | exact Hs | |].
  - intros x B HL; inversion HL; subst; cbn.
    + (** The term part's variable: its body, by [δ] *)
      assert (HD0 : Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ∋ #0 ≔ M[↑]ʷ : A[↑]ʷ) by constructor.
      pose proof (ctx_lets_lookup_def bs _ 0 _ _ HD0) as HD; cbn [Nat.add] in HD.
      pose proof (wf_exp_eq_var_delta _ _ _ _ _ _ H HD) as E1.
      rewrite !exp_sub_of_wk.
      rewrite (exp_wk_wk_ext M ↑ (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) in E1
        by (intros y; cbn; lia).
      exact E1.
    + (** A variable below it: the same variable on both sides *)
      replace (n + S (List.length bs)) with (S (n + List.length bs)) by lia.
      apply wf_exp_eq_refl; exact (wf_sub_apply _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hw) _ _ HL).
  - intros x U' HL; inversion HL; subst; cbn.
    + (** The module part's slot: its unit, by [δ] *)
      assert (HM0 : Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ∋ #0 ≔ₘ gunit_wk (gu_mk nil (md_alias E)) wk_shift) by constructor.
      pose proof (ctx_lets_lookup_mod bs _ 0 _ HM0) as HM; cbn [Nat.add] in HM.
      pose proof (wf_me_delta_slot _ _ _ _ _ H HM) as E1.
      rewrite (gunit_wk_wk_ext (gu_mk nil (md_alias E)) wk_shift (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) in E1
        by (intros y; cbn; lia).
      rewrite <- gunit_sub_of_wk in E1; exact E1.
    + (** A slot below it: the same slot on both sides *)
      pose proof (wf_sub_mod_image _ _ _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hw) HL) as E1; cbn in E1 |- *.
      replace (n + S (List.length bs)) with (S (n + List.length bs)) by lia; exact E1.
Qed.

(** In a chain's context, the identity is the chain's ζ-substitution
    weakened back past the chain: every defined variable is its definition,
    every slot its unit. *)
Lemma ctx_lets_unfold_sub : forall bs {Θ Ξ Γ},
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets Γ bs ->
    Θ ⍮ Ξ ⍮ ctx_lets Γ bs ⊢ˢ Id ≈ lets_sub bs ⨟ ι (wk_shiftn (List.length bs)) : ctx_lets Γ bs.
Proof.
  induction bs as [| b bs IH]; intros * H; cbn [lets_sub List.length].
  - eapply wf_sub_eq_respects_sb_eq; [ apply wf_sub_eq_refl, wf_sub_id, H |].
    intros x; cbn; f_equal; lia.
  - assert (K : Θ ⍮ Ξ ⍮ ctx_lets Γ (b :: bs) ⊢ˢ ι (wk_shiftn (List.length bs))
                  ≈ binding_zeta_sub b ⨟ ι (wk_shiftn (S (List.length bs))) : ctx_lets Γ (b :: nil))
      by (destruct b; cbn [ctx_lets binding_zeta_sub] in *;
          [ apply ctx_lets_shift_def_unfold | apply ctx_lets_shift_mod_unfold | apply ctx_lets_shift_dm_unfold ]; exact H).
    destruct b as [A M | U | A M U]; cbn [ctx_lets] in *;
      (eapply wf_sub_eq_respects_sb_eq;
       [ eapply wf_sub_eq_trans; [ exact (IH _ _ _ H) | eapply wf_sub_eq_compose_right; [ exact (lets_sub_wf bs H) | exact K ] ]
       | symmetry; apply sb_compose_assoc ]).
Qed.

(** In a chain's context, a typed term is its ζ-instance weakened back
    past the chain. *)
Lemma ctx_lets_unfold_definitions : forall bs {Θ Ξ Γ Y C},
    Θ ⍮ Ξ ⍮ ctx_lets Γ bs ⊢ Y : C ->
    Θ ⍮ Ξ ⍮ ctx_lets Γ bs ⊢ Y ≈ Y[lets_sub bs][wk_shiftn (List.length bs)]ʷ : C.
Proof.
  intros * HY.
  assert (⊢ Θ ⍮ Ξ ⍮ ctx_lets Γ bs) by (gen_presups; assumption).
  pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HY) (ctx_lets_unfold_sub bs H)) as E.
  rewrite !exp_sub_id, <- exp_sub_sub, exp_sub_of_wk in E; exact E.
Qed.

(** A weakened term under the substitution of the variable it skips is
    the term. *)
Lemma exp_shift_sub_extend : forall M σ e, M[↑]ʷ[sb_extend σ e] = M[σ].
Proof. intros; rewrite exp_sub_shift; apply exp_sub_sb_eq, sb_shift_extend. Qed.

(** A chain whose body is typed at a proposition of [Γ], weakened past the
    chain, is typed at that proposition. *)
Lemma lets_exp_typed_at_prop : forall bs {Θ Ξ Γ X P},
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets Γ bs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ ->
    Θ ⍮ Ξ ⍮ ctx_lets Γ bs ⊢ X : P[wk_shiftn (List.length bs)]ʷ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp bs X : P.
Proof.
  induction bs as [| b bs IH]; intros * HΓ HP HX; cbn [lets_exp List.fold_right List.length] in *.
  - rewrite <- (exp_wk_wk_ext P wk_id wk_id (wk_shiftn 0)), !exp_wk_id in HX by (intros x; cbn; lia); exact HX.
  - rewrite <- (exp_wk_wk_ext P ↑ (wk_shiftn (List.length bs)) (wk_shiftn (S (List.length bs)))) in HX
      by (intros x; cbn; lia).
    destruct b as [A M | U | A M U]; cbn [ctx_lets] in *;
      pose proof (wf_wk_cod _ _ _ _ _ (ctx_lets_wk_shiftn bs HΓ)) as Hb.
    + assert (HP' : Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ P[↑]ʷ : Propₘ)
        by (change Propₘ with (Propₘ[↑]ʷ); eapply (proj1 wk_preserves_wf); [ exact HP | apply wf_wk_shift, Hb ]).
      pose proof (IH _ _ _ _ _ HΓ HP' HX) as HL.
      inversion Hb; subst.
      replace P with (P[↑]ʷ[Id,,M]) by (rewrite exp_shift_sub_extend, exp_sub_id; reflexivity).
      eapply wf_let; [ eassumption | eassumption | eassumption | exact HP' | constructor | exact HL ].
    + assert (HP' : Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ P[↑]ʷ : Propₘ)
        by (change Propₘ with (Propₘ[↑]ʷ); eapply (proj1 wk_preserves_wf); [ exact HP | apply wf_wk_shift, Hb ]).
      pose proof (IH _ _ _ _ _ HΓ HP' HX) as HL.
      inversion Hb; subst.
      replace P with (P[↑]ʷ[Id ,,ₘ me_lit U]) by (rewrite exp_shift_sub_extend, exp_sub_id; reflexivity).
      eapply wf_let_mod; [ eassumption | exact HP' | constructor | constructor | exact HL ].
    + assert (HP' : Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊢ P[↑]ʷ : Propₘ)
        by (change Propₘ with (Propₘ[↑]ʷ); eapply (proj1 wk_preserves_wf); [ exact HP | apply wf_wk_shift, Hb ]).
      pose proof (IH _ _ _ _ _ HΓ HP' HX) as HL.
      inversion Hb; subst.
      replace P with (P[↑]ʷ[Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))]) by (rewrite exp_shift_sub_extend, exp_sub_id; reflexivity).
      eapply wf_let_dm; [ eassumption | eassumption | eassumption | exact HP' | constructor | constructor | exact HL ].
Qed.

(** ** Replacing a Chain

    A chain [cs'] replaces the typed chain [cs] over the body [X] at a
    proposition when a substitution [σ] maps the context of [cs] to the
    context of [cs'], fixing [X], and the two ζ-substitutions agree through
    [σ].  The typing of [σ] carries an equation for every definition and
    slot of [cs] (its definition, transported, equals its image), and the
    agreement of the ζ-substitutions carries the equations of the context
    part; those are the premises soundness discharges entry by entry. *)
Theorem lets_chain_replacement_typed : forall {Θ Ξ Γ cs cs' X P σ},
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp cs X : P ->
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets Γ cs' ->
    Θ ⍮ Ξ ⍮ ctx_lets Γ cs' ⊢ˢ σ : ctx_lets Γ cs ->
    X[σ] = X ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ⨟ lets_sub cs' ≈ lets_sub cs : ctx_lets Γ cs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp cs' X : P /\ Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp cs' X ≈ lets_exp cs X : P.
Proof.
  intros * HP Hw HΓ' Hσ HXσ Hz.
  destruct (lets_exp_inversion cs Hw) as (C & HX & HC0).
  (** at a proposition, the body's type is below it *)
  assert (HC : Θ ⍮ Ξ ⍮ Γ ⊢ C[lets_sub cs] ⊆ P)
    by (destruct HC0 as [-> | HC0]; [ eapply wf_subtyp_refl_typ; [ exact HP | constructor ] | exact HC0 ]).
  clear HC0.
  assert (HCs : exists SC, type_sort SC /\ Θ ⍮ Ξ ⍮ ctx_lets Γ cs ⊢ C : SC).
  { pose proof (presup_exp_typ_cases HX) as Hcs; inversion Hcs as [C0 SC HSC HCt | Hx1 Hx2]; subst; [ eauto |].
    exfalso; destruct (presup_subtyp_left_sorted HC) as (? & _ & HL); cbn in HL; exact (level_sort_untyped HL). }
  destruct HCs as (SC & HSC & HCt).
  pose proof (ctx_lets_wk_shiftn cs' HΓ') as Hwk.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hz) as Hσz.
  (** The body in the new chain's context, at [C[σ]] *)
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HX Hσ) as HXp; rewrite HXσ in HXp.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCt Hσ) as HCp; rewrite (type_sort_sub _ _ HSC) in HCp.
  (** [C[σ]] is, in that context, [C]'s ζ-instance weakened back *)
  pose proof (ctx_lets_unfold_definitions cs' HCp) as E1.
  pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HCt) Hz) as E2.
  rewrite (type_sort_sub _ _ HSC), <- exp_sub_sub in E2.
  pose proof (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ E2 _ _ Hwk) as E3; rewrite (type_sort_wk _ _ HSC) in E3.
  pose proof (proj1 (proj2 (proj2 wk_preserves_wf)) _ _ _ _ _ HC _ _ Hwk) as HC'.
  pose proof (proj1 wk_preserves_wf _ _ _ _ _ HP _ _ Hwk) as HP'; cbn in HP'.
  assert (HCPw : Θ ⍮ Ξ ⍮ ctx_lets Γ cs' ⊢ C[σ] ⊆ P[wk_shiftn (List.length cs')]ʷ).
  { eapply wf_subtyp_trans; [| exact HC' ].
    eapply proj1, wf_subtyp_of_exp_eq; [ exact HCp | | exact HSC | etransitivity; [ exact E1 | exact E3 ] ].
    gen_presups; assumption. }
  assert (HXP : Θ ⍮ Ξ ⍮ ctx_lets Γ cs' ⊢ X : P[wk_shiftn (List.length cs')]ʷ)
    by (eapply wf_exp_subtyp; [ exact HXp | exact HP' | constructor | exact HCPw ]).
  pose proof (lets_exp_typed_at_prop cs' HΓ' HP HXP) as Ht.
  split; [ exact Ht |].
  (** Both chains ζ-reduce, to instances of [X] equal through [σ] *)
  etransitivity; [ exact (lets_exp_zeta cs' Ht) |].
  etransitivity; [| symmetry; exact (lets_exp_zeta cs Hw) ].
  pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HX) Hz) as E4.
  rewrite <- (exp_sub_sub X σ (lets_sub cs')), <- (exp_sub_sub C σ (lets_sub cs')), HXσ in E4.
  eapply wf_exp_eq_subtyp; [ exact E4 | exact HP | constructor |].
  eapply wf_subtyp_trans; [| exact HC ].
  eapply proj1, wf_subtyp_of_exp_eq; [ | | exact HSC | exact E2 ]; gen_presups; assumption.
Qed.

(** ** A Chain Over the Images of a Substitution

    A proof [X] of a proposition [P] of [Γ] that reads only the first
    [|bs|] positions of [Γ], under a chain [bs] of definitions over [Δ]:
    [τ] maps [Γ] into the chain's context, as the chain's own variables at
    those positions (so [X[τ] = X]), and the chain's ζ-substitution after
    [τ] is [σ].  The chain is then typed at [P[σ]], and equal to [X[σ]].
    This is the readback of a kept proof [⋆ᵈ⟨X, ρ⟩] over an environment
    [ρ] glued to [σ]: the chain binds the readbacks of the entries of [ρ]
    ([read_proof_kept]).  For example, with [h : P] at position [0] of
    [Γ] and [ρ 0] read back as [W], the chain [ℓ y : P' ≔ W in #0]
    ([τ 0 = #0]) is [#0[σ]] when [W ≈ #0[σ]]. *)
Lemma lets_exp_of_sub : forall bs {Θ Ξ Δ Γ X P τ σ},
    Θ ⍮ Ξ ⍮ Γ ⊢ X : P ->
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ ->
    exp_scoped (List.length bs) X ->
    Θ ⍮ Ξ ⍮ ctx_lets Δ bs ⊢ˢ τ : Γ ->
    (forall x, x < List.length bs -> τ x = se_var x) ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ τ ⨟ lets_sub bs ≈ σ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ lets_exp bs X : P[σ] /\ Θ ⍮ Ξ ⍮ Δ ⊢ lets_exp bs X ≈ X[σ] : P[σ].
Proof.
  intros * HX HP Hs Hτ Hτx Hz.
  pose proof (wf_sub_dom _ _ _ _ _ Hτ) as HΓ'.
  pose proof (wf_sub_eq_right _ _ _ _ _ _ Hz) as Hσ.
  pose proof (ctx_lets_wk_shiftn bs HΓ') as Hwk.
  (** The proof in the chain's context, at [P[τ]] *)
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HX Hτ) as HXτ.
  rewrite (exp_scoped_sub_id _ _ _ Hs Hτx) in HXτ.
  (** [P[τ]] is [P[σ]], weakened past the chain *)
  assert (HPτ : Θ ⍮ Ξ ⍮ ctx_lets Δ bs ⊢ P[τ] : Propₘ)
    by (change Propₘ with (Propₘ[τ]); exact (sub_preserves_exp _ _ _ _ _ _ _ HP Hτ)).
  pose proof (ctx_lets_unfold_definitions bs HPτ) as E1.
  pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HP) Hz) as E2; cbn in E2.
  rewrite exp_sub_sub in E1.
  assert (E3 : Θ ⍮ Ξ ⍮ ctx_lets Δ bs ⊢ P[τ⨟lets_sub bs][wk_shiftn (List.length bs)]ʷ ≈ P[σ][wk_shiftn (List.length bs)]ʷ : Propₘ)
    by (change Propₘ with (Propₘ[wk_shiftn (List.length bs)]ʷ); exact (proj1 (proj2 wk_preserves_wf) _ _ _ _ _ _ E2 _ _ Hwk)).
  assert (HPσ : Θ ⍮ Ξ ⍮ Δ ⊢ P[σ] : Propₘ) by (change Propₘ with (Propₘ[σ]); exact (sub_preserves_exp _ _ _ _ _ _ _ HP Hσ)).
  assert (HPσw : Θ ⍮ Ξ ⍮ ctx_lets Δ bs ⊢ P[σ][wk_shiftn (List.length bs)]ʷ : Propₘ)
    by (change Propₘ with (Propₘ[wk_shiftn (List.length bs)]ʷ); exact (proj1 wk_preserves_wf _ _ _ _ _ HPσ _ _ Hwk)).
  assert (HXw : Θ ⍮ Ξ ⍮ ctx_lets Δ bs ⊢ X : P[σ][wk_shiftn (List.length bs)]ʷ)
    by (eapply wf_conv_sort; [ exact HXτ | exact HPσw | constructor | etransitivity; [ exact E1 | exact E3 ] ]).
  pose proof (lets_exp_typed_at_prop bs HΓ' HPσ HXw) as Ht.
  split; [ exact Ht |].
  (** ζ, then the substitutions' equation *)
  etransitivity; [ exact (lets_exp_zeta bs Ht) |].
  pose proof (sub_eq_preserves_exp_eq _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HX) Hz) as E4.
  rewrite <- (exp_sub_sub X τ (lets_sub bs)) in E4.
  rewrite (exp_scoped_sub_id _ _ _ Hs Hτx) in E4.
  eapply wf_exp_eq_conv_sort; [ exact E4 | exact HPσ | constructor | exact E2 ].
Qed.

(** The theorem the executable implementation cites: the readback of a kept
    proof, [bs] binding the positions of the environment it reads and [Ls]
    the local definitions in front of its term [X], replaced by a chain
    [bs'] the peeled environment reads back as. *)
Corollary lets_peeling_typed : forall {Θ Ξ Γ bs Ls X bs' P σ},
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp bs (lets_exp Ls X) : P ->
    ⊢ Θ ⍮ Ξ ⍮ ctx_lets Γ bs' ->
    Θ ⍮ Ξ ⍮ ctx_lets Γ bs' ⊢ˢ σ : ctx_lets Γ (bs ++ Ls) ->
    X[σ] = X ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ⨟ lets_sub bs' ≈ lets_sub (bs ++ Ls) : ctx_lets Γ (bs ++ Ls) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp bs' X : P /\ Θ ⍮ Ξ ⍮ Γ ⊢ lets_exp bs' X ≈ lets_exp bs (lets_exp Ls X) : P.
Proof.
  intros * HP Hw HΓ' Hσ HXσ Hz; rewrite <- lets_exp_app in *.
  exact (lets_chain_replacement_typed HP Hw HΓ' Hσ HXσ Hz).
Qed.
