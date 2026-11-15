(** * The Kinds of a λ Are Unique

    Two typings of a λ, in contexts extending one context by equal
    extensions, give it the same kinds ([fn_kinds_unique_ext_wf]): the
    premise the set model's interpretation of a λ reads
    ([fn_kinds_unique_ext]), proved from the typing.

    In one context ([fn_kinds_unique_wf]): the codomain kind is the kind
    of the λ's type ([term_kind_unique]), and a [Π] below a [Π] of one
    codomain kind keeps its domain kind ([subtyp_pi_domain_kind]); the
    domain kinds of the two inversions are that of the λ's own domain
    ([type_kind_unique]).  Across equal extensions: the extensions are
    related telescopes ([tele_rel_of_ext_eq]), along which a typing moves
    ([slot_transport_exp]); an assumption's two types, each below the
    other, are equal ([mutual_subtyp_exp_eq]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Import Inversions TermKinds SlotTransport.
From Mctt.Core.Syntactic Require Import CoreInversions.
From Mctt.Core.Syntactic.System Require Import Structural SlotConversion.
From Mctt Require Import Algorithmic.Strengthening.
From Mctt.Core.SetModel.Interpretation Require Import Functional ContextRelation.
Import Syntax_Notations Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section FnKinds.
  Context {GC : GCtx}.
  (** The global context is well formed *)
  Hypothesis Hg : ⊢ᵍ gc_deps ⍮ gc_stack.

(** ** In One Context *)

(** A sort's kind is the kind it computes to. *)
Lemma sort_kind_exp_kind : forall S κ, sort_kind S κ -> κ = sort_exp_kind S.
Proof.
  intros * Hk; exact (sort_kind_unique _ _ _ Hk (sort_kind_sort_exp_kind _ (sort_kind_type_sort _ _ Hk))).
Qed.

(** A type's sorts are of one kind: the kind of its normal form
    ([nbe_ty_kind_of_sort]). *)
Lemma type_kind_unique : forall Γ A S S' κ κ', Γ ⊢ A : S -> sort_kind S κ -> Γ ⊢ A : S' -> sort_kind S' κ' -> κ = κ'.
Proof.
  intros * HA Hk HA' Hk'.
  pose proof (sort_kind_type_sort _ _ Hk) as HS; pose proof (sort_kind_type_sort _ _ Hk') as HS'.
  destruct (nbe_ty_exists_sort HS HA) as [W HW].
  rewrite (sort_kind_exp_kind _ _ Hk), (sort_kind_exp_kind _ _ Hk').
  rewrite <- (nbe_ty_kind_of_sort HS HA HW), <- (nbe_ty_kind_of_sort HS' HA' HW); reflexivity.
Qed.

(** A [Π] is a type of a sort of its codomain kind. *)
Lemma pi_typed_kind : forall Γ κd κc A B C, Γ ⊢ a_pi κd κc A B : C ->
    exists S, sort_kind S κc /\ Γ ⊢ a_pi κd κc A B : S.
Proof.
  intros * H; destruct κc.
  - destruct (wf_pi_typed_large H) as [k Hk]; exists Typeω@k; split; [ constructor | exact Hk ].
  - exists Propₘ; split; [ constructor | eapply prop_former_typed; [ exact H | eauto 7 ] ].
  - destruct (wf_pi_typed_kind evaluated_kind_level H) as [k Hk]; exists LevelSort; split; [ constructor | exact Hk ].
Qed.

(** A proposition is related by subtyping to a proposition only by an
    equation at [Propₘ]: no proposition is a type of a large universe
    ([typ_prop_absurd]) or of levels ([level_type_not_prop]). *)
Lemma subtyp_prop_exp_eq : forall Γ A B, Γ ⊢ A ⊆ B -> Γ ⊢ A : Propₘ -> Γ ⊢ A ≈ B : Propₘ.
Proof.
  intros * Hs HA.
  destruct (subtyp_spec Hs)
    as [(S & HS & Heq) | [(U & V & [k1 HU] & _ & _)
       | [(κ1 & κc1 & A1 & A2 & B1 & B2 & Hev1 & [k1 Ha] & _) | (m & n & _ & HL & _)]]].
  - destruct HS as [i | |].
    + exfalso; eapply typ_prop_absurd; [| exact HA ]; gen_presups; eassumption.
    + exact Heq.
    + exfalso; eapply level_type_not_prop; [| exact HA ]; gen_presups; eassumption.
  - exfalso; eapply typ_prop_absurd; [| exact HA ]; gen_presups; eassumption.
  - exfalso; destruct Hev1; cbn [abs_kind_sort] in Ha;
      [ exact (typ_prop_absurd (presup_exp_eq_left Ha) HA) | exact (level_type_not_prop (presup_exp_eq_left Ha) HA) ].
  - exfalso; eapply level_type_not_prop; [| exact HA ]; gen_presups; eassumption.
Qed.

(** A [Π] below a [Π] of one codomain kind has its domain kind: the
    [Π] rule ([subtyp_pi_kind_inv]) for an evaluated codomain kind, and
    for a [∀] an equation at [Propₘ] ([exp_eq_all_inversion]). *)
Lemma subtyp_pi_domain_kind : forall Γ κd κd' κc A B A' B',
    Γ ⊢ a_pi κd κc A B ⊆ a_pi κd' κc A' B' -> κd = κd'.
Proof.
  intros * Hs; destruct κc.
  - exact (proj1 (subtyp_pi_kind_inv _ _ _ _ _ _ _ _ evaluated_kind_relevant Hs)).
  - assert (exists C, Γ ⊢ a_pi κd ak_propositional A B : C) as [C HC] by (gen_presups; eexists; eassumption).
    assert (HP : Γ ⊢ a_pi κd ak_propositional A B : Propₘ) by (eapply prop_former_typed; [ exact HC | eauto 7 ]).
    exact (proj1 (exp_eq_all_inversion (subtyp_prop_exp_eq _ _ _ Hs HP))).
  - exact (proj1 (subtyp_pi_kind_inv _ _ _ _ _ _ _ _ evaluated_kind_level Hs)).
Qed.

(** Types below each other at sorts of one kind have that kind's kinds:
    their sorts compute to one kind ([subtyp_type_sort_kind]). *)
Lemma subtyp_sort_kind_eq : forall Γ A A' S S' κ κ', Γ ⊢ A ⊆ A' ->
    Γ ⊢ A : S -> sort_kind S κ -> Γ ⊢ A' : S' -> sort_kind S' κ' -> κ = κ'.
Proof.
  intros * Hs HA Hk HA' Hk'.
  rewrite (sort_kind_exp_kind _ _ Hk), (sort_kind_exp_kind _ _ Hk').
  exact (subtyp_type_sort_kind Hs (sort_kind_type_sort _ _ Hk) (sort_kind_type_sort _ _ Hk') HA HA').
Qed.

(** Two typings of a λ in one context give it the same kinds. *)
Lemma fn_kinds_unique_wf : fn_kinds_unique.
Proof.
  intros Γ A M κd κc C B κd' κc' C' B' H H'.
  (** the codomain kinds: those of the λ's two types *)
  assert (exists S, Γ ⊢ a_pi κd κc C B : S) as [S0 HS0] by (gen_presups; eexists; eassumption).
  assert (exists S, Γ ⊢ a_pi κd' κc' C' B' : S) as [S1 HS1] by (gen_presups; eexists; eassumption).
  destruct (pi_typed_kind _ _ _ _ _ _ HS0) as (T0 & HT0 & HP0).
  destruct (pi_typed_kind _ _ _ _ _ _ HS1) as (T1 & HT1 & HP1).
  pose proof (term_kind_unique _ _ _ _ _ _ _ _ Hg H H' HP0 HT0 HP1 HT1) as <-.
  (** the domain kinds: each that of the λ's own domain *)
  destruct (wf_fn_inversion H) as (κd0 & κc0 & B0 & HM0 & Hs0).
  destruct (wf_fn_inversion H') as (κd1 & κc1 & B1 & HM1 & Hs1).
  assert (exists S, Γ ⊢ a_pi κd0 κc0 A B0 : S) as [S2 HS2] by (gen_presups; eexists; eassumption).
  assert (exists S, Γ ⊢ a_pi κd1 κc1 A B1 : S) as [S3 HS3] by (gen_presups; eexists; eassumption).
  destruct (pi_typed_kind _ _ _ _ _ _ HS2) as (T2 & HT2 & HP2).
  destruct (pi_typed_kind _ _ _ _ _ _ HS3) as (T3 & HT3 & HP3).
  pose proof (subtyp_sort_kind_eq _ _ _ _ _ _ _ Hs0 HP2 HT2 HP0 HT0) as ->.
  pose proof (subtyp_sort_kind_eq _ _ _ _ _ _ _ Hs1 HP3 HT3 HP1 HT1) as ->.
  pose proof (subtyp_pi_domain_kind _ _ _ _ _ _ _ _ Hs0) as ->.
  pose proof (subtyp_pi_domain_kind _ _ _ _ _ _ _ _ Hs1) as ->.
  destruct (ctx_decomp_kind (presup_exp_ctx HM0)) as (D0 & HD0 & HA0).
  destruct (ctx_decomp_kind (presup_exp_ctx HM1)) as (D1 & HD1 & HA1).
  split; [ exact (type_kind_unique _ _ _ _ _ _ HA0 HD0 HA1 HD1) | reflexivity ].
Qed.

(** ** Across Equal Extensions *)

(** Types each below the other, at sorts of one kind, are equal at a sort
    of that kind: their normal forms are equal up to proofs
    ([nbe_ty_of_mutual_subtyp], [exp_eq_of_nbe_ty_same]). *)
Lemma mutual_subtyp_exp_eq : forall Γ A A' S S' κ, Γ ⊢ A ⊆ A' -> Γ ⊢ A' ⊆ A ->
    Γ ⊢ A : S -> sort_kind S κ -> Γ ⊢ A' : S' -> sort_kind S' κ ->
    exists S'', sort_kind S'' κ /\ Γ ⊢ A ≈ A' : S''.
Proof.
  intros * Hs Hs' HA Hk HA' Hk'.
  destruct (sort_kind_common Hk Hk' HA HA') as (i & HAi & HA'i).
  destruct (nbe_ty_of_mutual_subtyp Hs Hs') as (W & W' & HW & HW' & E).
  exists (abs_kind_sort κ Typeω@i); split; [ apply sort_kind_abs_kind_sort |].
  exact (exp_eq_of_nbe_ty_same (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κ i)) HAi HA'i HW HW' E).
Qed.

(** A term of the source of related telescopes is equal to its image, in
    the target ([pair_transport_all] at [sub_pair_inline]). *)
Lemma tele_rel_exp_image : forall Γ Δ Δ2 M A, tele_rel gc_deps gc_stack Γ Δ Δ2 ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Δ2 ++ Γ ->
    Δ ++ Γ ⊢ M : A -> Δ2 ++ Γ ⊢ M ≈ M[inline_sub Δ] : A[inline_sub Δ].
Proof.
  intros * HR H1 H2 HM.
  pose proof (proj1 pair_transport_all _ _ _ _ _ HM _ _ _ (sub_pair_inline _ _ _ _ _ HR H1 H2)) as X.
  rewrite exp_sub_id in X; exact X.
Qed.

(** The same for a unit. *)
Lemma tele_rel_unit_image : forall Γ Δ Δ2 U U', tele_rel gc_deps gc_stack Γ Δ Δ2 ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Δ2 ++ Γ ->
    gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ᵘ U ≈ U' -> gc_deps ⍮ gc_stack ⍮ Δ2 ++ Γ ⊢ᵘ U ≈ U[inline_sub Δ]ᵘ.
Proof.
  intros * HR H1 H2 HU.
  pose proof (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 pair_transport_all))))) _ _ _ _ _ HU _ _ _
                (sub_pair_inline _ _ _ _ _ HR H1 H2))) as X.
  rewrite gunit_sub_id in X; exact X.
Qed.

(** Equal extensions are related telescopes, the right one the source,
    the left one the target. *)
Lemma tele_rel_of_ext_eq : forall Γ Ψ Ψ', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> tele_rel gc_deps gc_stack Γ Ψ' Ψ.
Proof.
  intros * H; remember gc_deps as Θ0 eqn:EΘ; remember gc_stack as Ξ0 eqn:EΞ.
  induction H; subst; [ constructor | | | |].
  all: match goal with H : _ ⍮ _ ⍮ _ ⊢ˣ _ ≈ _ |- _ =>
         let H1 := fresh "HΨ" in let H2 := fresh "HΨ'" in
         pose proof (ext_eq_ctx_left _ _ _ _ _ H) as H1; pose proof (ext_eq_ctx_right _ _ _ _ _ H) as H2 end.
  all: specialize (IHwf_ext_eq eq_refl eq_refl).
  all: specialize (IHwf_ext_eq Hg).
  - (* an assumption: the two types, each below the other, are equal *)
    rename H0 into HA, H1 into HSk, H2 into HA', H3 into HSk', H4 into Hs, H5 into Hs'.
    pose proof (tele_rel_exp_image _ _ _ _ _ IHwf_ext_eq HΨ' HΨ HA') as X.
    rewrite (type_sort_sub _ _ (sort_kind_type_sort _ _ HSk')) in X.
    destruct (mutual_subtyp_exp_eq _ _ _ _ _ _ Hs Hs' HA HSk (presup_exp_eq_left X) HSk') as (S2 & HS2 & E).
    destruct (exp_eq_trans_sort_kind HS2 HSk' E X) as (S3 & HS3 & E').
    econstructor; [ exact IHwf_ext_eq | exact E' | exact (sort_kind_type_sort _ _ HS3) ].
  - (* a definition: the types as an assumption's, the bodies equal *)
    rename H0 into HA, H1 into HS, H2 into HA', H3 into HS', H4 into Hs, H5 into Hs', H7 into HMM, H8 into HM'.
    pose proof (tele_rel_exp_image _ _ _ _ _ IHwf_ext_eq HΨ' HΨ HA') as X.
    rewrite (type_sort_sub _ _ HS') in X.
    pose proof (sort_kind_sort_exp_kind _ HS) as HSk; pose proof (sort_kind_sort_exp_kind _ HS') as HSk'.
    rewrite <- (subtyp_type_sort_kind Hs HS HS' HA (presup_exp_eq_left X)) in HSk'.
    destruct (mutual_subtyp_exp_eq _ _ _ _ _ _ Hs Hs' HA HSk (presup_exp_eq_left X) HSk') as (S2 & HS2 & E).
    destruct (exp_eq_trans_sort_kind HS2 HSk' E X) as (S3 & HS3 & E').
    pose proof (tele_rel_exp_image _ _ _ _ _ IHwf_ext_eq HΨ' HΨ HM') as XM.
    econstructor; [ exact IHwf_ext_eq | exact E' | exact (sort_kind_type_sort _ _ HS3) | | exact XM ].
    eapply wf_exp_eq_trans; [| exact XM ].
    eapply wf_exp_eq_conv_sort; [ exact HMM | exact (presup_exp_eq_right E') | exact (sort_kind_type_sort _ _ HS3) | exact E' ].
  - (* a module slot: the units equal, the source's to its image *)
    rename H0 into HU, H1 into HU'.
    pose proof (tele_rel_unit_image _ _ _ _ _ IHwf_ext_eq HΨ' HΨ HU') as X.
    apply tele_rel_mod; [ exact IHwf_ext_eq | eapply wf_unit_eq_trans; [ exact HU | exact X ] | exact X ].
  - (* a definition with a module part: as a definition and a slot *)
    rename H1 into HAA, H3 into HMM, H4 into HA', H5 into HM', H6 into HU, H7 into HU'.
    pose proof (tele_rel_exp_image _ _ _ _ _ IHwf_ext_eq HΨ' HΨ HA') as X; cbn [exp_sub] in X.
    pose proof (tele_rel_exp_image _ _ _ _ _ IHwf_ext_eq HΨ' HΨ HM') as XM.
    pose proof (tele_rel_unit_image _ _ _ _ _ IHwf_ext_eq HΨ' HΨ HU') as XU.
    assert (EA : Ψ ++ Γ ⊢ A ≈ A'[inline_sub Ψ'] : Typeω@i) by (eapply wf_exp_eq_trans; [ exact HAA | exact X ]).
    apply tele_rel_dm with (i := i);
      [ exact IHwf_ext_eq | exact EA | | exact XM | eapply wf_unit_eq_trans; [ exact HU | exact XU ] | exact XU ].
    eapply wf_exp_eq_trans; [| exact XM ].
    eapply wf_exp_eq_conv_sort; [ exact HMM | exact (presup_exp_eq_right EA) | constructor | exact EA ].
Qed.

(** Two typings of a λ in contexts extending one context by equal
    extensions give it the same kinds: the second moves to the first's
    context ([slot_transport_exp]). *)
Theorem fn_kinds_unique_ext_wf : fn_kinds_unique_ext.
Proof.
  intros Δ Δ' A M κd κc C B κd' κc' C' B' (Γ & Ψ & Ψ' & [-> -> HΨ]) H H'.
  pose proof (slot_transport_exp _ _ _ _ _ _ _ (tele_rel_of_ext_eq _ _ _ HΨ) (ext_eq_ctx_left _ _ _ _ _ HΨ) H') as H''.
  exact (fn_kinds_unique_wf _ _ _ _ _ _ _ _ _ _ _ H H'').
Qed.

End FnKinds.
