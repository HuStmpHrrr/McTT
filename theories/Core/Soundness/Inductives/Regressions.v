(** * Regressions for the Gluing of Groups

    [T (f : TF) := node (p : Phantom (T f) (f Z))], with
    [Phantom (A B) := mk (a : A)]: the view [Phantom (T f) (f Z)] has a
    phantom argument.  The gluing of [T] at [f := g] is one at [T] at a
    [g'] whose readback agrees with [g]'s up to proofs
    ([t_over_phantom_glu_moves]), at the relation of
    [Semantic.Inductives.NestingExamples.t_over_phantom_related]: the
    phantom argument never blocks the move.

    Both sides must be the values of typed terms [F] and [F'].  Readback
    agreement is only up to proofs, and a kept proof [⋆ᵈ⟨M, ρ⟩] reads back
    as [M] whatever [M] is, while the gluing of a type at its uniform
    parameters equates the type's syntactic parameters to their readback
    ([glu_params_top]), which is typed.  For [TF := Box] with
    [Box : Type := box (h : ⊤)], the value [g] of [box tt] and
    [g' := d_con … (⋆ᵈ⟨Type@0, ·⟩ :: nil)] read back as
    [nf_con … [nf_proof ⊤ tt]] and [nf_con … [nf_proof ⊤ Type@0]], equal up
    to proofs, so they are related; but [a_proof ⊤ Type@0] is not typed, so
    no type is glued at [T] at [g'], while [T (box tt)] is glued at [T] at
    [g].  With [F'] typed and glued to [g'], the readback of [g'] is typed
    as [F']'s, and the two readbacks are equal ([glu_nfs_eq_at_upto]). *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER Readback.
From Mctt.Core.Semantic.Inductives Require Import NestingExamples.
From Mctt.Core.Soundness.LogicalRelation Require Import Definitions CoreLemmas CoreTactics.
From Mctt.Core.Soundness.Weakening Require Import Lemmas.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section PhantomGluing.
  Context {GC : GCtx}.
  Variables (pP pT pmP pmT : qname) (TA TB TF SP ST Z : exp).

  Hypothesis HlP : ind_lookup gc_deps gc_stack pP = Some (phantom_group pmP TA TB SP).
  Hypothesis HlT : ind_lookup gc_deps gc_stack pT = Some (t_over_phantom_group pP pT pmT TF ST Z).

  #[local] Abbreviation D := (t_over_phantom_group pP pT pmT TF ST Z).

  (** The shape of the members of [T]'s group: both take the parameter [f]
      only, neither is a record view, and each constructor has one
      recursive argument, ending in a member at no parameter. *)
  Record phantom_member_shape (Mm : imember) : Prop := mk_phantom_member_shape
    { (** The member's parameters are [f : TF] *)
      phantom_member_params : im_params D Mm = ce_ass ak_relevant TF :: nil
      (** It has no non-uniform parameter *)
    ; phantom_member_nparams : im_nparams Mm = nil
      (** It is not a record view *)
    ; phantom_member_head : forall qr Is fl, im_head Mm <> mh_record qr Is fl
      (** Each constructor has one recursive argument, ending in a member
          at no parameter *)
    ; phantom_member_cons : forall c gs, ind_con Mm c = Some gs -> exists j, gs = ca_rec (pt_self j nil) :: nil }.

  Lemma phantom_members : forall m Mm, ind_member D m = Some Mm -> phantom_member_shape Mm.
  Proof.
    intros [| [| m]] Mm HM; unfold ind_member, t_over_phantom_group in HM; cbn in HM; [| | destruct m; discriminate ].
    all: injection HM as <-; constructor; [ reflexivity | reflexivity | intros; discriminate |].
    all: intros c gs Hc; unfold ind_con in Hc; cbn in Hc.
    all: destruct (String.eqb _ _); [ injection Hc as <-; eexists; reflexivity | discriminate ].
  Qed.

  (** Relations over an empty telescope do not depend on the family. *)
  Lemma tele_rel_nil_any : forall {X} tr tr' (vs vs' : list domain), tele_rel tr (@nil X) vs vs' -> tele_rel tr' (@nil X) vs vs'.
  Proof.
    intros * [L H]; destruct vs; [| discriminate ]; destruct vs'; [| destruct H ]; split; [ reflexivity | exact I ].
  Qed.

  Lemma tele_prefix_rel_zero_any : forall tr tr' vs vs', tele_prefix_rel tr 0 vs vs' -> tele_prefix_rel tr' 0 vs vs'.
  Proof.
    intros * [L H]; destruct vs; [| discriminate ]; destruct vs'; [| destruct H ]; split; [ reflexivity | exact I ].
  Qed.

  (** The empty list of terms evaluates to the empty list, and only to it. *)
  Lemma eval_exps_nil_inv : forall ρ bs, ⟦ nil ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ bs -> bs = nil.
  Proof. intros * H; inversion H; reflexivity. Qed.

  (** *** The Uniform Parameter Moves

      Let [g] and [g'] read back alike, [g'] being the value of a term
      [F'] glued to it.  Then terms glued to [g] by readback are glued to
      [g'] ([glu_nfs_eq_at_upto]: [F']'s readback is typed), and, as no
      other part of [T]'s gluing reads the uniform parameter but through
      telescopes that are empty for this group, so are the types and the
      elements. *)
  Section Move.
    Variables (g g' : domain) (F' : exp).
    Hypothesis HF' : params_glu_top (ce_ass ak_relevant TF :: nil) ⋅ (F' :: nil) (g' :: nil).
    Hypothesis Hgg : per_top_ps (ce_ass ak_relevant TF :: nil) (g :: nil) (g' :: nil).

    Lemma phantom_params_move : forall m Mm Γ Ps, ind_member D m = Some Mm ->
        glu_params_top D Mm Γ Ps (g :: nil) -> glu_params_top D Mm Γ Ps (g' :: nil).
    Proof.
      intros * HM [L Ht Hr].
      pose proof (phantom_member_params _ (phantom_members _ _ HM)) as EP.
      constructor; [ exact L | exact Ht |].
      intros Δ φ Ms Hφ HR.
      pose proof (kripke_to_empty _ (kripke_dom _ _ _ Hφ)) as Hψ.
      rewrite EP in HR, Hr |- *; cbn [List.rev List.app] in HR, Hr.
      destruct (Hgg (length Δ)) as [W1 W2 HW1 HW2 E].
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack)))))) as Fps.
      rewrite (Fps _ _ _ _ _ HR _ HW2).
      exact (glu_nfs_eq_at_upto _ _ _ _ _ _ E (Hr _ _ _ Hφ HW1) (params_glu_read _ _ _ _ HF' _ _ _ Hψ HW2)).
    Qed.

    Lemma phantom_components_move : forall NP NEl AP AEl DP DEl Γ Us,
        ind_glu_components pT D (g :: nil) NP NEl AP AEl DP DEl Γ Us ->
        ind_glu_components pT D (g' :: nil) NP NEl AP AEl DP DEl Γ Us.
    Proof.
      intros * [Cn Ca Cr]; constructor.
      - intros * HM _ Hk; exfalso.
        unfold im_nn in Hk; rewrite (phantom_member_nparams _ (phantom_members _ _ HM)) in Hk; cbn in Hk; lia.
      - intros * HM Hc Heq; exfalso.
        destruct (phantom_member_cons _ (phantom_members _ _ HM) _ _ Hc) as [j ->].
        destruct gs1 as [| ? [| ? ?]]; discriminate.
      - intros * HM Hc Heq Hn Hr Hvl HT HAs Hpre.
        pose proof (phantom_members _ _ HM) as HS.
        destruct (phantom_member_cons _ HS _ _ Hc) as [j ->].
        destruct gs1 as [| ? [| ? ?]]; cbn in Heq; try discriminate; injection Heq as <- <-.
        rewrite (phantom_member_nparams _ HS) in Hr; cbn [List.rev] in Hr.
        pose proof (Cr _ _ _ _ nil _ nil _ _ _ _ T HM Hc eq_refl Hn
                      ltac:(rewrite (phantom_member_nparams _ HS); exact (tele_rel_nil_any _ _ _ _ Hr)) Hvl HT HAs
                      (tele_prefix_rel_zero_any _ _ _ _ Hpre)) as H.
        cbn [glu_shape_typ] in H |- *.
        intros Mj Q bsr HMj HTj Hev.
        pose proof (eval_exps_nil_inv _ _ Hev) as ->.
        destruct (H Mj Q nil HMj HTj ltac:(constructor)) as [Hrel Hnp Htop].
        pose proof (phantom_members _ _ HMj) as HSj.
        constructor; [ rewrite (phantom_member_nparams _ HSj) in Hrel |- *; exact (tele_rel_nil_any _ _ _ _ Hrel) | exact Hnp |].
        intros Δ φ Hφ; exact (phantom_params_move _ _ _ _ HMj (Htop _ _ Hφ)).
    Qed.

    Lemma phantom_typ_at_move : forall NP NEl AP AEl DP DEl k Mk U Γ A Ps, ind_member D k = Some Mk ->
        ind_typ_at pT D (g :: nil) nil NP NEl AP AEl DP DEl k Mk U Γ A Ps ->
        ind_typ_at pT D (g' :: nil) nil NP NEl AP AEl DP DEl k Mk U Γ A Ps.
    Proof.
      intros * HM [HA Hk]; split; [ exact HA |].
      intros Δ φ Hφ; destruct (Hk _ _ Hφ) as [Ht Hs Hc Hn]; constructor; [| exact Hs | | exact Hn ].
      - exact (phantom_params_move _ _ _ _ HM Ht).
      - intros Ps' HE; exact (phantom_components_move _ _ _ _ _ _ _ _ (Hc Ps' HE)).
    Qed.

    Lemma phantom_elem_move : forall NEl AEl DP DEl,
        (forall k Γ Us Ns M m, ind_glu_elem pT D (g :: nil) NEl AEl DP DEl k Γ Us Ns M m ->
           ind_glu_elem pT D (g' :: nil) NEl AEl DP DEl k Γ Us Ns M m) /\
        (forall k Γ Us pre Ts t A N v, glu_rec pT D (g :: nil) NEl AEl DP DEl k Γ Us pre Ts t A N v ->
           forall j, t = pt_self j nil -> glu_rec pT D (g' :: nil) NEl AEl DP DEl k Γ Us pre Ts t A N v).
    Proof.
      intros NEl AEl DP DEl.
      apply ind_glu_elem_mut_ind_all.
      - (** A constructor *)
        intros * HM Hrv Href Hc HUl HNl Hbl Hvl HAl HMeq Hnp Hargs Hgnp Hty Harg Hrec IH.
        pose proof (phantom_members _ _ HM) as HS.
        destruct (phantom_member_cons _ HS _ _ Hc) as [j Egs].
        eapply ind_glu_elem_con; try eassumption.
        + rewrite (phantom_member_nparams _ HS) in Hnp |- *; exact (tele_rel_nil_any _ _ _ _ Hnp).
        + rewrite Egs in Hargs |- *; exact (tele_rel_nil_any _ _ _ _ Hargs).
        + intros * Heq HN HA Hv.
          rewrite Egs in Heq; destruct gs1 as [| ? [| ? ?]]; cbn in Heq; try discriminate; injection Heq as <- <-.
          exact (IH nil _ nil _ _ _ ltac:(exact Egs) HN HA Hv j eq_refl).
      - (** A neutral *)
        intros * HM Hrv Href Hb Hread Hnp Hex.
        pose proof (phantom_members _ _ HM) as HS.
        eapply ind_glu_elem_neut; try eassumption.
        rewrite (phantom_member_nparams _ HS) in Hnp |- *; exact (tele_rel_nil_any _ _ _ _ Hnp).
      - (** A record view: none in this group *)
        intros * HM Hh; exfalso; exact (phantom_member_head _ (phantom_members _ _ HM) _ _ _ Hh).
      - (** The end of a shape *)
        intros * HMj Hlen Hglu IH j0 Et; injection Et as _ ->.
        eapply glu_rec_self; [ exact HMj | |].
        + intros bsr Q Hev HA; pose proof (eval_exps_nil_inv _ _ Hev) as ->.
          destruct (Hlen nil Q ltac:(constructor) HA) as [HQ Hr].
          split; [ exact HQ |].
          rewrite (phantom_member_nparams _ (phantom_members _ _ HMj)) in Hr |- *; exact (tele_rel_nil_any _ _ _ _ Hr).
        + intros bsr Q Hev HA; pose proof (eval_exps_nil_inv _ _ Hev) as ->.
          exact (IH nil Q ltac:(constructor) HA).
      - (** A domain: none in this group *)
        intros * _ _ _ _ j Et; discriminate Et.
    Qed.

    Lemma phantom_exp_move : forall NP NEl AP AEl DP DEl k Mk elem_rel U Γ A M m, ind_member D k = Some Mk ->
        ind_glu_exp pT D (g :: nil) nil NP NEl AP AEl DP DEl k Mk elem_rel U Γ A M m ->
        ind_glu_exp pT D (g' :: nil) nil NP NEl AP AEl DP DEl k Mk elem_rel U Γ A M m.
    Proof.
      intros * HM [Ht Hp Ps Hat Hglu].
      refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ht Hp Ps (phantom_typ_at_move _ _ _ _ _ _ _ _ _ _ _ _ HM Hat) _).
      intros Δ φ Ps' Hφ HE; exact (proj1 (phantom_elem_move _ _ _ _) _ _ _ _ _ _ (Hglu _ _ _ Hφ HE)).
    Qed.
  End Move.

  (** [T] at [g] and at [g'], values of typed terms [F] and [F'] glued to
      them, whose readbacks agree up to proofs: the gluing of the one is the
      gluing of the other.  Without the typed terms the statement is false
      (see the header). *)
  Theorem t_over_phantom_glu_moves : forall i g g' F F' P El,
      ⋅ ⊢ F : TF -> ⋅ ⊢ F' : TF ->
      params_glu_top (ce_ass ak_relevant TF :: nil) ⋅ (F :: nil) (g :: nil) ->
      params_glu_top (ce_ass ak_relevant TF :: nil) ⋅ (F' :: nil) (g' :: nil) ->
      per_top_ps (ce_ass ak_relevant TF :: nil) (g :: nil) (g' :: nil) ->
      DG d_ind pT 0 (g :: nil) ∈ glu_univ_elem i ↘ P ↘ El ->
      DG d_ind pT 0 (g' :: nil) ∈ glu_univ_elem i ↘ P ↘ El.
  Proof.
    intros * _ _ HF HF' Hgg HG.
    pose proof (per_top_ps_sym _ _ _ Hgg) as Hg'g.
    remember (g :: nil) as xs eqn:Exs in HG.
    invert_glu_univ_elem HG.
    match goal with
    | H : ind_lookup _ _ pT = Some _ |- _ => rewrite HlT in H; injection H as <-
    end.
    match goal with
    | HM : ind_member _ 0 = Some ?M0, HL : length ?u = _, HR : per_univ_elem _ ?er (d_ind pT 0 _) _,
      HP : _ <∙> ind_glu_typ_pred _ _ _ _ _ _ _ _ _ _ _ _ _,
      HE : _ <∙> ind_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        rename HM into HM0, HL into HuL, HR into Hper, HP into HTP, HE into HEP
    end.
    destruct ups as [| u [| ? ?]]; cbn in HuL; try discriminate; cbn in Exs; injection Exs as -> ->.
    cbn [List.app] in Hper.
    (** [T] at [g'] is related to itself at the same relation: [g ≈ g'] at
        the relation of [t_over_phantom_related], which is [g]'s *)
    assert (Hr : per_univ_elem i elem_rel (d_ind pT 0 (g :: nil)) (d_ind pT 0 (g' :: nil))).
    { pose proof (t_over_phantom_related pP pT pmP pmT TA TB TF SP ST Z HlP HlT i g g' Hgg) as H1r.
      rewrite (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hper H1r); exact H1r. }
    pose proof (proj1 (per_univ_elem_trans _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Hr))) _ _ Hr) as Hr'.
    change (d_ind pT 0 (g' :: nil)) with (d_ind pT 0 ((g' :: nil) ++ nil)).
    simp glu_univ_elem.
    eapply glu_univ_elem_core_indty with (NP := NP) (NEl := NEl) (AP := AP) (AEl := AEl) (DP := DP) (DEl := DEl) (elem_rel := elem_rel);
      try eassumption.
    (** The telescopes of the group are empty: no non-uniform parameter,
        non-recursive argument or domain *)
    1, 3: intros * HM Hn; rewrite (phantom_member_nparams _ (phantom_members _ _ HM)) in Hn; destruct j; discriminate.
    1, 2: intros * HM _ Hc Hn; destruct (phantom_member_cons _ (phantom_members _ _ HM) _ _ Hc) as [? ->]; destruct j; discriminate.
    1, 2: intros * HM _ Hc Heq _ Hn; destruct (phantom_member_cons _ (phantom_members _ _ HM) _ _ Hc) as [? ->];
      destruct gs1 as [| ? [| ? ?]]; cbn in Heq; try discriminate; injection Heq as <- _; destruct j; discriminate.
    (** The types and the elements move both ways *)
    - intros Γ A; split; intros H; [ apply HTP in H | apply HTP ]; destruct H as [Ps HPs]; exists Ps;
        [ exact (phantom_typ_at_move g g' F' HF' Hgg _ _ _ _ _ _ _ _ _ _ _ _ HM0 HPs)
        | exact (phantom_typ_at_move g' g F HF Hg'g _ _ _ _ _ _ _ _ _ _ _ _ HM0 HPs) ].
    - intros Γ A M0 m0; split; intros H; [ apply HEP in H | apply HEP ];
        [ exact (phantom_exp_move g g' F' HF' Hgg _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 H)
        | exact (phantom_exp_move g' g F HF Hg'g _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 H) ].
  Qed.

End PhantomGluing.
