(** * The Extracted Normalizers Refine the Reference Ones

    The input–output equalities of the refinement of normalization: the
    normalizers of [Extraction.NbE] and those of [Reference.NbE] both
    compute the normal form [nbe] / [nbe_ty] specifies, which is unique
    ([functional_nbe], [functional_nbe_ty]), so they give the same normal
    form.  No simulation is needed here: the extracted normalizers are
    proved to meet the specification in [Extraction.NbE], through the
    simulation of [Extraction.Simulation].  The checkers' agreement is
    [Reference.TypeCheckAgreement].

    The extracted code runs on a fast context ([FCtx], [Extraction.Lookup])
    and nothing else, so the equalities are stated at every fast context
    [F], at the Core context it stands for ([fc_deps F], [fc_stack F]).
    Those are the canonical Core contexts, which every well-formed one is
    ([canon_of_wf]).  They are also stated at any canonical [Θ ⍮ Ξ] itself,
    with the reference side at [Θ ⍮ Ξ] and the extracted side at its
    translation [fctx_of] (the [_at] corollaries). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import NbE.
From Mctt.Extraction Require Import Lookup.
From Mctt.Extraction Require NbE.
From Mctt.Reference Require NbE.

(** The proofs, for the extracted code at any [F] whose Core context is
    [Θ ⍮ Ξ]: the theorems below take [Θ ⍮ Ξ] to be [fc_deps F ⍮ fc_stack F],
    the [_at] corollaries [F] to be the translation of [Θ ⍮ Ξ]. *)
Section NbEProofs.
  Variables (F : FCtx) (Θ : gdeps) (Ξ : gstack).
  Hypotheses (HΘ : fc_deps F = Θ) (HΞ : fc_stack F = Ξ).

  Lemma nbe_impl_refines_eq : forall G M A H H',
      proj1_sig (Reference.NbE.nbe_impl Θ Ξ G M A H) = proj1_sig (Extraction.NbE.nbe_impl F G M A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_impl Θ Ξ G M A H) as [W HW],
             (Extraction.NbE.nbe_impl F G M A H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_nbe; eassumption.
  Qed.

  Lemma nbe_ty_impl_refines_eq : forall G A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl Θ Ξ G A H) = proj1_sig (Extraction.NbE.nbe_ty_impl F G A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_ty_impl Θ Ξ G A H) as [W HW],
             (Extraction.NbE.nbe_ty_impl F G A H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_nbe_ty; eassumption.
  Qed.

  (** The extracted normalizers at an initial environment computed
      beforehand, as the checker runs them *)
  Lemma nbe_env_impl_refines_eq : forall G P M A H H',
      proj1_sig (Reference.NbE.nbe_impl Θ Ξ G M A H) = proj1_sig (Extraction.NbE.nbe_env_impl F G P M A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_impl Θ Ξ G M A H) as [W HW],
             (Extraction.NbE.nbe_env_impl F G P M A H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_nbe; eassumption.
  Qed.

  Lemma nbe_ty_env_impl_refines_eq : forall G P A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl Θ Ξ G A H) = proj1_sig (Extraction.NbE.nbe_ty_env_impl F G P A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_ty_impl Θ Ξ G A H) as [W HW],
             (Extraction.NbE.nbe_ty_env_impl F G P A H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_nbe_ty; eassumption.
  Qed.
End NbEProofs.

(** At every fast context *)
Section NbE.
  Variable F : FCtx.

  Theorem nbe_impl_refines : forall G M A H H',
      proj1_sig (Reference.NbE.nbe_impl (fc_deps F) (fc_stack F) G M A H) =
      proj1_sig (Extraction.NbE.nbe_impl F G M A H').
  Proof. exact (nbe_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem nbe_ty_impl_refines : forall G A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl (fc_deps F) (fc_stack F) G A H) =
      proj1_sig (Extraction.NbE.nbe_ty_impl F G A H').
  Proof. exact (nbe_ty_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem nbe_env_impl_refines : forall G P M A H H',
      proj1_sig (Reference.NbE.nbe_impl (fc_deps F) (fc_stack F) G M A H) =
      proj1_sig (Extraction.NbE.nbe_env_impl F G P M A H').
  Proof. exact (nbe_env_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem nbe_ty_env_impl_refines : forall G P A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl (fc_deps F) (fc_stack F) G A H) =
      proj1_sig (Extraction.NbE.nbe_ty_env_impl F G P A H').
  Proof. exact (nbe_ty_env_impl_refines_eq F _ _ eq_refl eq_refl). Qed.
End NbE.

(** At every canonical Core context, the extracted code at its
    translation *)
Section NbEAt.
  Variables (Θ : gdeps) (Ξ : gstack) (HcΘ : canon_deps Θ) (HcΞ : canon_stack Ξ).

  Corollary nbe_impl_refines_at : forall G M A H H',
      proj1_sig (Reference.NbE.nbe_impl Θ Ξ G M A H) =
      proj1_sig (Extraction.NbE.nbe_impl (fctx_of Θ Ξ HcΘ HcΞ) G M A H').
  Proof. exact (nbe_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary nbe_ty_impl_refines_at : forall G A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl Θ Ξ G A H) =
      proj1_sig (Extraction.NbE.nbe_ty_impl (fctx_of Θ Ξ HcΘ HcΞ) G A H').
  Proof. exact (nbe_ty_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary nbe_env_impl_refines_at : forall G P M A H H',
      proj1_sig (Reference.NbE.nbe_impl Θ Ξ G M A H) =
      proj1_sig (Extraction.NbE.nbe_env_impl (fctx_of Θ Ξ HcΘ HcΞ) G P M A H').
  Proof. exact (nbe_env_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary nbe_ty_env_impl_refines_at : forall G P A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl Θ Ξ G A H) =
      proj1_sig (Extraction.NbE.nbe_ty_env_impl (fctx_of Θ Ξ HcΘ HcΞ) G P A H').
  Proof. exact (nbe_ty_env_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.
End NbEAt.
