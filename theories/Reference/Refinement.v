(** * The Extracted Implementation Refines the Reference One

    The checker of [Extraction.TypeCheck] is refined from that of
    [Reference.TypeCheck] (see the head of [Extraction.TypeCheck]), and the
    normalizers of [Extraction.NbE] from those of [Reference.NbE], by the
    evaluation of [Extraction.FastEval], which skips unread recursive
    results.  These are the input–output equalities of the refinement:

    - the checkers decide the same judgments with the same specification, so
      they give the same decision and the same inferred normal form
      ([functional_alg_type_infer]);
    - the normalizers give the same normal form ([functional_nbe]);
    - the evaluators give related values ([dsim], [Extraction.Simulation]),
      from environments that agree where the term may read, and readback of
      related values gives the same normal form.

    The extracted code runs on a fast context ([FCtx], [Extraction.Lookup])
    and nothing else, so the equalities are stated at every fast context
    [F], at the Core context it stands for ([fc_deps F], [fc_stack F]).
    Those are the canonical Core contexts, which every well-formed one is
    ([canon_of_wf]).  The equalities of evaluation and normalization are
    also stated at any canonical [Θ ⍮ Ξ] itself, with the reference side
    at [Θ ⍮ Ξ] and the extracted side at its translation [fctx_of]
    (the [_at] corollaries). *)

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import Evaluation Readback.
From Mctt.Extraction Require Import Lookup FastEval Simulation TypeCheckBase.
From Mctt.Extraction Require Evaluation Readback NbE TypeCheck.
From Mctt.Reference Require Evaluation Readback NbE TypeCheck.
Import Domain_Notations Fixed_Notations.

(** The computational content of a decision, and of an inference. *)
Definition sumbool_result {P Q : Prop} (s : {P} + {Q}) : bool := if s then true else false.

Definition sumor_result {A} {P : A -> Prop} {Q : Prop} (s : {x | P x} + {Q}) : option A :=
  match s with
  | inleft (exist _ x _) => Some x
  | inright _ => None
  end.

(** Two decisions of one proposition give the same answer. *)
Lemma sumbool_result_iff : forall {P Q Q' : Prop} (s : {P} + {Q}) (s' : {P} + {Q'}),
    (Q -> ~ P) -> (Q' -> ~ P) -> sumbool_result s = sumbool_result s'.
Proof. intros * HQ HQ'; destruct s, s'; cbn; firstorder. Qed.

(** ** The Checkers *)

Section Checkers.
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

  Theorem type_check_in_refines : forall G A HA P M H H',
      sumbool_result (Extraction.TypeCheck.type_check_in F G A HA P M H) =
      sumbool_result (Reference.TypeCheck.type_check_in F G A HA P M H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.

  Theorem type_infer_in_refines : forall G HG P M H H',
      sumor_result (Extraction.TypeCheck.type_infer_in F G HG P M H) =
      sumor_result (Reference.TypeCheck.type_infer_in F G HG P M H').
  Proof.
    intros.
    destruct (Extraction.TypeCheck.type_infer_in F G HG P M H) as [[A HA] | HN],
             (Reference.TypeCheck.type_infer_in F G HG P M H') as [[A' HA'] | HN']; cbn;
      destruct_conjs;
      [ f_equal; eapply functional_alg_type_infer; [ exact (ctx_wf_gctx _ _ _ HG) | eassumption | eassumption ]
      | exfalso; eapply HN'; eassumption
      | exfalso; eapply HN; eassumption
      | reflexivity ].
  Qed.

  Theorem ext_check_refines : forall G HG Ψ H H',
      sumbool_result (Extraction.TypeCheck.ext_check F G HG Ψ H) =
      sumbool_result (Reference.TypeCheck.ext_check F G HG Ψ H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.

  Theorem unit_check_refines : forall G HG U H H',
      sumbool_result (Extraction.TypeCheck.unit_check F G HG U H) =
      sumbool_result (Reference.TypeCheck.unit_check F G HG U H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.

  Theorem modexp_check_refines : forall G HG M H H',
      sumbool_result (Extraction.TypeCheck.modexp_check F G HG M H) =
      sumbool_result (Reference.TypeCheck.modexp_check F G HG M H').
  Proof. intros; apply sumbool_result_iff; auto. Qed.
End Checkers.

(** ** Evaluation, Readback and Normalization *)

(** The proofs, for the extracted code at any [F] whose Core context is
    [Θ ⍮ Ξ]: the theorems below take [Θ ⍮ Ξ] to be [fc_deps F ⍮ fc_stack F],
    the [_at] corollaries [F] to be the translation of [Θ ⍮ Ξ]. *)
Section NbEProofs.
  Variables (F : FCtx) (Θ : gdeps) (Ξ : gstack).
  Hypotheses (HΘ : fc_deps F = Θ) (HΞ : fc_stack F = Ξ).

  Lemma eval_exp_impl_refines_eq : forall M p p' H H',
      env_agree Θ Ξ (fun x => ~ exp_fresh x M) p p' ->
      dsim Θ Ξ (proj1_sig (Reference.Evaluation.eval_exp_impl Θ Ξ M p H))
           (proj1_sig (Extraction.Evaluation.feval_exp_impl F M p' H')).
  Proof.
    intros * Hp.
    destruct (Reference.Evaluation.eval_exp_impl Θ Ξ M p H) as [a Ha],
             (Extraction.Evaluation.feval_exp_impl F M p' H') as [a' Ha']; cbn.
    rewrite HΘ, HΞ in Ha'.
    destruct (feval_exp_sim _ _ _ _ _ Ha _ Hp) as (a'' & Ha'' & Hs).
    rewrite (functional_feval_exp _ _ _ _ Ha' Ha''); exact Hs.
  Qed.

  Lemma read_typ_impl_refines_eq : forall s a a' H H',
      dsim Θ Ξ a a' ->
      proj1_sig (Reference.Readback.read_typ_impl Θ Ξ s a H) =
      proj1_sig (Extraction.Readback.fread_typ_impl F s a' H').
  Proof.
    intros * Ha.
    destruct (Reference.Readback.read_typ_impl Θ Ξ s a H) as [W HW],
             (Extraction.Readback.fread_typ_impl F s a' H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_fread_typ; [ eapply fread_typ_sim; eassumption | eassumption ].
  Qed.

  Lemma read_nf_impl_refines_eq : forall s d d' H H',
      dsim_nf Θ Ξ d d' ->
      proj1_sig (Reference.Readback.read_nf_impl Θ Ξ s d H) =
      proj1_sig (Extraction.Readback.fread_nf_impl F s d' H').
  Proof.
    intros * Hd.
    destruct (Reference.Readback.read_nf_impl Θ Ξ s d H) as [W HW],
             (Extraction.Readback.fread_nf_impl F s d' H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_fread_nf; [ eapply fread_nf_sim; eassumption | eassumption ].
  Qed.

  Lemma initial_env_impl_refines_eq : forall G H H',
      env_agree Θ Ξ (fun _ => True) (proj1_sig (Reference.NbE.initial_env_impl Θ Ξ G H))
                (proj1_sig (Extraction.NbE.initial_env_impl F G H')).
  Proof.
    intros.
    destruct (Reference.NbE.initial_env_impl Θ Ξ G H) as [p Hp],
             (Extraction.NbE.initial_env_impl F G H') as [p' (p0 & Hp0 & Hag)]; cbn.
    rewrite HΘ, HΞ in Hp0, Hag.
    rewrite (functional_initial_env _ _ Hp _ Hp0); exact Hag.
  Qed.

  Lemma nbe_ty_env_impl_refines_eq : forall G P P' A H H',
      proj1_sig (Reference.NbE.nbe_ty_env_impl Θ Ξ G P A H) =
      proj1_sig (Extraction.NbE.nbe_ty_env_impl F G P' A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_ty_env_impl Θ Ξ G P A H) as [W HW],
             (Extraction.NbE.nbe_ty_env_impl F G P' A H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_nbe_ty; eassumption.
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

  Lemma nbe_impl_refines_eq : forall G M A H H',
      proj1_sig (Reference.NbE.nbe_impl Θ Ξ G M A H) = proj1_sig (Extraction.NbE.nbe_impl F G M A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_impl Θ Ξ G M A H) as [W HW],
             (Extraction.NbE.nbe_impl F G M A H') as [W' HW']; cbn.
    rewrite HΘ, HΞ in HW'.
    eapply functional_nbe; eassumption.
  Qed.
End NbEProofs.

(** At every fast context *)
Section NbE.
  Variable F : FCtx.

  Theorem eval_exp_impl_refines : forall M p p' H H',
      env_agree (fc_deps F) (fc_stack F) (fun x => ~ exp_fresh x M) p p' ->
      dsim (fc_deps F) (fc_stack F) (proj1_sig (Reference.Evaluation.eval_exp_impl (fc_deps F) (fc_stack F) M p H))
           (proj1_sig (Extraction.Evaluation.feval_exp_impl F M p' H')).
  Proof. exact (eval_exp_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem read_typ_impl_refines : forall s a a' H H',
      dsim (fc_deps F) (fc_stack F) a a' ->
      proj1_sig (Reference.Readback.read_typ_impl (fc_deps F) (fc_stack F) s a H) =
      proj1_sig (Extraction.Readback.fread_typ_impl F s a' H').
  Proof. exact (read_typ_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem read_nf_impl_refines : forall s d d' H H',
      dsim_nf (fc_deps F) (fc_stack F) d d' ->
      proj1_sig (Reference.Readback.read_nf_impl (fc_deps F) (fc_stack F) s d H) =
      proj1_sig (Extraction.Readback.fread_nf_impl F s d' H').
  Proof. exact (read_nf_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem initial_env_impl_refines : forall G H H',
      env_agree (fc_deps F) (fc_stack F) (fun _ => True)
                (proj1_sig (Reference.NbE.initial_env_impl (fc_deps F) (fc_stack F) G H))
                (proj1_sig (Extraction.NbE.initial_env_impl F G H')).
  Proof. exact (initial_env_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem nbe_ty_env_impl_refines : forall G P P' A H H',
      proj1_sig (Reference.NbE.nbe_ty_env_impl (fc_deps F) (fc_stack F) G P A H) =
      proj1_sig (Extraction.NbE.nbe_ty_env_impl F G P' A H').
  Proof. exact (nbe_ty_env_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem nbe_ty_impl_refines : forall G A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl (fc_deps F) (fc_stack F) G A H) =
      proj1_sig (Extraction.NbE.nbe_ty_impl F G A H').
  Proof. exact (nbe_ty_impl_refines_eq F _ _ eq_refl eq_refl). Qed.

  Theorem nbe_impl_refines : forall G M A H H',
      proj1_sig (Reference.NbE.nbe_impl (fc_deps F) (fc_stack F) G M A H) =
      proj1_sig (Extraction.NbE.nbe_impl F G M A H').
  Proof. exact (nbe_impl_refines_eq F _ _ eq_refl eq_refl). Qed.
End NbE.

(** At every canonical Core context, the extracted code at its
    translation *)
Section NbEAt.
  Variables (Θ : gdeps) (Ξ : gstack) (HcΘ : canon_deps Θ) (HcΞ : canon_stack Ξ).

  Corollary eval_exp_impl_refines_at : forall M p p' H H',
      env_agree Θ Ξ (fun x => ~ exp_fresh x M) p p' ->
      dsim Θ Ξ (proj1_sig (Reference.Evaluation.eval_exp_impl Θ Ξ M p H))
           (proj1_sig (Extraction.Evaluation.feval_exp_impl (fctx_of Θ Ξ HcΘ HcΞ) M p' H')).
  Proof. exact (eval_exp_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary read_typ_impl_refines_at : forall s a a' H H',
      dsim Θ Ξ a a' ->
      proj1_sig (Reference.Readback.read_typ_impl Θ Ξ s a H) =
      proj1_sig (Extraction.Readback.fread_typ_impl (fctx_of Θ Ξ HcΘ HcΞ) s a' H').
  Proof. exact (read_typ_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary read_nf_impl_refines_at : forall s d d' H H',
      dsim_nf Θ Ξ d d' ->
      proj1_sig (Reference.Readback.read_nf_impl Θ Ξ s d H) =
      proj1_sig (Extraction.Readback.fread_nf_impl (fctx_of Θ Ξ HcΘ HcΞ) s d' H').
  Proof. exact (read_nf_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary initial_env_impl_refines_at : forall G H H',
      env_agree Θ Ξ (fun _ => True) (proj1_sig (Reference.NbE.initial_env_impl Θ Ξ G H))
                (proj1_sig (Extraction.NbE.initial_env_impl (fctx_of Θ Ξ HcΘ HcΞ) G H')).
  Proof. exact (initial_env_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary nbe_ty_env_impl_refines_at : forall G P P' A H H',
      proj1_sig (Reference.NbE.nbe_ty_env_impl Θ Ξ G P A H) =
      proj1_sig (Extraction.NbE.nbe_ty_env_impl (fctx_of Θ Ξ HcΘ HcΞ) G P' A H').
  Proof. exact (nbe_ty_env_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary nbe_ty_impl_refines_at : forall G A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl Θ Ξ G A H) =
      proj1_sig (Extraction.NbE.nbe_ty_impl (fctx_of Θ Ξ HcΘ HcΞ) G A H').
  Proof. exact (nbe_ty_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.

  Corollary nbe_impl_refines_at : forall G M A H H',
      proj1_sig (Reference.NbE.nbe_impl Θ Ξ G M A H) =
      proj1_sig (Extraction.NbE.nbe_impl (fctx_of Θ Ξ HcΘ HcΞ) G M A H').
  Proof. exact (nbe_impl_refines_eq _ _ _ (fctx_of_deps _ _ _ _) (fctx_of_stack _ _ _ _)). Qed.
End NbEAt.
