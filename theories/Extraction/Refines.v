(** * The Refinement at Any Lookup Data

    The input–output equalities of [Reference.Refinement], for the
    implementations at any [FCtx] ([Extraction.Lookup]): the data a command
    looks names up in, which the extracted checker builds once per check
    ([fctx_at]).  [Reference.Refinement] states them at the default,
    [fctx_none]; the proofs are the same, as every lookup an [FCtx] gives
    is the global context's. *)

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
Definition sumbool_result_f {P Q : Prop} (s : {P} + {Q}) : bool := if s then true else false.

Definition sumor_result_f {A} {P : A -> Prop} {Q : Prop} (s : {x | P x} + {Q}) : option A :=
  match s with
  | inleft (exist _ x _) => Some x
  | inright _ => None
  end.

Section Fixed_GCtx.
  Context {GC : GCtx} {F : FCtx gc_deps gc_stack}.

  Lemma sumbool_result_f_iff : forall {P Q Q' : Prop} (s : {P} + {Q}) (s' : {P} + {Q'}),
      (Q -> ~ P) -> (Q' -> ~ P) -> sumbool_result_f s = sumbool_result_f s'.
  Proof. intros * HQ HQ'; destruct s, s'; cbn; firstorder. Qed.

  Theorem type_check_in_refines_f : forall G A HA P M H H',
      sumbool_result_f (Extraction.TypeCheck.type_check_in G A HA P M H) =
      sumbool_result_f (Reference.TypeCheck.type_check_in G A HA P M H').
  Proof. intros; apply sumbool_result_f_iff; auto. Qed.

  Theorem type_infer_in_refines_f : forall G HG P M H H',
      sumor_result_f (Extraction.TypeCheck.type_infer_in G HG P M H) =
      sumor_result_f (Reference.TypeCheck.type_infer_in G HG P M H').
  Proof.
    intros.
    destruct (Extraction.TypeCheck.type_infer_in G HG P M H) as [[A HA] | HN],
             (Reference.TypeCheck.type_infer_in G HG P M H') as [[A' HA'] | HN']; cbn;
      destruct_conjs;
      [ f_equal; eapply functional_alg_type_infer; [ exact (ctx_wf_gctx _ _ _ HG) | eassumption | eassumption ]
      | exfalso; eapply HN'; eassumption
      | exfalso; eapply HN; eassumption
      | reflexivity ].
  Qed.

  Theorem ext_check_refines_f : forall G HG Ψ H H',
      sumbool_result_f (Extraction.TypeCheck.ext_check G HG Ψ H) =
      sumbool_result_f (Reference.TypeCheck.ext_check G HG Ψ H').
  Proof. intros; apply sumbool_result_f_iff; auto. Qed.

  Theorem unit_check_refines_f : forall G HG U H H',
      sumbool_result_f (Extraction.TypeCheck.unit_check G HG U H) =
      sumbool_result_f (Reference.TypeCheck.unit_check G HG U H').
  Proof. intros; apply sumbool_result_f_iff; auto. Qed.

  Theorem modexp_check_refines_f : forall G HG M H H',
      sumbool_result_f (Extraction.TypeCheck.modexp_check G HG M H) =
      sumbool_result_f (Reference.TypeCheck.modexp_check G HG M H').
  Proof. intros; apply sumbool_result_f_iff; auto. Qed.
End Fixed_GCtx.

(** ** Evaluation, Readback and Normalization *)

Section NbE.
  Variables (Θ : gdeps) (Ξ : gstack).
  Context {F : FCtx Θ Ξ}.

  Theorem eval_exp_impl_refines_f : forall M p p' H H',
      env_agree (fun x => ~ exp_fresh x M) p p' ->
      dsim (proj1_sig (Reference.Evaluation.eval_exp_impl Θ Ξ M p H))
           (proj1_sig (Extraction.Evaluation.feval_exp_impl Θ Ξ M p' H')).
  Proof.
    intros * Hp.
    destruct (Reference.Evaluation.eval_exp_impl Θ Ξ M p H) as [a Ha],
             (Extraction.Evaluation.feval_exp_impl Θ Ξ M p' H') as [a' Ha']; cbn.
    destruct (feval_exp_sim _ _ _ _ _ Ha _ Hp) as (a'' & Ha'' & Hs).
    rewrite (functional_feval_exp _ _ _ _ Ha' Ha''); exact Hs.
  Qed.

  Theorem read_typ_impl_refines_f : forall s a a' H H',
      dsim a a' ->
      proj1_sig (Reference.Readback.read_typ_impl Θ Ξ s a H) =
      proj1_sig (Extraction.Readback.fread_typ_impl Θ Ξ s a' H').
  Proof.
    intros * Ha.
    destruct (Reference.Readback.read_typ_impl Θ Ξ s a H) as [W HW],
             (Extraction.Readback.fread_typ_impl Θ Ξ s a' H') as [W' HW']; cbn.
    eapply functional_fread_typ; [ eapply fread_typ_sim; eassumption | eassumption ].
  Qed.

  Theorem read_nf_impl_refines_f : forall s d d' H H',
      dsim_nf d d' ->
      proj1_sig (Reference.Readback.read_nf_impl Θ Ξ s d H) =
      proj1_sig (Extraction.Readback.fread_nf_impl Θ Ξ s d' H').
  Proof.
    intros * Hd.
    destruct (Reference.Readback.read_nf_impl Θ Ξ s d H) as [W HW],
             (Extraction.Readback.fread_nf_impl Θ Ξ s d' H') as [W' HW']; cbn.
    eapply functional_fread_nf; [ eapply fread_nf_sim; eassumption | eassumption ].
  Qed.

  Theorem initial_env_impl_refines_f : forall G H H',
      env_agree (fun _ => True) (proj1_sig (Reference.NbE.initial_env_impl Θ Ξ G H))
                (proj1_sig (Extraction.NbE.initial_env_impl Θ Ξ G H')).
  Proof.
    intros.
    destruct (Reference.NbE.initial_env_impl Θ Ξ G H) as [p Hp],
             (Extraction.NbE.initial_env_impl Θ Ξ G H') as [p' (p0 & Hp0 & Hag)]; cbn.
    rewrite (functional_initial_env _ _ Hp _ Hp0); exact Hag.
  Qed.

  Theorem nbe_ty_env_impl_refines_f : forall G P P' A H H',
      proj1_sig (Reference.NbE.nbe_ty_env_impl Θ Ξ G P A H) =
      proj1_sig (Extraction.NbE.nbe_ty_env_impl Θ Ξ G P' A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_ty_env_impl Θ Ξ G P A H) as [W HW],
             (Extraction.NbE.nbe_ty_env_impl Θ Ξ G P' A H') as [W' HW']; cbn.
    eapply functional_nbe_ty; eassumption.
  Qed.

  Theorem nbe_ty_impl_refines_f : forall G A H H',
      proj1_sig (Reference.NbE.nbe_ty_impl Θ Ξ G A H) = proj1_sig (Extraction.NbE.nbe_ty_impl Θ Ξ G A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_ty_impl Θ Ξ G A H) as [W HW],
             (Extraction.NbE.nbe_ty_impl Θ Ξ G A H') as [W' HW']; cbn.
    eapply functional_nbe_ty; eassumption.
  Qed.

  Theorem nbe_impl_refines_f : forall G M A H H',
      proj1_sig (Reference.NbE.nbe_impl Θ Ξ G M A H) = proj1_sig (Extraction.NbE.nbe_impl Θ Ξ G M A H').
  Proof.
    intros.
    destruct (Reference.NbE.nbe_impl Θ Ξ G M A H) as [W HW],
             (Extraction.NbE.nbe_impl Θ Ξ G M A H') as [W' HW']; cbn.
    eapply functional_nbe; eassumption.
  Qed.
End NbE.
