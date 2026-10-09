(** * The Normalizer the Checker Runs

    The termination orders of normalization are those of the reference
    evaluation and readback ([Reference.Evaluation], [Reference.Readback]),
    which are the specification ([nbe], [nbe_ty]).  The normalizers compute
    by the evaluation that skips unread recursive results
    ([Extraction.FastEval]): its values are related to the reference ones
    ([Extraction.Simulation]), so they read back to the same normal forms,
    and the specifications are those of [Reference.NbE].

    An environment the normalizers start from is related to the initial
    environment of its context ([fenv]); the checker computes it once per
    context ([initial_env_impl]) and extends it under binders. *)
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Reference Require Import Evaluation Readback.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Extraction Require Import FastEval Simulation.
From Mctt.Extraction Require Evaluation Readback.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

Inductive initial_env_order (Θ : gdeps) (Ξ : gstack) : ctx -> Prop :=
| ie_nil : initial_env_order Θ Ξ nil
| ie_cons :
  `( initial_env_order Θ Ξ Γ ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_exp_order Θ Ξ A p) ->
     initial_env_order Θ Ξ (Γ ▹ A))
| ie_cons_def :
  `( initial_env_order Θ Ξ Γ ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_exp_order Θ Ξ M p) ->
     initial_env_order Θ Ξ (Γ ▸ A ≔ M))
| ie_cons_mod :
  `( initial_env_order Θ Ξ Γ ->
     initial_env_order Θ Ξ (Γ ▹ₘ U)).

#[local]
Hint Constructors initial_env_order : mctt.

Lemma initial_env_order_sound : forall Θ Ξ Γ p,
    initial_env Θ Ξ Γ p ->
    initial_env_order Θ Ξ Γ.
Proof.
  induction 1; solve [ econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear; mauto
                     | econstructor; eauto ].
Qed.

#[local]
Hint Resolve initial_env_order_sound : mctt.

(** The order of NbE in [Θ ⍮ Ξ ⍮ Γ]. *)
Inductive nbe_order Θ Ξ G M A : Prop :=
| nbe_order_run :
  `( initial_env_order Θ Ξ G ->
     (forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ A p) ->
     (forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ M p) ->
     (forall p a m,
         initial_env Θ Ξ G p ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
         ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
         read_nf_order Θ Ξ (List.length G) ⇓ a m) ->
     nbe_order Θ Ξ G M A ).

#[local]
Hint Constructors nbe_order : mctt.

Lemma nbe_order_sound : forall Θ Ξ G M A w,
    nbe Θ Ξ G M A w ->
    nbe_order Θ Ξ G M A.
Proof.
  induction 1;
    (econstructor; intros; functional_initial_env_rewrite_clear;
     functional_eval_rewrite_clear; functional_read_rewrite_clear; mauto).
Qed.

#[local]
Hint Resolve nbe_order_sound : mctt.

Inductive nbe_ty_order Θ Ξ G A : Prop :=
| nbe_ty_order_run :
  `( initial_env_order Θ Ξ G ->
     (forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ A p) ->
     (forall p a,
         initial_env Θ Ξ G p ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
         read_typ_order Θ Ξ (List.length G) a) ->
     nbe_ty_order Θ Ξ G A ).

#[local]
Hint Constructors nbe_ty_order : mctt.

Lemma nbe_ty_order_sound : forall Θ Ξ G A w,
    nbe_ty Θ Ξ G A w ->
    nbe_ty_order Θ Ξ G A.
Proof.
  induction 1;
    (econstructor; intros; functional_initial_env_rewrite_clear;
     functional_eval_rewrite_clear; functional_read_rewrite_clear; mauto).
Qed.

#[local]
Hint Resolve nbe_ty_order_sound : mctt.


(** ** The Fast Normalizer *)

(** An environment related, entry by entry, to the initial environment of
    [G]. *)
Definition fenv Θ Ξ G := { p' | exists p, initial_env Θ Ξ G p /\ env_agree (fun _ => True) p p' }.

Section Orders.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** The fast evaluation terminates where the reference one does, from an
      environment that agrees where the term may read, at a related value. *)
  Lemma feval_of_ref : forall M p p' a,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> env_agree (fun x => ~ exp_fresh x M) p p' ->
      Evaluation.feval_exp_order Θ Ξ M p' /\ forall a', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p' ↘ a' -> dsim a a'.
  Proof.
    intros * Ha Hp.
    destruct (feval_exp_sim Θ Ξ _ _ _ Ha _ Hp) as (a'' & Ha'' & Hs).
    split; [ eapply Evaluation.feval_exp_order_sound; eassumption |].
    intros a' Ha'; rewrite <- (functional_feval_exp _ _ _ _ Ha'' Ha'); exact Hs.
  Qed.

  Lemma eval_of_order : forall M p, eval_exp_order Θ Ξ M p -> exists a, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ a.
  Proof. intros * H; destruct (eval_exp_impl Θ Ξ M p H) as [a Ha]; eauto. Qed.

  Lemma read_typ_of_order : forall s a, read_typ_order Θ Ξ s a -> exists W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros * H; destruct (read_typ_impl Θ Ξ s a H) as [W HW]; eauto. Qed.

  Lemma read_nf_of_order : forall s d, read_nf_order Θ Ξ s d -> exists W, Rnf d in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros * H; destruct (read_nf_impl Θ Ξ s d H) as [W HW]; eauto. Qed.

  Lemma agree_all : forall P p p', env_agree (fun _ => True) p p' -> env_agree P p p'.
  Proof. intros * H; eapply env_agree_mono; [ exact H | intros; exact I ]. Qed.
End Orders.

#[local]
Ltac fnbe_obl :=
  repeat match goal with
    | H : initial_env_order _ _ (_ :: _) |- _ => progressive_invert H
    | H : nbe_ty_order _ _ _ _ |- _ => progressive_invert H
    | H : nbe_order _ _ _ _ _ |- _ => progressive_invert H
    | H : exists _, _ /\ _ |- _ => destruct H as (? & ? & ?)
    end.

Section InitialEnvImpl.
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl Θ Ξ G (H : initial_env_order Θ Ξ G) : fenv Θ Ξ G by struct H :=
  | Θ, Ξ, nil, H => exist _ nil _
  | Θ, Ξ, cons (ce_ass A) G, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      let (a, Ha) := Evaluation.feval_exp_impl Θ Ξ A p _ in
      exist _ (p ↦ ⇑! a (List.length G)) _
  | Θ, Ξ, cons (ce_def A M) G, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      let (m, Hm) := Evaluation.feval_exp_impl Θ Ξ M p _ in
      exist _ (p ↦ m) _
  | Θ, Ξ, cons (ce_mod U) G, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      exist _ (p ↦ᵐ dm_local p U nil) _.
  Next Obligation. (* nil *) exists nil; split; [ constructor | apply env_agree_nil ]. Qed.
  Next Obligation. (* initial_env_order G *) progressive_invert H; assumption. Defined.
  Next Obligation. (* the order of the type's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (feval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the extended environment *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha) end.
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ eassumption | repeat constructor; assumption | intros; exact I ].
  Qed.
  Next Obligation. (* initial_env_order G *) progressive_invert H; assumption. Defined.
  Next Obligation. (* the order of the definition's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (feval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the extended environment *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Hm) end.
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ eassumption | constructor; assumption | intros; exact I ].
  Qed.
  Next Obligation. (* initial_env_order G *) progressive_invert H; assumption. Defined.
  Next Obligation. (* the extended environment *)
    fnbe_obl.
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ eassumption | | intros; exact I ].
    constructor; constructor; [ apply agree_all; assumption | constructor ].
  Qed.
End InitialEnvImpl.

Section NbETyEnvDef.
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_env_impl Θ Ξ G (P : fenv Θ Ξ G) A (H : nbe_ty_order Θ Ξ G A) :
    { w | nbe_ty Θ Ξ G A w } :=
  | Θ, Ξ, G, exist _ p Hp, A, H =>
      let (a, Ha) := Evaluation.feval_exp_impl Θ Ξ A p _ in
      let (w, Hw) := Readback.fread_typ_impl Θ Ξ (List.length G) a _ in
      exist _ w _.
  Next Obligation. (* the order of the type's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (feval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of its fast readback *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0,
                    Hrd : forall p a, initial_env _ _ _ p -> _ -> read_typ_order _ _ _ a |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      destruct (read_typ_of_order _ _ _ _ (Hrd _ _ Hi Ha0)) as [W HW] end.
    eapply Readback.fread_typ_order_sound, fread_typ_sim; eassumption.
  Qed.
  Next Obligation. (* the normal form *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0,
                    Hrd : forall p a, initial_env _ _ _ p -> _ -> read_typ_order _ _ _ a |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      destruct (read_typ_of_order _ _ _ _ (Hrd _ _ Hi Ha0)) as [W HW] end.
    assert (w = W) as -> by (eapply functional_fread_typ; [ eassumption | eapply fread_typ_sim; eassumption ]).
    econstructor; eassumption.
  Qed.
End NbETyEnvDef.

(** From scratch, at the initial environment of the context. *)
Definition nbe_ty_impl Θ Ξ G A (H : nbe_ty_order Θ Ξ G A) : { w | nbe_ty Θ Ξ G A w } :=
  nbe_ty_env_impl Θ Ξ G (initial_env_impl Θ Ξ G (match H with nbe_ty_order_run _ _ _ _ HG _ _ => HG end)) A H.

Section NbEDef.
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_impl Θ Ξ G M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
  | Θ, Ξ, G, M, A, H with initial_env_impl Θ Ξ G _ => {
    | exist _ p Hp =>
        let (a, Ha) := Evaluation.feval_exp_impl Θ Ξ A p _ in
        let (m, Hm) := Evaluation.feval_exp_impl Θ Ξ M p _ in
        let (w, Hw) := Readback.fread_nf_impl Θ Ξ (List.length G) ⇓ a m _ in
        exist _ w _ }.
  Next Obligation. (* initial_env_order G *) destruct H; assumption. Defined.
  Next Obligation. (* the order of the type's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (feval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of the term's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [m Hm];
      eapply (feval_of_ref _ _ _ _ _ _ Hm); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of its fast readback *)
    fnbe_obl.
    match goal with Hi : initial_env _ _ _ ?p0,
                    HordA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p,
                    HordM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p,
                    Hrd : forall p a m, initial_env _ _ _ p -> _ -> _ -> read_nf_order _ _ _ _ |- _ =>
      destruct (eval_of_order _ _ _ _ (HordA _ Hi)) as [a0 Ha0];
      destruct (eval_of_order _ _ _ _ (HordM _ Hi)) as [m0 Hm0];
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Hm0 ltac:(apply agree_all; eassumption)) _ Hm);
      destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end.
    eapply Readback.fread_nf_order_sound, fread_nf_sim; [ eassumption | constructor; assumption ].
  Qed.
  Next Obligation. (* the normal form *)
    fnbe_obl.
    match goal with Hi : initial_env _ _ _ ?p0,
                    HordA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p,
                    HordM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p,
                    Hrd : forall p a m, initial_env _ _ _ p -> _ -> _ -> read_nf_order _ _ _ _ |- _ =>
      destruct (eval_of_order _ _ _ _ (HordA _ Hi)) as [a0 Ha0];
      destruct (eval_of_order _ _ _ _ (HordM _ Hi)) as [m0 Hm0];
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Hm0 ltac:(apply agree_all; eassumption)) _ Hm);
      destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end.
    assert (w = W) as -> by (eapply functional_fread_nf; [ eassumption | eapply fread_nf_sim; [ eassumption | constructor; assumption ] ]).
    econstructor; eassumption.
  Qed.
End NbEDef.
