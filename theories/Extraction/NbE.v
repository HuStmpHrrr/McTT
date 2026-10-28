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
From Mctt.Extraction Require Import Lookup.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

Inductive initial_env_order (Θ : gdeps) (Ξ : gstack) : ctx -> Prop :=
| initial_env_order_nil : initial_env_order Θ Ξ nil
| initial_env_order_cons :
  `( initial_env_order Θ Ξ Γ ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_exp_order Θ Ξ A p) ->
     initial_env_order Θ Ξ (Γ ▹ A))
| initial_env_order_cons_def :
  `( initial_env_order Θ Ξ Γ ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_exp_order Θ Ξ M p) ->
     initial_env_order Θ Ξ (Γ ▸ A ≔ M))
| initial_env_order_cons_mod :
  `( initial_env_order Θ Ξ Γ ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_modexp_order Θ Ξ (me_lit U) p) ->
     initial_env_order Θ Ξ (Γ ▹ₘ U))
(** A definition with a module part: its term and its unit *)
| initial_env_order_cons_dm :
  `( initial_env_order Θ Ξ Γ ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_exp_order Θ Ξ M p) ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_modexp_order Θ Ξ (me_lit U) p) ->
     initial_env_order Θ Ξ (Γ ▸ₘ A ≔ M ‖ U)).

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
Record nbe_order Θ Ξ G M A : Prop := nbe_order_run
  { nbe_order_init : initial_env_order Θ Ξ G
  ; nbe_order_typ : forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ A p
  ; nbe_order_exp : forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ M p
  ; nbe_order_read : forall p a m,
      initial_env Θ Ξ G p ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
      read_nf_order Θ Ξ (List.length G) ⇓ a m }.

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

Record nbe_ty_order Θ Ξ G A : Prop := nbe_ty_order_run
  { nbe_ty_order_init : initial_env_order Θ Ξ G
  ; nbe_ty_order_typ : forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ A p
  ; nbe_ty_order_read : forall p a,
      initial_env Θ Ξ G p ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
      read_typ_order Θ Ξ (List.length G) a }.

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
Definition fenv Θ Ξ G := { p' | exists p, initial_env Θ Ξ G p /\ env_agree Θ Ξ (fun _ => True) p p' }.

Section Orders.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** The fast evaluation terminates where the reference one does, from an
      environment that agrees where the term may read, at a related value. *)
  Lemma fast_eval_of_ref : forall M p p' a,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ a -> env_agree Θ Ξ (fun x => ~ exp_fresh x M) p p' ->
      Evaluation.fast_eval_exp_order Θ Ξ M p' /\ forall a', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ p' ↘ a' -> domain_simulation Θ Ξ a a'.
  Proof.
    intros * Ha Hp.
    destruct (fast_eval_exp_sim Θ Ξ _ _ _ Ha _ Hp) as (a'' & Ha'' & Hs).
    split; [ eapply Evaluation.fast_eval_exp_order_sound; eassumption |].
    intros a' Ha'; rewrite <- (functional_fast_eval_exp _ _ _ _ Ha'' Ha'); exact Hs.
  Qed.

  Lemma eval_of_order : forall M p, eval_exp_order Θ Ξ M p -> exists a, ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ a.
  Proof. intros * H; destruct (eval_exp_impl Θ Ξ M p H) as [a Ha]; eauto. Qed.

  (** Likewise for a module expression. *)
  Lemma fast_eval_modexp_of_ref : forall H p p' h,
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h -> env_agree Θ Ξ (fun x => ~ modexp_fresh x H) p p' ->
      Evaluation.fast_eval_modexp_order Θ Ξ H p' /\ forall h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ p' ↘ h' -> dmod_simulation Θ Ξ h h'.
  Proof.
    intros * Hh Hp.
    destruct (fast_eval_modexp_sim Θ Ξ _ _ _ Hh _ Hp) as (h'' & Hh'' & Hs).
    split; [ eapply Evaluation.fast_eval_modexp_order_sound; eassumption |].
    intros h' Hh'; rewrite <- (functional_fast_eval_modexp _ _ _ _ Hh'' Hh'); exact Hs.
  Qed.

  Lemma eval_modexp_of_order : forall H p, eval_modexp_order Θ Ξ H p -> exists h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ p ↘ h.
  Proof. intros * Ho; destruct (eval_modexp_impl Θ Ξ H p Ho) as [h Hh]; eauto. Qed.

  Lemma read_typ_of_order : forall s a, read_typ_order Θ Ξ s a -> exists W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros * H; destruct (read_typ_impl Θ Ξ s a H) as [W HW]; eauto. Qed.

  Lemma read_nf_of_order : forall s d, read_nf_order Θ Ξ s d -> exists W, Rnf d in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros * H; destruct (read_nf_impl Θ Ξ s d H) as [W HW]; eauto. Qed.

  Lemma agree_all : forall P p p', env_agree Θ Ξ (fun _ => True) p p' -> env_agree Θ Ξ P p p'.
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
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl G (H : initial_env_order Θ Ξ G) : fenv Θ Ξ G by struct H :=
  | nil, H => exist _ nil _
  | cons (ce_ass A) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ in
      exist _ (p ↦ ⇑! a (List.length G)) _
  | cons (ce_def A M) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ in
      exist _ (p ↦ m) _
  | cons (ce_mod U) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (h, Hh) := Evaluation.fast_eval_modexp_impl F (me_lit U) p _ in
      exist _ (p ↦ᵐ h) _
  | cons (ce_dm A M U) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ in
      let (h, Hh) := Evaluation.fast_eval_modexp_impl F (me_lit U) p _ in
      exist _ (p ↦ᵈ m ‖ h) _.
  Next Obligation. (* nil *) exists nil; split; [ constructor | apply env_agree_nil ]. Qed.
  Next Obligation. (* initial_env_order G *) progressive_invert H; assumption. Defined.
  Next Obligation. (* the order of the type's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the extended environment *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha) end.
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ eassumption | repeat constructor; assumption | intros; exact I ].
  Qed.
  Next Obligation. (* initial_env_order G *) progressive_invert H; assumption. Defined.
  Next Obligation. (* the order of the definition's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the extended environment *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Hm) end.
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ eassumption | constructor; assumption | intros; exact I ].
  Qed.
  Next Obligation. (* initial_env_order G *) progressive_invert H; assumption. Defined.
  Next Obligation. (* the order of the module's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_modexp_order _ _ (me_lit U) p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_modexp_of_order _ _ _ _ (Hord _ Hi)) as [h Hh];
      eapply (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the extended environment *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_modexp_order _ _ (me_lit U) p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_modexp_of_order _ _ _ _ (Hord _ Hi)) as [h0 Hh0];
      pose proof (proj2 (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh0 ltac:(apply agree_all; eassumption)) _ Hh) end.
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ eassumption | constructor; assumption | intros; exact I ].
  Qed.
  Next Obligation. (* initial_env_order G *) progressive_invert H; assumption. Defined.
  Next Obligation. (* the order of the term's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of the unit's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_modexp_order _ _ (me_lit U) p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_modexp_of_order _ _ _ _ (Hord _ Hi)) as [h Hh];
      eapply (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the extended environment *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Hm) end.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_modexp_order _ _ (me_lit U) p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_modexp_of_order _ _ _ _ (Hord _ Hi)) as [h0 Hh0];
      pose proof (proj2 (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh0 ltac:(apply agree_all; eassumption)) _ Hh) end.
    eexists; split; [ econstructor; eassumption |].
    eapply env_agree_cons; [ eassumption | constructor; assumption | intros; exact I ].
  Qed.
End InitialEnvImpl.

Section NbETyEnvDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_env_impl G (P : fenv Θ Ξ G) A (H : nbe_ty_order Θ Ξ G A) :
    { w | nbe_ty Θ Ξ G A w } :=
  | G, exist _ p Hp, A, H =>
      let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ in
      let (w, Hw) := Readback.fast_read_typ_impl F (List.length G) a _ in
      exist _ w _.
  Next Obligation. (* the order of the type's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of its fast readback *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0,
                    Hrd : forall p a, initial_env _ _ _ p -> _ -> read_typ_order _ _ _ a |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      destruct (read_typ_of_order _ _ _ _ (Hrd _ _ Hi Ha0)) as [W HW] end.
    eapply Readback.fast_read_typ_order_sound, fast_read_typ_sim; eassumption.
  Qed.
  Next Obligation. (* the normal form *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0,
                    Hrd : forall p a, initial_env _ _ _ p -> _ -> read_typ_order _ _ _ a |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      destruct (read_typ_of_order _ _ _ _ (Hrd _ _ Hi Ha0)) as [W HW] end.
    assert (w = W) as -> by (eapply functional_fast_read_typ; [ eassumption | eapply fast_read_typ_sim; eassumption ]).
    econstructor; eassumption.
  Qed.
End NbETyEnvDef.

(** From scratch, at the initial environment of the context. *)
Definition nbe_ty_impl (F : FCtx) G A (H : nbe_ty_order (fc_deps F) (fc_stack F) G A) :
    { w | nbe_ty (fc_deps F) (fc_stack F) G A w } :=
  nbe_ty_env_impl F G (initial_env_impl F G (match H with nbe_ty_order_run _ _ _ _ HG _ _ => HG end)) A H.

Section NbEDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_impl G M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
  | G, M, A, H with initial_env_impl F G _ => {
    | exist _ p Hp =>
        let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ in
        let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ in
        let (w, Hw) := Readback.fast_read_nf_impl F (List.length G) ⇓ a m _ in
        exist _ w _ }.
  Next Obligation. (* initial_env_order G *) destruct H; assumption. Defined.
  Next Obligation. (* the order of the type's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of the term's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [m Hm];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Hm); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of its fast readback *)
    fnbe_obl.
    match goal with Hi : initial_env _ _ _ ?p0,
                    HordA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p,
                    HordM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p,
                    Hrd : forall p a m, initial_env _ _ _ p -> _ -> _ -> read_nf_order _ _ _ _ |- _ =>
      destruct (eval_of_order _ _ _ _ (HordA _ Hi)) as [a0 Ha0];
      destruct (eval_of_order _ _ _ _ (HordM _ Hi)) as [m0 Hm0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hm0 ltac:(apply agree_all; eassumption)) _ Hm);
      destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end.
    eapply Readback.fast_read_nf_order_sound, fast_read_nf_sim; [ eassumption | constructor; assumption ].
  Qed.
  Next Obligation. (* the normal form *)
    fnbe_obl.
    match goal with Hi : initial_env _ _ _ ?p0,
                    HordA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p,
                    HordM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p,
                    Hrd : forall p a m, initial_env _ _ _ p -> _ -> _ -> read_nf_order _ _ _ _ |- _ =>
      destruct (eval_of_order _ _ _ _ (HordA _ Hi)) as [a0 Ha0];
      destruct (eval_of_order _ _ _ _ (HordM _ Hi)) as [m0 Hm0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hm0 ltac:(apply agree_all; eassumption)) _ Hm);
      destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end.
    assert (w = W) as -> by (eapply functional_fast_read_nf; [ eassumption | eapply fast_read_nf_sim; [ eassumption | constructor; assumption ] ]).
    econstructor; eassumption.
  Qed.
End NbEDef.

(** At an environment computed once for the context, as [nbe_ty_env_impl]. *)
Section NbEEnvDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** The normal form of a term at a type, from an environment related to
      the context's initial one. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_env_impl G (P : fenv Θ Ξ G) M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
  | G, exist _ p Hp, M, A, H =>
      let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ in
      let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ in
      let (w, Hw) := Readback.fast_read_nf_impl F (List.length G) ⇓ a m _ in
      exist _ w _.
  Next Obligation. (* the order of the type's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a Ha];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Ha); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of the term's fast evaluation *)
    fnbe_obl.
    match goal with Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0 |- _ =>
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [m Hm];
      eapply (fast_eval_of_ref _ _ _ _ _ _ Hm); apply agree_all; assumption end.
  Defined.
  Next Obligation. (* the order of its fast readback *)
    fnbe_obl.
    match goal with Hi : initial_env _ _ _ ?p0,
                    HordA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p,
                    HordM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p,
                    Hrd : forall p a m, initial_env _ _ _ p -> _ -> _ -> read_nf_order _ _ _ _ |- _ =>
      destruct (eval_of_order _ _ _ _ (HordA _ Hi)) as [a0 Ha0];
      destruct (eval_of_order _ _ _ _ (HordM _ Hi)) as [m0 Hm0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hm0 ltac:(apply agree_all; eassumption)) _ Hm);
      destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end.
    eapply Readback.fast_read_nf_order_sound, fast_read_nf_sim; [ eassumption | constructor; assumption ].
  Qed.
  Next Obligation. (* the normal form *)
    fnbe_obl.
    match goal with Hi : initial_env _ _ _ ?p0,
                    HordA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ A p,
                    HordM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p,
                    Hrd : forall p a m, initial_env _ _ _ p -> _ -> _ -> read_nf_order _ _ _ _ |- _ =>
      destruct (eval_of_order _ _ _ _ (HordA _ Hi)) as [a0 Ha0];
      destruct (eval_of_order _ _ _ _ (HordM _ Hi)) as [m0 Hm0];
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha0 ltac:(apply agree_all; eassumption)) _ Ha);
      pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hm0 ltac:(apply agree_all; eassumption)) _ Hm);
      destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end.
    assert (w = W) as -> by (eapply functional_fast_read_nf; [ eassumption | eapply fast_read_nf_sim; [ eassumption | constructor; assumption ] ]).
    econstructor; eassumption.
  Qed.
End NbEEnvDef.
