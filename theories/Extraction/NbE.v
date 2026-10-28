(** * The Normalizer the Checker Runs

    The termination orders of normalization are those of the reference
    evaluation and readback ([Reference.Evaluation], [Reference.Readback]),
    which are the specification ([nbe], [nbe_ty]).  The normalizers compute
    by the evaluation that skips unread recursive results
    ([Extraction.FastEval]): its values are related to the reference ones
    ([Extraction.Simulation]), so they read back to the same normal forms,
    and the specifications are those of [Reference.NbE].

    An environment the normalizers start from is related to the initial
    environment of its context ([fast_env]); the checker computes it once per
    context ([initial_env_impl]) and extends it under binders. *)
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Reference Require Import Evaluation Readback.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Extraction Require Import FastEval FastDomain Simulation.
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

(** A fast environment related, entry by entry, to the initial environment
    of [G] ([fast_env_agree]). *)
Definition fast_env Θ Ξ G := { p' : fenv | exists p, initial_env Θ Ξ G p /\ fast_env_agree Θ Ξ (fun _ => True) p p' }.

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
    (** A fast result: its relation and its rightness *)
    | H : _ /\ _ |- _ => destruct H
    end;
  cbn [fdomain_erase fdomain_ne_erase fdomain_nf_erase] in *.

(** The reference evaluation of a term or a unit the order quantifies over,
    at the initial environment, and the fast one, at the related fast
    environment, related ([fast_eval_of_ref]) *)
#[local]
Ltac fnbe_ref_of M :=
  match goal with
  | Hord : forall p, initial_env _ _ _ p -> eval_exp_order _ _ M p, Hi : initial_env _ _ _ ?p0,
    Hag : fast_env_agree _ _ _ ?p0 _ |- _ =>
      let a0 := fresh "a0" in let Ha0 := fresh "Ha0" in
      destruct (eval_of_order _ _ _ _ (Hord _ Hi)) as [a0 Ha0];
      pose proof (fast_eval_of_ref _ _ _ _ _ _ Ha0 (fast_env_agree_all _ _ _ _ _ Hag))
  | Hord : forall p, initial_env _ _ _ p -> eval_modexp_order _ _ M p, Hi : initial_env _ _ _ ?p0,
    Hag : fast_env_agree _ _ _ ?p0 _ |- _ =>
      let h0 := fresh "h0" in let Hh0 := fresh "Hh0" in
      destruct (eval_modexp_of_order _ _ _ _ (Hord _ Hi)) as [h0 Hh0];
      pose proof (fast_eval_modexp_of_ref _ _ _ _ _ _ Hh0 (fast_env_agree_all _ _ _ _ _ Hag))
  end.

(** The fast results' relations to the reference ones *)
#[local]
Ltac fnbe_sims :=
  repeat match goal with
    | Hs : _ /\ (forall a', ⟦ ?M ⟧ᶠ _ ⍮ _ ⍮ _ ↘ a' -> _), Ha : ⟦ ?M ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
        pose proof (proj2 Hs _ Ha); clear Hs
    | Hs : _ /\ (forall h', ⟦ ?M ⟧ᵐᶠ _ ⍮ _ ⍮ _ ↘ h' -> _), Hh : ⟦ ?M ⟧ᵐᶠ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
        pose proof (proj2 Hs _ Hh); clear Hs
    end.

(** The obligations of the normalizers *)
#[local]
Ltac fnbe_solve :=
  intros; fnbe_obl;
  lazymatch goal with
  | |- initial_env_order _ _ _ => assumption
  | |- fenv_ok _ _ _ => eapply fast_env_agree_ok; eassumption
  | |- fdomain_ok _ _ _ => assumption
  | |- fdomain_nf_ok _ _ _ => constructor; assumption
  (** The order of a fast evaluation, from the reference one *)
  | |- Evaluation.fast_eval_exp_order _ _ ?M _ => fnbe_ref_of M; tauto
  | |- Evaluation.fast_eval_modexp_order _ _ ?M _ => fnbe_ref_of M; tauto
  (** The empty environment *)
  | |- exists p, initial_env _ _ nil p /\ _ =>
      exists nil; split; [ constructor | apply fast_env_agree_nil ]
  (** One entry more *)
  | |- exists p, initial_env _ _ (ce_ass ?A :: _) p /\ _ =>
      fnbe_ref_of A; fnbe_sims;
      eexists; split; [ econstructor; eassumption |];
      eapply fast_env_agree_term; [ eassumption | repeat constructor; assumption | repeat constructor; assumption ]
  | |- exists p, initial_env _ _ (ce_def _ ?M :: _) p /\ _ =>
      fnbe_ref_of M; fnbe_sims;
      eexists; split; [ econstructor; eassumption |];
      eapply fast_env_agree_term; eassumption
  | |- exists p, initial_env _ _ (ce_mod ?U :: _) p /\ _ =>
      fnbe_ref_of (me_lit U); fnbe_sims;
      eexists; split; [ econstructor; eassumption |];
      eapply fast_env_agree_mod; eassumption
  | |- exists p, initial_env _ _ (ce_dm _ ?M ?U :: _) p /\ _ =>
      fnbe_ref_of M; fnbe_ref_of (me_lit U); fnbe_sims;
      eexists; split; [ econstructor; eassumption |];
      eapply fast_env_agree_dm; eassumption
  (** The order of a fast readback, and the normal form, from the
      reference ones *)
  | |- Readback.fast_read_typ_order _ _ _ _ =>
      match goal with Hi : initial_env _ _ _ _, HA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ ?A p,
                      Hrd : forall p a, initial_env _ _ _ p -> _ -> read_typ_order _ _ _ a |- _ =>
        fnbe_ref_of A; fnbe_sims;
        match goal with Ha0 : ⟦ A ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => destruct (read_typ_of_order _ _ _ _ (Hrd _ _ Hi Ha0)) as [W HW] end
      end;
      eapply Readback.fast_read_typ_order_sound, fast_read_typ_sim; eassumption
  | |- nbe_ty _ _ _ _ ?w =>
      match goal with Hi : initial_env _ _ _ _, HA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ ?A p,
                      Hrd : forall p a, initial_env _ _ _ p -> _ -> read_typ_order _ _ _ a |- _ =>
        fnbe_ref_of A; fnbe_sims;
        match goal with Ha0 : ⟦ A ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => destruct (read_typ_of_order _ _ _ _ (Hrd _ _ Hi Ha0)) as [W HW] end
      end;
      match goal with Hw : Rtypᶠ _ in _ ⍮ _ ⍮ _ ↘ w, HW : Rtyp _ in _ ⍮ _ ⍮ _ ↘ ?W |- _ =>
        assert (w = W) as -> by (eapply functional_fast_read_typ; [ exact Hw | eapply fast_read_typ_sim; eassumption ]) end;
      econstructor; eassumption
  | |- Readback.fast_read_nf_order _ _ _ _ =>
      match goal with Hi : initial_env _ _ _ _,
                      HA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ ?A p,
                      HM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ ?M p,
                      Hrd : forall p a m, initial_env _ _ _ p -> ⟦ ?A ⟧ _ ⍮ _ ⍮ p ↘ a -> ⟦ ?M ⟧ _ ⍮ _ ⍮ p ↘ m -> _ |- _ =>
        fnbe_ref_of A; fnbe_ref_of M; fnbe_sims;
        match goal with Ha0 : ⟦ A ⟧ _ ⍮ _ ⍮ _ ↘ _, Hm0 : ⟦ M ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
          destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end
      end;
      eapply Readback.fast_read_nf_order_sound, fast_read_nf_sim; [ eassumption | constructor; assumption ]
  | |- nbe _ _ _ _ _ ?w =>
      match goal with Hi : initial_env _ _ _ _,
                      HA : forall p, initial_env _ _ _ p -> eval_exp_order _ _ ?A p,
                      HM : forall p, initial_env _ _ _ p -> eval_exp_order _ _ ?M p,
                      Hrd : forall p a m, initial_env _ _ _ p -> ⟦ ?A ⟧ _ ⍮ _ ⍮ p ↘ a -> ⟦ ?M ⟧ _ ⍮ _ ⍮ p ↘ m -> _ |- _ =>
        fnbe_ref_of A; fnbe_ref_of M; fnbe_sims;
        match goal with Ha0 : ⟦ A ⟧ _ ⍮ _ ⍮ _ ↘ _, Hm0 : ⟦ M ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
          destruct (read_nf_of_order _ _ _ _ (Hrd _ _ _ Hi Ha0 Hm0)) as [W HW] end
      end;
      match goal with Hw : Rnfᶠ _ in _ ⍮ _ ⍮ _ ↘ w, HW : Rnf _ in _ ⍮ _ ⍮ _ ↘ ?W |- _ =>
        assert (w = W) as -> by (eapply functional_fast_read_nf; [ exact Hw | eapply fast_read_nf_sim; [ eassumption | constructor; assumption ] ]) end;
      econstructor; eassumption
  end.

(** The operations on fast values, read through their erasure equations *)
#[local] Opaque fenv_var fenv_mod fextend_env fextend_env_mod fextend_env_dm fenv_args fdlvl_suc fdlvl_max
  fdlvl_lit fdm_clo fkinds_placeholders fkinds_body_entry fkinds_items_gen_env felim_grp_of carry.

Section InitialEnvImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl G (H : initial_env_order Θ Ξ G) : fast_env Θ Ξ G by struct H :=
  | nil, H => exist _ nil _
  | cons (ce_ass A) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ _ in
      exist _ (fextend_env p (fd_neut a (fd_var (List.length G)))) _
  | cons (ce_def A M) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ _ in
      exist _ (fextend_env p m) _
  | cons (ce_mod U) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (h, Hh) := Evaluation.fast_eval_modexp_impl F (me_lit U) p _ _ in
      exist _ (fextend_env_mod p h) _
  | cons (ce_dm A M U) G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ _ in
      let (h, Hh) := Evaluation.fast_eval_modexp_impl F (me_lit U) p _ _ in
      exist _ (fextend_env_dm p m h) _.
  Solve All Obligations with fnbe_solve.
End InitialEnvImpl.

Section NbETyEnvDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_env_impl G (P : fast_env Θ Ξ G) A (H : nbe_ty_order Θ Ξ G A) :
    { w | nbe_ty Θ Ξ G A w } :=
  | G, exist _ p Hp, A, H =>
      let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ _ in
      let (w, Hw) := Readback.fast_read_typ_impl F (List.length G) a _ _ in
      exist _ w _.
  Solve All Obligations with fnbe_solve.
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
        let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ _ in
        let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ _ in
        let (w, Hw) := Readback.fast_read_nf_impl F (List.length G) (fd_dom a m) _ _ in
        exist _ w _ }.
  Next Obligation. (* initial_env_order G *) destruct H; assumption. Defined.
  Solve All Obligations with fnbe_solve.
End NbEDef.

(** At an environment computed once for the context, as [nbe_ty_env_impl]. *)
Section NbEEnvDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** The normal form of a term at a type, from an environment related to
      the context's initial one. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_env_impl G (P : fast_env Θ Ξ G) M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
  | G, exist _ p Hp, M, A, H =>
      let (a, Ha) := Evaluation.fast_eval_exp_impl F A p _ _ in
      let (m, Hm) := Evaluation.fast_eval_exp_impl F M p _ _ in
      let (w, Hw) := Readback.fast_read_nf_impl F (List.length G) (fd_dom a m) _ _ in
      exist _ w _.
  Solve All Obligations with fnbe_solve.
End NbEEnvDef.
