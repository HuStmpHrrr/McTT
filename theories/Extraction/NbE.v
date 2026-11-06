(** * The Normalizer the Checker Runs

    Normalization ([nbe], [nbe_ty]) at its termination orders
    ([initial_env_order], [nbe_order], [nbe_ty_order]), which are stated
    over the evaluation and readback of [Core.Semantic] and follow from
    them ([nbe_order_sound] and the like).  The normalizers compute on fast
    values ([Extraction.Evaluation], [Extraction.Readback]): each fast
    result erases to the one the specification names.

    An environment the normalizers start from is a fast environment that
    erases to the initial environment of its context ([fast_env]); the
    checker computes it once per context ([initial_env_impl]) and extends it
    under binders ([fast_env_ass] and the like). *)
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Semantic Require Import Evaluation Readback.
From Mctt.Extraction Require Import FastDomain.
From Mctt.Extraction Require Evaluation Readback.
From Mctt.Extraction Require Import Evaluation Readback Lookup.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** ** The Orders *)

(** The order of the initial environment of a context: each entry's type
    and, as [initial_env] evaluates them, its body and unit *)
Inductive initial_env_order (Θ : gdeps) (Ξ : gstack) : ctx -> Prop :=
(** The empty context *)
| initial_env_order_nil : initial_env_order Θ Ξ nil
(** An assumption: its type *)
| initial_env_order_cons :
  `( initial_env_order Θ Ξ Γ ->
     (forall ρ, initial_env Θ Ξ Γ ρ -> eval_exp_order Θ Ξ A ρ) ->
     initial_env_order Θ Ξ (Γ ▹{κ} A))
(** A definition: its type, then its body at a type of a universe or of
    levels only *)
| initial_env_order_cons_def :
  `( initial_env_order Θ Ξ Γ ->
     (forall ρ, initial_env Θ Ξ Γ ρ -> eval_exp_order Θ Ξ A ρ) ->
     (forall ρ a, initial_env Θ Ξ Γ ρ -> ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> evaluated_kind (domain_kind a) ->
           eval_exp_order Θ Ξ M ρ) ->
     initial_env_order Θ Ξ (Γ ▸ A ≔ M))
(** A module: its unit *)
| initial_env_order_cons_mod :
  `( initial_env_order Θ Ξ Γ ->
     (forall ρ, initial_env Θ Ξ Γ ρ -> eval_modexp_order Θ Ξ (me_lit U) ρ) ->
     initial_env_order Θ Ξ (Γ ▹ₘ U))
(** A definition with a module part: its type, its term and its unit *)
| initial_env_order_cons_dm :
  `( initial_env_order Θ Ξ Γ ->
     (forall ρ, initial_env Θ Ξ Γ ρ -> eval_exp_order Θ Ξ A ρ) ->
     (forall ρ, initial_env Θ Ξ Γ ρ -> eval_exp_order Θ Ξ M ρ) ->
     (forall ρ, initial_env Θ Ξ Γ ρ -> eval_modexp_order Θ Ξ (me_lit U) ρ) ->
     initial_env_order Θ Ξ (Γ ▸ₘ A ≔ M ‖ U)).

#[local]
Hint Constructors initial_env_order : mctt.

Lemma initial_env_order_sound : forall Θ Ξ Γ ρ,
    initial_env Θ Ξ Γ ρ ->
    initial_env_order Θ Ξ Γ.
Proof.
  induction 1; econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear;
    eauto using eval_exp_order_sound, eval_modexp_order_sound;
    exfalso; eapply evaluated_kind_not_propositional; eassumption.
Qed.

#[local]
Hint Resolve initial_env_order_sound : mctt.

(** The order of NbE in [Θ ⍮ Ξ ⍮ Γ] ([nbe]): the term is evaluated and
    read back at a type of a universe or of levels, and kept as a proof,
    then read back, at a proposition ([nbe_term]). *)
Record nbe_order Θ Ξ G M A : Prop := nbe_order_run
  { (** The initial environment of the context *)
    nbe_order_init : initial_env_order Θ Ξ G
    (** The type *)
  ; nbe_order_typ : forall ρ, initial_env Θ Ξ G ρ -> eval_exp_order Θ Ξ A ρ
    (** The term, at a type of a universe or of levels *)
  ; nbe_order_exp : forall ρ a,
      initial_env Θ Ξ G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      evaluated_kind (domain_kind a) ->
      eval_exp_order Θ Ξ M ρ
    (** Its readback there *)
  ; nbe_order_read : forall ρ a m,
      initial_env Θ Ξ G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      evaluated_kind (domain_kind a) ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
      read_nf_order Θ Ξ (List.length G) ⇓ a m
    (** The readback of the kept proof, at a proposition *)
  ; nbe_order_read_proof : forall ρ a,
      initial_env Θ Ξ G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      domain_kind a = ak_propositional ->
      read_nf_order Θ Ξ (List.length G) ⇓ a ⋆ᵈ⟨M, ρ⟩ }.

#[local]
Hint Constructors nbe_order : mctt.

Lemma nbe_order_sound : forall Θ Ξ G M A w,
    nbe Θ Ξ G M A w ->
    nbe_order Θ Ξ G M A.
Proof.
  intros * [ρ a Hi Ha Hw]; destruct Hw as [w Hk Hr | m w Hk Hm Hr];
    econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear;
    eauto using initial_env_order_sound, eval_exp_order_sound, read_nf_order_sound;
    exfalso; eapply evaluated_kind_not_propositional; eassumption.
Qed.

#[local]
Hint Resolve nbe_order_sound : mctt.

(** The order of NbE of a type ([nbe_ty]) *)
Record nbe_ty_order Θ Ξ G A : Prop := nbe_ty_order_run
  { (** The initial environment of the context *)
    nbe_ty_order_init : initial_env_order Θ Ξ G
    (** The type *)
  ; nbe_ty_order_typ : forall ρ, initial_env Θ Ξ G ρ -> eval_exp_order Θ Ξ A ρ
    (** Its readback as a type *)
  ; nbe_ty_order_read : forall ρ a,
      initial_env Θ Ξ G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      read_typ_order Θ Ξ (List.length G) a }.

#[local]
Hint Constructors nbe_ty_order : mctt.

Lemma nbe_ty_order_sound : forall Θ Ξ G A w,
    nbe_ty Θ Ξ G A w ->
    nbe_ty_order Θ Ξ G A.
Proof.
  induction 1;
    econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear;
    eauto using initial_env_order_sound, eval_exp_order_sound, read_typ_order_sound.
Qed.

#[local]
Hint Resolve nbe_ty_order_sound : mctt.

(** ** The Fast Environments *)

(** A right fast environment that erases to the initial environment of
    [G] *)
Definition fast_env Θ Ξ G := { ρ : fenv | initial_env Θ Ξ G (fenv_erase ρ) /\ fenv_ok Θ Ξ ρ }.

Section FastEnv.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** The empty context's *)
  Lemma fast_env_nil : initial_env Θ Ξ nil (fenv_erase nil) /\ fenv_ok Θ Ξ nil.
  Proof. split; constructor. Qed.

  (** An assumption: a fresh variable of its type *)
  Lemma fast_env_ass : forall G κ A ρ a,
      initial_env Θ Ξ G (fenv_erase ρ) /\ fenv_ok Θ Ξ ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      initial_env Θ Ξ (G ▹{κ} A) (fenv_erase (fextend_env ρ (fd_neut a (fd_var (List.length G))) (fentry_type_value a))) /\
      fenv_ok Θ Ξ (fextend_env ρ (fd_neut a (fd_var (List.length G))) (fentry_type_value a)).
  Proof.
    intros * [Hi Hρ] [Ha Hok]; split; [ exact (initial_env_cons _ _ _ _ _ _ _ Hi Ha) |].
    repeat constructor; assumption.
  Qed.

  (** A definition at a type of a universe or of levels: its body's
      value *)
  Lemma fast_env_def : forall G A M ρ a m,
      initial_env Θ Ξ G (fenv_erase ρ) /\ fenv_ok Θ Ξ ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      evaluated_kind (fdomain_kind a) ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m /\ fdomain_ok Θ Ξ m ->
      initial_env Θ Ξ (G ▸ A ≔ M) (fenv_erase (fextend_env ρ m (fentry_type_value a))) /\
      fenv_ok Θ Ξ (fextend_env ρ m (fentry_type_value a)).
  Proof.
    intros * [Hi Hρ] [Ha Hok] Hk [Hm Hmok]; split; [| repeat constructor; assumption ].
    eapply initial_env_cons_def; [ exact Hi | exact Ha | rewrite fdomain_kind_erase; exact Hk | exact Hm ].
  Qed.

  (** A definition at a proposition: its body kept *)
  Lemma fast_env_def_proof : forall G A M ρ a,
      initial_env Θ Ξ G (fenv_erase ρ) /\ fenv_ok Θ Ξ ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      fdomain_kind a = ak_propositional ->
      initial_env Θ Ξ (G ▸ A ≔ M) (fenv_erase (fextend_env ρ (fd_proof M ρ) (fentry_type_value a))) /\
      fenv_ok Θ Ξ (fextend_env ρ (fd_proof M ρ) (fentry_type_value a)).
  Proof.
    intros * [Hi Hρ] [Ha Hok] Hk; split; [| repeat constructor; assumption ].
    eapply initial_env_cons_def_proof; [ exact Hi | exact Ha | rewrite fdomain_kind_erase; exact Hk ].
  Qed.

  (** A module: the value of its unit *)
  Lemma fast_env_mod : forall G U ρ h,
      initial_env Θ Ξ G (fenv_erase ρ) /\ fenv_ok Θ Ξ ρ ->
      ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h ->
      initial_env Θ Ξ (G ▹ₘ U) (fenv_erase (fextend_env_mod ρ h U)) /\ fenv_ok Θ Ξ (fextend_env_mod ρ h U).
  Proof.
    intros * [Hi Hρ] [Hh Hok]; split; [ exact (initial_env_cons_mod _ _ _ _ _ _ Hi Hh) | repeat constructor; assumption ].
  Qed.

  (** A definition with a module part: its term's value, at its type, and
      its unit's *)
  Lemma fast_env_dm : forall G A M U ρ a m h,
      initial_env Θ Ξ G (fenv_erase ρ) /\ fenv_ok Θ Ξ ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m /\ fdomain_ok Θ Ξ m ->
      ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h ->
      initial_env Θ Ξ (G ▸ₘ A ≔ M ‖ U) (fenv_erase (fextend_env_dm ρ m (fentry_type_value a) h U)) /\
      fenv_ok Θ Ξ (fextend_env_dm ρ m (fentry_type_value a) h U).
  Proof.
    intros * [Hi Hρ] [Ha Haok] [Hm Hmok] [Hh Hhok]; split; [| repeat constructor; assumption ].
    exact (initial_env_cons_dm _ _ _ _ _ _ _ _ _ _ Hi Ha Hm Hh).
  Qed.
End FastEnv.

(** ** The Fast Normalizers *)

(** A kind other than the propositions' is evaluated. *)
Lemma evaluated_kind_of_not_propositional : forall κ, κ <> ak_propositional -> evaluated_kind κ.
Proof. intros κ H; destruct (evaluated_kind_or_propositional κ); [ assumption | contradiction ]. Qed.

(** Split the orders, the fast environments and the fast results; a kind
    other than the propositions' is evaluated *)
#[local]
Ltac fast_nbe_obligation :=
  repeat match goal with
    | H : initial_env_order _ _ (_ :: _) |- _ => progressive_invert H
    | H : nbe_ty_order _ _ _ _ |- _ => destruct H
    | H : nbe_order _ _ _ _ _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : ?κ <> ak_propositional |- _ => apply evaluated_kind_of_not_propositional in H
    end;
  repeat match goal with
    | H : evaluated_kind (fdomain_kind ?a) |- _ =>
        assert_fails (idtac; match goal with _ : evaluated_kind (domain_kind (fdomain_erase a)) |- _ => idtac end);
        pose proof (eq_rect_r evaluated_kind H (fdomain_kind_erase a))
    | H : fdomain_kind ?a = ak_propositional |- _ =>
        assert_fails (idtac; match goal with _ : domain_kind (fdomain_erase a) = _ |- _ => idtac end);
        pose proof (fdomain_kind_erase_eq _ _ H)
    end.

(** The obligations of the normalizers *)
#[local]
Ltac fast_nbe_obligation_solve :=
  intros; cbv beta in *; fast_nbe_obligation;
  lazymatch goal with
  | |- initial_env_order _ _ _ => assumption
  | |- fenv_ok _ _ _ => assumption
  | |- fdomain_ok _ _ _ => assumption
  | |- fdomain_nf_ok _ _ _ => repeat constructor; assumption
  | |- eval_exp_order _ _ _ _ => eauto
  | |- eval_modexp_order _ _ _ _ => eauto
  | |- initial_env _ _ (ce_ass _ _ :: _) _ /\ _ => apply fast_env_ass; split; assumption
  | |- initial_env _ _ (ce_mod _ :: _) _ /\ _ => apply fast_env_mod; split; assumption
  | |- initial_env _ _ (ce_dm _ _ _ :: _) _ /\ _ => apply fast_env_dm; split; assumption
  | |- initial_env _ _ (ce_def _ _ :: _) _ /\ _ =>
      first [ apply fast_env_def_proof; [ split | split |]; assumption
            | apply fast_env_def; [ split | split | | split ]; assumption ]
  | |- read_typ_order _ _ _ _ => eauto
  | |- read_nf_order _ _ _ _ => cbn [fdomain_nf_erase fdomain_erase]; eauto
  | |- nbe_ty _ _ _ _ _ => econstructor; eassumption
  | |- nbe _ _ _ _ _ _ => econstructor; [ eassumption | eassumption |];
      first [ eapply nbe_term_proof; [ rewrite fdomain_kind_erase; assumption | eassumption ]
            | eapply nbe_term_evaluated; [ rewrite fdomain_kind_erase; assumption | eassumption | eassumption ] ]
  end.

Section InitialEnvImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** The fast initial environment of a context *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl G (H : initial_env_order Θ Ξ G) : fast_env Θ Ξ G by struct H :=
  | nil, H => exist _ nil (fast_env_nil Θ Ξ)
  | cons (ce_ass κ A) G, H =>
      let (ρ, Hρ) := initial_env_impl G _ in
      let (a, Ha) := fast_eval_exp_impl F A ρ _ _ in
      exist _ (fextend_env ρ (fd_neut a (fd_var (List.length G))) (fentry_type_value a)) _
  (** A definition, by the kind of its type *)
  | cons (ce_def A M) G, H with initial_env_impl G _ := {
    | exist _ ρ Hρ with fast_eval_exp_impl F A ρ _ _ := {
      | exist _ a Ha with abs_kind_eq_dec (fdomain_kind a) ak_propositional := {
        | left Hk => exist _ (fextend_env ρ (fd_proof M ρ) (fentry_type_value a)) _
        | right Hk =>
            let (m, Hm) := fast_eval_exp_impl F M ρ _ _ in
            exist _ (fextend_env ρ m (fentry_type_value a)) _ } } }
  | cons (ce_mod U) G, H =>
      let (ρ, Hρ) := initial_env_impl G _ in
      let (h, Hh) := fast_eval_modexp_impl F (me_lit U) ρ _ _ in
      exist _ (fextend_env_mod ρ h U) _
  | cons (ce_dm A M U) G, H =>
      let (ρ, Hρ) := initial_env_impl G _ in
      let (a, Ha) := fast_eval_exp_impl F A ρ _ _ in
      let (m, Hm) := fast_eval_exp_impl F M ρ _ _ in
      let (h, Hh) := fast_eval_modexp_impl F (me_lit U) ρ _ _ in
      exist _ (fextend_env_dm ρ m (fentry_type_value a) h U) _.
  Solve All Obligations with fast_nbe_obligation_solve.
End InitialEnvImpl.

Section NbETyEnvDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** The normal form of a type, from the fast initial environment of the
      context *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_env_impl G (P : fast_env Θ Ξ G) A (H : nbe_ty_order Θ Ξ G A) :
    { w | nbe_ty Θ Ξ G A w } :=
  | G, exist _ ρ Hρ, A, H =>
      let (a, Ha) := fast_eval_exp_impl F A ρ _ _ in
      let (w, Hw) := fast_read_typ_impl F (List.length G) a _ _ in
      exist _ w _.
  Solve All Obligations with fast_nbe_obligation_solve.
End NbETyEnvDef.

(** From scratch, at the initial environment of the context. *)
Definition nbe_ty_impl (F : FCtx) G A (H : nbe_ty_order (fc_deps F) (fc_stack F) G A) :
    { w | nbe_ty (fc_deps F) (fc_stack F) G A w } :=
  nbe_ty_env_impl F G (initial_env_impl F G (nbe_ty_order_init _ _ _ _ H)) A H.

(** At an environment computed once for the context, as [nbe_ty_env_impl]. *)
Section NbEEnvDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** The normal form of a term at a type, from the fast initial
      environment of the context: at a proposition, the term kept and read
      back; otherwise, its value read back *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations nbe_env_impl G (P : fast_env Θ Ξ G) M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
  | G, exist _ ρ Hρ, M, A, H with fast_eval_exp_impl F A ρ _ _ := {
    | exist _ a Ha with abs_kind_eq_dec (fdomain_kind a) ak_propositional := {
      | left Hk =>
          let (w, Hw) := fast_read_nf_impl F (List.length G) (fd_dom a (fd_proof M ρ)) _ _ in
          exist _ w _
      | right Hk =>
          let (m, Hm) := fast_eval_exp_impl F M ρ _ _ in
          let (w, Hw) := fast_read_nf_impl F (List.length G) (fd_dom a m) _ _ in
          exist _ w _ } }.
  Solve All Obligations with fast_nbe_obligation_solve.
End NbEEnvDef.

(** From scratch, at the initial environment of the context. *)
Definition nbe_impl (F : FCtx) G M A (H : nbe_order (fc_deps F) (fc_stack F) G M A) :
    { w | nbe (fc_deps F) (fc_stack F) G M A w } :=
  nbe_env_impl F G (initial_env_impl F G (nbe_order_init _ _ _ _ _ H)) M A H.
