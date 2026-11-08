(** * The Normalizer the Checker Runs

    Normalization ([nbe], [nbe_ty]) of a term or type that has a normal
    form ([nbe_order], [nbe_ty_order], [initial_env_order]: the normal form
    of [Core.Semantic.NbE] exists).  The normalizers compute on fast values
    ([Extraction.Evaluation], [Extraction.Readback]) with the skip on
    ([skip_on_mode]): the recursive results no branch reads are not
    computed, and a kept proof reads back as its term.  The fast normal
    form is the reference one up to proofs ([Extraction.Simulation]); when
    it has no proof in it, it is the reference one
    ([nf_ne_proof_free_eq]).  Otherwise the normalizers compute again with
    the skip off, from the context's initial environment computed with the
    skip off too, and get the reference normal form exactly
    ([Extraction.FastEquiv]).

    An environment the normalizers start from is a fast environment that
    simulates the initial environment of its context ([fast_env]); the
    checker computes it once per context ([initial_env_impl]) and extends it
    under binders ([fast_env_ass] and the like). *)
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Semantic Require Import Evaluation Readback.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Syntactic.Levels Require Import Levels.
From Mctt.Extraction Require Import FastEval FastRead FastEquiv FastDomain Simulation.
From Mctt.Extraction Require Evaluation Readback.
From Mctt.Extraction Require Import Evaluation Readback Lookup.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** The normalizers run with the skip on; the skip off is named where it
    is used. *)
#[local] Existing Instance skip_on_mode.

(** ** The Orders

    A normalizer is called where the reference normal form exists: its
    termination follows from the existence of the reference derivations,
    which the fast ones simulate. *)

(** The initial environment of a context exists. *)
Definition initial_env_order (Θ : gdeps) (Ξ : gstack) (G : ctx) : Prop := exists ρ, initial_env Θ Ξ G ρ.

Lemma initial_env_order_sound : forall Θ Ξ G ρ, initial_env Θ Ξ G ρ -> initial_env_order Θ Ξ G.
Proof. intros * H; exists ρ; exact H. Qed.

(** The normal form of a term at a type exists. *)
Definition nbe_order (Θ : gdeps) (Ξ : gstack) (G : ctx) (M A : exp) : Prop := exists w, nbe Θ Ξ G M A w.

Lemma nbe_order_sound : forall Θ Ξ G M A w, nbe Θ Ξ G M A w -> nbe_order Θ Ξ G M A.
Proof. intros * H; exists w; exact H. Qed.

Lemma nbe_order_init : forall Θ Ξ G M A, nbe_order Θ Ξ G M A -> initial_env_order Θ Ξ G.
Proof. intros * [w [ρ a Hi _ _]]; exists ρ; exact Hi. Qed.

(** The normal form of a type exists. *)
Definition nbe_ty_order (Θ : gdeps) (Ξ : gstack) (G : ctx) (A : exp) : Prop := exists w, nbe_ty Θ Ξ G A w.

Lemma nbe_ty_order_sound : forall Θ Ξ G A w, nbe_ty Θ Ξ G A w -> nbe_ty_order Θ Ξ G A.
Proof. intros * H; exists w; exact H. Qed.

Lemma nbe_ty_order_init : forall Θ Ξ G A, nbe_ty_order Θ Ξ G A -> initial_env_order Θ Ξ G.
Proof. intros * [w [ρ a Hi _ _]]; exists ρ; exact Hi. Qed.

Lemma initial_env_order_tail : forall Θ Ξ e G, initial_env_order Θ Ξ (e :: G) -> initial_env_order Θ Ξ G.
Proof. intros * [ρ H]; inversion H; subst; eexists; eassumption. Qed.

(** A kind other than the propositions' is evaluated. *)
Lemma evaluated_kind_of_not_propositional : forall κ, κ <> ak_propositional -> evaluated_kind κ.
Proof. intros κ H; destruct (evaluated_kind_or_propositional κ); [ assumption | contradiction ]. Qed.

(** ** The Fast Environments, with the Skip On *)

Section FastEnv.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A fast environment simulates the initial environment of [G]. *)
  Definition fast_env_simulates (G : ctx) (ρ : fenv) : Prop :=
    exists ρc, initial_env Θ Ξ G ρc /\ fast_env_agree Θ Ξ (fun _ => True) ρc ρ.

  Lemma fast_env_simulates_ok : forall G ρ, fast_env_simulates G ρ -> fenv_ok Θ Ξ ρ.
  Proof. intros * (ρc & _ & _ & H); exact H. Qed.

  (** The empty context's *)
  Lemma fast_env_simulates_nil : fast_env_simulates nil nil.
  Proof. exists nil; split; [ constructor | apply fast_env_agree_nil ]. Qed.

  (** A term evaluated in a reference environment evaluates, fast, in a
      simulating one, to a related value. *)
  Lemma fast_eval_of_core : forall M ρc ρ a, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρc ↘ a -> fast_env_agree Θ Ξ (fun _ => True) ρc ρ ->
      exists a', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ a' /\ domain_simulation Θ Ξ a a'.
  Proof. intros * Ha Hag; exact (fast_eval_exp_sim Θ Ξ _ _ _ Ha _ (fast_env_agree_all Θ Ξ _ _ _ Hag)). Qed.

  Lemma fast_eval_value_of_core : forall M ρc ρ a d, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρc ↘ a -> fast_env_agree Θ Ξ (fun _ => True) ρc ρ ->
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase d -> domain_simulation Θ Ξ a (fdomain_erase d).
  Proof.
    intros * Ha Hag Hd; destruct (fast_eval_of_core _ _ _ _ Ha Hag) as (a' & Ha' & Hs).
    rewrite (functional_fast_eval_exp _ _ _ _ Hd Ha'); exact Hs.
  Qed.

  Lemma fast_eval_order_of_core : forall M ρc ρ a, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρc ↘ a -> fast_env_agree Θ Ξ (fun _ => True) ρc ρ ->
      fast_eval_exp_order Θ Ξ M (fenv_erase ρ).
  Proof. intros * Ha Hag; destruct (fast_eval_of_core _ _ _ _ Ha Hag) as (a' & Ha' & _); exact (fast_eval_exp_order_sound Θ Ξ _ _ _ Ha'). Qed.

  Lemma fast_eval_modexp_of_core : forall H ρc ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρc ↘ h -> fast_env_agree Θ Ξ (fun _ => True) ρc ρ ->
      exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ h' /\ dmod_simulation Θ Ξ h h'.
  Proof. intros * Hh Hag; exact (fast_eval_modexp_sim Θ Ξ _ _ _ Hh _ (fast_env_agree_all Θ Ξ _ _ _ Hag)). Qed.

  Lemma fast_eval_modexp_value_of_core : forall H ρc ρ h d, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρc ↘ h -> fast_env_agree Θ Ξ (fun _ => True) ρc ρ ->
      ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdmod_erase d -> dmod_simulation Θ Ξ h (fdmod_erase d).
  Proof.
    intros * Hh Hag Hd; destruct (fast_eval_modexp_of_core _ _ _ _ Hh Hag) as (h' & Hh' & Hs).
    rewrite (functional_fast_eval_modexp _ _ _ _ Hd Hh'); exact Hs.
  Qed.

  Lemma fast_eval_modexp_order_of_core : forall H ρc ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρc ↘ h -> fast_env_agree Θ Ξ (fun _ => True) ρc ρ ->
      fast_eval_modexp_order Θ Ξ H (fenv_erase ρ).
  Proof.
    intros * Hh Hag; destruct (fast_eval_modexp_of_core _ _ _ _ Hh Hag) as (h' & Hh' & _).
    exact (fast_eval_modexp_order_sound Θ Ξ _ _ _ Hh').
  Qed.

  (** Related types are of one kind. *)
  Lemma fast_kind_of_core : forall a d, domain_simulation Θ Ξ a (fdomain_erase d) -> domain_kind a = fdomain_kind d.
  Proof. intros * H; rewrite (domain_kind_sim Θ Ξ _ _ H), fdomain_kind_erase; reflexivity. Qed.

  (** The context's entry and the reference environment under it *)
  #[local]
  Ltac entry_inv :=
    match goal with
    | Ho : initial_env_order _ _ (_ :: _) |- _ =>
        let ρ1 := fresh "ρ1" in let H1 := fresh "H1" in destruct Ho as [ρ1 H1]; inversion H1; subst; clear H1
    end;
    match goal with
    | Hs : fast_env_simulates _ _ |- _ =>
        let ρc := fresh "ρc" in let Hi := fresh "Hi" in let Hag := fresh "Hag" in destruct Hs as (ρc & Hi & Hag)
    end;
    functional_initial_env_rewrite_clear.

  (** An assumption: a fresh variable of its type *)
  Lemma fast_env_ass_order : forall G κ A ρ, initial_env_order Θ Ξ (G ▹{κ} A) -> fast_env_simulates G ρ ->
      fast_eval_exp_order Θ Ξ A (fenv_erase ρ).
  Proof. intros * Ho Hs; entry_inv; eapply fast_eval_order_of_core; eassumption. Qed.

  Lemma fast_env_ass : forall G κ A ρ a, initial_env_order Θ Ξ (G ▹{κ} A) -> fast_env_simulates G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      fast_env_simulates (G ▹{κ} A) (fextend_env ρ (fd_neut a (fd_var (List.length G))) (fentry_type_value a)).
  Proof.
    intros * Ho Hs [Ha Hok]; entry_inv.
    match goal with He : ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρc ↘ ?ac |- _ =>
      exists (ρc ↦ ⇑! ac (List.length G) ⦂ entry_type_value ac); split; [ constructor; assumption |];
      apply fast_env_agree_term;
        [ exact Hag
        | cbn [fdomain_erase fdomain_ne_erase]; constructor; [ eapply fast_eval_value_of_core; eassumption | constructor ]
        | repeat constructor; assumption
        | constructor; assumption ] end.
  Qed.

  (** A definition: its type, then its body, kept at a proposition *)
  Lemma fast_env_def_typ_order : forall G A M ρ, initial_env_order Θ Ξ (G ▸ A ≔ M) -> fast_env_simulates G ρ ->
      fast_eval_exp_order Θ Ξ A (fenv_erase ρ).
  Proof. intros * Ho Hs; entry_inv; eapply fast_eval_order_of_core; eassumption. Qed.

  Lemma fast_env_def_order : forall G A M ρ a, initial_env_order Θ Ξ (G ▸ A ≔ M) -> fast_env_simulates G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a -> fdomain_kind a <> ak_propositional ->
      fast_eval_exp_order Θ Ξ M (fenv_erase ρ).
  Proof.
    intros * Ho Hs Ha Hk; entry_inv; [ eapply fast_eval_order_of_core; eassumption |].
    exfalso; apply Hk; rewrite <- (fast_kind_of_core _ _ ltac:(eapply fast_eval_value_of_core; eassumption)); assumption.
  Qed.

  Lemma fast_env_def : forall G A M ρ a m, initial_env_order Θ Ξ (G ▸ A ≔ M) -> fast_env_simulates G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a -> fdomain_kind a <> ak_propositional ->
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m /\ fdomain_ok Θ Ξ m ->
      fast_env_simulates (G ▸ A ≔ M) (fextend_env ρ m (fentry_type_value a)).
  Proof.
    intros * Ho Hs [Ha Haok] Hk [Hm Hmok]; entry_inv.
    - match goal with He : ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρc ↘ ?mc, Hea : ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρc ↘ ?ac |- _ =>
        exists (ρc ↦ mc ⦂ entry_type_value ac); split; [ econstructor; eassumption |];
        apply fast_env_agree_term;
          [ exact Hag | eapply fast_eval_value_of_core; eassumption | assumption | constructor; assumption ] end.
    - exfalso; apply Hk; rewrite <- (fast_kind_of_core _ _ ltac:(eapply fast_eval_value_of_core; eassumption)); assumption.
  Qed.

  Lemma fast_env_def_proof : forall G A M ρ a, initial_env_order Θ Ξ (G ▸ A ≔ M) -> fast_env_simulates G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a -> fdomain_kind a = ak_propositional ->
      fast_env_simulates (G ▸ A ≔ M) (fextend_env ρ (fd_proof M ρ) (fentry_type_value a)).
  Proof.
    intros * Ho Hs [Ha Haok] Hk; entry_inv.
    - match goal with He : ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρc ↘ ?ac, Hev : evaluated_kind (domain_kind ?ac) |- _ =>
        exfalso; eapply evaluated_kind_not_propositional; [ exact Hev |];
        rewrite (fast_kind_of_core _ _ (fast_eval_value_of_core _ _ _ _ _ He Hag Ha)); exact Hk end.
    - match goal with Hea : ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρc ↘ ?ac |- _ =>
        exists (ρc ↦ ⋆ᵈ⟨M, ρc⟩ ⦂ entry_type_value ac); split; [ econstructor; eassumption |];
        apply fast_env_agree_term;
          [ exact Hag | cbn [fdomain_erase]; constructor | constructor; exact (proj2 Hag) | constructor; assumption ] end.
  Qed.

  (** A module: its unit's closure *)
  Lemma fast_env_mod_order : forall G U ρ, initial_env_order Θ Ξ (G ▹ₘ U) -> fast_env_simulates G ρ ->
      fast_eval_modexp_order Θ Ξ (me_lit U) (fenv_erase ρ).
  Proof. intros * Ho Hs; entry_inv; eapply fast_eval_modexp_order_of_core; eassumption. Qed.

  Lemma fast_env_mod : forall G U ρ h, initial_env_order Θ Ξ (G ▹ₘ U) -> fast_env_simulates G ρ ->
      ⟦ me_lit U ⟧ᵐᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h ->
      fast_env_simulates (G ▹ₘ U) (fextend_env_mod ρ h U).
  Proof.
    intros * Ho Hs [Hh Hok]; entry_inv.
    match goal with He : ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ ρc ↘ ?hc |- _ =>
      exists (ρc ↦ᵐ hc ⦂ U); split; [ econstructor; eassumption |];
      apply fast_env_agree_mod; [ exact Hag | eapply fast_eval_modexp_value_of_core; eassumption | assumption ] end.
  Qed.

  (** A definition with a module part: its type, its term and its unit *)
  Lemma fast_env_dm_order : forall G A M U ρ, initial_env_order Θ Ξ (G ▸ₘ A ≔ M ‖ U) -> fast_env_simulates G ρ ->
      fast_eval_exp_order Θ Ξ A (fenv_erase ρ) /\ fast_eval_exp_order Θ Ξ M (fenv_erase ρ) /\
      fast_eval_modexp_order Θ Ξ (me_lit U) (fenv_erase ρ).
  Proof.
    intros * Ho Hs; entry_inv; split; [| split ];
      solve [ eapply fast_eval_order_of_core; eassumption | eapply fast_eval_modexp_order_of_core; eassumption ].
  Qed.

  Lemma fast_env_dm : forall G A M U ρ a m h, initial_env_order Θ Ξ (G ▸ₘ A ≔ M ‖ U) -> fast_env_simulates G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m /\ fdomain_ok Θ Ξ m ->
      ⟦ me_lit U ⟧ᵐᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h ->
      fast_env_simulates (G ▸ₘ A ≔ M ‖ U) (fextend_env_dm ρ m (fentry_type_value a) h U).
  Proof.
    intros * Ho Hs [Ha Haok] [Hm Hmok] [Hh Hhok]; entry_inv.
    match goal with
    | Hea : ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρc ↘ ?ac, Hem : ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρc ↘ ?mc, Heh : ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ ρc ↘ ?hc |- _ =>
        exists (ρc ↦ᵈ mc ⦂ entry_type_value ac ‖ hc ⦂ U); split; [ econstructor; eassumption |];
        apply fast_env_agree_dm;
          [ exact Hag | eapply fast_eval_value_of_core; eassumption | assumption | constructor; assumption
          | eapply fast_eval_modexp_value_of_core; eassumption | assumption ]
    end.
  Qed.
End FastEnv.

(** A fast environment that simulates the initial environment of [G] *)
Definition fast_env Θ Ξ G := { ρ : fenv | fast_env_simulates Θ Ξ G ρ }.

(** ** The Exact Environments, with the Skip Off

    The fallback's: a fast environment that erases to the initial
    environment of [G], computed with the skip off, at which fast
    evaluation and readback are the reference ones. *)

Section ExactEnv.
  Variables (Θ : gdeps) (Ξ : gstack).

  Definition exact_env_spec (G : ctx) (ρ : fenv) : Prop := initial_env Θ Ξ G (fenv_erase ρ) /\ fenv_ok Θ Ξ ρ.

  Lemma exact_env_nil : exact_env_spec nil nil.
  Proof. split; constructor. Qed.

  (** With the skip off, fast evaluation is the reference one. *)
  Lemma exact_eval : forall M ρ a, @fast_eval_exp skip_off_mode Θ Ξ M ρ a -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a.
  Proof. exact (proj1 (fast_to_core_eval Θ Ξ)). Qed.

  Lemma exact_eval_modexp : forall H ρ h, @fast_eval_modexp skip_off_mode Θ Ξ H ρ h -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (fast_to_core_eval Θ Ξ)))))). Qed.

  Lemma exact_eval_spec : forall M ρ d, @fast_eval_exp skip_off_mode Θ Ξ M ρ (fdomain_erase d) /\ fdomain_ok Θ Ξ d ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ fdomain_erase d /\ fdomain_ok Θ Ξ d.
  Proof. intros * [H Hok]; split; [ apply exact_eval, H | exact Hok ]. Qed.

  Lemma exact_eval_modexp_spec : forall H ρ d, @fast_eval_modexp skip_off_mode Θ Ξ H ρ (fdmod_erase d) /\ fdmod_ok Θ Ξ d ->
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ fdmod_erase d /\ fdmod_ok Θ Ξ d.
  Proof. intros * [Hh Hok]; split; [ apply exact_eval_modexp, Hh | exact Hok ]. Qed.

  Lemma exact_eval_order : forall M ρ a, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> @fast_eval_exp_order skip_off_mode Θ Ξ M ρ.
  Proof. intros * H; exact (fast_eval_exp_order_sound Θ Ξ _ _ _ (proj1 (core_to_fast_eval Θ Ξ) _ _ _ H)). Qed.

  Lemma exact_eval_modexp_order : forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> @fast_eval_modexp_order skip_off_mode Θ Ξ H ρ.
  Proof.
    intros * Hh; exact (fast_eval_modexp_order_sound Θ Ξ _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (core_to_fast_eval Θ Ξ))))) _ _ _ Hh)).
  Qed.

  Lemma exact_read_typ : forall s a A, @fast_read_typ skip_off_mode Θ Ξ s a A -> Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A.
  Proof. exact (proj1 (proj2 (proj2 (fast_to_core_read Θ Ξ)))). Qed.

  Lemma exact_read_nf : forall s n W, @fast_read_nf skip_off_mode Θ Ξ s n W -> Rnf n in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. exact (proj1 (fast_to_core_read Θ Ξ)). Qed.

  Lemma exact_read_typ_order : forall s a A, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A -> @fast_read_typ_order skip_off_mode Θ Ξ s a.
  Proof. intros * H; exact (fast_read_typ_order_sound Θ Ξ _ _ _ (proj1 (proj2 (proj2 (core_to_fast_read Θ Ξ))) _ _ _ H)). Qed.

  Lemma exact_read_nf_order : forall s n W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> @fast_read_nf_order skip_off_mode Θ Ξ s n.
  Proof. intros * H; exact (fast_read_nf_order_sound Θ Ξ _ _ _ (proj1 (core_to_fast_read Θ Ξ) _ _ _ H)). Qed.

  (** The reference environment under the context's entry *)
  #[local]
  Ltac exact_entry_inv :=
    match goal with
    | Ho : initial_env_order _ _ (_ :: _) |- _ =>
        let ρ1 := fresh "ρ1" in let H1 := fresh "H1" in destruct Ho as [ρ1 H1]; inversion H1; subst; clear H1
    end;
    match goal with Hs : exact_env_spec _ _ |- _ => let Hi := fresh "Hi" in let Hok := fresh "Hok" in destruct Hs as [Hi Hok] end;
    functional_initial_env_rewrite_clear.

  (** The orders of the entries' evaluations *)
  Lemma exact_env_ass_order : forall G κ A ρ, initial_env_order Θ Ξ (G ▹{κ} A) -> exact_env_spec G ρ ->
      @fast_eval_exp_order skip_off_mode Θ Ξ A (fenv_erase ρ).
  Proof. intros * Ho Hs; exact_entry_inv; eapply exact_eval_order; eassumption. Qed.

  Lemma exact_env_def_typ_order : forall G A M ρ, initial_env_order Θ Ξ (G ▸ A ≔ M) -> exact_env_spec G ρ ->
      @fast_eval_exp_order skip_off_mode Θ Ξ A (fenv_erase ρ).
  Proof. intros * Ho Hs; exact_entry_inv; eapply exact_eval_order; eassumption. Qed.

  Lemma exact_env_def_order : forall G A M ρ a, initial_env_order Θ Ξ (G ▸ A ≔ M) -> exact_env_spec G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a -> fdomain_kind a <> ak_propositional ->
      @fast_eval_exp_order skip_off_mode Θ Ξ M (fenv_erase ρ).
  Proof.
    intros * Ho Hs Ha Hk; exact_entry_inv; functional_eval_rewrite_clear; [ eapply exact_eval_order; eassumption |].
    exfalso; apply Hk; rewrite <- fdomain_kind_erase; assumption.
  Qed.

  Lemma exact_env_mod_order : forall G U ρ, initial_env_order Θ Ξ (G ▹ₘ U) -> exact_env_spec G ρ ->
      @fast_eval_modexp_order skip_off_mode Θ Ξ (me_lit U) (fenv_erase ρ).
  Proof. intros * Ho Hs; exact_entry_inv; eapply exact_eval_modexp_order; eassumption. Qed.

  Lemma exact_env_dm_order : forall G A M U ρ, initial_env_order Θ Ξ (G ▸ₘ A ≔ M ‖ U) -> exact_env_spec G ρ ->
      @fast_eval_exp_order skip_off_mode Θ Ξ A (fenv_erase ρ) /\ @fast_eval_exp_order skip_off_mode Θ Ξ M (fenv_erase ρ) /\
      @fast_eval_modexp_order skip_off_mode Θ Ξ (me_lit U) (fenv_erase ρ).
  Proof.
    intros * Ho Hs; exact_entry_inv; split; [| split ];
      solve [ eapply exact_eval_order; eassumption | eapply exact_eval_modexp_order; eassumption ].
  Qed.

  (** The environments extended by the entries' values *)
  Lemma exact_env_ass : forall G κ A ρ a, exact_env_spec G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      exact_env_spec (G ▹{κ} A) (fextend_env ρ (fd_neut a (fd_var (List.length G))) (fentry_type_value a)).
  Proof.
    intros * [Hi Hρ] [Ha Hok]; split; [ exact (initial_env_cons _ _ _ _ _ _ _ Hi Ha) |].
    repeat constructor; assumption.
  Qed.

  Lemma exact_env_def : forall G A M ρ a m, exact_env_spec G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a -> fdomain_kind a <> ak_propositional ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m /\ fdomain_ok Θ Ξ m ->
      exact_env_spec (G ▸ A ≔ M) (fextend_env ρ m (fentry_type_value a)).
  Proof.
    intros * [Hi Hρ] [Ha Hok] Hk [Hm Hmok]; split; [| repeat constructor; assumption ].
    eapply initial_env_cons_def; [ exact Hi | exact Ha | | exact Hm ].
    rewrite fdomain_kind_erase; apply evaluated_kind_of_not_propositional; exact Hk.
  Qed.

  Lemma exact_env_def_proof : forall G A M ρ a, exact_env_spec G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a -> fdomain_kind a = ak_propositional ->
      exact_env_spec (G ▸ A ≔ M) (fextend_env ρ (fd_proof M ρ) (fentry_type_value a)).
  Proof.
    intros * [Hi Hρ] [Ha Hok] Hk; split; [| repeat constructor; assumption ].
    eapply initial_env_cons_def_proof; [ exact Hi | exact Ha | rewrite fdomain_kind_erase; exact Hk ].
  Qed.

  Lemma exact_env_mod : forall G U ρ h, exact_env_spec G ρ ->
      ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h ->
      exact_env_spec (G ▹ₘ U) (fextend_env_mod ρ h U).
  Proof.
    intros * [Hi Hρ] [Hh Hok]; split; [ exact (initial_env_cons_mod _ _ _ _ _ _ Hi Hh) | repeat constructor; assumption ].
  Qed.

  Lemma exact_env_dm : forall G A M U ρ a m h, exact_env_spec G ρ ->
      ⟦ A ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a /\ fdomain_ok Θ Ξ a ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m /\ fdomain_ok Θ Ξ m ->
      ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdmod_erase h /\ fdmod_ok Θ Ξ h ->
      exact_env_spec (G ▸ₘ A ≔ M ‖ U) (fextend_env_dm ρ m (fentry_type_value a) h U).
  Proof.
    intros * [Hi Hρ] [Ha Haok] [Hm Hmok] [Hh Hhok]; split; [| repeat constructor; assumption ].
    exact (initial_env_cons_dm _ _ _ _ _ _ _ _ _ _ Hi Ha Hm Hh).
  Qed.
End ExactEnv.

(** ** The Normal Forms, from Fast Ones

    With the skip on, a fast normal form computed in a simulating
    environment is the reference one up to proofs; free of proofs, it is
    the reference one. *)

Section FromFast.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma eq_of_upto_proof_free : forall W W', nf_eq_upto_proofs W W' -> nf_proof_freeb W' = true -> W = W'.
  Proof.
    intros * Hup Hpf; symmetry; apply (proj1 nf_ne_proof_free_eq); [ apply (proj1 nf_proof_freeb_iff), Hpf |].
    symmetry; exact Hup.
  Qed.

  (** The reference evaluation of a type, at the reference environment
      [fast_env_simulates] names *)
  #[local]
  Ltac core_env :=
    match goal with
    | Hs : fast_env_simulates _ _ _ _ |- _ =>
        let ρc := fresh "ρc" in let Hic := fresh "Hic" in let Hag := fresh "Hag" in destruct Hs as (ρc & Hic & Hag)
    end;
    functional_initial_env_rewrite_clear.

  Lemma nbe_ty_eval_order : forall G A ρ, nbe_ty_order Θ Ξ G A -> fast_env_simulates Θ Ξ G ρ ->
      fast_eval_exp_order Θ Ξ A (fenv_erase ρ).
  Proof. intros * [w [ρ0 m Hi He Hr]] Hs; core_env; eapply fast_eval_order_of_core; eassumption. Qed.

  Lemma nbe_ty_read_order : forall G A ρ a, nbe_ty_order Θ Ξ G A -> fast_env_simulates Θ Ξ G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a -> fast_read_typ_order Θ Ξ (List.length G) (fdomain_erase a).
  Proof.
    intros * [w [ρ0 m Hi He Hr]] Hs Ha; core_env.
    destruct (fast_read_typ_simulation Θ Ξ _ _ _ _ Hr (fast_eval_value_of_core Θ Ξ _ _ _ _ _ He Hag Ha)) as (W' & HW' & _).
    exact (fast_read_typ_order_sound Θ Ξ _ _ _ HW').
  Qed.

  Lemma nbe_ty_of_fast : forall G A ρ a w, nbe_ty_order Θ Ξ G A -> fast_env_simulates Θ Ξ G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a -> Rtypᶠ fdomain_erase a in Θ ⍮ Ξ ⍮ List.length G ↘ w ->
      nf_proof_freeb w = true -> nbe_ty Θ Ξ G A w.
  Proof.
    intros * [w0 [ρ0 m Hi He Hr]] Hs Ha Hw Hpf; core_env.
    destruct (fast_read_typ_simulation Θ Ξ _ _ _ _ Hr (fast_eval_value_of_core Θ Ξ _ _ _ _ _ He Hag Ha)) as (W' & HW' & Hup).
    rewrite (functional_fast_read_typ _ _ _ _ HW' Hw) in Hup.
    rewrite <- (eq_of_upto_proof_free _ _ Hup Hpf); econstructor; eassumption.
  Qed.

  Lemma nbe_eval_typ_order : forall G M A ρ, nbe_order Θ Ξ G M A -> fast_env_simulates Θ Ξ G ρ ->
      fast_eval_exp_order Θ Ξ A (fenv_erase ρ).
  Proof. intros * [w [ρ0 a Hi He Hr]] Hs; core_env; eapply fast_eval_order_of_core; eassumption. Qed.

  Lemma nbe_eval_order : forall G M A ρ a, nbe_order Θ Ξ G M A -> fast_env_simulates Θ Ξ G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a -> fdomain_kind a <> ak_propositional ->
      fast_eval_exp_order Θ Ξ M (fenv_erase ρ).
  Proof.
    intros * [w [ρ0 a0 Hi He Hr]] Hs Ha Hk; core_env.
    pose proof (fast_kind_of_core Θ Ξ _ _ (fast_eval_value_of_core Θ Ξ _ _ _ _ _ He Hag Ha)) as Hka.
    destruct Hr as [w Hp _ | m w _ Hm _]; [ exfalso; apply Hk; rewrite <- Hka; exact Hp |].
    eapply fast_eval_order_of_core; eassumption.
  Qed.

  Lemma nbe_read_order : forall G M A ρ a m, nbe_order Θ Ξ G M A -> fast_env_simulates Θ Ξ G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a -> fdomain_kind a <> ak_propositional ->
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m ->
      fast_read_nf_order Θ Ξ (List.length G) (⇓ (fdomain_erase a) (fdomain_erase m)).
  Proof.
    intros * [w [ρ0 a0 Hi He Hr]] Hs Ha Hk Hm; core_env.
    pose proof (fast_eval_value_of_core Θ Ξ _ _ _ _ _ He Hag Ha) as Hsa.
    pose proof (fast_kind_of_core Θ Ξ _ _ Hsa) as Hka.
    destruct Hr as [w Hp _ | m0 w _ Hm0 Hw]; [ exfalso; apply Hk; rewrite <- Hka; exact Hp |].
    destruct (fast_read_nf_simulation Θ Ξ _ _ _ _ Hw
                (domain_nf_simulation_dom _ _ _ _ _ _ Hsa (fast_eval_value_of_core Θ Ξ _ _ _ _ _ Hm0 Hag Hm))) as (W' & HW' & _).
    exact (fast_read_nf_order_sound Θ Ξ _ _ _ HW').
  Qed.

  Lemma nbe_of_fast : forall G M A ρ a m w, nbe_order Θ Ξ G M A -> fast_env_simulates Θ Ξ G ρ ->
      ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase a -> fdomain_kind a <> ak_propositional ->
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ fenv_erase ρ ↘ fdomain_erase m ->
      Rnfᶠ ⇓ (fdomain_erase a) (fdomain_erase m) in Θ ⍮ Ξ ⍮ List.length G ↘ w ->
      nf_proof_freeb w = true -> nbe Θ Ξ G M A w.
  Proof.
    intros * [w0 [ρ0 a0 Hi He Hr]] Hs Ha Hk Hm Hw Hpf; core_env.
    pose proof (fast_eval_value_of_core Θ Ξ _ _ _ _ _ He Hag Ha) as Hsa.
    pose proof (fast_kind_of_core Θ Ξ _ _ Hsa) as Hka.
    destruct Hr as [w1 Hp _ | m0 w1 Hev Hm0 Hw1]; [ exfalso; apply Hk; rewrite <- Hka; exact Hp |].
    destruct (fast_read_nf_simulation Θ Ξ _ _ _ _ Hw1
                (domain_nf_simulation_dom _ _ _ _ _ _ Hsa (fast_eval_value_of_core Θ Ξ _ _ _ _ _ Hm0 Hag Hm))) as (W' & HW' & Hup).
    rewrite (functional_fast_read_nf _ _ _ _ HW' Hw) in Hup.
    rewrite <- (eq_of_upto_proof_free _ _ Hup Hpf); econstructor; [ eassumption | eassumption | eapply nbe_term_evaluated; eassumption ].
  Qed.
End FromFast.

(** ** The Exact Normal Forms

    With the skip off, from an exact environment, the fast normal form is
    the reference one. *)

Section FromExact.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac exact_core_env :=
    match goal with Hs : exact_env_spec _ _ _ _ |- _ => let Hi := fresh "Hi" in let Hok := fresh "Hok" in destruct Hs as [Hi Hok] end;
    functional_initial_env_rewrite_clear.

  Lemma nbe_ty_exact_eval_order : forall G A ρ, nbe_ty_order Θ Ξ G A -> exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp_order skip_off_mode Θ Ξ A (fenv_erase ρ).
  Proof. intros * [w [ρ0 m Hi0 He Hr]] Hs; exact_core_env; eapply exact_eval_order; eassumption. Qed.

  Lemma nbe_ty_exact_read_order : forall G A ρ a, nbe_ty_order Θ Ξ G A -> exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp skip_off_mode Θ Ξ A (fenv_erase ρ) (fdomain_erase a) ->
      @fast_read_typ_order skip_off_mode Θ Ξ (List.length G) (fdomain_erase a).
  Proof.
    intros * [w [ρ0 m Hi0 He Hr]] Hs Ha; exact_core_env; apply exact_eval in Ha; functional_eval_rewrite_clear.
    eapply exact_read_typ_order; eassumption.
  Qed.

  Lemma nbe_ty_of_exact : forall G A ρ a w, exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp skip_off_mode Θ Ξ A (fenv_erase ρ) (fdomain_erase a) ->
      @fast_read_typ skip_off_mode Θ Ξ (List.length G) (fdomain_erase a) w -> nbe_ty Θ Ξ G A w.
  Proof. intros * [Hi _] Ha Hw; econstructor; [ exact Hi | apply exact_eval, Ha | apply exact_read_typ, Hw ]. Qed.

  Lemma nbe_exact_eval_typ_order : forall G M A ρ, nbe_order Θ Ξ G M A -> exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp_order skip_off_mode Θ Ξ A (fenv_erase ρ).
  Proof. intros * [w [ρ0 a Hi0 He Hr]] Hs; exact_core_env; eapply exact_eval_order; eassumption. Qed.

  Lemma nbe_exact_eval_order : forall G M A ρ a, nbe_order Θ Ξ G M A -> exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp skip_off_mode Θ Ξ A (fenv_erase ρ) (fdomain_erase a) -> fdomain_kind a <> ak_propositional ->
      @fast_eval_exp_order skip_off_mode Θ Ξ M (fenv_erase ρ).
  Proof.
    intros * [w [ρ0 a0 Hi0 He Hr]] Hs Ha Hk; exact_core_env; apply exact_eval in Ha; functional_eval_rewrite_clear.
    destruct Hr as [w Hp _ | m w _ Hm _]; [ exfalso; apply Hk; rewrite <- fdomain_kind_erase; exact Hp |].
    eapply exact_eval_order; eassumption.
  Qed.

  Lemma nbe_exact_read_order : forall G M A ρ a m, nbe_order Θ Ξ G M A -> exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp skip_off_mode Θ Ξ A (fenv_erase ρ) (fdomain_erase a) -> fdomain_kind a <> ak_propositional ->
      @fast_eval_exp skip_off_mode Θ Ξ M (fenv_erase ρ) (fdomain_erase m) ->
      @fast_read_nf_order skip_off_mode Θ Ξ (List.length G) (⇓ (fdomain_erase a) (fdomain_erase m)).
  Proof.
    intros * [w [ρ0 a0 Hi0 He Hr]] Hs Ha Hk Hm; exact_core_env; apply exact_eval in Ha, Hm; functional_eval_rewrite_clear.
    destruct Hr as [w Hp _ | m0 w Hev Hm0 Hw]; [ exfalso; apply Hk; rewrite <- fdomain_kind_erase; exact Hp |].
    functional_eval_rewrite_clear; eapply exact_read_nf_order; eassumption.
  Qed.

  Lemma nbe_exact_read_proof_order : forall G M A ρ a, nbe_order Θ Ξ G M A -> exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp skip_off_mode Θ Ξ A (fenv_erase ρ) (fdomain_erase a) -> fdomain_kind a = ak_propositional ->
      @fast_read_nf_order skip_off_mode Θ Ξ (List.length G) (⇓ (fdomain_erase a) ⋆ᵈ⟨M, fenv_erase ρ⟩).
  Proof.
    intros * [w [ρ0 a0 Hi0 He Hr]] Hs Ha Hk; exact_core_env; apply exact_eval in Ha; functional_eval_rewrite_clear.
    destruct Hr as [w _ Hw | m0 w Hev _ _];
      [| exfalso; eapply evaluated_kind_not_propositional; [ exact Hev | rewrite fdomain_kind_erase; exact Hk ] ].
    eapply exact_read_nf_order; eassumption.
  Qed.

  Lemma nbe_of_exact : forall G M A ρ a m w, exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp skip_off_mode Θ Ξ A (fenv_erase ρ) (fdomain_erase a) -> fdomain_kind a <> ak_propositional ->
      @fast_eval_exp skip_off_mode Θ Ξ M (fenv_erase ρ) (fdomain_erase m) ->
      @fast_read_nf skip_off_mode Θ Ξ (List.length G) (⇓ (fdomain_erase a) (fdomain_erase m)) w -> nbe Θ Ξ G M A w.
  Proof.
    intros * [Hi _] Ha Hk Hm Hw; econstructor; [ exact Hi | apply exact_eval, Ha |].
    eapply nbe_term_evaluated; [ rewrite fdomain_kind_erase; apply evaluated_kind_of_not_propositional, Hk
                               | apply exact_eval, Hm | apply exact_read_nf, Hw ].
  Qed.

  Lemma nbe_of_exact_proof : forall G M A ρ a w, exact_env_spec Θ Ξ G ρ ->
      @fast_eval_exp skip_off_mode Θ Ξ A (fenv_erase ρ) (fdomain_erase a) -> fdomain_kind a = ak_propositional ->
      @fast_read_nf skip_off_mode Θ Ξ (List.length G) (⇓ (fdomain_erase a) ⋆ᵈ⟨M, fenv_erase ρ⟩) w -> nbe Θ Ξ G M A w.
  Proof.
    intros * [Hi _] Ha Hk Hw; econstructor; [ exact Hi | apply exact_eval, Ha |].
    eapply nbe_term_proof; [ rewrite fdomain_kind_erase; exact Hk | apply exact_read_nf, Hw ].
  Qed.
End FromExact.

(** ** The Normalizers *)

Section InitialEnvImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** The fast initial environment of a context, with the skip on *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl G (H : initial_env_order Θ Ξ G) : fast_env Θ Ξ G by struct G :=
  | nil, H => exist _ nil (fast_env_simulates_nil Θ Ξ)
  | cons (ce_ass κ A) G, H =>
      let (ρ, Hρ) := initial_env_impl G (initial_env_order_tail _ _ _ _ H) in
      let (a, Ha) := fast_eval_exp_impl F A ρ (fast_env_simulates_ok _ _ _ _ Hρ) (fast_env_ass_order _ _ _ _ _ _ H Hρ) in
      exist _ (fextend_env ρ (fd_neut a (fd_var (List.length G))) (fentry_type_value a)) (fast_env_ass _ _ _ _ _ _ _ H Hρ Ha)
  (** A definition, by the kind of its type *)
  | cons (ce_def A M) G, H =>
      let (ρ, Hρ) := initial_env_impl G (initial_env_order_tail _ _ _ _ H) in
      let (a, Ha) := fast_eval_exp_impl F A ρ (fast_env_simulates_ok _ _ _ _ Hρ) (fast_env_def_typ_order _ _ _ _ _ _ H Hρ) in
      match abs_kind_eq_dec (fdomain_kind a) ak_propositional with
      | left Hk => exist _ (fextend_env ρ (fd_proof M ρ) (fentry_type_value a)) (fast_env_def_proof _ _ _ _ _ _ _ H Hρ Ha Hk)
      | right Hk =>
          let (m, Hm) := fast_eval_exp_impl F M ρ (fast_env_simulates_ok _ _ _ _ Hρ)
                           (fast_env_def_order _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hk) in
          exist _ (fextend_env ρ m (fentry_type_value a)) (fast_env_def _ _ _ _ _ _ _ _ H Hρ Ha Hk Hm)
      end
  | cons (ce_mod U) G, H =>
      let (ρ, Hρ) := initial_env_impl G (initial_env_order_tail _ _ _ _ H) in
      let (h, Hh) := fast_eval_modexp_impl F (me_lit U) ρ (fast_env_simulates_ok _ _ _ _ Hρ) (fast_env_mod_order _ _ _ _ _ H Hρ) in
      exist _ (fextend_env_mod ρ h U) (fast_env_mod _ _ _ _ _ _ H Hρ Hh)
  | cons (ce_dm A M U) G, H =>
      let (ρ, Hρ) := initial_env_impl G (initial_env_order_tail _ _ _ _ H) in
      let Ho := fast_env_dm_order _ _ _ _ _ _ _ H Hρ in
      let (a, Ha) := fast_eval_exp_impl F A ρ (fast_env_simulates_ok _ _ _ _ Hρ) (proj1 Ho) in
      let (m, Hm) := fast_eval_exp_impl F M ρ (fast_env_simulates_ok _ _ _ _ Hρ) (proj1 (proj2 Ho)) in
      let (h, Hh) := fast_eval_modexp_impl F (me_lit U) ρ (fast_env_simulates_ok _ _ _ _ Hρ) (proj2 (proj2 Ho)) in
      exist _ (fextend_env_dm ρ m (fentry_type_value a) h U) (fast_env_dm _ _ _ _ _ _ _ _ _ _ H Hρ Ha Hm Hh).

  (** The exact initial environment of a context, with the skip off, for
      the fallback *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations initial_env_exact_impl G (H : initial_env_order Θ Ξ G) : { ρ | exact_env_spec Θ Ξ G ρ } by struct G :=
  | nil, H => exist _ nil (exact_env_nil Θ Ξ)
  | cons (ce_ass κ A) G, H =>
      let (ρ, Hρ) := initial_env_exact_impl G (initial_env_order_tail _ _ _ _ H) in
      let (a, Ha) := fast_eval_exp_impl F (SM := skip_off_mode) A ρ (proj2 Hρ) (exact_env_ass_order _ _ _ _ _ _ H Hρ) in
      exist _ (fextend_env ρ (fd_neut a (fd_var (List.length G))) (fentry_type_value a))
        (exact_env_ass _ _ _ _ _ _ _ Hρ (exact_eval_spec _ _ _ _ _ Ha))
  | cons (ce_def A M) G, H =>
      let (ρ, Hρ) := initial_env_exact_impl G (initial_env_order_tail _ _ _ _ H) in
      let (a, Ha) := fast_eval_exp_impl F (SM := skip_off_mode) A ρ (proj2 Hρ) (exact_env_def_typ_order _ _ _ _ _ _ H Hρ) in
      match abs_kind_eq_dec (fdomain_kind a) ak_propositional with
      | left Hk => exist _ (fextend_env ρ (fd_proof M ρ) (fentry_type_value a))
                     (exact_env_def_proof _ _ _ _ _ _ _ Hρ (exact_eval_spec _ _ _ _ _ Ha) Hk)
      | right Hk =>
          let (m, Hm) := fast_eval_exp_impl F (SM := skip_off_mode) M ρ (proj2 Hρ)
                           (exact_env_def_order _ _ _ _ _ _ _ H Hρ (proj1 (exact_eval_spec _ _ _ _ _ Ha)) Hk) in
          exist _ (fextend_env ρ m (fentry_type_value a))
            (exact_env_def _ _ _ _ _ _ _ _ Hρ (exact_eval_spec _ _ _ _ _ Ha) Hk (exact_eval_spec _ _ _ _ _ Hm))
      end
  | cons (ce_mod U) G, H =>
      let (ρ, Hρ) := initial_env_exact_impl G (initial_env_order_tail _ _ _ _ H) in
      let (h, Hh) := fast_eval_modexp_impl F (SM := skip_off_mode) (me_lit U) ρ (proj2 Hρ) (exact_env_mod_order _ _ _ _ _ H Hρ) in
      exist _ (fextend_env_mod ρ h U) (exact_env_mod _ _ _ _ _ _ Hρ (exact_eval_modexp_spec _ _ _ _ _ Hh))
  | cons (ce_dm A M U) G, H =>
      let (ρ, Hρ) := initial_env_exact_impl G (initial_env_order_tail _ _ _ _ H) in
      let Ho := exact_env_dm_order _ _ _ _ _ _ _ H Hρ in
      let (a, Ha) := fast_eval_exp_impl F (SM := skip_off_mode) A ρ (proj2 Hρ) (proj1 Ho) in
      let (m, Hm) := fast_eval_exp_impl F (SM := skip_off_mode) M ρ (proj2 Hρ) (proj1 (proj2 Ho)) in
      let (h, Hh) := fast_eval_modexp_impl F (SM := skip_off_mode) (me_lit U) ρ (proj2 Hρ) (proj2 (proj2 Ho)) in
      exist _ (fextend_env_dm ρ m (fentry_type_value a) h U)
        (exact_env_dm _ _ _ _ _ _ _ _ _ _ Hρ (exact_eval_spec _ _ _ _ _ Ha) (exact_eval_spec _ _ _ _ _ Hm)
           (exact_eval_modexp_spec _ _ _ _ _ Hh)).
End InitialEnvImpl.

Section NbETyEnvDef.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** The normal form of a type with the skip off, from the exact initial
      environment of the context, computed afresh *)
  Definition nbe_ty_exact_impl G A (H : nbe_ty_order Θ Ξ G A) : { w | nbe_ty Θ Ξ G A w } :=
    let (ρ, Hρ) := initial_env_exact_impl F G (nbe_ty_order_init _ _ _ _ H) in
    let (a, Ha) := fast_eval_exp_impl F (SM := skip_off_mode) A ρ (proj2 Hρ) (nbe_ty_exact_eval_order _ _ _ _ _ H Hρ) in
    let (w, Hw) := fast_read_typ_impl F (SM := skip_off_mode) (List.length G) a (proj2 Ha)
                     (nbe_ty_exact_read_order _ _ _ _ _ _ H Hρ (proj1 Ha)) in
    exist _ w (nbe_ty_of_exact _ _ _ _ _ _ _ Hρ (proj1 Ha) Hw).

  (** The normal form of a type, from the fast initial environment of the
      context: with the skip on, and, if it has a proof in it, again with
      the skip off *)
  Definition nbe_ty_env_impl G (P : fast_env Θ Ξ G) A (H : nbe_ty_order Θ Ξ G A) : { w | nbe_ty Θ Ξ G A w } :=
    let (ρ, Hρ) := P in
    let (a, Ha) := fast_eval_exp_impl F A ρ (fast_env_simulates_ok _ _ _ _ Hρ) (nbe_ty_eval_order _ _ _ _ _ H Hρ) in
    let (w, Hw) := fast_read_typ_impl F (List.length G) a (proj2 Ha) (nbe_ty_read_order _ _ _ _ _ _ H Hρ (proj1 Ha)) in
    match inspect (nf_proof_freeb w) with
    | exist _ true Hpf => exist _ w (nbe_ty_of_fast _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hw Hpf)
    | exist _ false _ => nbe_ty_exact_impl G A H
    end.
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

  (** The normal form of a term at a type with the skip off, from the exact
      initial environment of the context, computed afresh: at a
      proposition, the term kept and read back; otherwise, its value read
      back *)
  Definition nbe_exact_impl G M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
    let (ρ, Hρ) := initial_env_exact_impl F G (nbe_order_init _ _ _ _ _ H) in
    let (a, Ha) := fast_eval_exp_impl F (SM := skip_off_mode) A ρ (proj2 Hρ) (nbe_exact_eval_typ_order _ _ _ _ _ _ H Hρ) in
    match abs_kind_eq_dec (fdomain_kind a) ak_propositional with
    | left Hk =>
        let (w, Hw) := fast_read_nf_impl F (SM := skip_off_mode) (List.length G) (fd_dom a (fd_proof M ρ))
                         (fdomain_nf_ok_dom _ _ _ _ (proj2 Ha) (fdomain_ok_proof _ _ _ _ (proj2 Hρ)))
                         (nbe_exact_read_proof_order _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hk) in
        exist _ w (nbe_of_exact_proof _ _ _ _ _ _ _ _ Hρ (proj1 Ha) Hk Hw)
    | right Hk =>
        let (m, Hm) := fast_eval_exp_impl F (SM := skip_off_mode) M ρ (proj2 Hρ)
                         (nbe_exact_eval_order _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hk) in
        let (w, Hw) := fast_read_nf_impl F (SM := skip_off_mode) (List.length G) (fd_dom a m)
                         (fdomain_nf_ok_dom _ _ _ _ (proj2 Ha) (proj2 Hm))
                         (nbe_exact_read_order _ _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hk (proj1 Hm)) in
        exist _ w (nbe_of_exact _ _ _ _ _ _ _ _ _ Hρ (proj1 Ha) Hk (proj1 Hm) Hw)
    end.

  (** The normal form of a term at a type, from the fast initial
      environment of the context, with the skip on: at a type of a
      universe or of levels, its value read back, and, if that has a proof
      in it, again with the skip off; at a proposition the normal form is
      a proof, so it is computed with the skip off. *)
  Definition nbe_env_impl G (P : fast_env Θ Ξ G) M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
    let (ρ, Hρ) := P in
    let (a, Ha) := fast_eval_exp_impl F A ρ (fast_env_simulates_ok _ _ _ _ Hρ) (nbe_eval_typ_order _ _ _ _ _ _ H Hρ) in
    match abs_kind_eq_dec (fdomain_kind a) ak_propositional with
    | left _ => nbe_exact_impl G M A H
    | right Hk =>
        let (m, Hm) := fast_eval_exp_impl F M ρ (fast_env_simulates_ok _ _ _ _ Hρ)
                         (nbe_eval_order _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hk) in
        let (w, Hw) := fast_read_nf_impl F (List.length G) (fd_dom a m) (fdomain_nf_ok_dom _ _ _ _ (proj2 Ha) (proj2 Hm))
                         (nbe_read_order _ _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hk (proj1 Hm)) in
        match inspect (nf_proof_freeb w) with
        | exist _ true Hpf => exist _ w (nbe_of_fast _ _ _ _ _ _ _ _ _ H Hρ (proj1 Ha) Hk (proj1 Hm) Hw Hpf)
        | exist _ false _ => nbe_exact_impl G M A H
        end
    end.
End NbEEnvDef.

(** From scratch, at the initial environment of the context. *)
Definition nbe_impl (F : FCtx) G M A (H : nbe_order (fc_deps F) (fc_stack F) G M A) :
    { w | nbe (fc_deps F) (fc_stack F) G M A w } :=
  nbe_env_impl F G (initial_env_impl F G (nbe_order_init _ _ _ _ _ H)) M A H.
