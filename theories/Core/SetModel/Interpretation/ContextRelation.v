(** * Equal Extensions and the Values Read in Them

    Two contexts that extend one context by equal extensions read a term
    alike: its values in the two are equal ([set_interp_functional_ext]).
    A term's value depends on its context only through the kinds a typing
    gives its λs, so this rests on the kinds agreeing in the two
    ([fn_kinds_unique_ext]), a consequence of the NbE theorems.  Under a
    binder both contexts grow by the same entries, and the extensions stay
    equal ([wf_ext_eq_extend_same], [wf_ext_eq_app_same]). *)

From Stdlib Require Import List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Functional.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

(** ** Extending Equal Extensions *)

(** Equal extensions grow by an entry well formed after each into equal
    extensions. *)
Lemma wf_ext_eq_extend_same : forall Θ Ξ Γ Ψ Ψ' e, Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Ψ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ e :: Ψ' ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ e :: Ψ ≈ e :: Ψ'.
Proof.
  intros * HΨ Hc Hc'. inversion Hc; subst; inversion Hc'; subst.
  - match goal with HA : Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ ?A : ?S, HS : sort_kind ?S _ |- _ =>
      pose proof (wf_subtyp_refl_typ _ _ _ _ _ HA (sort_kind_type_sort _ _ HS)) end.
    eapply wf_ext_eq_ass; eassumption.
  - match goal with HA : Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ ?A : ?S, HS : type_sort ?S |- _ =>
      pose proof (wf_subtyp_refl_typ _ _ _ _ _ HA HS) end.
    eapply wf_ext_eq_def; try eassumption. apply wf_exp_eq_refl; eassumption.
  - eapply wf_ext_eq_mod; eassumption.
  - match goal with HA : Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ ?A : a_typ ?i, HA' : Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ ?A : a_typ ?j |- _ =>
      assert (Hi : i <= max i j) by lia; assert (Hj : j <= max i j) by lia;
      pose proof (lift_exp_ge _ _ _ _ _ _ Hi HA) as HAm; pose proof (lift_exp_ge _ _ _ _ _ _ Hj HA') as HAm' end.
    eapply wf_ext_eq_dm; try eassumption; apply wf_exp_eq_refl; eassumption.
Qed.

(** The same for a telescope. *)
Lemma wf_ext_eq_app_same : forall Θ Ξ Γ Ψ Ψ' Φ, Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    ⊢ Θ ⍮ Ξ ⍮ Φ ++ Ψ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Φ ++ Ψ' ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Φ ++ Ψ ≈ Φ ++ Ψ'.
Proof.
  induction Φ as [| e Φ IH]; intros HΨ Hc Hc'; cbn in *; [exact HΨ |].
  apply wf_ext_eq_extend_same; rewrite <- ?app_assoc; [| exact Hc | exact Hc'].
  apply IH; [exact HΨ | eapply ctx_decomp_tail; exact Hc | eapply ctx_decomp_tail; exact Hc'].
Qed.

Section ContextRelation.
  Context {GC : GCtx}.

(** [ctx_ext_equal_with Δ Δ' Γ Ψ Ψ']: [Δ] and [Δ'] extend [Γ] by the
    equal extensions [Ψ] and [Ψ']. *)
Record ctx_ext_equal_with (Δ Δ' Γ Ψ Ψ' : ctx) : Prop :=
  { (** [Δ] is [Γ] extended by [Ψ] *)
    ctx_ext_equal_left : Δ = Ψ ++ Γ
    (** [Δ'] is [Γ] extended by [Ψ'] *)
  ; ctx_ext_equal_right : Δ' = Ψ' ++ Γ
    (** The extensions are equal *)
  ; ctx_ext_equal_ext : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' }.

(** [Δ] and [Δ'] extend one context by equal extensions. *)
Definition ctx_ext_equal (Δ Δ' : ctx) : Prop := exists Γ Ψ Ψ', ctx_ext_equal_with Δ Δ' Γ Ψ Ψ'.

(** Two typings of a λ in contexts extending one context by equal
    extensions give it the same kinds. *)
Definition fn_kinds_unique_ext : Prop :=
  forall Δ Δ' A M κd κc C B κd' κc' C' B', ctx_ext_equal Δ Δ' ->
    gc_deps ⍮ gc_stack ⍮ Δ ⊢ a_fn A M : a_pi κd κc C B ->
    gc_deps ⍮ gc_stack ⍮ Δ' ⊢ a_fn A M : a_pi κd' κc' C' B' -> κd = κd' /\ κc = κc'.

(** The same context is an equal extension of itself, by nothing. *)
Lemma ctx_ext_equal_refl : forall Δ, ⊢ gc_deps ⍮ gc_stack ⍮ Δ -> ctx_ext_equal Δ Δ.
Proof. intros Δ HΔ. exists Δ, nil, nil. constructor; [reflexivity | reflexivity | constructor; exact HΔ]. Qed.

Lemma fn_kinds_unique_of_ext : fn_kinds_unique_ext -> fn_kinds_unique.
Proof. intros H Γ A M κd κc C B κd' κc' C' B' HT HT'. apply (H Γ Γ A M κd κc C B κd' κc' C' B'); [apply ctx_ext_equal_refl; exact (presup_exp_ctx HT) | exact HT | exact HT']. Qed.

Lemma ctx_ext_equal_extend : forall Δ Δ' Φ, ctx_ext_equal Δ Δ' ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Φ ++ Δ -> ⊢ gc_deps ⍮ gc_stack ⍮ Φ ++ Δ' -> ctx_ext_equal (Φ ++ Δ) (Φ ++ Δ').
Proof.
  intros * (Γ & Ψ & Ψ' & [-> -> HΨ]) Hc Hc'. exists Γ, (Φ ++ Ψ), (Φ ++ Ψ').
  constructor; [rewrite app_assoc; reflexivity | rewrite app_assoc; reflexivity |].
  apply wf_ext_eq_app_same; assumption.
Qed.

(** ** Values in Equal Extensions *)

  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique_ext.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** The functionality of every reading across equal extensions *)
Definition set_interp_functional_ext_all :=
  set_interp_functional_rel_all T γ Hmods ctx_ext_equal Hfn ctx_ext_equal_extend.

Theorem set_interp_functional_ext : forall Δ ρ M v, set_interp T γ Δ ρ M v ->
    forall Δ' ρ' v', ctx_ext_equal Δ Δ' -> set_env_eq γ ρ ρ' -> set_interp T γ Δ' ρ' M v' -> set_eq v v'.
Proof. exact (proj1 set_interp_functional_ext_all). Qed.

Theorem set_interp_modexp_functional_ext : forall Δ ρ H m, set_interp_modexp T γ Δ ρ H m ->
    forall Δ' ρ' m', ctx_ext_equal Δ Δ' -> set_env_eq γ ρ ρ' -> set_interp_modexp T γ Δ' ρ' H m' -> set_module_eq γ m m'.
Proof. exact (proj1 (proj2 (proj2 (proj2 set_interp_functional_ext_all)))). Qed.

End ContextRelation.
