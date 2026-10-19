(** * Typing What Module Expressions Denote

    The typing lemmas presupposition needs about telescopes, and the
    invariant of descriptions: what a well-formed module expression denotes
    is typed ([desc_ok]).  Its term part is a type, its δ-reduct inhabits
    it, its arguments are typed against the parameters they fill, and the
    entries of its module part denote typed descriptions in turn. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Export Paths.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Telescopes *)

Lemma ctx_lookup_app_r : forall E T x A,
    T ∋ #x : A ->
    E ++ T ∋ #(x + length E) : A[wk_shiftn (length E)]ʷ.
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, (exp_wk_wk_eq _ _ _ wk_shiftn_zero), exp_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- (exp_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- exp_wk_wk.
    constructor; auto.
Qed.

Lemma ctx_lookup_def_app_r : forall E T x A M,
    T ∋ #x ≔ M : A ->
    E ++ T ∋ #(x + length E) ≔ M[wk_shiftn (length E)]ʷ : A[wk_shiftn (length E)]ʷ.
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, !(exp_wk_wk_eq _ _ _ wk_shiftn_zero), !exp_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- !(exp_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- !exp_wk_wk.
    constructor; auto.
Qed.

Lemma ctx_lookup_mod_app_r : forall E T x U,
    T ∋ #x ≔ₘ U ->
    E ++ T ∋ #(x + length E) ≔ₘ gunit_wk U (wk_shiftn (length E)).
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, (gunit_wk_wk_eq _ _ _ wk_shiftn_zero), gunit_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- (gunit_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- gunit_wk_wk.
    constructor; auto.
Qed.

Lemma wf_wk_shiftn_app : forall Θ Ξ E T,
    ⊢ Θ ⍮ Ξ ⍮ E ++ T ->
    ⊢ Θ ⍮ Ξ ⍮ T ->
    Θ ⍮ Ξ ⍮ E ++ T ⊢ʷ wk_shiftn (length E) : T.
Proof.
  intros; econstructor; [ eassumption | assumption | | |];
    intros; [ apply ctx_lookup_app_r | apply ctx_lookup_def_app_r | apply ctx_lookup_mod_app_r ]; assumption.
Qed.

Lemma ctx_app_wf_right : forall Θ Ξ E T, ⊢ Θ ⍮ Ξ ⍮ E ++ T -> ⊢ Θ ⍮ Ξ ⍮ T.
Proof.
  induction E as [| B E IH]; intros * H; cbn in *; [ assumption |].
  apply IH; eapply ctx_decomp_tail; eassumption.
Qed.

(** [wf_let] at a universe, which [Typeω@j[Id,,M]] is by computation only. *)
Lemma wf_let_typ : forall Θ Ξ Γ oA A M B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : Typeω@j ->
    let_ann oA A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B : Typeω@j[Id,,M]) as Hl by (eapply wf_let; cycle 3; [ solve_let_ann | eassumption .. ]).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_zeta_typ : forall Θ Ξ Γ oA A M B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : Typeω@j ->
    let_ann oA A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ B[Id,,M] : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ B[Id,,M] : Typeω@j[Id,,M]) as Hl
      by (eapply wf_exp_eq_let_zeta; cycle 3; [ solve_let_ann | eassumption .. ]).
  exact Hl.
Qed.

(** The same for a local module. *)
Lemma wf_let_mod_typ : forall Θ Ξ Γ U B j,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : Typeω@j[Id ,,ₘ me_lit U]) as Hl by (eapply wf_let_mod; [ eassumption | econstructor; eauto using presup_exp_ctx | eassumption ]).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_mod_zeta_typ : forall Θ Ξ Γ U B j,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Typeω@j[Id ,,ₘ me_lit U]) as Hl
      by (eapply wf_exp_eq_let_mod_zeta; [ eassumption | econstructor; eauto using presup_exp_ctx | eassumption ]).
  exact Hl.
Qed.

#[export]
Hint Resolve wf_let_typ wf_exp_eq_let_zeta_typ wf_let_mod_typ wf_exp_eq_let_mod_zeta_typ : mctt.

Lemma ctx_pi_wf : forall Θ Ξ Δ Γ A i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Typeω@j.
Proof.
  induction Δ as [| [B | B N | U] Δ IH]; intros * HΔ HA; cbn in *; [ eauto | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Typeω@?k |- _ =>
      eapply IH; [ eauto using presup_exp_ctx |];
      eapply wf_pi_large; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
    end.
  - (** A definition is generalized as a [let], which is a type at the type's
        own level. *)
    eapply IH; [ eauto using presup_exp_ctx |].
    eapply wf_let_typ; cycle 3; [ solve_let_ann | eassumption .. ].
  - (** So is a module slot, as a [let module]. *)
    eapply IH; [ eauto using presup_unit_eq_ctx |].
    eapply wf_let_mod_typ; eassumption.
Qed.

Lemma ctx_fn_wf : forall Θ Ξ Δ Γ A M i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  induction Δ as [| [B | B N | U] Δ IH]; intros * HΔ HA HM; cbn in *; [ assumption | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Typeω@?k |- _ =>
      eapply IH with (i := max k i); [ eauto using presup_exp_ctx | |];
      [ eapply wf_pi_large; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
      | econstructor; eassumption ]
    end.
  - (** The body's [let] has the type [A[Id,,N]], which is the type's [let] by
        ζ. *)
    assert (Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ ℓ B ≔ N in A : Typeω@i) by (eapply wf_let_typ; cycle 3; [ solve_let_ann | eassumption .. ]).
    eapply IH with (i := i); [ eauto using presup_exp_ctx | eassumption |].
    eapply wf_exp_subtyp'; [ eapply wf_let; cycle 3; [ solve_let_ann | eassumption .. ] |].
    eapply wf_subtyp_refl; [ eassumption |].
    eapply wf_exp_eq_sym, wf_exp_eq_let_zeta_typ; cycle 3; [ solve_let_ann | eassumption .. ].
  - assert (Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ ℓₘ U in A : Typeω@i) by (eapply wf_let_mod_typ; eassumption).
    eapply IH with (i := i); [ eauto using presup_unit_eq_ctx | eassumption |].
    eapply wf_exp_subtyp'; [ eapply wf_let_mod; eassumption |].
    eapply wf_subtyp_refl; [ eassumption |].
    eapply wf_exp_eq_sym, wf_exp_eq_let_mod_zeta_typ; eassumption.
Qed.

Corollary ctx_pi_wf0 : forall Θ Ξ Δ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Typeω@j.
Proof.
  intros; eapply ctx_pi_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption ].
Qed.

Corollary ctx_fn_wf0 : forall Θ Ξ Δ A M i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  intros; eapply ctx_fn_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption.. ].
Qed.

(** A closed judgment holds in any context. *)
Lemma closed_weaken_exp : forall Θ Ξ Γ M A,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A ->
    exp_scoped 0 M -> exp_scoped 0 A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ HM HsM HsA.
  rewrite <- (exp_closed_wk M (wk_shiftn (length Γ)) HsM),
    <- (exp_closed_wk A (wk_shiftn (length Γ)) HsA).
  eapply wk_preserves_exp; [ exact HM |].
  pose proof (wf_wk_shiftn_app Θ Ξ Γ nil) as Hw; rewrite List.app_nil_r in Hw.
  apply Hw; [ assumption | constructor; eapply ctx_wf_gctx; eassumption ].
Qed.

(** ** Telescopes Filled by Lists of Terms

    A telescope of assumptions over [Γ] is filled by terms of [Γ] typed one by
    one at the instances of its types: the terms are a substitution into it,
    and a term of a [Π] over it applies to them. *)

Lemma ctx_ext_refl : forall Θ Ξ Δ Γ, tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΔ; cbn in *; [ constructor; assumption |].
  inversion_clear Hass as [| ? ? [A ->] Hass'].
  destruct (ctx_decomp HΔ) as [HΔ' [i HA]].
  econstructor; [ apply IH; assumption | exact HA | apply wf_exp_eq_refl, HA | exact HA ].
Qed.

Lemma ctx_sub_wf : forall Θ Ξ Γ Γ' Δ σ,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ σ ++ Γ'.
Proof.
  intros * Hσ Hass HΔ; eapply ext_eq_ctx_left, sub_preserves_ext; [ apply ctx_ext_refl; eassumption | exact Hσ ].
Qed.

Lemma wf_sub_of_list : forall Θ Ξ Δ Γ Γ0 σ Ms,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ0 -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Γ0 ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list σ Ms : Δ ++ Γ0.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ Hl HMs.
  - destruct Ms; [ exact Hσ | discriminate ].
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite <- List.app_assoc in HΔ |- *; cbn [List.app] in HΔ |- *.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [k HA0]].
    cbn [sb_of_list]; eapply IH; [ exact Hass | exact HΔ | | lia |].
    + eapply wf_sub_extend; [ exact Hσ | exact HA0 |].
      apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ].
    + intros k' N T HN HT; apply (HMs (S k')); [ exact HN | rewrite tele_insts_snoc; exact HT ].
Qed.

Corollary wf_sub_of_list_id : forall Θ Ξ Δ Γ Ms,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ms : Δ ++ Γ.
Proof. intros; eapply wf_sub_of_list; eauto using wf_sub_id, ctx_app_wf_tail. Qed.

Lemma wf_apps_ctx_pi_n : forall n Θ Ξ Δ Γ B i M Ms,
    List.length Δ = n ->
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ms : B[sb_of_list Id Ms].
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HM Hl HMs.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; cbn; rewrite exp_sub_id; exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [k HA0]].
    destruct (ctx_pi_wf _ _ _ _ _ _ HΔ HB) as [j HPi].
    assert (HM0 : Θ ⍮ Ξ ⍮ Γ ⊢ M0 : A0)
      by (rewrite <- (exp_sub_id A0); apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (Happ : Θ ⍮ Ξ ⍮ Γ ⊢ M $ M0 : (ctx_pi Δ B)[Id,,M0])
      by (eapply wf_app with (i := max k j);
          [ eapply lift_exp_max_left; exact HA0 | eapply lift_exp_max_right; exact HPi | exact HM | exact HM0 ]).
    rewrite ctx_pi_sub in Happ.
    pose proof (wf_sub_single _ _ _ _ _ _ HA0 HM0) as Hs.
    assert (HΔ' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ (Id,,M0) ++ Γ) by (eapply ctx_sub_wf; eassumption).
    pose proof (wf_sub_ext _ _ _ _ _ _ Hs HΔ' HΔ) as Hs'.
    cbn [apps_exp sb_of_list].
    replace (B[sb_of_list (Id,,M0) Ms]) with (B[sb_qn (List.length Δ) (Id,,M0)][sb_of_list Id Ms])
      by (replace (List.length Δ) with (List.length Ms) by lia; apply exp_sub_qn_of_list).
    eapply (IH _ _ (tele_sub Δ (Id,,M0))); [ rewrite length_tele_sub; lia | apply tele_ass_sub; exact Hass | exact HΔ' | | exact Happ
               | rewrite length_tele_sub; lia |].
    + exact (sub_preserves_exp _ _ _ _ _ _ _ HB Hs').
    + intros k' N T HN HT; apply (HMs (S k')); [ exact HN |].
      rewrite tele_insts_snoc; cbn [List.nth_error].
      rewrite tele_insts_tele_sub in HT; rewrite <- HT; f_equal.
      apply tele_insts_sb_eq; symmetry; apply sb_compose_id_right.
Qed.

Corollary wf_apps_ctx_pi : forall Θ Ξ Δ Γ B i M Ms,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ms : B[sb_of_list Id Ms].
Proof. intros; eapply wf_apps_ctx_pi_n; eauto. Qed.



(** ** Telescopes Substituted *)

(** An extension read off a context. *)
Lemma ext_of_ctx' : forall Θ Ξ X Γ, ⊢ Θ ⍮ Ξ ⍮ X ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ X ≈ X.
Proof.
  induction X as [| [A | A M | U] X IH]; intros * H; cbn in H.
  - constructor; exact H.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Typeω@?i |- _ =>
      eapply wf_ext_eq_ass; [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HA ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Typeω@?i, HM : _ ⍮ _ ⍮ X ++ Γ ⊢ M : A |- _ =>
      eapply wf_ext_eq_def;
        [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HM
        | eapply wf_exp_eq_refl; exact HM | exact HA | exact HM ] end.
  - inversion H; subst.
    match goal with HU : _ ⍮ _ ⍮ X ++ Γ ⊢ᵘ U ≈ U |- _ =>
      eapply wf_ext_eq_mod; [ apply IH; eauto using presup_unit_eq_ctx | exact HU | exact HU ] end.
Qed.

Lemma ctx_sub_wf_gen : forall Θ Ξ Γ Γ' Ψ σ,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ'.
Proof.
  intros * Hσ HΨ; eapply ext_eq_ctx_left, sub_preserves_ext; [ apply ext_of_ctx'; exact HΨ | exact Hσ ].
Qed.

(** The outermost assumption of a telescope, past the definitions and
    modules outside it, and the substitution removing those. *)
Lemma tele_split_wf : forall Θ Ξ R Γ, ⊢ Θ ⍮ Ξ ⍮ rev R ++ Γ ->
    match tele_split R with
    | inl (B, T, τ) =>
        (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ B : Typeω@i) /\ ⊢ Θ ⍮ Ξ ⍮ T ++ ce_ass B :: Γ /\
        Θ ⍮ Ξ ⍮ T ++ ce_ass B :: Γ ⊢ˢ τ : rev R ++ Γ
    | inr τ => Θ ⍮ Ξ ⍮ Γ ⊢ˢ τ : rev R ++ Γ
    end.
Proof.
  induction R as [| [B0 | B0 N | U] R IH]; intros * HR; cbn [rev tele_split] in *.
  - exact (wf_sub_id _ _ _ HR).
  - rewrite <- List.app_assoc in *; cbn [List.app] in *.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HR)) as [_ HB].
    split; [ exact HB | split; [ exact HR | exact (wf_sub_id _ _ _ HR) ] ].
  - rewrite <- List.app_assoc in HR; cbn [List.app] in HR.
    pose proof (ctx_app_wf_tail _ _ _ _ HR) as HD.
    destruct (ctx_decomp_def HD) as (HΓ & [i HB0] & HN).
    pose proof (wf_sub_single_def _ _ _ _ _ _ HB0 HN) as Hs.
    specialize (IH _ HR).
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + destruct IH as ([j HB'] & HT' & Hτ).
      split; [ exists j; exact (sub_preserves_exp _ _ _ _ _ _ _ HB' Hs) |].
      assert (HT'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (T' ++ ce_ass B' :: nil) (Id,,N) ++ Γ)
        by (eapply ctx_sub_wf_gen; [ exact Hs | rewrite <- List.app_assoc; exact HT' ]).
      rewrite tele_sub_app in HT''; cbn [tele_sub centry_sub length] in HT''; rewrite <- List.app_assoc in HT''; cbn [List.app] in HT''.
      split; [ exact HT'' |].
      eapply wf_sub_compose; [ exact Hτ |].
      pose proof (wf_sub_ext _ _ (T' ++ ce_ass B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      apply Hx; [ exact HT'' | exact HT' ].
    + eapply wf_sub_compose; [ exact IH | exact Hs ].
  - rewrite <- List.app_assoc in HR; cbn [List.app] in HR.
    pose proof (ctx_app_wf_tail _ _ _ _ HR) as HD.
    destruct (ctx_decomp_mod HD) as (HΓ & HU).
    pose proof (wf_sub_single_mod _ _ _ _ HU) as Hs.
    specialize (IH _ HR).
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + destruct IH as ([j HB'] & HT' & Hτ).
      split; [ exists j; exact (sub_preserves_exp _ _ _ _ _ _ _ HB' Hs) |].
      assert (HT'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (T' ++ ce_ass B' :: nil) (Id ,,ₘ me_lit U) ++ Γ)
        by (eapply ctx_sub_wf_gen; [ exact Hs | rewrite <- List.app_assoc; exact HT' ]).
      rewrite tele_sub_app in HT''; cbn [tele_sub centry_sub length] in HT''; rewrite <- List.app_assoc in HT''; cbn [List.app] in HT''.
      split; [ exact HT'' |].
      eapply wf_sub_compose; [ exact Hτ |].
      pose proof (wf_sub_ext _ _ (T' ++ ce_ass B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      apply Hx; [ exact HT'' | exact HT' ].
    + eapply wf_sub_compose; [ exact IH | exact Hs ].
Qed.

(** ** What Well-Formed Module Expressions Denote Exists *)

Lemma tele_open_split : forall R B T, tele_open R = Some (B, T) -> exists τ, tele_split R = inl (B, T, τ).
Proof.
  induction R as [| [B0 | B0 N | U] R IH]; intros * H; cbn in H |- *; try discriminate.
  - injection H as <- <-; eauto.
  - destruct (tele_open R) as [[B' T'] |]; [| discriminate ]; injection H as <- <-.
    destruct (IH _ _ eq_refl) as (τ & ->); eauto.
  - destruct (tele_open R) as [[B' T'] |]; [| discriminate ]; injection H as <- <-.
    destruct (IH _ _ eq_refl) as (τ & ->); eauto.
Qed.

(** The parameters inside the outermost one are parameters. *)
Lemma tele_split_ass : forall Θ B Θ'' τ, tele_ass Θ -> tele_split (rev Θ) = inl (B, Θ'', τ) -> tele_ass Θ''.
Proof.
  intros * Ha Hs.
  destruct (List.exists_last (l := Θ)) as (Θ0 & e & ->); [ intros ->; discriminate |].
  apply List.Forall_app in Ha as [Ha0 He]; inversion He as [| ? ? [X ->] _]; subst.
  rewrite rev_app_distr in Hs; cbn in Hs; injection Hs as _ <- _; rewrite rev_involutive; exact Ha0.
Qed.

Lemma udenote_is_mod : forall Θ Ξ Γ o U R, udenote Θ Ξ Γ o U R -> ds_is_mod R.
Proof.
  intros * Hu; inversion Hu; subst;
    [ match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ =>
        destruct sm, o; cbn in Hb; try discriminate; injection Hb as <-; exact I end |].
  match goal with Hm : ds_mod _ _ _ = Some _ |- _ =>
    destruct R0 as [| | | ? p kd ?]; cbn in Hm; try discriminate; try (injection Hm as <-; exact I);
    destruct (ind_lookup Θ Ξ p) as [D |]; [| discriminate ];
    destruct (ind_mpath D kd) as [pm |]; [| discriminate ];
    destruct (gc_body Θ Ξ pm) as [[? ?] |]; [ injection Hm as <-; exact I | discriminate ] end.
Qed.

Lemma ds_is_mod_mod : forall Θ Ξ R, ds_is_mod R -> ds_mod Θ Ξ R = Some R.
Proof. intros * H; destruct R; cbn in *; tauto. Qed.

(** The module part of a member of a group: the module stored at the
    member's path. *)
Lemma ds_mod_ind_inv : forall Θ Ξ Θ' pq k Ns R, ds_mod Θ Ξ (ds_ind Θ' pq k Ns) = Some R ->
    exists D pm T Φ, ind_lookup Θ Ξ pq = Some D /\ ind_mpath D k = Some pm /\ gc_body Θ Ξ pm = Some (T, Φ) /\
      R = ds_closed Θ' pm T Φ Ns.
Proof.
  intros * Hm; cbn in Hm.
  destruct (ind_lookup Θ Ξ pq) as [D |] eqn:Hl; [| discriminate ].
  destruct (ind_mpath D k) as [pm |] eqn:Hp; [| discriminate ].
  destruct (gc_body Θ Ξ pm) as [[T Φ] |] eqn:Hb; [| discriminate ].
  injection Hm as <-; exists D, pm, T, Φ; repeat split; assumption.
Qed.

(** "R at N" is defined where an application of a module is typed: a
    module part with a parameter left. *)
Lemma ds_at_total : forall Θ Ξ R T B T1 N,
    ds_mtele Θ Ξ R = Some T -> tele_view T = Some (B, T1) -> exists R', ds_at R N = Some R'.
Proof.
  intros * Ht Hv; destruct R as [A om | Δ Φ | Θ0 ? T0 Φ Ns | Θ0 p kd Ns]; cbn in *.
  - discriminate.
  - injection Ht as ->; unfold tele_view in Hv; destruct (tele_open_split _ _ _ Hv) as (τ & ->); eauto.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; eauto.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; eauto.
Qed.

(** An application keeps the module part. *)
Lemma ds_at_mod : forall Θ Ξ R N R' Rm, ds_mod Θ Ξ R = Some Rm -> ds_at R N = Some R' -> exists Rm', ds_mod Θ Ξ R' = Some Rm'.
Proof.
  intros * Hm Ha; destruct R as [A om | Δ Φ | Θ0 ? T0 Φ Ns | Θ0 p kd Ns]; cbn in Hm, Ha; try discriminate.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?]; [ injection Ha as <-; eexists; reflexivity | discriminate ].
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; eexists; reflexivity.
  - destruct (ind_lookup Θ Ξ p) as [D |] eqn:Hl; [| discriminate ].
    destruct (ind_mpath D kd) as [pm |] eqn:Hp; [| discriminate ].
    destruct (gc_body Θ Ξ pm) as [[T1 Φ1] |] eqn:Hb; [| discriminate ].
    destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; cbn; rewrite Hl, Hp, Hb; eexists; reflexivity.
Qed.

(** A slot's unit, read one binder further. *)
Lemma udenote_shift : forall Θ Ξ Γ e U R, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> gunit_scoped (length Γ) U ->
    udenote Θ Ξ Γ None U R -> udenote Θ Ξ (e :: Γ) None (gunit_wk U ↑) (ds_sub R (ι ↑)).
Proof.
  intros * He HU Hu.
  pose proof (wf_wk_shift _ _ _ _ He) as Hφ.
  pose proof (wf_gctx_closed _ _ _ (ctx_decomp_tail He)) as Hc.
  rewrite <- gunit_sub_of_wk.
  eapply (proj1 (proj2 (mdenote_sub_all _ _ Hc))); [ exact Hu | exact (slots_ok_ctx _ (wf_ctx_scoped _ _ _ (ctx_decomp_tail He))) | left; exact HU |].
  apply wk_mod_compat_sub, (wf_wk_mod_compat _ _ _ _ _ Hφ).
Qed.

Definition slots_denote (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  forall x U, Γ ∋ #x ≔ₘ U -> exists R, udenote Θ Ξ Γ None U R.

Lemma slots_denote_cons : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> slots_denote Θ Ξ Γ ->
    (forall U, e = ce_mod U -> exists R, udenote Θ Ξ Γ None U R) -> slots_denote Θ Ξ (e :: Γ).
Proof.
  intros * He HΓ H0 x U Hl; inversion Hl; subst.
  - destruct (H0 _ eq_refl) as [R HR]; eexists; eapply udenote_shift; [ exact He | | exact HR ].
    destruct (ctx_decomp_mod He) as [_ HU]; destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (_ & HUs & _); exact HUs.
  - match goal with Hl0 : Γ ∋ # ?n ≔ₘ ?U0 |- _ =>
      destruct (HΓ _ _ Hl0) as [R HR]; eexists; eapply udenote_shift; [ exact He | | exact HR ];
      pose proof (ctx_scoped_lookup_mod _ _ _ 0 (wf_ctx_scoped _ _ _ (ctx_decomp_tail He)) Hl0) as Hs;
      rewrite Nat.add_0_r in Hs; exact Hs end.
Qed.


(** ** Applying Abstracted Descriptions *)

Lemma ctx_fn_app : forall T Δ M, ctx_fn (T ++ Δ) M = ctx_fn Δ (ctx_fn T M).
Proof. induction T as [| [] T IH]; intros; cbn; auto. Qed.

(** An abstracted description given its outermost parameter is the
    description substituted, abstracted over the rest. *)
Lemma ds_at_up : forall Θ'' B R N,
    ds_at (ds_up (Θ'' ++ ce_ass B :: nil) R) N =
    Some (ds_up (tele_sub Θ'' (Id,,N)) (ds_sub R (sb_qn (length Θ'') (Id,,N)))).
Proof.
  intros; destruct R as [A om | Δ Φ | Θ0 ? T Φ Ns | Θ0 p kd Ns]; cbn [ds_up ds_sub].
  - cbn [ds_at]; rewrite ctx_pi_app; cbn [ctx_pi pi_view].
    destruct om as [M |]; cbn [option_map].
    + rewrite ctx_fn_app; cbn [ctx_fn fn_view].
      rewrite ctx_pi_sub, ctx_fn_sub; reflexivity.
    + rewrite ctx_pi_sub; reflexivity.
  - cbn [ds_at]; rewrite List.app_assoc, rev_app_distr; cbn [rev List.app tele_split].
    rewrite rev_involutive, tele_sub_app, length_app; f_equal; f_equal;
      apply gmod_sub_sb_eq; rewrite sb_compose_id_left, sb_qn_plus; reflexivity.
  - cbn [ds_at]; rewrite List.app_assoc, rev_app_distr; cbn [rev List.app tele_split].
    rewrite rev_involutive, tele_sub_app, length_app.
    rewrite (map_sub_sb_eq Ns (Id ⨟ sb_qn (length Θ0 + length Θ'') (Id,,N)) (sb_qn (length Θ0) (sb_qn (length Θ'') (Id,,N))));
      [ reflexivity |].
    rewrite sb_compose_id_left, sb_qn_plus; reflexivity.
  - cbn [ds_at]; rewrite List.app_assoc, rev_app_distr; cbn [rev List.app tele_split].
    rewrite rev_involutive, tele_sub_app, length_app.
    rewrite (map_sub_sb_eq Ns (Id ⨟ sb_qn (length Θ0 + length Θ'') (Id,,N)) (sb_qn (length Θ0) (sb_qn (length Θ'') (Id,,N))));
      [ reflexivity |].
    rewrite sb_compose_id_left, sb_qn_plus; reflexivity.
Qed.

(** ** A Literal Given its Outermost Parameter *)

Lemma ds_up_nil : forall R, ds_up nil R = R.
Proof.
  intros [A [M |] | Δ Φ | Θ p T Φ Ns | Θ p kd Ns]; cbn; rewrite ?List.app_nil_r; reflexivity.
Qed.

Lemma ds_up_cat : forall A B R, ds_up (A ++ B) R = ds_up B (ds_up A R).
Proof.
  intros A B [A0 om | Δ Φ | Θ p T Φ Ns | Θ p kd Ns]; cbn; rewrite ?List.app_assoc; try reflexivity.
  rewrite ctx_pi_app; f_equal; destruct om; cbn; [ rewrite ctx_fn_app |]; reflexivity.
Qed.

(** A unit of the context after [Δ], abstracted over [Δ]. *)
Lemma udenote_abs : forall Θ Ξ Γ Δ U R, udenote Θ Ξ (Δ ++ Γ) None U R -> udenote Θ Ξ Γ None (gunit_abs Δ U) (ds_up Δ R).
Proof.
  intros * Hu; inversion Hu; subst; cbn [gunit_abs].
  - match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => destruct sm; cbn in Hb; [ injection Hb as <- | discriminate ] end.
    eapply un_body; [ rewrite <- app_assoc; eassumption | reflexivity ].
  - rewrite <- ds_up_cat; eapply un_alias; [ rewrite <- app_assoc; eassumption | eassumption ].
Qed.

Lemma sub_mod_compat_single : forall Γ X N, sub_mod_compat (Id,,N) Γ (ce_ass X :: Γ).
Proof.
  intros * x U Hl; inversion Hl; subst; right; eexists; split; [ reflexivity |].
  rewrite gunit_sub_shift_extend, gunit_sub_id; assumption.
Qed.

(** A unit read with its outermost parameter in the context. *)
Lemma udenote_last : forall Θ Ξ Γ Δ X D R,
    udenote Θ Ξ Γ None (gu_mk (Δ ++ ce_ass X :: nil) D) R ->
    exists R1, udenote Θ Ξ (ce_ass X :: Γ) None (gu_mk Δ D) R1 /\ R = ds_up (ce_ass X :: nil) R1.
Proof.
  intros * Hu; inversion Hu; subst.
  - match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => destruct sm; cbn in Hb; [| discriminate ]; injection Hb as <- end.
    exists (ds_open Δ Φ Φx); split; [ eapply un_body; [ rewrite <- List.app_assoc in *; eassumption | reflexivity ] | reflexivity ].
  - exists (ds_up Δ R'); split; [ eapply un_alias; [ rewrite <- List.app_assoc in *; eassumption | eassumption ] |].
    rewrite ds_up_cat; reflexivity.
Qed.

(** [β]: what the literal given an argument denotes is what the instantiated
    literal does. *)
Lemma udenote_beta : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ Δ X D N R,
    ctx_scoped 0 Γ -> gunit_scoped (length Γ) (gu_mk (Δ ++ ce_ass X :: nil) D) ->
    udenote Θ Ξ Γ None (gu_mk (Δ ++ ce_ass X :: nil) D) R ->
    exists R', ds_at R N = Some R' /\ udenote Θ Ξ Γ None (gu_mk Δ D)[Id,,N]ᵘ R'.
Proof.
  intros Θ Ξ Hc * HΓ HU Hu.
  destruct (udenote_last _ _ _ _ _ _ _ Hu) as (R1 & Hu1 & ->).
  rewrite gunit_scoped_mk, ctx_scoped_app, List.length_app in HU; destruct HU as [[HΔ HX] HD]; cbn in HX, HΔ.
  exists (ds_sub R1 (Id,,N)); split.
  - change (ce_ass X :: nil) with (nil ++ ce_ass X :: nil); rewrite ds_at_up; cbn [tele_sub sb_qn length].
    rewrite ds_up_nil; reflexivity.
  - eapply (proj1 (proj2 (mdenote_sub_all _ _ Hc))); [ exact Hu1 | apply (slots_ok_ctx (ce_ass X :: Γ)) | left | apply sub_mod_compat_single ].
    + cbn [ctx_scoped]; split; [ rewrite Nat.add_0_r; apply HX | exact HΓ ].
    + rewrite gunit_scoped_mk; cbn [length]; split; [ exact HΔ |].
      replace (length Δ + S (length Γ)) with (length Δ + 1 + length Γ) by lia; exact HD.
Qed.

(** Both sides of [β] denote one module. *)
Lemma mdenote_beta : forall Θ Ξ Γ Δ X D N,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) D ≈ gu_mk (Δ ++ ce_ass X :: nil) D ->
    forall R, udenote Θ Ξ Γ None (gu_mk (Δ ++ ce_ass X :: nil) D) R ->
    exists R', mdenote Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) R' /\
      mdenote Θ Ξ Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ) R' /\ ds_mod Θ Ξ R' = Some R'.
Proof.
  intros * HU R Hu.
  destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (HΓ & HUs & _).
  pose proof (wf_gctx_closed _ _ _ (presup_unit_eq_ctx HU)) as Hc.
  destruct (udenote_beta _ _ Hc _ _ _ _ N _ HΓ HUs Hu) as (R' & Ha & Hu').
  exists R'; split; [ eapply dn_app; [ apply dn_lit; exact Hu | exact Ha ] |].
  split; [ apply dn_lit; exact Hu' | apply ds_is_mod_mod; eapply udenote_is_mod; exact Hu' ].
Qed.


(** ** Typed Descriptions *)

Lemma tele_sub_closed : forall Δ σ, ctx_scoped 0 Δ -> tele_sub Δ σ = Δ.
Proof.
  intros * HΔ; rewrite (tele_scoped_sub_agree _ _ σ Id HΔ) by lia; apply tele_sub_id.
Qed.

Lemma gm_noopen_sub : forall Φ σ, gm_noopen Φ -> gm_noopen (gmod_sub Φ σ).
Proof. induction Φ; intros * H; cbn in *; auto. Qed.

Lemma gm_prefix_body_ctx : forall Φ y Φ1, gm_noopen Φ -> gm_prefix_upto Φ y = Some Φ1 ->
    exists Ψ, body_ctx Φ = Ψ ++ body_ctx Φ1.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * Hn Hp; cbn in Hn, Hp; [ discriminate | | contradiction ].
  destruct (String.eqb y x); [ injection Hp as <-; exists nil; reflexivity |].
  destruct (IH _ _ Hn Hp) as (Ψ & HΨ).
  destruct E as [? ? ? [] | ? ? | ? ? ? ? | ? ? ? ?]; cbn; rewrite HΨ; eexists (_ :: Ψ); reflexivity.
Qed.

Lemma gens_append_noopen : forall gs Φ k, gm_noopen Φ -> gm_noopen (gens_append Φ k gs).
Proof.
  induction gs as [| g gs IH]; intros * Hn; cbn; [ exact Hn |].
  destruct (ig_entry g); apply IH; exact Hn.
Qed.

Lemma body_xp_result_noopen : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> gm_noopen Φx.
Proof. induction 1; cbn; auto using gens_append_noopen. Qed.

(** ** Closed Telescopes and Their Outermost Parameters *)

Lemma wf_sub_to_nil : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id : ⋅.
Proof.
  intros * HΓ; econstructor; [ exact HΓ | constructor; eapply ctx_wf_gctx; exact HΓ | | |];
    intros * Hl; inversion Hl.
Qed.

(** A closed telescope well formed over nothing is so over any context. *)
Lemma closed_tele_wf : forall Θ Ξ T Γ, ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ T ++ Γ.
Proof.
  intros * Hs HT HΓ.
  rewrite <- (tele_sub_closed T Id Hs).
  eapply ctx_sub_wf_gen; [ exact (wf_sub_to_nil _ _ _ HΓ) | rewrite List.app_nil_r; exact HT ].
Qed.

Lemma tele_view_ass : forall T B T', tele_ass T -> tele_view T = Some (B, T') -> T = T' ++ ce_ass B :: nil.
Proof.
  intros * Ha Hv; unfold tele_view in Hv.
  destruct (rev T) as [| e R] eqn:Er; [ discriminate |].
  assert (Ha' : tele_ass (rev T)) by (apply List.Forall_rev; exact Ha).
  rewrite Er in Ha'; inversion Ha' as [| ? ? [A HA] _]; subst e.
  cbn in Hv; injection Hv as <- <-.
  rewrite <- (rev_involutive T), Er; reflexivity.
Qed.

(** The outermost assumption of a telescope extended inside by more. *)
Lemma tele_open_app_inl : forall R1 R2 B T τ, tele_split R1 = inl (B, T, τ) ->
    exists T', tele_open (R1 ++ R2) = Some (B, T').
Proof.
  induction R1 as [| [B0 | B0 N | U] R1 IH]; intros * Hs; cbn in Hs |- *; try discriminate.
  - injection Hs as <- <- <-; eauto.
  - destruct (tele_split R1) as [[[B' T'] τ'] |] eqn:E; [| discriminate ]; injection Hs as <- <- <-.
    destruct (IH R2 _ _ _ eq_refl) as (T'' & ->); eauto.
  - destruct (tele_split R1) as [[[B' T'] τ'] |] eqn:E; [| discriminate ]; injection Hs as <- <- <-.
    destruct (IH R2 _ _ _ eq_refl) as (T'' & ->); eauto.
Qed.

Lemma tele_open_app_inr : forall R1 R2 τ B T, tele_split R1 = inr τ -> tele_open (R1 ++ R2) = Some (B, T) ->
    exists B0 T0, tele_open R2 = Some (B0, T0) /\ B = B0[τ].
Proof.
  induction R1 as [| [B0 | B0 N | U] R1 IH]; intros * Hs Ho; cbn in Hs, Ho |- *; try discriminate.
  - injection Hs as <-; exists B, T; split; [ exact Ho | symmetry; apply exp_sub_id ].
  - destruct (tele_split R1) as [[[B' T'] τ'] | τ'] eqn:E; [ discriminate |]; injection Hs as <-.
    destruct (tele_open (R1 ++ R2)) as [[B1 T1] |] eqn:Ho1; [| discriminate ]; injection Ho as <- _.
    destruct (IH _ _ _ _ eq_refl Ho1) as (B2 & T2 & HR2 & ->); exists B2, T2; split; [ exact HR2 | apply exp_sub_sub ].
  - destruct (tele_split R1) as [[[B' T'] τ'] | τ'] eqn:E; [ discriminate |]; injection Hs as <-.
    destruct (tele_open (R1 ++ R2)) as [[B1 T1] |] eqn:Ho1; [| discriminate ]; injection Ho as <- _.
    destruct (IH _ _ _ _ eq_refl Ho1) as (B2 & T2 & HR2 & ->); exists B2, T2; split; [ exact HR2 | apply exp_sub_sub ].
Qed.

(** The module of a member of a group of inductive types is over the
    group's uniform parameters. *)
Lemma ind_mlookup_uparams : forall Θ Ξ p pq k D, ind_mlookup Θ Ξ p = Some (pq, k, D) ->
    gc_module Θ Ξ p = Some (mr_body (ind_uparams D) (Some (pq, k, D))).
Proof.
  intros * Hl; destruct (ind_mlookup_module _ _ _ _ Hl) as [T Hm].
  rewrite Hm; unfold gc_module, gc_module_u in Hm.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | |].
  - destruct (gm_submodule_entry _ _ _ _ _ _ _ _ Hm) as (pv & Φ' & He).
    rewrite (gm_entry_submodule _ (gu_params U ++ T0) _ _ _ _ _ _ _ He) in Hm; injection Hm as ->; reflexivity.
  - destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; cbn in Hm; [ discriminate |].
    destruct (gm_submodule_entry _ _ _ _ _ _ _ _ Hm) as (pv & Φ' & He).
    rewrite (gm_entry_submodule _ (gu_params U) _ _ _ _ _ _ _ He) in Hm; injection Hm as ->; reflexivity.
Qed.

Lemma ind_mlookup_gc_body : forall Θ Ξ p pq k D T Φ, ind_mlookup Θ Ξ p = Some (pq, k, D) ->
    gc_body Θ Ξ p = Some (T, Φ) -> T = ind_uparams D.
Proof.
  intros * Hl Hb; destruct (gc_body_module _ _ _ _ _ Hb) as [oD Hm].
  rewrite (ind_mlookup_uparams _ _ _ _ _ _ Hl) in Hm; injection Hm as -> _; reflexivity.
Qed.



(** A closed module or an inductive type with no outside parameter records
    its arguments. *)
Lemma ds_ats_closed_nil : forall Ns p T Φ Ms, ds_ats (ds_closed nil p T Φ Ms) Ns = Some (ds_closed nil p T Φ (Ms ++ Ns)).
Proof.
  induction Ns as [| N Ns IH]; intros; cbn; [ rewrite List.app_nil_r; reflexivity |].
  rewrite (List.map_ext _ (fun M => M) exp_sub_id), List.map_id, IH, <- List.app_assoc; reflexivity.
Qed.

Lemma ds_ats_ind_nil : forall Ns p k Ms, ds_ats (ds_ind nil p k Ms) Ns = Some (ds_ind nil p k (Ms ++ Ns)).
Proof.
  induction Ns as [| N Ns IH]; intros; cbn; [ rewrite List.app_nil_r; reflexivity |].
  rewrite (List.map_ext _ (fun M => M) exp_sub_id), List.map_id, IH, <- List.app_assoc; reflexivity.
Qed.

(** ** What a Filed Module Denotes *)

Lemma mdenote_apps : forall Θ Ξ Γ Ns H R R', mdenote Θ Ξ Γ H R -> ds_ats R Ns = Some R' ->
    mdenote Θ Ξ Γ (me_apps H Ns) R'.
Proof.
  induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha |- *; [ injection Ha as <-; exact Hm |].
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  eapply IH; [ eapply dn_app; eassumption | exact Ha ].
Qed.

(** A stored module, a body or the module of a member of a group of
    inductive types, is denoted by its path: its module part is the stored
    body at the path. *)
Lemma qname_mod_denote : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ Γ, loc Θ Ξ p T Φ ->
    exists R, mdenote Θ Ξ Γ (qname_mod p) R /\
      (R = ds_closed nil p T Φ nil \/
       (exists pq k D, R = ds_ind nil pq k nil /\ gc_body Θ Ξ p = Some (T, Φ) /\ ind_mlookup Θ Ξ p = Some (pq, k, D))).
Proof.
  intros Θ Ξ Hg * Hl.
  destruct Hl as [Hl | Hl].
  - exists (ds_closed nil p T Φ nil); split; [ apply (mdenote_of_loc _ _ Hg _ p); [ apply mod_qname_qname_mod | left; exact Hl ] |].
    left; reflexivity.
  - destruct (gc_body_module _ _ _ _ _ Hl) as [[[[pq k] D] |] Hm].
    + assert (Hi : ind_mlookup Θ Ξ p = Some (pq, k, D)) by (rewrite ind_mlookup_unfold, Hm; reflexivity).
      destruct (ind_mparent _ _ Hg _ _ _ _ Hi) as (mq & y & Tq & Φq & pv & Φ' & -> & Hlq & He).
      exists (ds_ind nil pq k nil); split; [| right; exists pq, k, D; split; [ reflexivity | split; [ exact Hl | exact Hi ] ] ].
      rewrite qname_mod_in.
      pose proof (proj2 (loc_closed _ _ Hg _ _ _ (loc_mod_loc _ _ _ _ _ Hlq))) as Hc.
      destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ Hc) He) as (Φ0 & Hp).
      eapply dn_mem; [ exact (mdenote_of_loc _ _ Hg _ _ _ _ Γ (mod_qname_qname_mod mq) Hlq) | reflexivity
                     | cbn; rewrite Hp; reflexivity | constructor | reflexivity ].
    + exists (ds_closed nil p T Φ nil); split; [ apply (mdenote_of_loc _ _ Hg _ p); [ apply mod_qname_qname_mod | right; split; assumption ] |].
      left; reflexivity.
Qed.

Lemma filed_denote : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ Γ Ns, gc_loc Θ Ξ p = Some (T, Φ) ->
    exists R, mdenote Θ Ξ Γ (me_apps (qname_mod p) Ns) R /\ ds_mod Θ Ξ R = Some (ds_closed nil p T Φ Ns).
Proof.
  intros Θ Ξ Hg * Hgl.
  assert (Hl : loc Θ Ξ p T Φ) by (unfold gc_loc in Hgl; destruct (gc_frame Ξ p) eqn:E;
    [ injection Hgl as ->; left; exact E | right; exact Hgl ]).
  destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hl) as (R & Hm & [-> | (pq & k & D & -> & Hb & Hi)]).
  - exists (ds_closed nil p T Φ (nil ++ Ns)); split; [ eapply mdenote_apps; [ exact Hm | apply ds_ats_closed_nil ] | reflexivity ].
  - exists (ds_ind nil pq k (nil ++ Ns)); split; [ eapply mdenote_apps; [ exact Hm | apply ds_ats_ind_nil ] |].
    destruct (ind_mlookup_selfpath _ _ Hg _ _ _ _ Hi) as [Hp _ _].
    cbn; rewrite (ind_mlookup_group _ _ Hg _ _ _ _ Hi), Hp, Hb; reflexivity.
Qed.

(** ** Descriptions Read Where They Are Stored

    What a module expression denotes is read where it is: a local body is
    expanded, with no open left, and a closed module is the body stored at
    its path ([ds_canon]).  So the unit a module part stands for
    ([ds_unit]) denotes that module part again. *)

Definition ds_canon (Θ : gdeps) (Ξ : gstack) (R : mdesc) : Prop :=
  match R with
  | ds_open _ _ Φx => gm_noopen Φx
  | ds_closed _ p T Φ _ => loc Θ Ξ p T Φ
  | _ => True
  end.

Lemma ds_canon_mod : forall Θ Ξ R Rm, ds_canon Θ Ξ R -> ds_mod Θ Ξ R = Some Rm -> ds_canon Θ Ξ Rm.
Proof.
  intros * Hc Hm; destruct R as [A om | Δ Φ | Θ0 p T Φ Ns | Θ0 p kd Ns]; try (cbn in Hm |- *; discriminate);
    try (cbn in Hm |- *; injection Hm as <-; exact Hc).
  destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (D & pm & T & Φ & _ & _ & Hb & ->); right; exact Hb.
Qed.

Lemma ds_canon_at : forall Θ Ξ R N R', ds_canon Θ Ξ R -> ds_at R N = Some R' -> ds_canon Θ Ξ R'.
Proof.
  intros * Hc Ha; destruct R as [A om | Δ Φ | Θ0 p T Φ Ns | Θ0 p kd Ns]; cbn in Ha, Hc.
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; exact I.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?]; [ injection Ha as <-; cbn; apply gm_noopen_sub; exact Hc | discriminate ].
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; exact Hc.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
Qed.

Lemma ds_canon_ats : forall Θ Ξ Ns R R', ds_canon Θ Ξ R -> ds_ats R Ns = Some R' -> ds_canon Θ Ξ R'.
Proof.
  intros Θ Ξ; induction Ns as [| N Ns IH]; intros * Hc Ha; cbn in Ha; [ injection Ha as <-; exact Hc |].
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  exact (IH _ _ (ds_canon_at _ _ _ _ _ Hc E) Ha).
Qed.

Lemma ds_canon_up : forall Θ Ξ Θ' R, ds_canon Θ Ξ R -> ds_canon Θ Ξ (ds_up Θ' R).
Proof. intros * Hc; destruct R; exact Hc. Qed.

Lemma ds_canon_sub : forall Θ Ξ R σ, ds_canon Θ Ξ R -> ds_canon Θ Ξ (ds_sub R σ).
Proof. intros * Hc; destruct R; cbn in *; try exact Hc; apply gm_noopen_sub; exact Hc. Qed.

Lemma ds_canon_read : forall Θ Ξ rd R R', ds_canon Θ Ξ R -> ds_read rd R = Some R' -> ds_canon Θ Ξ R'.
Proof.
  intros Θ Ξ [Δ Φ' | Θ' Ns M] * Hc Hr; cbn in Hr.
  - destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
    apply ds_canon_up, ds_canon_sub; exact Hc.
  - destruct (ds_ats R Ns) as [R1 |] eqn:E; cbn in Hr; [ injection Hr as <- | discriminate ].
    apply ds_canon_up; pose proof (ds_canon_ats _ _ _ _ _ Hc E) as H1;
      apply ds_named_cases; destruct R1 as [? [] | | |]; exact H1.
Qed.

Lemma body_xp_noopen_refl : forall Θ Ξ Γ Φ, gm_noopen Φ -> body_xp Θ Ξ Γ Φ Φ.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros HΦ; cbn in HΦ; [ constructor | constructor; apply IH, HΦ | contradiction ].
Qed.

Lemma body_xp_noopen_id : forall Θ Ξ Γ Φ Φx, gm_noopen Φ -> body_xp Θ Ξ Γ Φ Φx -> Φx = Φ.
Proof.
  intros * HΦ Hx; revert HΦ; induction Hx; intros HΦ; cbn in HΦ; [ reflexivity | | contradiction ].
  rewrite IHHx by exact HΦ; reflexivity.
Qed.

Theorem mdenote_canon_all : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> ds_canon Θ Ξ R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R ->
       (forall qq Δ Φ, o = Some qq -> U = gu_mk Δ (md_body sm_closed Φ) -> loc Θ Ξ qq Δ Φ) -> ds_canon Θ Ξ R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R ->
       (forall qq pv Δ Φ, o = Some qq -> E = ge_mod pv (gu_mk Δ (md_body sm_closed Φ)) -> loc Θ Ξ qq Δ Φ) -> ds_canon Θ Ξ R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> True) /\
    (forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> True).
Proof.
  intros Θ Ξ Hg; apply mdenote_all_ind; intros; try exact I.
  - (* a loaded unit or an open frame *)
    match goal with Hu : gc_unit _ _ _ = Some _ |- _ => destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl) end.
    match goal with Hq0 : mod_qname _ = Some _ |- _ => rewrite Hq0 in Hq; injection Hq as <- end; exact Hl.
  - (* a slot *) match goal with IH : (forall qq Δ Φ, None = Some qq -> _) -> _ |- _ => apply IH; discriminate end.
  - (* a literal *) match goal with IH : (forall qq Δ Φ, None = Some qq -> _) -> _ |- _ => apply IH; discriminate end.
  - (* an application *) eapply ds_canon_at; eassumption.
  - (* a selection *)
    rename H0 into IH0, e into Hmod, e0 into He, H1 into IHe, e2 into Hr.
    pose proof (ds_canon_mod _ _ _ _ IH0 Hmod) as Hc.
    eapply ds_canon_read; [| exact Hr ].
    apply IHe; intros qq pv Δ Φ1 Ho HE; subst E.
    destruct R0m as [A om | Δ0 Φ0 | Θ0 p T Φ Ns | Θ0 p kd Ns]; cbn in He, Ho; try discriminate.
    injection Ho as <-.
    destruct (gm_prefix_upto Φ y) as [[| Φ' x E0 | Φ' H0 its] |] eqn:Hp; try discriminate; injection He as _ HE _.
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E1 & [= <- <- <-] & Hen).
    destruct E0 as [| pv0 [Δ1 [[|] Φ2 | E2]] | | ]; cbn in HE; try discriminate.
    injection HE as <- <- <-.
    destruct (loc_child_mod _ _ Hg _ _ _ Hc _ _ _ _ _ Hen) as [Hb _]; right; exact Hb.
  - (* a body *)
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => rename Hb into Hds end.
    match goal with Hx : body_xp _ _ _ _ _ |- _ => rename Hx into Hbx end.
    match goal with Hs : forall qq Δ Φ, _ -> _ -> loc _ _ _ _ _ |- _ => rename Hs into Hst end.
    destruct sm; cbn in Hds.
    + injection Hds as <-; exact (body_xp_result_noopen _ _ _ _ _ Hbx).
    + destruct o as [qq |]; cbn in Hds; [ injection Hds as <- | discriminate ].
      pose proof (Hst qq Δ Φ eq_refl eq_refl) as Hl.
      pose proof (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hl))) as Hn.
      rewrite (body_xp_noopen_id _ _ _ _ _ Hn Hbx); exact Hl.
  - (* an alias *)
    apply ds_canon_up; eapply ds_canon_mod; eassumption.
  - (* a module *)
    match goal with IH : (forall qq Δ Φ, _ -> _ -> _) -> ds_canon _ _ _, Hs : forall qq pv Δ Φ, _ -> _ -> _ |- _ =>
      apply IH; intros qq Δ Φ Ho HU; subst; exact (Hs qq _ Δ Φ eq_refl eq_refl) end.
Qed.

Lemma mdenote_canon : forall Θ Ξ Γ H R, ⊢ᵍ Θ ⍮ Ξ -> mdenote Θ Ξ Γ H R -> ds_canon Θ Ξ R.
Proof. intros * Hg Hm; exact (proj1 (mdenote_canon_all _ _ Hg) _ _ _ Hm). Qed.

(** ** Local Bodies Read Where They Are

    The expansion an open description carries is the expansion of its
    written body where the description is read ([ds_xp]): so the literal
    of the written body denotes the description again ([ds_unit_denote]). *)

Definition ds_xp (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (R : mdesc) : Prop :=
  match R with
  | ds_open Δ Φ Φx => body_xp Θ Ξ (Δ ++ Γ) Φ Φx
  | _ => True
  end.

Lemma ds_scoped_mono : forall R n m, n <= m -> ds_scoped n R -> ds_scoped m R.
Proof.
  intros [A om | Δ Φ Φx | Θ0 ? T Φ Ns0 | Θ0 p Ns0] * Hnm HR; cbn in *.
  - destruct HR as [HA Hom]; split; [ eapply exp_scoped_mono; [| exact HA ]; lia |].
    destruct om; cbn in *; [ eapply exp_scoped_mono; [| exact Hom ]; lia | exact I ].
  - destruct HR as [HR1 HR2]; split; [ eapply gunit_scoped_mono; [| exact HR1 ] | eapply gunit_scoped_mono; [| exact HR2 ] ]; lia.
  - destruct HR as (HΘ0 & HU & HNs0); split; [ eapply ctx_scoped_mono'; [| exact HΘ0 ]; lia | split; [ exact HU |] ].
    eapply List.Forall_impl; [| exact HNs0 ]; intros; eapply exp_scoped_mono; [| eassumption ]; lia.
  - destruct HR as (HΘ0 & HNs0); split; [ eapply ctx_scoped_mono'; [| exact HΘ0 ]; lia |].
    eapply List.Forall_impl; [| exact HNs0 ]; intros; eapply exp_scoped_mono; [| eassumption ]; lia.
Qed.

Lemma ds_xp_sub : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ R m Γ' σ,
    slots_ok m Γ -> ds_scoped m R -> ds_xp Θ Ξ Γ R -> sub_mod_compat σ Γ' Γ -> ds_xp Θ Ξ Γ' (ds_sub R σ).
Proof.
  intros Θ Ξ Hc Γ [| Δ Φ Φx | |] * HS HR Hx Hσ; cbn in *; try exact I.
  destruct HR as [HR _]; rewrite gunit_scoped_mk in HR; destruct HR as [HΔ [_ HΦ]].
  eapply (proj1 (proj2 (proj2 (proj2 (mdenote_sub_all _ _ Hc))))); [ exact Hx | apply slots_ok_app; eassumption | exact HΦ |].
  apply sub_mod_compat_ext; exact Hσ.
Qed.

Lemma ds_xp_at : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ R N R' m,
    slots_ok m Γ -> ds_scoped m R -> ds_xp Θ Ξ Γ R -> ds_at R N = Some R' -> ds_xp Θ Ξ Γ R'.
Proof.
  intros Θ Ξ Hc Γ [A om | Δ Φ Φx | Θ0 p T Φ Ns | Θ0 p kd Ns] N R' m HS HR Hx Ha; cbn in Ha.
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M) |]; try discriminate; injection Ha as <-; exact I.
  - destruct (tele_split (rev Δ)) as [[[B Δ'] τ] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn [ds_xp] in *.
    destruct HR as [HR _]; rewrite gunit_scoped_mk in HR; destruct HR as [HΔ [_ HΦ]].
    pose proof (tele_split_compat (rev Δ) Γ) as Hτ; rewrite E, rev_involutive in Hτ.
    eapply (proj1 (proj2 (proj2 (proj2 (mdenote_sub_all _ _ Hc))))); [ exact Hx | apply slots_ok_app; eassumption | exact HΦ |].
    eapply sub_mod_compat_compose; [ exact Hτ |].
    apply sub_mod_compat_ext, sub_mod_compat_single_term; intros; discriminate.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
Qed.

Lemma ds_xp_ats : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ Ns R R' m,
    slots_ok m Γ -> ds_scoped m R -> List.Forall (exp_scoped m) Ns -> ds_xp Θ Ξ Γ R -> ds_ats R Ns = Some R' -> ds_xp Θ Ξ Γ R'.
Proof.
  intros Θ Ξ Hc Γ; induction Ns as [| N Ns IH]; intros * HS HR HNs Hx Ha; cbn in Ha; [ injection Ha as <-; exact Hx |].
  inversion HNs; subst.
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  eapply IH; [ exact HS | eapply ds_at_scoped; eassumption | assumption | eapply ds_xp_at; eassumption | exact Ha ].
Qed.

Lemma ds_xp_up : forall Θ Ξ Γ Θ' R, ds_xp Θ Ξ (Θ' ++ Γ) R -> ds_xp Θ Ξ Γ (ds_up Θ' R).
Proof. intros * Hx; destruct R; cbn in *; try exact I; rewrite <- List.app_assoc; exact Hx. Qed.

Lemma ds_xp_mod : forall Θ Ξ Γ R Rm, ds_xp Θ Ξ Γ R -> ds_mod Θ Ξ R = Some Rm -> ds_xp Θ Ξ Γ Rm.
Proof.
  intros * Hx Hm; destruct R as [| | | Θ0 p kd Ns]; try (cbn in Hm; discriminate); try (cbn in Hm; injection Hm as <-; exact Hx).
  destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (? & ? & ? & ? & _ & _ & _ & ->); exact I.
Qed.

Lemma ds_xp_self : forall Θ Ξ Γ M R, ds_xp Θ Ξ Γ R -> ds_xp Θ Ξ Γ (ds_self M R).
Proof. intros * Hx; destruct R as [? [] | | |]; exact Hx. Qed.

Lemma ds_xp_named : forall Θ Ξ Γ Θ' Ns M R, ds_xp Θ Ξ Γ R -> ds_xp Θ Ξ Γ (ds_named Θ' Ns M R).
Proof. intros * Hx; apply ds_named_cases; [ exact Hx | apply ds_xp_self; exact Hx ]. Qed.

Theorem mdenote_xp_all : forall Θ Ξ, gctx_closed Θ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> forall m, slots_ok m Γ -> modexp_scoped m H -> ds_xp Θ Ξ Γ R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> forall m, slots_ok m Γ ->
       (gunit_scoped m U \/ exists T Φ, U = gu_body T Φ /\ unit_closed T Φ) -> ds_xp Θ Ξ Γ R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> forall m, slots_ok m Γ -> entry_sc m E -> ds_xp Θ Ξ Γ R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> True) /\
    (forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> True).
Proof.
  intros Θ Ξ Hc; pose proof (mdenote_scoped_all _ _ Hc) as (Hsm & Hsu & Hse & _).
  apply mdenote_all_ind; intros; try exact I.
  - (* a slot *)
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> _, HΓ : slots_ok ?m ?Γ, Hl : ?Γ ∋ # ?x ≔ₘ _,
                    Hx : modexp_scoped _ (me_var _) |- _ =>
      cbn in Hx; apply (IH m HΓ); left; exact (HΓ _ _ Hx Hl) end.
  - (* a literal *)
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> _ |- _ => eapply IH; [ eassumption | left; cbn in *; assumption ] end.
  - (* an application *)
    rename H0 into IH, e into Ha, H1 into HS, H2 into HH; cbn in HH; destruct HH as [HH HN].
    eapply ds_xp_at; [ exact Hc | exact HS | eapply Hsm; eassumption | eapply IH; eassumption | exact Ha ].
  - (* a selection *)
    rename H0 into IH0, e into Hmod, e0 into He, H1 into IHe; rename H2 into HS, H3 into HH; cbn in HH.
    match goal with Hr0 : ds_read _ _ = Some _ |- _ => rename Hr0 into Hr end.
    match goal with Hm0 : mdenote _ _ _ H R0 |- _ => rename Hm0 into Hd0 end.
    match goal with Hed : edenote _ _ _ _ E R |- _ => rename Hed into Hde end.
    pose proof (ds_mod_scoped _ _ _ _ _ Hc (Hsm _ _ _ Hd0 _ HS HH) Hmod) as HR0m.
    destruct (ds_entry_scoped _ _ _ _ _ _ HR0m He) as (HΓy & HE & Hrd).
    assert (HSy : slots_ok (length Γy + m0) (Γy ++ Γ)) by (apply slots_ok_app; assumption).
    pose proof (IHe _ HSy HE) as Hx.
    pose proof (Hse _ _ _ _ Hde _ HSy HE) as HRs.
    destruct rd as [Δ Φ' | Θ0 Ns M]; cbn in Hr.
    + destruct Hrd as (-> & HΔ & HΦ').
      destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [| discriminate ]; injection Hr as <-.
      apply ds_xp_up.
      eapply ds_xp_sub; [ exact Hc | exact HSy | exact HRs | exact Hx |].
      rewrite <- List.app_assoc; apply sub_mod_compat_fill; exact Hf.
    + destruct Hrd as (-> & HΘ0 & HNs & HM); cbn [List.app length] in *.
      destruct (ds_ats R Ns) as [R1 |] eqn:Ea; cbn in Hr; [| discriminate ]; injection Hr as <-.
      apply ds_xp_up, ds_xp_named.
      (* a closed entry: closed, read under the outside parameters *)
      destruct R0m as [| | Θa pa Ta Φa Nsa |]; cbn in He; try discriminate;
        [ destruct (gm_prefix_upto _ y) as [[| ? ? [[|] ? ? [] | | | ] | ] |]; discriminate |].
      destruct HR0m as (_ & HU0 & _).
      destruct (ds_entry_closed _ _ _ _ _ _ _ _ _ HU0 He) as (_ & HE0 & _).
      assert (HR0 : ds_scoped 0 R) by (eapply Hse; [ exact Hde | intros ? ? Hx0; lia | exact HE0 ]).
      assert (Hw : ds_xp Θ Ξ (Θ0 ++ Γ) R).
      { rewrite <- (ds_closed_sub R (ι (wk_shiftn (length Θ0))) HR0).
        eapply (ds_xp_sub _ _ Hc _ _ 0); [ intros ? ? Hlt; exfalso; lia | exact HR0 | exact Hx |].
        apply wk_mod_compat_sub; intros x U Hl.
        replace (wk_shiftn (length Θ0) x) with (x + length Θ0) by reflexivity.
        apply ctx_lookup_mod_app_r; exact Hl. }
      eapply ds_xp_ats; [ exact Hc | apply slots_ok_app; eassumption | eapply ds_scoped_mono; [| exact HR0 ]; lia | exact HNs | exact Hw | exact Ea ].
  - (* a body *)
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => destruct sm, o; cbn in Hb; try discriminate; injection Hb as <- end;
      first [ assumption | exact I ].
  - (* an alias *)
    match goal with Hu : gunit_scoped _ _ \/ _ |- _ => destruct Hu as [HU | (T & Φ0 & [=] & _)] end.
    rewrite gunit_scoped_mk in HU; destruct HU as [HΔ HE]; cbn in HE.
    apply ds_xp_up; eapply ds_xp_mod; [| eassumption ].
    match goal with IH : forall m, slots_ok m (_ ++ _) -> _ -> _ |- _ => eapply IH end;
      [ apply slots_ok_app; eassumption | exact HE ].
  - (* a module *)
    match goal with IH : forall m, slots_ok m _ -> _ -> _ |- _ => eapply IH; [ eassumption |] end.
    cbn in *; assumption.
Qed.

Corollary mdenote_xp : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Γ H R, mdenote Θ Ξ Γ H R -> ctx_scoped 0 Γ -> modexp_scoped (length Γ) H -> ds_xp Θ Ξ Γ R.
Proof. intros * Hc * Hm HΓ HH; exact (proj1 (mdenote_xp_all _ _ Hc) _ _ _ Hm _ (slots_ok_ctx _ HΓ) HH). Qed.

(** What a well-formed module expression denotes is read where it is. *)
Lemma wf_mdenote_xp : forall Θ Ξ Γ H H' R,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> ds_xp Θ Ξ Γ R.
Proof.
  intros * HH Hm; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  eapply (proj1 (mdenote_xp_all _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)))); [ exact Hm | apply slots_ok_ctx, HΓ | exact HHs ].
Qed.

Lemma wf_mdenote_mod_xp : forall Θ Ξ Γ H H' R Rm,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> ds_mod Θ Ξ R = Some Rm -> ds_xp Θ Ξ Γ Rm.
Proof. intros * HH Hm Hd; eapply ds_xp_mod; [ eapply wf_mdenote_xp; eassumption | exact Hd ]. Qed.

Lemma ds_mod_is_mod : forall Θ Ξ R Rm, ds_mod Θ Ξ R = Some Rm -> ds_is_mod Rm.
Proof.
  intros * Hm; destruct R as [| | | Θ0 p kd Ns]; try (cbn in Hm; discriminate); try (cbn in Hm; injection Hm as <-; exact I).
  destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (? & ? & ? & ? & _ & _ & _ & ->); exact I.
Qed.

Lemma ds_is_mod_up : forall Θ' R, ds_is_mod R -> ds_is_mod (ds_up Θ' R).
Proof. intros * H; destruct R; cbn in *; tauto. Qed.

Lemma ds_at_is_mod : forall R N R', ds_is_mod R -> ds_at R N = Some R' -> ds_is_mod R'.
Proof.
  intros * Hm Ha; destruct R as [| Δ Φ | Θ p T Φ Ns |]; cbn in Hm, Ha; try contradiction.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] |]; [ injection Ha as <-; exact I | discriminate ].
  - destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
Qed.

Lemma ds_ats_is_mod : forall Ns R R', ds_is_mod R -> ds_ats R Ns = Some R' -> ds_is_mod R'.
Proof.
  induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha; [ injection Ha as <-; exact Hm |].
  destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
  exact (IH _ _ (ds_at_is_mod _ _ _ Hm E) Ha).
Qed.

(** Reading a term as a name changes nothing else. *)
Lemma ds_self_mod : forall M R, ds_is_mod R -> ds_self M R = R.
Proof. intros M [] H; cbn in H; first [ contradiction | reflexivity ]. Qed.

Lemma ds_at_ind : forall Θ' p k Ns N R', ds_at (ds_ind Θ' p k Ns) N = Some R' -> exists Θ'' Ns', R' = ds_ind Θ'' p k Ns'.
Proof.
  intros * Ha; cbn in Ha; destruct (tele_split (rev Θ')) as [[[? ?] ?] | ?]; injection Ha as <-; eauto.
Qed.

Lemma ds_ats_ind : forall Ns Θ' p k Ms R', ds_ats (ds_ind Θ' p k Ms) Ns = Some R' -> exists Θ'' Ns', R' = ds_ind Θ'' p k Ns'.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn [ds_ats] in Ha; [ injection Ha as <-; eauto |].
  destruct (ds_at (ds_ind Θ' p k Ms) N) as [R1 |] eqn:E; [| discriminate ].
  destruct (ds_at_ind _ _ _ _ _ _ E) as (? & ? & ->); exact (IH _ _ _ _ _ Ha).
Qed.

(** The unit a module part stands for denotes it. *)
Lemma ds_unit_denote : forall Θ Ξ Rm, ⊢ᵍ Θ ⍮ Ξ -> ds_canon Θ Ξ Rm -> ds_is_mod Rm ->
    forall Γ, ds_xp Θ Ξ Γ Rm -> exists R, mdenote Θ Ξ Γ (ds_unit Rm) R /\ ds_mod Θ Ξ R = Some Rm.
Proof.
  intros * Hg Hc Hm Γ Hx; destruct Rm as [A om | Δ Φ Φx | [| e Θ'] p T Φ Ns | Θ0 p kd Ns]; cbn in Hm, Hc, Hx |- *; try contradiction.
  - exists (ds_open Δ Φ Φx); split; [| reflexivity ].
    apply dn_lit; eapply un_body; [ exact Hx | reflexivity ].
  - exact (filed_denote _ _ Hg _ _ _ Γ Ns (gc_loc_of_loc _ _ Hg _ _ _ Hc)).
  - destruct (filed_denote _ _ Hg _ _ _ ((e :: Θ') ++ Γ) Ns (gc_loc_of_loc _ _ Hg _ _ _ Hc)) as (R & HR & HRm).
    exists (ds_up (e :: Θ') (ds_closed nil p T Φ Ns)); split; [ apply dn_lit; eapply un_alias; eassumption | reflexivity ].
Qed.

Theorem denote_exists :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     slots_denote Θ Ξ Γ /\ slots_denote Θ Ξ (Ψ ++ Γ) /\ slots_denote Θ Ξ (Ψ' ++ Γ)) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     slots_denote Θ Ξ Γ /\ (exists R, udenote Θ Ξ Γ None U R) /\ (exists R, udenote Θ Ξ Γ None U' R)) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     slots_denote Θ Ξ Γ /\
     (exists R Rm, mdenote Θ Ξ Γ H R /\ ds_mod Θ Ξ R = Some Rm) /\
     (exists R Rm, mdenote Θ Ξ Γ H' R /\ ds_mod Θ Ξ R = Some Rm)).
Proof.
  apply syntactic_wf_mut_ind; intros; destruct_conjs.
  (* the context of a judgment is the context of one of its premises *)
  all: try match goal with |- slots_denote _ _ ?G => solve [ assumption ] end.
  (* the empty context *)
  all: try solve [ intros x U Hl; inversion Hl ].
  (* context extensions *)
  all: try solve [ apply slots_denote_cons; [ econstructor; eassumption | assumption | first [ intros; discriminate | intros ? [= <-]; eauto ] ] ].
  all: try match goal with |- slots_denote _ _ _ /\ _ => split; [ assumption |] end.
  (* extensions of extensions *)
  all: try solve [ cbn [List.app]; split; (apply slots_denote_cons;
      [ first [ econstructor; eassumption | eapply wf_ctx_extend_mod; eapply wf_unit_eq_refl_left; eassumption ]
      | assumption | first [ intros; discriminate | intros ? [= <-]; eauto ] ]) ].
  all: try solve [
    match goal with Hm : mdenote _ _ _ ?H ?R, Ht : ds_mtele _ _ ?R = Some _
      |- (exists _ _, mdenote _ _ _ ?H _ /\ _) /\ (exists _ _, mdenote _ _ _ ?H _ /\ _) =>
        unfold ds_mtele in Ht; destruct (ds_mod _ _ R) as [Rm |] eqn:Hmd; [| discriminate ];
        split; exists R, Rm; split; assumption
    end ].
  all: try solve [ split; assumption ].
  all: try solve [ split; eexists; eassumption ].
  (* units *)
  all: try solve [ split; eexists; econstructor; solve [ eassumption | reflexivity ] ].
  (* an alias of a literal, and the literal over both telescopes *)
  all: try solve [
    match goal with HR : udenote _ _ _ None (gu_mk ?Δ' ?D) ?R
      |- (exists _, udenote _ _ _ _ (gu_mk ?Δ (md_alias (me_lit (gu_mk ?Δ' ?D)))) _) /\ _ =>
        split; [ eexists; eapply un_alias; [ apply dn_lit; exact HR | apply ds_is_mod_mod, (udenote_is_mod _ _ _ _ _ _ HR) ] |];
        change (gu_mk (Δ' ++ Δ) D) with (gunit_abs Δ (gu_mk Δ' D)); eexists; apply udenote_abs; exact HR
    end ].
  (* two module expressions denoting the same module *)
  all: try solve [
    match goal with
    | Hm : mdenote _ _ _ ?H ?R, Hm' : mdenote _ _ _ ?H' ?R, Hd : ds_mod _ _ ?R = Some ?Rm
      |- (exists _ _, mdenote _ _ _ ?H _ /\ _) /\ (exists _ _, mdenote _ _ _ ?H' _ /\ _) =>
        split; exists R, Rm; split; assumption
    end ].
  (* a unit *)
  all: try solve [ split; do 2 eexists; (split; [ econstructor; eassumption | reflexivity ]) ].
  (* a slot *)
  all: try solve [
    match goal with Hs : slots_denote _ _ _, Hl : _ ∋ # _ ≔ₘ _ |- _ => destruct (Hs _ _ Hl) as [R HR] end;
    split; exists R, R; (split; [ econstructor; eassumption | apply ds_is_mod_mod, (udenote_is_mod _ _ _ _ _ _ HR) ]) ].
  (* a literal *)
  all: try solve [
    match goal with HR : udenote _ _ _ _ ?U ?R, HR' : udenote _ _ _ _ ?U' ?R' |- (exists _ _, mdenote _ _ _ (me_lit ?U) _ /\ _) /\ (exists _ _, mdenote _ _ _ (me_lit ?U') _ /\ _) =>
      split; [ exists R, R | exists R', R' ];
      (split; [ econstructor; eassumption | apply ds_is_mod_mod; eapply udenote_is_mod; eassumption ]) end ].
  (* a unit or a selection: a module part with a telescope *)
  all: try solve [
    match goal with
    | Hm : mdenote _ _ _ ?H ?R, Ht : ds_mtele _ _ ?R = Some _, Hm' : mdenote _ _ _ ?H' ?R', Ht' : ds_mtele _ _ ?R' = Some _
      |- (exists _ _, mdenote _ _ _ ?H _ /\ _) /\ (exists _ _, mdenote _ _ _ ?H' _ /\ _) =>
        unfold ds_mtele in Ht, Ht';
        destruct (ds_mod _ _ R) as [Rm |] eqn:Hmd; [| discriminate ];
        destruct (ds_mod _ _ R') as [Rm' |] eqn:Hmd'; [| discriminate ];
        split; [ exists R, Rm | exists R', Rm' ]; split; assumption
    end ].
  (* an application *)
  all: try solve [
    match goal with
    | Hm : mdenote _ _ _ ?H ?R, Ht : ds_mtele _ _ ?R = Some ?T, Hv : tele_view ?T = Some _,
      Hm' : mdenote _ _ _ ?H' ?R', Ht' : ds_mtele _ _ ?R' = Some ?T', Hv' : tele_view ?T' = Some _
      |- (exists _ _, mdenote _ _ _ (me_app ?H ?N) _ /\ _) /\ (exists _ _, mdenote _ _ _ (me_app ?H' ?N') _ /\ _) =>
        destruct (ds_at_total _ _ _ _ _ _ N Ht Hv) as (R1 & Ha);
        destruct (ds_at_total _ _ _ _ _ _ N' Ht' Hv') as (R1' & Ha');
        unfold ds_mtele in Ht, Ht';
        destruct (ds_mod _ _ R) as [Rm |] eqn:Hmd; [| discriminate ];
        destruct (ds_mod _ _ R') as [Rm' |] eqn:Hmd'; [| discriminate ];
        destruct (ds_at_mod _ _ _ _ _ _ Hmd Ha) as (Rm1 & Hm1);
        destruct (ds_at_mod _ _ _ _ _ _ Hmd' Ha') as (Rm1' & Hm1');
        split; do 2 eexists; (split; [ econstructor; eassumption | eassumption ])
    end ].
  all: try solve [ split; do 2 eexists; split; eassumption ].
  (* a loaded unit or an open frame *)
  all: try solve [
    match goal with Hu : gc_unit _ _ ?H = Some ?TΦ |- _ =>
      destruct TΦ as [T Φ]; destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & _);
      split; exists (ds_closed nil mp T Φ nil), (ds_closed nil mp T Φ nil); (split; [ apply dn_unit; assumption | reflexivity ])
    end ].
  (* [β]: both sides denote one module *)
  all: try solve [
    match goal with HU : wf_unit_eq _ _ _ (gu_mk (?Δ ++ ce_ass ?X :: nil) ?D) _, HR : udenote _ _ _ None (gu_mk _ ?D) ?R
      |- (exists _ _, mdenote _ _ _ (me_app _ ?N) _ /\ _) /\ _ =>
        let Hb1 := fresh "Hb" in let Hb2 := fresh "Hb" in let Hb3 := fresh "Hb" in
        destruct (mdenote_beta _ _ _ _ _ _ N HU _ HR) as (R' & Hb1 & Hb2 & Hb3);
        rewrite gunit_sub_mk in Hb2; cbn [moddef_sub] in Hb2;
        split; exists R', R'; split; assumption
    end ].
  (* an alias with no parameter *)
  all: try solve [
    match goal with HE : mdenote _ _ _ ?E ?R, HEm : ds_mod _ _ ?R = Some ?Rm |- (exists _ _, mdenote _ _ _ (me_lit (gu_mk nil (md_alias ?E))) _ /\ _) /\ _ =>
      split; [ exists (ds_up nil Rm), (ds_up nil Rm); split; [ apply dn_lit; econstructor; eassumption |]
             | exists R, Rm; split; assumption ];
      rewrite ds_up_nil; apply ds_is_mod_mod; exact (ds_mod_is_mod _ _ _ _ HEm)
    end ].
  (* a selection: the unit its module part stands for *)
  all: try solve [
    match goal with Hm : mdenote _ _ ?G (me_mem ?H ?y) ?R, Hd : ds_mod _ _ ?R = Some ?Rm,
      HH : wf_modexp_eq _ _ _ (me_mem ?H ?y) _
      |- (exists _ _, mdenote _ _ _ (me_mem ?H ?y) _ /\ _) /\ (exists _ _, mdenote _ _ _ (ds_unit ?Rm) _ /\ _) =>
        let Hg := fresh "Hg" in
        pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg;
        destruct (ds_unit_denote _ _ _ Hg (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm) Hd) (ds_mod_is_mod _ _ _ _ Hd) G
                    (wf_mdenote_mod_xp _ _ _ _ _ _ _ HH Hm Hd))
          as (R' & HR' & HR'm);
        split; [ exists R, Rm | exists R', Rm ]; split; assumption
    end ].
Qed.

(** A stored module is a well-formed module expression: its root is a
    loaded unit or an open frame, and each selection below it denotes a
    module with a telescope. *)
Lemma loc_modexp_wf : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> forall p T Φ, loc Θ Ξ p T Φ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ qname_mod p ≈ qname_mod p.
Proof.
  intros Θ Ξ Γ HΓ; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  intros [u ch]; revert u; induction ch as [| y ch IH] using List.rev_ind; intros u T Φ Hl.
  - destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hl) as (R & Hm & _).
    unfold qname_mod in Hm |- *; cbn [q_unit q_chain me_mems] in Hm |- *.
    inversion Hm; subst; eapply wf_me_unit; eassumption.
  - change {| q_unit := u; q_chain := ch ++ y :: nil |} with (qname_in {| q_unit := u; q_chain := ch |} y) in *.
    destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hl) as (R & Hm & HR).
    assert (Ht : exists T0, ds_mtele Θ Ξ R = Some T0).
    { destruct HR as [-> | (pq & k & D & -> & Hb & Hi)]; unfold ds_mtele; cbn; [ eexists; reflexivity |].
      destruct (ind_mlookup_selfpath _ _ Hg _ _ _ _ Hi) as [Hmp _ _].
      rewrite (ind_mlookup_group _ _ Hg _ _ _ _ Hi), Hmp, Hb; cbn; eexists; reflexivity. }
    destruct Ht as (T0 & Ht).
    assert (Hp : exists T' Φ', loc Θ Ξ {| q_unit := u; q_chain := ch |} T' Φ').
    { destruct Hl as [Hf | Hb].
      - pose proof (gc_unit_of_frame Θ _ _ _ _ _ (mod_qname_qname_mod _) Hf) as Hu.
        rewrite qname_mod_in in Hu.
        destruct (gc_unit_mem_parent _ _ Hg _ _ _ _ Hu) as (T' & Φ' & Hu' & _).
        destruct (gc_unit_loc _ _ _ _ _ Hu') as (mp & Hq & Hl'); rewrite mod_qname_qname_mod in Hq; injection Hq as <-.
        eauto.
      - destruct (gc_body_module _ _ _ _ _ Hb) as [oD Hmd].
        destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hmd) as (Tq & Φq & Hlq & _).
        exists Tq, Φq; apply loc_mod_loc; exact Hlq. }
    destruct Hp as (T' & Φ' & Hp).
    rewrite qname_mod_in in Hm |- *.
    eapply wf_me_mem; [ exact (IH _ _ _ Hp) | exact Hm | exact Ht | exact Hm | exact Ht ].
Qed.


(** A description is left alone by a substitution fixing its variables. *)
Lemma ds_sub_fix : forall R n σ, ds_scoped n R -> (forall x, x < n -> σ x = se_var x) -> ds_sub R σ = R.
Proof.
  intros [A om | Δ Φ Φx | Θ0 ? T Φ Ns | Θ0 p kd Ns] * HR Hσ; cbn in HR |- *.
  - destruct HR as [HA Hom]; rewrite (proj1 syn_scoped_sub_id _ _ _ HA Hσ).
    destruct om as [M |]; cbn in *; [ rewrite (proj1 syn_scoped_sub_id _ _ _ Hom Hσ) |]; reflexivity.
  - destruct HR as [HR1 HR2].
    pose proof (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id))) _ _ _ HR1 Hσ) as HU.
    pose proof (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id))) _ _ _ HR2 Hσ) as HU2.
    rewrite gunit_sub_mk in HU, HU2; injection HU as HΔ HΦ; injection HU2 as _ HΦx; rewrite HΔ, HΦ, HΦx; reflexivity.
  - destruct HR as (HΘ & _ & HNs).
    rewrite (tele_scoped_sub_agree _ _ σ Id HΘ ltac:(intros; rewrite Hσ by lia; reflexivity)), tele_sub_id.
    f_equal; rewrite <- (List.map_id Ns) at 2; apply List.map_ext_in; intros M HM.
    eapply (proj1 syn_scoped_sub_id); [ eapply List.Forall_forall in HNs; [ exact HNs | exact HM ] |].
    apply sb_qn_fix; exact Hσ.
  - destruct HR as (HΘ & HNs).
    rewrite (tele_scoped_sub_agree _ _ σ Id HΘ ltac:(intros; rewrite Hσ by lia; reflexivity)), tele_sub_id.
    f_equal; rewrite <- (List.map_id Ns) at 2; apply List.map_ext_in; intros M HM.
    eapply (proj1 syn_scoped_sub_id); [ eapply List.Forall_forall in HNs; [ exact HNs | exact HM ] |].
    apply sb_qn_fix; exact Hσ.
Qed.

(** A judgment over a closed telescope, read over the telescope on top of
    any context. *)
Lemma closed_tele_weaken_exp : forall Θ Ξ T Γ M A,
    ctx_scoped 0 T -> Θ ⍮ Ξ ⍮ T ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ T ++ Γ -> Θ ⍮ Ξ ⍮ T ++ Γ ⊢ M : A.
Proof.
  intros * Hs HM HTΓ.
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ HM) as (_ & HsM & HsA).
  assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub T Id ++ Γ ⊢ˢ sb_qn (length T) Id : T ++ ⋅).
  { apply wf_sub_ext; [ apply wf_sub_to_nil, (ctx_app_wf_tail _ _ _ _ HTΓ) | rewrite tele_sub_id; exact HTΓ |
      rewrite List.app_nil_r; eapply presup_exp_ctx; exact HM ]. }
  rewrite tele_sub_id in Hσ; rewrite List.app_nil_r in Hσ.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM Hσ) as H.
  assert (Hfix : forall x, x < length T -> sb_qn (length T) Id x = se_var x)
    by (intros x Hx; apply (sb_qn_fix _ _ 0); [ intros; lia | lia ]).
  rewrite (proj1 syn_scoped_sub_id _ _ _ HsM Hfix), (proj1 syn_scoped_sub_id _ _ _ HsA Hfix) in H; exact H.
Qed.

(** What a coherent body says of one of its entries. *)
Definition ge_coh (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A _ => exists A0, A = ctx_pi T A0
  | ge_mod _ (gu_mk Δ (md_body _ Φ')) => tele_ass Δ /\ gm_coh (Δ ++ T) Φ'
  | ge_mod _ (gu_mk Δ (md_alias _)) => exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  | ge_ind _ _ _ D Φ' => (exists Δ0, ind_uparams D = Δ0 ++ T /\ tele_ass Δ0) /\ gm_coh (ind_uparams D) Φ' /\ gm_defs Φ'
  | ge_ind_alias _ Δ _ _ _ _ => exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  end.

Lemma gm_coh_prefix : forall T Φ y Φ0 E, gm_coh T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> ge_coh T E.
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hc Hp; cbn in Hc, Hp; [ discriminate | |].
  - destruct (String.eqb y x); [ injection Hp as -> -> -> |].
    + destruct E as [b pv A B | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Δa pma pa ka Nsa]; cbn; apply Hc.
    + destruct E0 as [b pv A B | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Δa pma pa ka Nsa]; (eapply IH; [ apply Hc | exact Hp ]).
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

Lemma loc_coh : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ -> gm_coh T Φ.
Proof.
  intros * Hg * [Hl | Hl]; [| exact (gc_body_coh _ _ Hg _ _ _ Hl) ].
  unfold gc_frame in Hl.
  destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
  injection Hl as <- <-; exact (wf_gstack_coh _ _ Hg _ _ _ _ Ef).
Qed.


(** The entries of a local body before a member, filled in, form a
    well-typed substitution. *)
Lemma wf_gm_fill : forall Θ Ξ Φ Γ0 σ,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ0 -> gm_fill Φ = Some σ -> Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ σ : body_ctx Φ ++ Γ0.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * HΦ Hf; cbn in Hf |- *.
  - injection Hf as <-; apply wf_sub_id; exact HΦ.
  - destruct E as [b pv A [M |] | pv U | ? ? ? ? | ? ? ? ?]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:E0; cbn in Hf; try discriminate; injection Hf as <-; cbn [body_ctx List.app] in HΦ |- *.
    + destruct (ctx_decomp_def HΦ) as (HΓ & [i HA] & HM).
      pose proof (IH _ _ HΓ eq_refl) as Hσ.
      eapply wf_sub_extend_def; [ exact Hσ | exact HA | exact HM | eapply sub_preserves_exp; eassumption |].
      apply wf_exp_eq_refl; eapply sub_preserves_exp; eassumption.
    + destruct (ctx_decomp_mod HΦ) as (HΓ & HU).
      pose proof (IH _ _ HΓ eq_refl) as Hσ.
      eapply wf_sub_extend_mod; [ exact Hσ | exact HU | eapply sub_preserves_unit; eassumption ].
  - discriminate.
Qed.

(** ** The Parts of a Well-formed Unit

    A well-formed literal unit is a well-formed body or alias over a
    telescope of assumptions ([unit_full]).  Its parts are invariant under
    moving parameters between the unit and the context. *)

(** The body before a member of a well-formed body unit, the member
    included, extends a well-formed context. *)
Lemma body_prefix_wf : forall Θ Ξ Γ Δ Φ x Φx,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ -> gm_prefix_upto Φ x = Some Φx ->
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ.
Proof.
  intros * HC Hx.
  destruct (gm_prefix_upto_body_ctx _ _ _ Hx) as [Ψ HΨ]; rewrite HΨ, <- app_assoc in HC.
  exact (ctx_app_wf_right _ _ _ _ HC).
Qed.

Lemma body_prefix_mod_wf : forall Θ Ξ Γ Δ Φ y Φ' pm Uy,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ -> gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    Θ ⍮ Ξ ⍮ body_ctx Φ' ++ Δ ++ Γ ⊢ᵘ Uy ≈ Uy.
Proof.
  intros * HC Hx; pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hx) as H; cbn in H.
  exact (proj2 (ctx_decomp_mod H)).
Qed.

(** The levels of the types of the definitions of a well-formed body. *)
Lemma body_levels : forall Θ Ξ Γ Φ, ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ -> gm_noopen Φ ->
    exists lv : String.string -> nat, forall y Φ0 b pv A M, gm_prefix_upto Φ y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
      Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Γ ⊢ A : Typeω@(lv y).
Proof.
  intros Θ Ξ Γ Φ; induction Φ as [| Φ IH x E | Φ IH H its]; intros HC Hn; cbn in Hn.
  - exists (fun _ => 0); intros * Hp; discriminate.
  - assert (HC' : ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ)
      by (destruct E as [? ? ? [] | | | ]; cbn [body_ctx List.app] in HC; exact (ctx_decomp_tail HC)).
    destruct (IH HC' Hn) as [lv Hlv].
    assert (Hcase : exists i, forall b pv A M, E = ge_def b pv A (Some M) -> Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ ⊢ A : Typeω@i).
    { destruct E as [b pv A [M |] | | | ]; try (exists 0; intros; discriminate).
      cbn [body_ctx List.app] in HC; destruct (ctx_decomp_def HC) as (_ & [i Hi] & _).
      exists i; intros * [= <- <- <- <-]; exact Hi. }
    destruct Hcase as [i Hi].
    exists (fun z => if String.eqb z x then i else lv z); intros y Φ0 b pv A M Hp; cbn in Hp.
    destruct (String.eqb_spec y x) as [-> | Hne].
    + injection Hp as <- ->; exact (Hi _ _ _ _ eq_refl).
    + apply String.eqb_neq in Hne; rewrite ?Hne; exact (Hlv _ _ _ _ _ _ Hp).
  - contradiction.
Qed.

Definition unit_full (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ (md_body sm_open Φ) =>
      exists Φx (lv : String.string -> nat),
        body_xp Θ Ξ (Δ ++ Γ) Φ Φx /\ ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ /\
        (forall y Φ0 b pv A M σ,
            gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) -> gm_fill Φ0 = Some σ ->
            Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : Typeω@(lv y) /\ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] : A[σ]) /\
        (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H) /\
        tele_ass Δ /\ body_shape Φ Φ /\ body_shape Φx Φx /\ List.NoDup (gm_names Φ)
  | gu_mk Δ (md_body sm_closed _) => False
  | gu_mk Δ (md_alias E) => ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ /\ tele_ass Δ /\ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E
  end.

(** A body's definitions, filled in, are typed when its entries extend a
    well-formed context. *)
Lemma body_defs_wf : forall Θ Ξ Γ Δ Φx, ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ -> gm_noopen Φx ->
    exists lv : String.string -> nat,
      forall y Φ0 b pv A M σ,
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) -> gm_fill Φ0 = Some σ ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : Typeω@(lv y) /\ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] : A[σ].
Proof.
  intros * HΦ Hn.
  destruct (body_levels _ _ _ _ HΦ Hn) as [lv Hlv]; exists lv.
  intros y Φ0 b pv A M σ Hp Hf.
  pose proof (body_prefix_wf _ _ _ _ _ _ _ HΦ Hp) as HΦ1; cbn [body_ctx List.app] in HΦ1.
  destruct (ctx_decomp_def HΦ1) as (HΦ0 & _ & HM).
  pose proof (wf_gm_fill _ _ _ _ _ HΦ0 Hf) as Hσ.
  split; [ exact (sub_preserves_typ _ _ _ _ _ _ _ (Hlv _ _ _ _ _ _ Hp) Hσ) | exact (sub_preserves_exp _ _ _ _ _ _ _ HM Hσ) ].
Qed.

Lemma unit_eq_of_full : forall Θ Ξ Γ U, unit_full Θ Ξ Γ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  intros * HU; destruct U as [Δ [[] Φ | E]]; cbn in HU; try contradiction.
  - destruct HU as (Φx & lv & Hx & HC & Hd & Ho & Ha & Hs & Hsx & Hn).
    assert (HΔ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ) by exact (ctx_app_wf_tail _ _ _ _ HC).
    assert (Hsame : forall y Φ0 E Φ0' E', gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) ->
              gm_prefix_upto Φx y = Some (gm_ext Φ0' y E') -> Φ0' = Φ0 /\ E' = E)
      by (intros * H1 H2; rewrite H1 in H2; injection H2 as -> ->; split; reflexivity).
    eapply wf_unit_eq_body with (lv := lv); try eassumption; try reflexivity.
    + apply ext_of_ctx'; exact HΔ.
    + apply ext_of_ctx'; rewrite <- app_assoc; exact HC.
    + apply ext_of_ctx'; rewrite <- app_assoc; exact HC.
    + intros * H1 H2 Hf1 Hf2; exact (proj1 (Hd _ _ _ _ _ _ _ H1 Hf1)).
    + intros * H1 H2 Hf1 Hf2; destruct (Hsame _ _ _ _ _ H1 H2) as [-> [= -> -> -> ->]]; rewrite Hf1 in Hf2; injection Hf2 as ->.
      apply wf_exp_eq_refl; exact (proj1 (Hd _ _ _ _ _ _ _ H1 Hf1)).
    + intros * H1 H2 Hf1 Hf2; exact (proj2 (Hd _ _ _ _ _ _ _ H1 Hf1)).
    + intros * H1 H2 Hf1 Hf2; destruct (Hsame _ _ _ _ _ H1 H2) as [-> [= -> -> -> ->]]; rewrite Hf1 in Hf2; injection Hf2 as ->.
      apply wf_exp_eq_refl; exact (proj2 (Hd _ _ _ _ _ _ _ H1 Hf1)).
    + intros * H1 H2 Hf1 Hf2; destruct (Hsame _ _ _ _ _ H1 H2) as [-> [= -> ->]]; rewrite Hf1 in Hf2; injection Hf2 as ->.
      pose proof (body_prefix_mod_wf _ _ _ _ _ _ _ _ _ HC H1) as HU0.
      apply (sub_preserves_unit _ _ _ _ _ _ _ HU0).
      apply wf_gm_fill; [ exact (presup_unit_eq_ctx HU0) | exact Hf1 ].
    + intros * H1 H2 Hf1 Hf2; destruct (Hsame _ _ _ _ _ H1 H2) as [-> [= -> -> -> ->]]; rewrite Hf1 in Hf2; injection Hf2 as ->.
      exact (proj1 (Hd _ _ _ _ _ _ _ H1 Hf1)).
    + intros * H1 H2 Hf1 Hf2; destruct (Hsame _ _ _ _ _ H1 H2) as [-> [= -> -> -> ->]]; rewrite Hf1 in Hf2; injection Hf2 as ->.
      exact (proj2 (Hd _ _ _ _ _ _ _ H1 Hf1)).
    + intros * H1 H2 Hf1 Hf2; destruct (Hsame _ _ _ _ _ H1 H2) as [-> [= -> ->]]; rewrite Hf1 in Hf2; injection Hf2 as ->.
      pose proof (body_prefix_mod_wf _ _ _ _ _ _ _ _ _ HC H1) as HU0.
      apply (sub_preserves_unit _ _ _ _ _ _ _ HU0).
      apply wf_gm_fill; [ exact (presup_unit_eq_ctx HU0) | exact Hf1 ].
    + (* the opens, each filled in *)
      intros k Φ0 H Φ0' H' σ σ' Hk Hk' Hf Hf'.
      rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf in Hf'; injection Hf' as <-.
      pose proof (Ho _ _ _ (body_opens_at_nth _ _ _ _ _ Hk)) as HH.
      eapply sub_preserves_modexp; [ exact HH |].
      apply wf_gm_fill; [ exact (presup_modexp_eq_ctx HH) | exact Hf ].
    + intros k Φ0 H Φ0' H' σ σ' Hk Hk' Hf Hf'.
      rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf in Hf'; injection Hf' as <-.
      pose proof (Ho _ _ _ (body_opens_at_nth _ _ _ _ _ Hk)) as HH.
      eapply sub_preserves_modexp; [ exact HH |].
      apply wf_gm_fill; [ exact (presup_modexp_eq_ctx HH) | exact Hf ].
  - destruct HU as (HΔ & Ha & HE).
    eapply wf_unit_eq_alias; try eassumption; apply ext_of_ctx'; exact HΔ.
Qed.

(** A well-formed body extension with well-formed open targets is a
    well-formed body unit. *)
Lemma unit_full_body : forall Θ Ξ Γ Δ Φ Φx,
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H) ->
    tele_ass Δ -> body_shape Φ Φ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    unit_full Θ Ξ Γ (gu_open Δ Φ).
Proof.
  intros * Hx HC Ho Ha Hs Hsx Hn.
  destruct (body_defs_wf _ _ _ _ _ HC (body_xp_result_noopen _ _ _ _ _ Hx)) as [lv Hd].
  cbn [unit_full]; exists Φx, lv; exact (conj Hx (conj HC (conj Hd (conj Ho (conj Ha (conj Hs (conj Hsx Hn))))))).
Qed.

Section DescOk.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** The arguments [Ns] fill, in order, the outermost parameters of the
      closed telescope [T], in [Γ]. *)
  #[warnings="-cannot-define-projection"]
  Record args_ok (Γ : ctx) (T : ctx) (Ns : list exp) : Prop := mk_args_ok
    { ao_rest : ctx
    ; ao_filled : ctx
    ; ao_split : T = ao_rest ++ ao_filled
    ; ao_length : length ao_filled = length Ns
    ; ao_ass : tele_ass ao_filled
    ; ao_scoped : ctx_scoped 0 ao_filled
    ; ao_wf : ⊢ Θ ⍮ Ξ ⍮ ao_filled ++ Γ
    ; ao_args : forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts ao_filled Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A }.

  (** [desc_ok Γ R]: the description [R] is typed in [Γ].  A term is of a
      type, its δ-reduct of that type; an inductive type exists and is given
      typed arguments; an open module's expanded body is a well-formed
      extension, each of its module entries denoting typed descriptions, and
      its written body is a well-formed unit under its parameters; a closed module is
      stored, at a location of a past global context it grew from, and given
      typed arguments: so a description stays typed as the global context
      grows. *)
  Inductive desc_ok : ctx -> mdesc -> Prop :=
  | dok_term : forall Γ A om,
      (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) ->
      (forall M, om = Some M -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A) ->
      desc_ok Γ (ds_term A om)
  | dok_ind : forall Γ Θ' pq k Ns D Mk pm,
      ind_lookup Θ Ξ pq = Some D ->
      ind_member D k = Some Mk ->
      k < ind_ndecl D ->
      ind_mpath D k = Some pm ->
      ind_mlookup Θ Ξ pm = Some (pq, k, D) ->
      tele_ass (ind_uparams D) -> ctx_scoped 0 (ind_uparams D) -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ->
      ⊢ Θ ⍮ Ξ ⍮ Θ' ++ Γ ->
      args_ok (Θ' ++ Γ) (ind_uparams D) Ns ->
      tele_ass Θ' ->
      desc_ok Γ (ds_ind Θ' pq k Ns)
  | dok_open : forall Γ Δ Φw Φ,
      ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ ->
      gm_noopen Φ ->
      (forall y Φ0 pm U, gm_prefix_upto Φ y = Some (gm_ext Φ0 y (ge_mod pm U)) ->
         forall R, udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U R -> desc_ok (body_ctx Φ0 ++ Δ ++ Γ) R) ->
      tele_ass Δ -> body_shape Φ Φ -> List.NoDup (gm_names Φ) ->
      Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_open nil Φw ≈ gu_open nil Φw ->
      desc_ok Γ (ds_open Δ Φw Φ)
  | dok_closed : forall Γ Θ' T Φ Ns Θ0 Ξ0 p,
      ⊢ᵍ Θ0 ⍮ Ξ0 -> gc_sub Θ0 Ξ0 Θ Ξ -> loc Θ0 Ξ0 p T Φ ->
      tele_ass T -> ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T ->
      ⊢ Θ ⍮ Ξ ⍮ Θ' ++ Γ ->
      args_ok (Θ' ++ Γ) T Ns ->
      tele_ass Θ' ->
      desc_ok Γ (ds_closed Θ' p T Φ Ns).

  Lemma args_ok_sub : forall Γ T Ns Γ' σ, args_ok Γ T Ns -> Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ ->
      args_ok Γ' T (List.map (fun M => M[σ]) Ns).
  Proof.
    intros * [T1 T2 -> Hl Ha Hs HT2 HN] Hσ.
    exists T1 T2; [ reflexivity | rewrite length_map; exact Hl | exact Ha | exact Hs
                   | rewrite <- (tele_sub_closed T2 σ Hs); eapply ctx_sub_wf_gen; eassumption |].
    intros k N A HNk HAk.
    rewrite List.nth_error_map in HNk; destruct (nth_error Ns k) as [N0 |] eqn:HN0; [| discriminate ]; injection HNk as <-.
    rewrite <- (tele_insts_sub T2 0 Id Id σ Ns Ha Hs ltac:(intros; lia)), List.nth_error_map in HAk.
    destruct (nth_error (tele_insts T2 Id Ns) k) as [A0 |] eqn:HA0; [| discriminate ]; injection HAk as <-.
    exact (sub_preserves_exp _ _ _ _ _ _ _ (HN _ _ _ HN0 HA0) Hσ).
  Qed.

  (** A typed description moves along a substitution. *)
  Lemma desc_ok_sub : ⊢ᵍ Θ ⍮ Ξ -> forall Γ R, desc_ok Γ R ->
      forall Γ' σ, Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> desc_ok Γ' (ds_sub R σ).
  Proof.
    intros Hg.
    induction 1 as [Γ A om HA HM | Γ Θ' pq k Ns D Mk pm Hl HMk Hk Hmp Hml Ha Hs HT HΘ' Hargs HaΘ
                   | Γ Δ Φw Φ HΦ Hn Hent IH HaΔ Hsh Hnd HUw | Γ Θ' T Φ Ns Θ0 Ξ0 p Hg0 Hsub0 Hloc Ha Hs HT HΘ' Hargs HaΘ];
      intros Γ' σ Hσ; cbn [ds_sub].
    - constructor.
      + destruct HA as [i HA]; exists i; exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ).
      + intros M HM'; destruct om as [M0 |]; cbn in HM'; [ injection HM' as <- | discriminate ].
        exact (sub_preserves_exp _ _ _ _ _ _ _ (HM M0 eq_refl) Hσ).
    - assert (HΘ'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ' σ ++ Γ') by (eapply ctx_sub_wf_gen; eassumption).
      econstructor; [ exact Hl | exact HMk | exact Hk | exact Hmp | exact Hml | exact Ha | exact Hs | exact HT | exact HΘ''
                    | | apply tele_ass_sub; exact HaΘ ].
      eapply args_ok_sub; [ exact Hargs | apply wf_sub_ext; assumption ].
    - constructor.
      4: apply tele_ass_sub; exact HaΔ.
      4: apply body_shape_sub; exact Hsh.
      4: rewrite gm_names_sub; exact Hnd.
      4: { pose proof (sub_preserves_unit _ _ _ _ _ _ _ HUw
                         (wf_sub_ext _ _ _ _ _ _ Hσ
                            (ctx_sub_wf_gen _ _ _ _ _ _ Hσ (ctx_app_wf_tail _ _ _ _ HΦ))
                            (ctx_app_wf_tail _ _ _ _ HΦ))) as HU'.
           rewrite gunit_sub_mk in HU'; exact HU'. }
      + rewrite body_ctx_sub, List.app_assoc, <- tele_sub_app.
        eapply ctx_sub_wf_gen; [ exact Hσ | rewrite <- List.app_assoc; exact HΦ ].
      + apply gm_noopen_sub; exact Hn.
      + intros y Φ0' pm U' Hp' R2 Hu2.
        rewrite gm_prefix_upto_sub in Hp'.
        destruct (gm_prefix_upto Φ y) as [Φ1 |] eqn:Hp; cbn in Hp'; [| discriminate ].
        destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E & -> & _).
        cbn in Hp'; injection Hp' as <- HE.
        destruct E as [| pm0 U | | ]; cbn in HE; try discriminate; injection HE as Hpm HU'; subst pm0 U'.
        destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
        rewrite HΨ in HΦ; cbn [body_ctx] in HΦ.
        pose proof (ctx_app_wf_tail _ _ _ _ ltac:(rewrite <- List.app_assoc in HΦ; exact HΦ)) as HΦ0.
        cbn [List.app] in HΦ0; destruct (ctx_decomp_mod HΦ0) as [HΓ0 HU].
        destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R HR] & _).
        set (σy := sb_qn (length (body_ctx Φ0 ++ Δ)) σ).
        assert (HΓ0' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ0 ++ Δ) σ ++ Γ')
          by (eapply ctx_sub_wf_gen; [ exact Hσ | rewrite <- List.app_assoc; exact HΓ0 ]).
        assert (Hσy : Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ0 ++ Δ) σ ++ Γ' ⊢ˢ σy : (body_ctx Φ0 ++ Δ) ++ Γ)
          by (apply wf_sub_ext; [ exact Hσ | exact HΓ0' | rewrite <- List.app_assoc; exact HΓ0 ]).
        destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (HΓs & HUs & _).
        pose proof (proj1 (proj2 (mdenote_sub_all _ _ (wf_gstack_closed _ _ Hg))) _ _ _ _ HR _
                      (slots_ok_ctx _ HΓs) (or_introl HUs) _ _
                      (wf_sub_mod_compat _ _ _ _ _ ltac:(rewrite <- List.app_assoc in Hσy; exact Hσy))) as HRs.
        rewrite tele_sub_app, <- List.app_assoc in HRs.
        replace (U[σy]ᵘ) with (gunit_sub U (sb_qn (gm_binders Φ0) (sb_qn (length Δ) σ))) in HRs
          by (unfold σy; rewrite List.length_app, length_body_ctx, sb_qn_plus; reflexivity).
        rewrite <- body_ctx_sub in HRs.
        pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ HRs _ Hu2) as <-.
        eapply (IH y Φ0 pm U ltac:(exact Hp) R HR).
        rewrite body_ctx_sub; rewrite tele_sub_app in Hσy; rewrite <- !List.app_assoc in Hσy; exact Hσy.
    - assert (HΘ'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ' σ ++ Γ') by (eapply ctx_sub_wf_gen; eassumption).
      econstructor; [ exact Hg0 | exact Hsub0 | exact Hloc | exact Ha | exact Hs | exact HT | exact HΘ'' | | apply tele_ass_sub; exact HaΘ ].
      eapply args_ok_sub; [ exact Hargs | apply wf_sub_ext; assumption ].
  Qed.

  (** One more argument, for the next parameter. *)
  Lemma args_ok_snoc : forall Γ T Ns C T1' N, args_ok Γ T Ns -> tele_ass T -> ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T ->
      tele_view (List.firstn (length T - length Ns) T) = Some (C, T1') ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : C[sb_of_list Id Ns] -> args_ok Γ T (Ns ++ N :: nil).
  Proof.
    intros * [T1 T2 -> Hl Ha2 Hs2 HT2 HN] Ha Hs HT Hv HN0.
    replace (firstn (length (T1 ++ T2) - length Ns) (T1 ++ T2)) with T1 in Hv
      by (rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
    apply List.Forall_app in Ha as [Ha1 _].
    pose proof (tele_view_ass _ _ _ Ha1 Hv) as ->.
    rewrite <- List.app_assoc in Hs, HT; cbn [List.app] in Hs, HT.
    assert (Hs' : ctx_scoped 0 (ce_ass C :: T2)) by (apply ctx_scoped_app_iff in Hs as [_ Hs]; exact Hs).
    exists T1' (ce_ass C :: T2).
    - rewrite <- List.app_assoc; reflexivity.
    - cbn; rewrite List.length_app, Hl; cbn; lia.
    - constructor; [ eauto | exact Ha2 ].
    - exact Hs'.
    - apply closed_tele_wf; [ exact Hs' | exact (ctx_app_wf_tail _ _ _ _ HT) | exact (ctx_app_wf_tail _ _ _ _ HT2) ].
    - intros k N1 A HNk HAk.
      change (ce_ass C :: T2) with ((ce_ass C :: nil) ++ T2) in HAk.
      rewrite tele_insts_app in HAk by (first [ exact Ha2 | lia ]).
      destruct (Nat.lt_ge_cases k (length Ns)) as [Hk | Hk].
      + rewrite List.nth_error_app1 in HNk by exact Hk.
        rewrite List.nth_error_app1 in HAk by (rewrite length_tele_insts by exact Ha2; lia).
        exact (HN _ _ _ HNk HAk).
      + rewrite List.nth_error_app2 in HNk by exact Hk.
        rewrite List.nth_error_app2 in HAk by (rewrite length_tele_insts by exact Ha2; lia).
        rewrite length_tele_insts in HAk by exact Ha2.
        rewrite <- Hl, Nat.min_id in HAk; rewrite <- Hl in HNk.
        destruct (k - length T2) as [| k'] eqn:Ek; cbn in HNk, HAk; [| destruct k'; discriminate ].
        injection HNk as <-; injection HAk as <-; exact HN0.
  Qed.

  Lemma sb_of_list_map_agree : forall Ns τ x, x < length Ns ->
      (sb_of_list Id Ns ⨟ τ) x = sb_of_list Id (List.map (fun M => M[τ]) Ns) x.
  Proof.
    intros * Hx; unfold sb_compose.
    rewrite (sb_of_list_nth _ _ _ a_True Hx), (sb_of_list_nth _ _ _ a_True[τ]) by (rewrite length_map; exact Hx).
    rewrite length_map, (List.map_nth (fun M => M[τ])); reflexivity.
  Qed.

  (** Supplying the next parameter of a module part over the outside
      parameters [Θ'] and the arguments [Ns] of a closed telescope [T]: an
      outside parameter, past the definitions and modules outside it, or
      else the next parameter of [T]. *)
  Lemma args_at : forall Γ Θ' T Ns B T1 N,
      tele_ass T -> ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T -> ⊢ Θ ⍮ Ξ ⍮ Θ' ++ Γ -> args_ok (Θ' ++ Γ) T Ns ->
      tele_view (tele_sub (List.firstn (length T - length Ns) T) (sb_of_list Id Ns) ++ Θ') = Some (B, T1) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
      match tele_split (rev Θ') with
      | inl (_, Θ'', τ) =>
          ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ'' (Id,,N) ++ Γ /\
          args_ok (tele_sub Θ'' (Id,,N) ++ Γ) T (List.map (fun M => M[τ ⨟ sb_qn (length Θ'') (Id,,N)]) Ns)
      | inr τ => args_ok Γ T (List.map (fun M => M[τ]) Ns ++ N :: nil)
      end.
  Proof.
    intros * Ha Hs HT HΘ' Hargs Hv HN.
    unfold tele_view in Hv; rewrite List.rev_app_distr in Hv.
    pose proof (tele_split_wf _ _ (rev Θ') Γ ltac:(rewrite rev_involutive; exact HΘ')) as Hsw.
    rewrite rev_involutive in Hsw.
    destruct (tele_split (rev Θ')) as [[[B' Θ''] τ] | τ] eqn:Es.
    - destruct (tele_open_app_inl _ (rev (tele_sub (List.firstn (length T - length Ns) T) (sb_of_list Id Ns))) _ _ _ Es) as (T' & Ho).
      rewrite Ho in Hv; injection Hv as <- _.
      destruct Hsw as ([i HB] & HΘ'' & Hτ).
      pose proof (wf_sub_single _ _ _ _ _ _ HB HN) as Hs1.
      assert (HΘN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ'' (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      split; [ exact HΘN |].
      eapply args_ok_sub; [ exact Hargs |].
      eapply wf_sub_compose; [ exact Hτ | apply wf_sub_ext; assumption ].
    - destruct (tele_open_app_inr _ _ _ _ _ Es Hv) as (B0 & T0 & Ho & ->).
      fold (tele_view (tele_sub (List.firstn (length T - length Ns) T) (sb_of_list Id Ns))) in Ho.
      rewrite tele_view_sub in Ho.
      destruct (tele_view (List.firstn (length T - length Ns) T)) as [[C T1'] |] eqn:HvC; cbn in Ho; [| discriminate ].
      injection Ho as <- _.
      pose proof (args_ok_sub _ _ _ _ _ Hargs Hsw) as Hargs'.
      eapply args_ok_snoc; [ exact Hargs' | exact Ha | exact Hs | exact HT | rewrite length_map; exact HvC |].
      rewrite exp_sub_sub in HN.
      destruct Hargs as [T1x T2 -> Hl _ _ _ _].
      replace (firstn (length (T1x ++ T2) - length Ns) (T1x ++ T2)) with T1x in HvC
        by (rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
      apply List.Forall_app in Ha as [Ha1 _].
      pose proof (tele_view_ass _ _ _ Ha1 HvC) as ->.
      rewrite <- List.app_assoc in Hs; cbn [List.app] in Hs.
      apply ctx_scoped_app_iff in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HC _].
      rewrite Hl, Nat.add_0_r in HC.
      erewrite exp_scoped_sub_agree; [ exact HN | exact HC |].
      intros; symmetry; apply sb_of_list_map_agree; assumption.
  Qed.

  Lemma desc_ok_up : forall Γ Θ'' R, desc_ok (Θ'' ++ Γ) R -> ⊢ Θ ⍮ Ξ ⍮ Θ'' ++ Γ -> tele_ass Θ'' -> desc_ok Γ (ds_up Θ'' R).
  Proof.
    intros * HR HΘ HaΘ; inversion HR; subst; cbn [ds_up].
    all: try solve [ first [ econstructor; try eassumption; first [ rewrite <- List.app_assoc; assumption | apply List.Forall_app; split; assumption ]
                           | constructor; first [ rewrite <- !List.app_assoc; assumption | apply List.Forall_app; split; assumption | assumption ] ] ].
    match goal with H : exists i, _ |- _ => destruct H end.
    constructor.
    - exact (ctx_pi_wf _ _ _ _ _ _ HΘ ltac:(eassumption)).
    - intros M HM; destruct om as [M0 |]; cbn in HM; [ injection HM as <- | discriminate ].
      eapply ctx_fn_wf; [ exact HΘ | eassumption |].
      match goal with HM' : forall M, Some M0 = Some M -> _ |- _ => apply HM'; reflexivity end.
  Qed.

  (** An open description read in the context extended by its parameters. *)
  Lemma desc_ok_open_root : forall Γ Δ Φw Φ, tele_ass Δ -> desc_ok Γ (ds_open Δ Φw Φ) <-> desc_ok (Δ ++ Γ) (ds_open nil Φw Φ).
  Proof.
    intros * Ha; split; intros H; inversion H; subst; constructor; cbn [List.app] in *; first [ assumption | constructor ].
  Qed.

  Lemma desc_ok_closed_root : forall Γ Θ' p T Φ Ns, tele_ass Θ' -> desc_ok Γ (ds_closed Θ' p T Φ Ns) <-> desc_ok (Θ' ++ Γ) (ds_closed nil p T Φ Ns).
  Proof. intros * Ha; split; intros H; inversion H; subst; econstructor; cbn [List.app] in *; first [ eassumption | constructor ]. Qed.

  Lemma desc_ok_ind_root : forall Γ Θ' pq k Ns, tele_ass Θ' -> desc_ok Γ (ds_ind Θ' pq k Ns) <-> desc_ok (Θ' ++ Γ) (ds_ind nil pq k Ns).
  Proof. intros * Ha; split; intros H; inversion H; subst; econstructor; cbn [List.app] in *; first [ eassumption | constructor ]. Qed.

  (** "R at N", where the module part of [R] takes a parameter [N] fills. *)
  Lemma desc_ok_at : ⊢ᵍ Θ ⍮ Ξ -> forall Γ R T B T1 N R',
      desc_ok Γ R -> ds_mtele Θ Ξ R = Some T -> tele_view T = Some (B, T1) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : B -> ds_at R N = Some R' -> desc_ok Γ R'.
  Proof.
    intros Hg * HR Ht Hv HN Ha.
    inversion HR as [Γ0 A om HA HM | Γ0 Θ' pq k Ns D Mk pm Hl HMk Hk Hmp Hml Hau Hsu HTu HΘ' Hargs HaΘ
                    | Γ0 Δ Φw Φ HΦ Hn Hent HaΔ Hsh Hnd HUw | Γ0 Θ' T0 Φ Ns Θ0 Ξ0 p Hg0 Hsub0 Hloc Ha0 Hs0 HT0 HΘ' Hargs HaΘ];
      subst; unfold ds_mtele in Ht; cbn in Ht, Ha; unfold ds_tele in Ht.
    - discriminate.
    - (* a member of a group of inductive types *)
      rewrite Hl, Hmp in Ht.
      destruct (gc_body Θ Ξ pm) as [[T0 Φ0] |] eqn:Hb; [| discriminate ].
      pose proof (ind_mlookup_gc_body _ _ _ _ _ _ _ _ Hml Hb) as ->.
      destruct (Nat.leb (length Ns) (length (ind_uparams D))); [| discriminate ]; injection Ht as <-.
      pose proof (args_at _ _ _ _ _ _ _ Hau Hsu HTu HΘ' Hargs Hv HN) as Hat.
      destruct (tele_split (rev Θ')) as [[[B' Θ''] τ] | τ] eqn:Es; injection Ha as <-.
      + destruct Hat as [HΘN HargsN]; econstructor; try eassumption.
        apply tele_ass_sub; exact (tele_split_ass _ _ _ _ HaΘ Es).
      + econstructor; try eassumption; [ cbn [List.app]; eapply ctx_app_wf_tail; exact HΘ' | constructor ].
    - (* an open module *)
      injection Ht as <-.
      unfold tele_view in Hv; destruct (tele_open_split _ _ _ Hv) as (τ & Es).
      rewrite Es in Ha; injection Ha as <-.
      pose proof (tele_split_wf Θ Ξ (rev Δ) Γ) as Hsw; rewrite rev_involutive, Es in Hsw.
      destruct (Hsw ltac:(eapply ctx_app_wf_tail; exact HΦ)) as ([i HB] & HT1 & Hτ).
      pose proof (wf_sub_single _ _ _ _ _ _ HB HN) as Hs1.
      assert (HT1N : ⊢ Θ ⍮ Ξ ⍮ tele_sub T1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      assert (HσN : Θ ⍮ Ξ ⍮ tele_sub T1 (Id,,N) ++ Γ ⊢ˢ τ ⨟ sb_qn (length T1) (Id,,N) : Δ ++ Γ)
        by (eapply wf_sub_compose; [ exact Hτ | apply wf_sub_ext; assumption ]).
      assert (HaT1 : tele_ass (tele_sub T1 (Id,,N)))
        by (apply tele_ass_sub; exact (tele_split_ass _ _ _ _ HaΔ Es)).
      apply (desc_ok_open_root _ _ _ _ HaT1).
      apply (desc_ok_open_root _ _ _ _ HaΔ) in HR.
      exact (desc_ok_sub Hg _ _ HR _ _ HσN).
    - (* a closed module *)
      destruct (Nat.leb (length Ns) (length T0)); [| discriminate ]; injection Ht as <-.
      pose proof (args_at _ _ _ _ _ _ _ Ha0 Hs0 HT0 HΘ' Hargs Hv HN) as Hat.
      destruct (tele_split (rev Θ')) as [[[B' Θ''] τ] | τ] eqn:Es; injection Ha as <-.
      + destruct Hat as [HΘN HargsN]; econstructor; try eassumption.
        apply tele_ass_sub; exact (tele_split_ass _ _ _ _ HaΘ Es).
      + econstructor; try eassumption; [ cbn [List.app]; eapply ctx_app_wf_tail; exact HΘ' | constructor ].
  Qed.

  (** The module part. *)
  Lemma desc_ok_mod : ⊢ᵍ Θ ⍮ Ξ -> forall Γ R Rm, desc_ok Γ R -> ds_mod Θ Ξ R = Some Rm -> desc_ok Γ Rm.
  Proof.
    intros Hg * HR Hm; inversion HR; subst; try (cbn in Hm; discriminate); try (cbn in Hm; injection Hm as <-; exact HR).
    destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hm) as (D' & pm' & T0 & Φ0 & Hl' & Hmp' & Hb & ->).
    match goal with Hl : ind_lookup _ _ _ = Some ?D0, Hmp : ind_mpath ?D0 _ = Some _, Hml : ind_mlookup _ _ _ = Some _ |- _ =>
      rewrite Hl in Hl'; injection Hl' as <-; rewrite Hmp in Hmp'; injection Hmp' as <-;
      pose proof (ind_mlookup_gc_body _ _ _ _ _ _ _ _ Hml Hb) as -> end.
    econstructor; [ exact Hg | apply gc_sub_refl | right; exact Hb | eassumption .. ].
  Qed.

  (** An entry of an open module: a definition is typed by the extension the
      body is, a module entry by the clause for it; the entries before it are
      filled in by a well-typed substitution. *)
  Lemma desc_ok_entry_open : ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ Φw Φ y Γy E rd R R',
      desc_ok Γ (ds_open Δ Φw Φ) -> ds_entry (ds_open Δ Φw Φ) y = Some (Γy, E, rd) ->
      edenote Θ Ξ (Γy ++ Γ) None E R -> ds_read rd R = Some R' -> desc_ok Γ R'.
  Proof.
    intros Hg * HR He Hed Hr; inversion HR as [| | Γ0 Δ0 Φw0 Φ0 HΦ Hn Hent HaΔ Hsh Hnd HUw |]; subst.
    cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ1 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
    rewrite HΨ in HΦ.
    assert (HΦ1 : ⊢ Θ ⍮ Ξ ⍮ body_ctx (Φ1 ⊳ y ↦ E1) ++ Δ ++ Γ)
      by (eapply ctx_app_wf_tail; rewrite <- List.app_assoc in HΦ; exact HΦ).
    assert (HΦ1' : ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ1 ++ Δ ++ Γ)
      by (destruct E1 as [? ? ? [] | | | ]; cbn [body_ctx List.app] in HΦ1; eauto using ctx_decomp_tail).
    destruct E1 as [[|] pv A [M |] | pv U | | ]; try discriminate; injection He as <- <- <-; cbn in Hr.
    all: destruct (gm_fill Φ1) as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    all: pose proof (wf_gm_fill _ _ _ _ _ HΦ1' Hf) as Hσ.
    all: apply desc_ok_up; [| exact (wf_sub_dom _ _ _ _ _ Hσ) | exact HaΔ ].
    all: eapply desc_ok_sub; [ exact Hg | | exact Hσ ].
    - (* a local definition, transparent *)
      inversion Hed; subst; cbn [body_ctx List.app] in HΦ1.
      destruct (ctx_decomp_def HΦ1) as (HΓ1 & HA & HM).
      constructor; [ exact HA |].
      intros M' HM'; injection HM' as <-; exact HM.
    - inversion Hed; subst; cbn [body_ctx List.app] in HΦ1.
      eapply Hent; [ exact Hp |].
      rewrite List.app_assoc; assumption.
  Qed.

  (** A description abstracted over [Δa], given arguments for the outermost
      parameters of [Δa]. *)
  Lemma ats_up_ok : ⊢ᵍ Θ ⍮ Ξ -> forall Ns Γ Δa R,
      ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> tele_ass Δa -> length Ns <= length Δa ->
      (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      desc_ok (Δa ++ Γ) R ->
      exists R', ds_ats (ds_up Δa R) Ns = Some R' /\ desc_ok Γ R'.
  Proof.
    intros Hg; induction Ns as [| N Ns IH]; intros * HΔ Ha Hl HNs HR.
    - exists (ds_up Δa R); split; [ reflexivity | apply desc_ok_up; assumption ].
    - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
      unfold tele_ass in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? [C ->] _]; subst.
      rewrite tele_insts_snoc in HNs.
      pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
      rewrite <- List.app_assoc in HΔ, HR; cbn [List.app] in HΔ, HR.
      destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [i HC]].
      pose proof (wf_sub_single _ _ _ _ _ _ HC HN) as Hs1.
      assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass C :: Γ)
        by (apply wf_sub_ext; assumption).
      cbn [ds_ats]; rewrite ds_at_up.
      apply IH.
      + exact HΔN.
      + apply tele_ass_sub; exact Ha1.
      + rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
      + intros k N1 A HN1 HA.
        rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
        exact (HNs (S k) N1 A HN1 HA).
      + exact (desc_ok_sub Hg _ _ HR _ _ Hσ).
  Qed.

  (** A term of no δ-reduct abstracted over [Δa], given arguments for the
      outermost parameters of [Δa], is typed with the name [M] it is read as,
      at the arguments, as its δ-reduct. *)
  Lemma ats_up_self_ok : ⊢ᵍ Θ ⍮ Ξ -> forall Ns Γ Δa A M,
      ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> tele_ass Δa -> length Ns <= length Δa ->
      (forall k N B, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some B -> Θ ⍮ Ξ ⍮ Γ ⊢ N : B) ->
      (exists i, Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ A : Typeω@i) -> Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi Δa A ->
      exists R', ds_ats (ds_up Δa (ds_term A None)) Ns = Some R' /\ desc_ok Γ (ds_self (apps M Ns) R').
  Proof.
    intros Hg; induction Ns as [| N Ns IH]; intros * HΔ Ha Hl HNs [i HA] HM.
    - exists (ds_up Δa (ds_term A None)); split; [ reflexivity |]; cbn.
      destruct (ctx_pi_wf _ _ _ _ _ _ HΔ HA) as [j Hj].
      constructor; [ exists j; exact Hj | intros ? [= <-]; exact HM ].
    - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
      unfold tele_ass in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? [C ->] _]; subst.
      rewrite tele_insts_snoc in HNs.
      pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
      rewrite <- List.app_assoc in HΔ, HA; cbn [List.app] in HΔ, HA.
      destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [k HC]].
      pose proof (wf_sub_single _ _ _ _ _ _ HC HN) as Hs1.
      assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass C :: Γ)
        by (apply wf_sub_ext; assumption).
      rewrite ctx_pi_snoc in HM.
      destruct (ctx_pi_wf _ _ _ _ _ _ HΔ HA) as [j HPi].
      assert (Happ : Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : (ctx_pi Δ1 A)[Id,,N])
        by (eapply wf_app with (i := max k j);
            [ eapply lift_exp_max_left; exact HC | eapply lift_exp_max_right; exact HPi | exact HM | exact HN ]).
      rewrite ctx_pi_sub in Happ.
      cbn [ds_ats]; rewrite ds_at_up; cbn [ds_sub option_map].
      apply (IH _ _ _ (M $ N)).
      + exact HΔN.
      + apply tele_ass_sub; exact Ha1.
      + rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
      + intros k' N1 B HN1 HB.
        rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HB by apply sb_compose_id_right.
        exact (HNs (S k') N1 B HN1 HB).
      + exists i; exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ).
      + exact Happ.
  Qed.

  Lemma args_ok_ext : forall Γ T Ns Δ0, args_ok Γ T Ns -> args_ok Γ (Δ0 ++ T) Ns.
  Proof.
    intros * [T1 T2 -> Hl Ha Hs HT HN]; exists (Δ0 ++ T1) T2; try assumption; rewrite List.app_assoc; reflexivity.
  Qed.

  Lemma args_ok_length : forall Γ T Ns, args_ok Γ T Ns -> length Ns <= length T.
  Proof. intros * [T1 T2 -> Hl _ _ _ _]; rewrite List.length_app; lia. Qed.

  Lemma args_ok_insts : forall Γ T Ns, args_ok Γ T Ns ->
      forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts T Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A.
  Proof.
    intros * [T1 T2 -> Hl Ha _ _ HN] * HNk HAk.
    rewrite <- (List.app_nil_r Ns) in HAk.
    rewrite tele_insts_app in HAk by (first [ exact Ha | lia ]).
    rewrite List.nth_error_app1 in HAk.
    - exact (HN _ _ _ HNk HAk).
    - rewrite length_tele_insts by exact Ha.
      assert (k < length Ns) by (apply List.nth_error_Some; congruence); lia.
  Qed.

  (** A description over a closed telescope on top of [Γ] is one on top of
      any extension of [Γ], when it mentions nothing of [Γ]. *)
  Lemma desc_ok_tele_weaken : ⊢ᵍ Θ ⍮ Ξ -> forall Δa Γ' Γ R,
      ctx_scoped 0 Δa -> ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ' ++ Γ ->
      ds_scoped (length Δa) R -> desc_ok (Δa ++ Γ) R -> desc_ok (Δa ++ Γ' ++ Γ) R.
  Proof.
    intros Hg * Hs HΔΓ HΔΓ' HR Hok.
    pose proof (ctx_app_wf_tail _ _ _ _ HΔΓ') as HΓ'Γ.
    assert (Hw : Θ ⍮ Ξ ⍮ Γ' ++ Γ ⊢ˢ ι (wk_shiftn (length Γ')) : Γ)
      by (apply wf_sub_of_wk, wf_wk_shiftn_app; [ exact HΓ'Γ | exact (ctx_app_wf_tail _ _ _ _ HΓ'Γ) ]).
    assert (Hσ : Θ ⍮ Ξ ⍮ Δa ++ Γ' ++ Γ ⊢ˢ sb_qn (length Δa) (ι (wk_shiftn (length Γ'))) : Δa ++ Γ).
    { pose proof (wf_sub_ext _ _ Δa _ _ _ Hw) as Hx; rewrite tele_sub_closed in Hx by exact Hs.
      exact (Hx HΔΓ' HΔΓ). }
    pose proof (desc_ok_sub Hg _ _ Hok _ _ Hσ) as H.
    rewrite (ds_sub_fix _ _ _ HR) in H; [ exact H |].
    intros x Hx; apply (sb_qn_fix _ _ 0); [ intros; lia | lia ].
  Qed.
End DescOk.
