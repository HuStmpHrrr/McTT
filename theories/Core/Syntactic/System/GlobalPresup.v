(** * Presupposition

    Presupposition is proved for all twelve judgments at once.  A global is used
    at its resolved type without premising that it is a type, and a definition's
    type is not checked separately from its body; that each is a type is what
    presupposition of the entry's own derivation gives, and that derivation is
    part of [⊢g], so the induction has to range over the global judgments too.

    Every entry is closed and every path absolute, so a global context only
    ever grows by embedding: everything that resolves keeps resolving to the
    same entry ([gc_sub]), and a judgment moves along an embedding unchanged
    ([emb_preserves_wf]).  The induction over the global judgments is stated
    once, for an arbitrary notion [V] of a valid entry ([global_induction]):
    each entry is valid in every context its insertion context embeds into.
    Presupposition is its instance at syntactic typing; the two semantic models
    are the others. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Structural.
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
    T ∋ #x ⇒ₘ U ->
    E ++ T ∋ #(x + length E) ⇒ₘ gunit_wk U (wk_shiftn (length E)).
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, (gunit_wk_wk_eq _ _ _ wk_shiftn_zero), gunit_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- (gunit_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- gunit_wk_wk.
    constructor; auto.
Qed.

Lemma wf_wk_shiftn_app : forall Θ Ξ E T,
    ⊢ Θ ⍮ Ξ ⍮ E ++ T ->
    ⊢ Θ ⍮ Ξ ⍮ T ->
    Θ ⍮ Ξ ⍮ E ++ T ⊢w wk_shiftn (length E) : T.
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
      econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
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
      [ econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
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
    Θ ⍮ Ξ ⍮ Γ' ⊢s σ : Γ -> tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ σ ++ Γ'.
Proof.
  intros * Hσ Hass HΔ; eapply ext_eq_ctx_left, sub_preserves_ext; [ apply ctx_ext_refl; eassumption | exact Hσ ].
Qed.

Lemma wf_sub_of_list : forall Θ Ξ Δ Γ Γ0 σ Ms,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ0 -> Θ ⍮ Ξ ⍮ Γ ⊢s σ : Γ0 ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list σ Ms : Δ ++ Γ0.
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
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Ms : Δ ++ Γ.
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


(** ** Embeddings

    [Emb Θ1 Ξ1 Θ2 Ξ2]: the target is well formed and everything that resolves
    at the source resolves, to the same entry, at the target. *)

Record Emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { em_wf : ⊢g Θ2 ⍮ Ξ2
  ; em_res : gc_sub Θ1 Ξ1 Θ2 Ξ2 }.

Lemma Emb_refl : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> Emb Θ Ξ Θ Ξ.
Proof. intros; constructor; [ assumption | apply gc_sub_refl ]. Qed.

(** An embedding preceded by a growth of resolution. *)
Lemma Emb_pre : forall Θ1 Ξ1 Θ Ξ Θ2 Ξ2,
    gc_sub Θ1 Ξ1 Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> Emb Θ1 Ξ1 Θ2 Ξ2.
Proof. intros * H [Hg He]; constructor; [ assumption | eapply gc_sub_trans; eassumption ]. Qed.

(** Member types and δ-reducts grow with resolution. *)
Lemma member_type_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ H ch R,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> member_type Θ1 Ξ1 Γ H ch R -> member_type Θ2 Ξ2 Γ H ch R.
Proof. intros * Hs; exact (proj1 (member_type_gc_sub _ _ _ _ Hs) _ _ _ _). Qed.

Lemma member_unfold_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ H x M,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> member_unfold Θ1 Ξ1 Γ H x M -> member_unfold Θ2 Ξ2 Γ H x M.
Proof. intros * Hs; exact (member_unfold_gc_sub _ _ _ _ Hs _ _ _ _). Qed.

Lemma body_xp_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ Φ Φx,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> body_xp Θ1 Ξ1 Γ Φ Φx -> body_xp Θ2 Ξ2 Γ Φ Φx.
Proof. intros * Hs; exact (proj1 (proj2 (proj2 (member_type_gc_sub_all _ _ _ _ Hs))) _ _ _). Qed.

(** A judgment moves along an embedding unchanged. *)
Theorem emb_preserves_wf : forall Θ1 Ξ1 Θ2 Ξ2,
    Emb Θ1 Ξ1 Θ2 Ξ2 ->
    (forall Γ, ⊢ Θ1 ⍮ Ξ1 ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A') /\
    (forall Γ Ψ Ψ', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Γ U U', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ᵘ U ≈ U' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Γ H H', Θ1 ⍮ Ξ1 ⍮ Γ ⊢ᵐ H ≈ H' -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵐ H ≈ H').
Proof.
  intros * [Hg Hs].
  assert (H :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ = Θ1 -> Ξ = Ξ1 -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ A ⊆ A') /\
    (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = Θ1 -> Ξ = Ξ1 -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵐ H ≈ H')).
  { apply syntactic_wf_mut_ind; intros; subst;
      repeat match goal with IH : ?x = ?x -> ?x' = ?x' -> _ |- _ => specialize (IH eq_refl eq_refl) end;
      try solve [ econstructor; eauto using gc_sub_resolve, member_type_emb, member_unfold_emb, body_xp_emb, ind_lookup_gc_sub, gc_sub_ind_alias ].
    all: econstructor; eauto. }
  destruct H as (Hc & He & Hq & Hst & Hx & Hu & Hm).
  repeat split; intros; eauto.
Qed.

(** ** The Induction over Insertion, for an Abstract Notion of Validity *)

(** The entries an entry contributes, read below its own path. *)
Definition ge_entries (E : gentry) (ip : list String.string) : option gentry :=
  match E with
  | ge_def _ _ _ _ => match ip with nil => Some E | _ => None end
  | ge_mod _ U => gm_resolve (gu_mod U) ip
  | ge_ind _ _ Φ => gm_resolve Φ ip
  | ge_ind_alias _ _ _ _ => None
  end.

Lemma gm_resolve_ext_here : forall Φ x E ip,
    gm_resolve (Φ ⊳ x ↦ E) (x :: ip) = ge_entries E ip.
Proof.
  intros; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [Δ' [Φ' | E']] | ? ? Φ' | ? ? ? ?]; cbn; rewrite ?gm_resolve_nil; reflexivity.
Qed.

Lemma gm_resolve_ext_inv : forall Φ x E ip E0,
    gm_resolve (Φ ⊳ x ↦ E) ip = Some E0 ->
    (exists ip', ip = x :: ip' /\ ge_entries E ip' = Some E0) \/ gm_resolve Φ ip = Some E0.
Proof.
  intros * H.
  destruct ip as [| y ip']; [ cbn in H; discriminate |].
  destruct (String.eqb_spec y x) as [-> |].
  - left; exists ip'; split; [ reflexivity |]; rewrite <- (gm_resolve_ext_here Φ x); exact H.
  - right; cbn in H; destruct (String.eqb_spec y x) as [Heq | ?]; [ contradiction | exact H ].
Qed.

Lemma qname_strip_app : forall mp ip, qname_strip mp (qname_app mp ip) = Some ip.
Proof.
  intros; unfold qname_strip, qname_app; cbn; rewrite path_beq_refl; apply strip_prefix_app.
Qed.

Lemma qname_strip_app_inv : forall mp p ip, qname_strip mp p = Some ip -> p = qname_app mp ip.
Proof.
  intros [fp ms] [fq ns] ip H; unfold qname_strip, qname_app in *; cbn in *.
  destruct (path_beq fp fq) eqn:Hb; [| discriminate ].
  apply path_beq_true in Hb; subst.
  apply strip_prefix_spec in H; subst; reflexivity.
Qed.

Lemma qname_app_in : forall mp x ip, qname_app (qname_in mp x) ip = qname_app mp (x :: ip).
Proof. intros; unfold qname_app, qname_in; cbn; rewrite <- List.app_assoc; reflexivity. Qed.

(** Reading a frame: what is in it, or what is outside it. *)
Lemma gc_resolve_frame : forall Θ mp U Ξ p E,
    gc_resolve Θ ((mp, U) :: Ξ) p = Some E ->
    (exists ip, p = qname_app mp ip /\ gm_resolve (gu_mod U) ip = Some E) \/
    gc_resolve Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_resolve, gc_resolve_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_resolve_frame_here : forall Θ mp U Ξ ip,
    gc_resolve Θ ((mp, U) :: Ξ) (qname_app mp ip) = gm_resolve (gu_mod U) ip.
Proof. intros; unfold gc_resolve, gc_resolve_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gc_module_frame : forall Θ mp U Ξ p r,
    gc_module Θ ((mp, U) :: Ξ) p = Some r ->
    (exists x ip, p = qname_app mp (x :: ip) /\ gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip = Some r) \/
    gc_module Θ Ξ p = Some r.
Proof.
  intros * H; unfold gc_module, gc_module_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; destruct ip as [| x ip]; [ discriminate |].
    exists x, ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_module_frame_here : forall Θ mp U Ξ x ip,
    gc_module Θ ((mp, U) :: Ξ) (qname_app mp (x :: ip)) = gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip.
Proof. intros; unfold gc_module, gc_module_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gc_body_frame : forall Θ mp U Ξ p r,
    gc_body Θ ((mp, U) :: Ξ) p = Some r ->
    (exists x ip, p = qname_app mp (x :: ip) /\ gm_subbody (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip = Some r) \/
    gc_body Θ Ξ p = Some r.
Proof.
  intros * H; unfold gc_body in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; destruct ip as [| x ip]; [ discriminate |].
    exists x, ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_body_frame_here : forall Θ mp U Ξ x ip,
    gc_body Θ ((mp, U) :: Ξ) (qname_app mp (x :: ip)) = gm_subbody (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip.
Proof. intros; unfold gc_body; cbn; rewrite qname_strip_app; reflexivity. Qed.

(** The inductive aliases an entry contributes, read below its own path:
    itself, if it is one, and those of its body. *)
Definition ge_ind_targets (E : gentry) (ip : list String.string) : option ind_alias_view :=
  match ip, E with
  | nil, _ => ge_ind_target E
  | _ :: _, ge_mod _ (gu_mk _ (md_body Φ)) => gm_ind_target Φ ip
  | _ :: _, ge_ind _ _ Φ => gm_ind_target Φ ip
  | _, _ => None
  end.

Lemma gm_ind_target_ext_here : forall Φ x E ip,
    gm_ind_target (Φ ⊳ x ↦ E) (x :: ip) = ge_ind_targets E ip.
Proof.
  intros; unfold gm_ind_target, ge_ind_targets; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [? [? | ?]] | ? ? ? | ? ? ? ?]; reflexivity.
Qed.

Lemma gm_ind_target_ext_inv : forall Φ x E ip v,
    gm_ind_target (Φ ⊳ x ↦ E) ip = Some v ->
    (exists ip', ip = x :: ip' /\ ge_ind_targets E ip' = Some v) \/ gm_ind_target Φ ip = Some v.
Proof.
  intros * H.
  destruct ip as [| y ip']; [ unfold gm_ind_target in H; cbn in H; discriminate |].
  destruct (String.eqb_spec y x) as [-> |].
  - left; exists ip'; split; [ reflexivity |]; rewrite <- (gm_ind_target_ext_here Φ x); exact H.
  - right; unfold gm_ind_target in *; cbn in H; destruct (String.eqb_spec y x) as [Heq | ?]; [ contradiction | exact H ].
Qed.

Lemma gm_ind_target_nil : forall Φ, gm_ind_target Φ nil = None.
Proof. intros; unfold gm_ind_target; rewrite gm_entry_nil; reflexivity. Qed.

Lemma ind_alias_lookup_frame : forall Θ mp U Ξ p v,
    ind_alias_lookup Θ ((mp, U) :: Ξ) p = Some v ->
    (exists ip, p = qname_app mp ip /\ gm_ind_target (gu_mod U) ip = Some v) \/
    ind_alias_lookup Θ Ξ p = Some v.
Proof.
  intros * H; unfold ind_alias_lookup, ind_alias_lookup_u in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma ind_alias_lookup_frame_here : forall Θ mp U Ξ ip,
    ind_alias_lookup Θ ((mp, U) :: Ξ) (qname_app mp ip) = gm_ind_target (gu_mod U) ip.
Proof. intros; unfold ind_alias_lookup, ind_alias_lookup_u; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma ind_alias_lookup_file : forall Θ fp U p,
    ind_alias_lookup ((fp, U) :: Θ) nil p = ind_alias_lookup Θ ((q_abs fp nil, U) :: nil) p.
Proof.
  intros; unfold ind_alias_lookup, ind_alias_lookup_u; cbn [gs_find gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl; reflexivity.
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

(** A filed unit has the modules its closed frame had: the declarations of
    inductive types among them. *)
Lemma ind_lookup_file : forall Θ fp U p,
    ind_lookup ((fp, U) :: Θ) nil p = ind_lookup Θ ((q_abs fp nil, U) :: nil) p.
Proof.
  intros; unfold ind_lookup, ind_lookup_u, gc_module, gc_module_u; cbn [gs_find_tele gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl.
    destruct (q_chain p) as [| x ip]; cbn; [ reflexivity | rewrite List.app_nil_r; reflexivity ].
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

(** The module an entry is, read at its own path, over the telescope [T]. *)
Definition ge_module (T : ctx) (E : gentry) : option modres :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body _)) => Some (mr_body (Δ ++ T) None)
  | ge_mod _ (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')) nil)
  | ge_ind _ D _ => Some (mr_body (ind_uparams D) (Some D))
  | ge_ind_alias _ Δ p Ns => Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns))) nil)
  end.

Lemma gm_submodule_ext_here_nil : forall T Φ x E, gm_submodule T (Φ ⊳ x ↦ E) x nil = ge_module T E.
Proof. intros; cbn; rewrite String.eqb_refl; destruct E as [| ? [Δ [? | ?]] | ? ? ? | ? ? ? ?]; reflexivity. Qed.

(** The body an entry is, read at its own path, over the telescope [T]. *)
Definition ge_selfbody (T : ctx) (E : gentry) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ | ge_mod _ (gu_mk _ (md_alias _)) | ge_ind_alias _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body Φ)) => Some (Δ ++ T, Φ)
  | ge_ind _ D Φ => Some (ind_uparams D, Φ)
  end.

Lemma gm_subbody_ext_here_nil : forall T Φ x E, gm_subbody T (Φ ⊳ x ↦ E) x nil = ge_selfbody T E.
Proof. intros; cbn; rewrite String.eqb_refl; destruct E as [| ? [Δ [? | ?]] | ? ? ? | ? ? ? ?]; reflexivity. Qed.

(** The submodules an entry contributes, read below its own path, for an
    entry checked over the telescope [T]. *)
Definition ge_submodule (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option modres :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ (gu_mk Δ (md_body Φ)) => gm_submodule (Δ ++ T) Φ x ip
  | ge_mod _ (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')) (x :: ip))
  | ge_ind _ D Φ => gm_submodule (ind_uparams D) Φ x ip
  | ge_ind_alias _ Δ p Ns => Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns))) (x :: ip))
  end.

Lemma gm_submodule_ext_here : forall T Φ x E z ip r,
    ge_submodule T E z ip = Some r -> gm_submodule T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [Φ' | E']] | ? ? ? | ? ? ? ?]; cbn in H; [ discriminate | exact H | exact H | exact H | exact H ].
Qed.

Lemma gm_submodule_ext_inv : forall T Φ x E y ip r,
    gm_submodule T (Φ ⊳ x ↦ E) y ip = Some r ->
    (y = x /\ ip = nil /\ ge_module T E = Some r) \/
    (exists z ip', y = x /\ ip = z :: ip' /\ ge_submodule T E z ip' = Some r) \/
    gm_submodule T Φ y ip = Some r.
Proof.
  intros * H; cbn in H; destruct (String.eqb_spec y x) as [-> |]; [| right; right; exact H ].
  destruct ip as [| z ip'].
  - left; split; [ reflexivity | split; [ reflexivity |] ].
    rewrite <- (gm_submodule_ext_here_nil T Φ x); cbn; rewrite String.eqb_refl; exact H.
  - right; left; exists z, ip'; split; [ reflexivity | split; [ reflexivity |] ].
    destruct E as [| ? [Δ' [Φ' | E']] | ? ? ? | ? ? ? ?]; cbn in *; try discriminate; exact H.
Qed.

(** The body modules an entry contributes, read below its own path. *)
Definition ge_subbody (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod _ U => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  | ge_ind _ D Φ => gm_subbody (ind_uparams D) Φ x ip
  | ge_ind_alias _ _ _ _ => None
  end.

Lemma gm_subbody_ext_here : forall T Φ x E z ip r,
    ge_subbody T E z ip = Some r -> gm_subbody T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [Φ' | E']] | ? ? ? | ? ? ? ?]; cbn in H; [ discriminate | exact H | | exact H | discriminate ].
  destruct z; discriminate.
Qed.

(** [Ctb Θ2 Ξ2 T mp E]: the target [Θ2 ⍮ Ξ2] has, at the path [mp], what
    the entry [E], checked over the telescope [T], contributes: its
    definitions, its module and its submodules, its body and its sub-bodies,
    these perhaps grown. *)
Definition Ctb (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (mp : qname) (E : gentry) : Prop :=
  (forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> gc_resolve Θ2 Ξ2 (qname_app mp ip) = Some E0) /\
  (forall r, ge_module T E = Some r -> gc_module Θ2 Ξ2 mp = Some r) /\
  (forall x (ip : list String.string) r, ge_submodule T E x ip = Some r ->
     gc_module Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) /\
  (forall T' Φ, ge_selfbody T E = Some (T', Φ) ->
     exists Φ', gc_body Θ2 Ξ2 mp = Some (T', Φ') /\ gm_grows Φ Φ') /\
  (forall x (ip : list String.string) T' Φ, ge_subbody T E x ip = Some (T', Φ) ->
     exists Φ', gc_body Θ2 Ξ2 (qname_app mp (x :: ip)) = Some (T', Φ') /\ gm_grows Φ Φ') /\
  (forall (ip : list String.string) v, ge_ind_targets E ip = Some v -> ind_alias_lookup Θ2 Ξ2 (qname_app mp ip) = Some v).

(** What a frame extended by an entry contributes, at an embedding of it. *)
Lemma Ctb_frame : forall Θ mp Δ Φ x E Ξ Θ2 Ξ2,
    gc_sub Θ ((mp, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ) Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (Δ ++ gs_tele Ξ) (qname_in mp x) E.
Proof.
  intros * Hs; repeat split.
  - intros ip0 E1 HE1; rewrite qname_app_in; apply (gc_sub_resolve _ _ _ _ _ _ Hs).
    rewrite gc_resolve_frame_here; cbn [gu_mod]; rewrite gm_resolve_ext_here; exact HE1.
  - intros r Hr0; rewrite <- (qname_app_nil (qname_in _ _)), qname_app_in; apply (gc_sub_module _ _ _ _ _ _ Hs).
    rewrite gc_module_frame_here; cbn [gu_mod gu_params]; rewrite gm_submodule_ext_here_nil; exact Hr0.
  - intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_sub_module _ _ _ _ _ _ Hs).
    rewrite gc_module_frame_here; cbn [gu_mod gu_params]; apply gm_submodule_ext_here; exact Hr0.
  - intros T' Φ' Hr0; rewrite <- (qname_app_nil (qname_in _ _)), qname_app_in; apply (gc_sub_body _ _ _ _ _ _ _ Hs).
    rewrite gc_body_frame_here; cbn [gu_mod gu_params]; rewrite gm_subbody_ext_here_nil; exact Hr0.
  - intros z ip0 T' Φ' Hr0; rewrite qname_app_in; apply (gc_sub_body _ _ _ _ _ _ _ Hs).
    rewrite gc_body_frame_here; cbn [gu_mod gu_params]; apply gm_subbody_ext_here; exact Hr0.
  - intros ip0 v Hv; rewrite qname_app_in; apply (gc_sub_ind_alias _ _ _ _ _ _ Hs).
    rewrite ind_alias_lookup_frame_here; cbn [gu_mod]; rewrite gm_ind_target_ext_here; exact Hv.
Qed.

(** Pushing a nested module's frame embeds into any context that has its
    entries, submodules and bodies where the frame says. *)
Lemma Emb_nested : forall Θ Ξ mp Δ' Φ' Θ2 Ξ2,
    Emb Θ Ξ Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (gs_tele Ξ) mp (ge_body false Δ' Φ') ->
    Emb Θ ((mp, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof.
  intros * [Hg Hs] (Hin & _ & Hmod & _ & Hbod & Hia); constructor; [ assumption | split; [| split; [| split ] ] ].
  - intros p E Hr; destruct (gc_resolve_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      eauto using gc_sub_resolve.
  - intros p r Hr; destruct (gc_module_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      eauto using gc_sub_module.
  - intros p T Φ Hr; destruct (gc_body_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      eauto using gc_sub_body.
  - intros p v Hr; destruct (ind_alias_lookup_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      [| eauto using gc_sub_ind_alias ].
    destruct ip as [| z ip]; [ cbn [gu_mod] in Hm; rewrite gm_ind_target_nil in Hm; discriminate |].
    apply Hia; exact Hm.
Qed.

(** Declaring an entry in the innermost frame embeds into any context that
    has what the entry contributes, where the frame says. *)
Lemma Emb_entry : forall Θ mq Δ Φ0 Ξ y E Θ2 Ξ2,
    Emb Θ ((mq, gu_body Δ Φ0) :: Ξ) Θ2 Ξ2 ->
    Ctb Θ2 Ξ2 (Δ ++ gs_tele Ξ) (qname_in mq y) E ->
    Emb Θ ((mq, gu_body Δ (Φ0 ⊳ y ↦ E)) :: Ξ) Θ2 Ξ2.
Proof.
  intros * [Hg Hs] (Hin & Hm0 & Hmod & Hb0 & Hbod & Hia); constructor; [ assumption | split; [| split; [| split ] ] ].
  - intros p E0 Hr; unfold gc_resolve, gc_resolve_u in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; cbn [gu_mod] in Hr.
      destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ].
      * rewrite <- qname_app_in; exact (Hin _ _ HE).
      * apply (gc_sub_resolve _ _ _ _ _ _ Hs); rewrite gc_resolve_frame_here; exact HΦ.
    + apply (gc_sub_resolve _ _ _ _ _ _ Hs); unfold gc_resolve, gc_resolve_u; cbn; rewrite Hst; exact Hr.
  - intros p r Hr; unfold gc_module, gc_module_u in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; destruct ip as [| x ip]; [ discriminate |]; cbn [gu_mod gu_params] in Hr.
      destruct (gm_submodule_ext_inv _ _ _ _ _ _ _ Hr) as [(-> & -> & HE) | [(z & ip' & -> & -> & HE) | HΦ]].
      * rewrite <- (qname_app_in mq y nil), qname_app_nil; exact (Hm0 _ HE).
      * rewrite <- qname_app_in; exact (Hmod _ _ _ HE).
      * apply (gc_sub_module _ _ _ _ _ _ Hs); rewrite gc_module_frame_here; exact HΦ.
    + apply (gc_sub_module _ _ _ _ _ _ Hs); unfold gc_module, gc_module_u; cbn; rewrite Hst; exact Hr.
  - intros p T Φ Hr; unfold gc_body in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; destruct ip as [| x ip]; [ discriminate |]; cbn [gu_mod gu_params gm_subbody] in Hr.
      destruct (String.eqb_spec x y) as [-> |].
      * destruct ip as [| z ip'].
        -- rewrite <- (qname_app_in mq y nil), qname_app_nil; apply Hb0.
           rewrite <- (gm_subbody_ext_here_nil _ Φ0 y); cbn; rewrite String.eqb_refl; exact Hr.
        -- rewrite <- qname_app_in; apply Hbod.
           destruct E as [| ? [Δ' [Φ' | E']] | ? ? ? | ? ? ? ?]; cbn in *; try discriminate; exact Hr.
      * apply (gc_sub_body _ _ _ _ _ _ _ Hs); rewrite gc_body_frame_here; exact Hr.
    + apply (gc_sub_body _ _ _ _ _ _ _ Hs); unfold gc_body; cbn; rewrite Hst; exact Hr.
  - intros p v Hr; unfold ind_alias_lookup, ind_alias_lookup_u in Hr; cbn in Hr.
    destruct (qname_strip mq p) as [ip |] eqn:Hst.
    + apply qname_strip_app_inv in Hst as ->; cbn [gu_mod] in Hr.
      destruct (gm_ind_target_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ].
      * rewrite <- qname_app_in; exact (Hia _ _ HE).
      * apply (gc_sub_ind_alias _ _ _ _ _ _ Hs); rewrite ind_alias_lookup_frame_here; exact HΦ.
    + apply (gc_sub_ind_alias _ _ _ _ _ _ Hs); unfold ind_alias_lookup, ind_alias_lookup_u; cbn; rewrite Hst; exact Hr.
Qed.

(** An inductive type contributes what it did before one more member. *)
Lemma Ctb_ind_ext : forall Θ2 Ξ2 T mp pv D Φ x b pv' A B,
    gm_fresh x Φ -> Ctb Θ2 Ξ2 T mp (ge_ind pv D (Φ ⊳ x ↦ ge_def b pv' A B)) -> Ctb Θ2 Ξ2 T mp (ge_ind pv D Φ).
Proof.
  intros * Hf (Hin & Hm0 & Hmod & Hb0 & Hbod & Hia); repeat split.
  - intros ip E0 HE; apply Hin; cbn [ge_entries] in HE |- *; apply gm_resolve_ext_fresh; assumption.
  - exact Hm0.
  - intros z ip r Hr; apply Hmod; cbn [ge_submodule] in Hr |- *; apply gm_submodule_ext_fresh; assumption.
  - intros T' Φ' HB; cbn [ge_selfbody] in HB; injection HB as <- <-.
    destruct (Hb0 _ _ eq_refl) as (Φ'' & HΦ'' & Hg); exists Φ''; split; [ exact HΦ'' |].
    eapply gm_grows_trans; [| exact Hg ]; apply gmg_ext; [ constructor | assumption ].
  - intros z ip T' Φ' HB; apply Hbod; cbn [ge_subbody] in HB |- *; apply gm_subbody_ext_fresh; assumption.
  - intros [| z ip] v Hv; [ discriminate |]; apply Hia; cbn [ge_ind_targets] in Hv |- *.
    apply gm_ind_target_ext_fresh; assumption.
Qed.

(** The telescope of the frames' parameters is a well-formed context: the
    innermost frame's module was checked over it, one frame out, and pushing
    the frame is an embedding. *)
Lemma wf_gs_tele : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ.
Proof.
  intros Θ [| [mp U] Ξ] Hg; [ constructor; exact Hg |].
  destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (Hs0 & HU & Hff).
  assert (HP : ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ)
    by exact (wf_gmod_ctx _ _ _ _ _ (wf_gunit_mod _ _ _ _ HU)).
  destruct (emb_preserves_wf Θ Ξ Θ ((mp, U) :: Ξ)) as (Hc & _).
  - constructor; [ exact Hg | apply gc_sub_push; exact Hff ].
  - exact (Hc _ HP).
Qed.

(** Every frame of a well-formed stack belongs to a unit not filed. *)
Lemma wf_gstack_frames : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall mp U, List.In (mp, U) Ξ -> gds_lookup Θ (q_unit mp) = None.
Proof.
  induction 1 as [| | Θ Ξ mq Δ Φ HΞ IH HV Hff]; intros mp V0 Hin; try (cbn in Hin; contradiction).
  destruct Hin as [[= <- <-] | Hin]; [| eauto ].
  destruct Ξ as [| [mr W] Ξ']; cbn in Hff.
  - exact (proj1 Hff).
  - destruct Hff as (x & -> & _); cbn; apply (IH mr W); left; reflexivity.
Qed.

(** What the derivation of a declaration gives, at any global context: its
    parameters, sort and the types of its constructors' arguments are well
    formed. *)
Definition decl_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : Prop :=
  tele_ass (ind_params D) /\ decl_mvc D /\ ind_nu D <= ind_np D /\
  ⊢ Θ ⍮ Ξ ⍮ ind_params D /\
  ind_sort_univ (ind_sort D) /\
  (exists i, Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort D : Typeω@i) /\
  (exists n, Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort_lvl (ind_sort D) : Level@n) /\
  (forall c gs gs1 A gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_arg A :: gs2 ->
     Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D
       ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + ind_nn D)]ʷ) /\
  (forall c gs gs1 t gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.length (ptyp_ps t) = ind_nn D) /\
  (forall c gs gs1 t gs2 k P T, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.nth_error (ptyp_ps t) k = Some P ->
     List.nth_error (tele_insts (ind_nparams D)
                       (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + ind_nn D))) (ptyp_ps t)) k
       = Some T ->
     Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ ind_params D ⊢ P : T) /\
  (forall Δ1 T Δ2, ind_nparams D = Δ1 ++ ce_ass T :: Δ2 ->
     Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ) /\
  List.NoDup (List.map fst (ind_cons D)) /\
  (forall c gs gs1 t gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
     ptyp_simple t = true /\
     forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ ind_params D
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + ind_nn D)]ʷ).

Lemma decl_typed_emb : forall Θ Ξ Θ2 Ξ2 D, Emb Θ Ξ Θ2 Ξ2 -> decl_typed Θ Ξ D -> decl_typed Θ2 Ξ2 D.
Proof.
  intros * He (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & [i Hi] & [n Hn] & HA & HPl & HP & HN & Hnd & Hsh).
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _).
  repeat split; eauto.
  all: match goal with Hi : In _ _, He' : _ = _ ++ ca_rec _ :: _ |- _ =>
         destruct (Hsh _ _ _ _ _ Hi He') as [Hs1 Hs2]; eauto end.
Qed.

(** ** The Types of a Declaration Are Types

    The type of the type former, of a constructor and of a recursive
    argument, at a declaration [decl_typed] says is well formed. *)

Lemma params_split : forall D, ind_params D = ind_nparams D ++ ind_uparams D.
Proof. intros; unfold ind_nparams, ind_uparams; symmetry; apply List.firstn_skipn. Qed.

(** The uniform parameters of a typed declaration are a well-formed
    telescope of assumptions. *)
Lemma decl_typed_uparams : forall Θ Ξ D, decl_typed Θ Ξ D -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D /\ tele_ass (ind_uparams D).
Proof.
  intros * (Ha & _ & _ & HP & _).
  rewrite params_split in Ha, HP; split; [ exact (ctx_app_wf_right _ _ _ _ HP) |].
  apply Forall_app in Ha as [_ Ha]; exact Ha.
Qed.

Lemma ind_sort_univ_wk : forall S φ, ind_sort_univ S -> ind_sort_univ S[φ]ʷ /\ (ind_sort_lvl S)[φ]ʷ = ind_sort_lvl S[φ]ʷ.
Proof. intros * [[i ->] | [t ->]]; cbn; unfold ind_sort_univ; split; eauto. Qed.

Lemma sort_large : forall Θ Ξ Γ S A n,
    ind_sort_univ S -> Θ ⍮ Ξ ⍮ Γ ⊢ ind_sort_lvl S : Level@n -> Θ ⍮ Ξ ⍮ Γ ⊢ A : S ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j.
Proof. intros * [[i ->] | [t ->]] HL HA; [ eauto | exists 0; eapply wf_exp_suniv_large; eassumption ]. Qed.

Lemma wf_wk_shiftn_app' : forall Θ Ξ E T, ⊢ Θ ⍮ Ξ ⍮ E ++ T -> Θ ⍮ Ξ ⍮ E ++ T ⊢w wk_shiftn (List.length E) : T.
Proof. intros; apply wf_wk_shiftn_app; [ assumption | eapply ctx_app_wf_tail; eassumption ]. Qed.

(** The sort, and its level, under the binders [E] above the uniform
    parameters. *)
Lemma sort_under : forall Θ Ξ D E,
    decl_typed Θ Ξ D -> ⊢ Θ ⍮ Ξ ⍮ E ++ ind_uparams D ->
    (exists i, Θ ⍮ Ξ ⍮ E ++ ind_uparams D ⊢ (ind_sort D)[wk_shiftn (List.length E)]ʷ : Typeω@i) /\
    (exists n, Θ ⍮ Ξ ⍮ E ++ ind_uparams D ⊢ ind_sort_lvl (ind_sort D)[wk_shiftn (List.length E)]ʷ : Level@n) /\
    ind_sort_univ (ind_sort D)[wk_shiftn (List.length E)]ʷ.
Proof.
  intros * (_ & _ & _ & _ & HS & [i Hi] & [n Hn] & _) HE.
  pose proof (wf_wk_shiftn_app' _ _ _ _ HE) as Hw.
  destruct (ind_sort_univ_wk (ind_sort D) (wk_shiftn (List.length E)) HS) as [HS' Hl].
  split; [| split; [| exact HS' ] ].
  - exists i; exact (wk_preserves_exp _ _ _ _ _ _ _ Hi Hw).
  - exists n; rewrite <- Hl; exact (wk_preserves_exp _ _ _ _ _ _ _ Hn Hw).
Qed.

(** The variables [#(|Φ| + |Δ| - 1)], …, [#|Φ|] are of the types of the
    closed telescope [Δ] under [Φ], one by one. *)
Lemma wf_vars_tele : forall Θ Ξ Φ Δ,
    tele_ass Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> ⊢ Θ ⍮ Ξ ⍮ Φ ++ Δ ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      Θ ⍮ Ξ ⍮ Φ ++ Δ ⊢ N : T.
Proof.
  intros * Hass Hs Hmv HΔ k N T HN HT.
  apply vars_from_nth_error in HN as [Hk ->].
  apply tele_insts_nth in HT as (A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HsA : exp_scoped k A).
  { rewrite HΔeq in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HsA _].
    rewrite List.length_rev, Nat.add_0_r in HsA; congruence. }
  assert (HmA : exp_mvc 0 A).
  { unfold ctx_mvc in Hmv; rewrite HΔeq in Hmv; apply List.Forall_app in Hmv as [_ Hmv].
    apply List.Forall_cons_iff in Hmv as [HmA _]; exact HmA. }
  replace (A[sb_of_list Id (List.firstn k (vars_from (List.length Φ) (List.length Δ)))])
    with (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ).
  - apply wf_vlookup; [ exact HΔ |].
    replace (List.length Φ + (List.length Δ - 1 - k)) with (0 + List.length (Φ ++ List.rev l2))
      by (rewrite List.length_app, List.length_rev; lia).
    replace (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ)
      with (A[↑]ʷ[wk_shiftn (List.length (Φ ++ List.rev l2))]ʷ)
      by (rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app, List.length_rev; lia).
    rewrite HΔeq, List.app_assoc.
    apply ctx_lookup_app_r; constructor.
  - rewrite <- exp_sub_of_wk; eapply exp_scoped_mvc_agree; [ exact HsA | exact HmA |].
    intros x Hx; rewrite sb_of_list_firstn_vars by lia; cbn; f_equal; lia.
Qed.

(** A term of a [Π] over a closed telescope applies to terms of its types. *)
Lemma wf_apps_closed_pi : forall Θ Ξ Δ B i Ψ M Ms,
    tele_ass Δ -> ctx_scoped 0 Δ -> exp_scoped (List.length Δ) B -> Θ ⍮ Ξ ⍮ Δ ⊢ B : Typeω@i ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ -> Θ ⍮ Ξ ⍮ Ψ ⊢ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ apps M Ms : B[sb_of_list Id Ms].
Proof.
  intros * Hass Hs HsB HB HΨ HM Hl HMs.
  assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ Δ ++ ⋅) by (rewrite List.app_nil_r; eapply presup_exp_ctx; exact HB).
  pose proof (wf_wk_shiftn_app Θ Ξ Ψ ⋅) as Hw; rewrite List.app_nil_r in Hw.
  specialize (Hw HΨ ltac:(constructor; eapply ctx_wf_gctx; eassumption)).
  assert (HΔΨ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Ψ).
  { pose proof (wk_preserves_ext _ _ _ _ _ _ _ (ctx_ext_refl _ _ _ _ Hass HΔ0) Hw) as Hx.
    rewrite tele_closed_wk in Hx by exact Hs; eapply ext_eq_ctx_left; exact Hx. }
  eapply wf_apps_ctx_pi; [ exact Hass | exact HΔΨ | | exact HM | exact Hl | exact HMs ].
  pose proof (wf_wk_ext _ _ Δ _ _ _ Hw) as Hq.
  rewrite tele_closed_wk in Hq by exact Hs; specialize (Hq HΔΨ HΔ0).
  rewrite <- (exp_scoped_wk_id B (List.length Δ + 0) (wk_qn (List.length Δ) (wk_shiftn (List.length Ψ))))
    by (rewrite Nat.add_0_r; assumption || (intros; apply wk_qn_fix with (n := 0); [ lia | lia ])).
  assert (HB0 : Θ ⍮ Ξ ⍮ Δ ++ ⋅ ⊢ B : Typeω@i) by (rewrite List.app_nil_r; exact HB).
  exact (wk_preserves_exp _ _ _ _ _ _ _ HB0 Hq).
Qed.

Lemma ind_sort_shift_typed : forall Θ Ξ D,
    decl_typed Θ Ξ D -> exists i, Θ ⍮ Ξ ⍮ ind_params D ⊢ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ : Typeω@i.
Proof.
  intros * HD; pose proof HD as (_ & _ & _ & HΔ & _).
  rewrite params_split in HΔ |- *.
  destruct (sort_under _ _ _ _ HD HΔ) as ([i Hi] & _); rewrite length_nparams in Hi; eauto.
Qed.

Lemma ind_ty_typed0 : forall Θ Ξ D, decl_typed Θ Ξ D -> exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ind_ty D : Typeω@j.
Proof.
  intros * HD; destruct (ind_sort_shift_typed _ _ _ HD) as [i Hi].
  unfold ind_ty; eapply ctx_pi_wf0; exact Hi.
Qed.

Lemma ind_ty_typed : forall Θ Ξ Γ D,
    decl_typed Θ Ξ D -> decl_closed D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty D : Typeω@j.
Proof.
  intros * HD Hc HΓ; destruct (ind_ty_typed0 _ _ _ HD) as [j Hj]; exists j.
  eapply closed_weaken_exp; [ exact HΓ | exact Hj | apply decl_closed_ind_ty, Hc | exact I ].
Qed.

(** The type former applied to terms of the parameters' types, of which the
    type is the sort at them. *)
Lemma wf_ind_apps : forall Θ Ξ Ψ p D Ms,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Ψ ->
    List.length Ms = ind_np D ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts (ind_params D) Id Ms) k = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind p) Ms : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms].
Proof.
  intros * HD Hc Hl HΨ HMl HMs.
  destruct (ind_sort_shift_typed _ _ _ HD) as [i Hi].
  pose proof Hc as (Hass & Hle & Hs & HsS & _).
  eapply wf_apps_closed_pi; [ exact Hass | exact Hs | | exact Hi | exact HΨ | | exact HMl | exact HMs ].
  - eapply exp_scoped_wk; [ exact HsS |]; intros x Hx; unfold wk_shiftn, ind_nn; unfold ind_np in *; lia.
  - eapply wf_ind; eassumption.
Qed.

(** The sort at variables, or at terms of variables, is the sort shifted. *)
Lemma sort_at_vars : forall D Ms j,
    exp_mvc 0 (ind_sort D) -> exp_scoped (ind_nu D) (ind_sort D) -> ind_nu D <= ind_np D ->
    List.length Ms = ind_nn D ->
    (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id (vars_from j (ind_nu D) ++ Ms)]
    = (ind_sort D)[wk_shiftn j]ʷ.
Proof.
  intros * Hm Hs Hle Hl.
  rewrite exp_sub_wk, <- exp_sub_of_wk; eapply exp_scoped_mvc_agree; [ exact Hs | exact Hm |].
  intros x Hx; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite sb_of_list_app, <- Hl, Nat.add_comm, sb_of_list_ge, sb_of_list_vars by exact Hx; cbn; f_equal; lia.
Qed.

(** The type at the uniform parameters and the non-uniform ones [Ps] of
    the context [Tb] over the parameters, moved into the context [E] over
    them by [wk_pat pat], is a type. *)
Lemma rec_leaf_typed : forall Θ Ξ p D E Tb pat Ps,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ ind_params D -> List.length pat = List.length E -> pat_nargs pat = List.length Tb ->
    Θ ⍮ Ξ ⍮ E ++ ind_params D ⊢w wk_pat pat : Tb ++ ind_params D ->
    List.length Ps = ind_nn D ->
    (forall k P T, List.nth_error Ps k = Some P ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length Tb + ind_nn D))) Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Tb ++ ind_params D ⊢ P : T) ->
    exists j, Θ ⍮ Ξ ⍮ E ++ ind_params D
      ⊢ apps (a_ind p) (ind_uvars D (List.length pat) ++ List.map (fun P => P[wk_pat pat]ʷ) Ps) : Typeω@j.
Proof.
  intros * HD Hc Hl HΨ Hpat Hpn Hφ HPl HP.
  pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _).
  pose proof Hc as (_ & _ & Hs & HsS & _).
  unfold ind_uvars.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (E ++ ind_nparams D) ++ ind_uparams D)
    by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
  assert (HlE : List.length (E ++ ind_nparams D) = List.length pat + ind_nn D)
    by (rewrite List.length_app, length_nparams, Hpat; reflexivity).
  assert (Huvars : vars_from (List.length pat + ind_nn D) (ind_nu D) = vars_from (List.length (E ++ ind_nparams D)) (List.length (ind_uparams D)))
    by (rewrite HlE, length_ind_uparams by exact Hle; reflexivity).
  assert (Hus : ctx_scoped 0 (ind_uparams D)).
  { rewrite params_split in Hs; apply ctx_scoped_app in Hs as [_ Hs]; exact Hs. }
  assert (Huass : tele_ass (ind_uparams D)) by (apply Forall_skipn'; exact Hass).
  assert (Humv : ctx_mvc (ind_uparams D)) by (apply Forall_skipn'; exact Hmv).
  pose proof (wf_ind_apps _ _ _ p D (vars_from (List.length pat + ind_nn D) (ind_nu D) ++ List.map (fun P => P[wk_pat pat]ʷ) Ps) HD Hc Hl HΨ)
    as HR.
  rewrite sort_at_vars in HR by (try rewrite List.length_map; assumption).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, <- params_split, HlE in Hn; rewrite HlE in HSu.
  eapply sort_large; [ exact HSu | exact Hn |].
  apply HR.
  - rewrite List.length_app, List.length_map, HPl; rewrite length_vars_from.
    unfold ind_nn in *; unfold ind_np in *; lia.
  - rewrite params_split; intros k N T HN HT.
    rewrite tele_insts_app in HT; [| exact Huass | rewrite length_vars_from, length_ind_uparams by exact Hle; reflexivity ].
    assert (Hl1 : List.length (vars_from (List.length pat + ind_nn D) (ind_nu D)) = ind_nu D) by apply length_vars_from.
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (vars_from (List.length pat + ind_nn D) (ind_nu D))) = ind_nu D)
      by (rewrite length_tele_insts by exact Huass; rewrite Hl1, length_ind_uparams by exact Hle; lia).
    destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      rewrite List.app_assoc; rewrite Huvars in HN, HT.
      eapply wf_vars_tele; [ exact Huass | exact Hus | exact Humv | exact HE | exact HN | exact HT ].
    + rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
      rewrite Hl1 in HN; rewrite Hl2 in HT.
      apply nth_error_map_inv in HN as (P & HPk & ->).
      set (s := List.length Tb + ind_nn D).
      assert (Hti : tele_insts (ind_nparams D) (sb_of_list Id (vars_from (List.length pat + ind_nn D) (ind_nu D))) (List.map (fun P => P[wk_pat pat]ʷ) Ps)
                    = List.map (fun T => T[wk_pat pat]ʷ) (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn s)) Ps)).
      { rewrite <- !map_sub_of_wk; symmetry.
        eapply (tele_insts_sub_mvc _ (ind_nu D));
          [ apply decl_closed_nparams_ass, Hc | apply Forall_firstn'; exact Hmv | apply decl_closed_nparams_scoped, Hc |].
        intros x Hx; rewrite sb_of_list_vars by exact Hx; cbn.
        unfold s; rewrite <- Hpn.
        replace (x + (pat_nargs pat + ind_nn D)) with (pat_nargs pat + (ind_nn D + x)) by lia.
        rewrite wk_pat_ge; f_equal; lia. }
      rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      rewrite <- params_split.
      exact (wk_preserves_exp _ _ _ _ _ _ _ (HP _ _ _ HPk HT0) Hφ).
Qed.

Lemma doms_ctx_cons : forall B Bs, doms_ctx (B :: Bs) = doms_ctx Bs ++ ce_ass B :: nil.
Proof. reflexivity. Qed.

Lemma ptyp_tele_pi : forall B t, ptyp_tele (pt_pi B t) = ptyp_tele t ++ ce_ass B :: nil.
Proof. reflexivity. Qed.

(** The type of a shape is a type: by its domains, each at the sort, and
    its leaf. *)
Lemma rec_shape_typed : forall Θ Ξ p D t E Tb pat,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ ind_params D -> List.length pat = List.length E -> pat_nargs pat = List.length Tb ->
    Θ ⍮ Ξ ⍮ E ++ ind_params D ⊢w wk_pat pat : Tb ++ ind_params D ->
    List.length (ptyp_ps t) = ind_nn D ->
    (forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ Tb ++ ind_params D
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length Tb + ind_nn D)]ʷ) ->
    (forall k P T, List.nth_error (ptyp_ps t) k = Some P ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + List.length Tb + ind_nn D))) (ptyp_ps t)) k
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ Tb ++ ind_params D ⊢ P : T) ->
    exists j, Θ ⍮ Ξ ⍮ E ++ ind_params D ⊢ ptyp_ty p D pat t : Typeω@j.
Proof.
  intros Θ Ξ p D t; induction t as [k Ps | k Ps | B t IH]; intros * HD Hc Hl HΨ Hpat Hpn Hφ HPl HB HP; cbn [ptyp_ty].
  1, 2: eapply rec_leaf_typed; eassumption.
  pose proof (HB nil B (ptyp_doms t) eq_refl) as HB0; cbn [doms_ctx List.rev List.map List.app List.length] in HB0.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (Tb ++ ind_nparams D) ++ ind_uparams D)
    by (rewrite <- List.app_assoc, <- params_split; exact (wf_wk_cod _ _ _ _ _ Hφ)).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, <- params_split, List.length_app, length_nparams in Hn; rewrite List.length_app, length_nparams in HSu.
  destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j1 Hj1].
  pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj1 Hφ) as Hj1'; cbn in Hj1'.
  destruct (IH (ce_ass B[wk_pat pat]ʷ :: E) (ce_ass B :: Tb) (false :: pat) HD Hc Hl) as [j2 Hj2].
  - cbn [List.app]; econstructor; exact Hj1'.
  - cbn; lia.
  - cbn; lia.
  - cbn [List.app wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj1 | exact Hj1' ].
  - exact HPl.
  - intros Bs1 B' Bs2 E'; specialize (HB (B :: Bs1) B' Bs2 ltac:(cbn; rewrite E'; reflexivity)).
    rewrite doms_ctx_cons, <- List.app_assoc in HB; cbn [List.app List.length] in HB |- *.
    replace (List.length Bs1 + S (List.length Tb) + ind_nn D) with (S (List.length Bs1) + List.length Tb + ind_nn D) by lia; exact HB.
  - intros k P T HPk HT; specialize (HP k P T HPk).
    unfold ptyp_depth in HP, HT; cbn [ptyp_doms List.length] in HP.
    rewrite ptyp_tele_pi, <- List.app_assoc in HP; cbn [List.app List.length] in HT |- *.
    apply HP; cbn [ptyp_ps].
    replace (S (length (ptyp_doms t)) + length Tb + ind_nn D) with (length (ptyp_doms t) + S (length Tb) + ind_nn D) by lia; exact HT.
  - exists (max j1 j2); eapply wf_pi; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_max_right; exact Hj2 ].
Qed.

(** The arguments before a constructor's argument are a well-formed
    context, which [wk_pat] sends to the one of the non-recursive arguments
    before it. *)
Lemma cargs_ctx_wf : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 gs2, gs = gs1 ++ gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D gs1 ++ ind_params D /\ ⊢ Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D /\
      Θ ⍮ Ξ ⍮ cargs_ctx p D gs1 ++ ind_params D ⊢w wk_pat (cargs_pat gs1) : cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hc Hl Hin gs1; induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
  - pose proof HD as (_ & _ & _ & HΔ & _).
    split; [ exact HΔ | split; [ exact HΔ | exact (wf_wk_id _ _ _ HΔ) ] ].
  - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
    destruct (IH _ Heq) as (HΨ & HSt & Hφ).
    rewrite cargs_ctx_snoc, cargs_pat_snoc.
    pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _ & _ & HA & HPl & HP & _).
    destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app].
    + rewrite cargs_strat_snoc_arg.
      specialize (HA _ _ _ _ _ Hin Heq).
      assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
        by (rewrite <- List.app_assoc, <- params_split; exact HSt).
      destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
      rewrite <- List.app_assoc, <- params_split, List.length_app, length_nparams in Hn; rewrite List.length_app, length_nparams in HSu.
      destruct (sort_large _ _ _ _ _ _ HSu Hn HA) as [j Hj].
      pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj Hφ) as Hj'; cbn in Hj'.
      split; [ econstructor; exact Hj' | split; [ econstructor; exact Hj |] ].
      cbn [wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj | exact Hj' ].
    + rewrite cargs_strat_snoc_rec.
      pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
      destruct (rec_shape_typed _ _ p D Ps (cargs_ctx p D gs1) (cargs_strat gs1) (cargs_pat gs1) HD Hc Hl HΨ
                  ltac:(rewrite length_cargs_pat, length_cargs_ctx; reflexivity) (pat_nargs_cargs_pat gs1) Hφ
                  (HPl _ _ _ _ _ Hin Heq) (proj2 (Hsh _ _ _ _ _ Hin Heq)) (fun k P T => HP _ _ _ _ _ k P T Hin Heq)) as [j Hj].
      split; [ econstructor; exact Hj | split; [ exact HSt |] ].
      cbn [wk_pat]; eapply wf_wk_compose; [ apply wf_wk_shift; econstructor; exact Hj | exact Hφ ].
Qed.



(** ** The Shapes of the Recursive Arguments, Domain by Domain *)

Lemma doms_ctx_length : forall Bs, List.length (doms_ctx Bs) = List.length Bs.
Proof. intros; unfold doms_ctx; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma doms_ctx_app : forall Bs1 Bs2, doms_ctx (Bs1 ++ Bs2) = doms_ctx Bs2 ++ doms_ctx Bs1.
Proof. intros; unfold doms_ctx; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma repeat_false_cons : forall n (l : list bool), List.repeat false n ++ false :: l = false :: List.repeat false n ++ l.
Proof. induction n as [| n IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma sh_ctx_snoc : forall Bs pat B,
    sh_ctx pat (Bs ++ B :: nil) = ce_ass B[wk_pat (List.repeat false (List.length Bs) ++ pat)]ʷ :: sh_ctx pat Bs.
Proof.
  induction Bs as [| B0 Bs IH]; intros; cbn [sh_ctx List.app List.length List.repeat]; [ reflexivity |].
  rewrite IH, repeat_false_cons; reflexivity.
Qed.

Lemma length_sh_ctx : forall Bs pat, List.length (sh_ctx pat Bs) = List.length Bs.
Proof. induction Bs as [| B Bs IH]; intros; cbn [sh_ctx]; [ reflexivity |]; rewrite List.length_app, IH; cbn; lia. Qed.

Lemma ptyp_ps_skip : forall k t, ptyp_ps (ptyp_skip k t) = ptyp_ps t.
Proof. induction k as [| k IH]; intros [k0 Ps | k0 Ps | B t]; cbn; auto. Qed.

Lemma ptyp_doms_skip : forall k t, ptyp_doms (ptyp_skip k t) = List.skipn k (ptyp_doms t).
Proof. induction k as [| k IH]; intros [k0 Ps | k0 Ps | B t]; cbn; auto. Qed.

Lemma pat_nargs_falses : forall k pat, pat_nargs (List.repeat false k ++ pat) = k + pat_nargs pat.
Proof. induction k as [| k IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma doms_split_nth : forall (Bs : list exp) k B, List.nth_error Bs k = Some B ->
    Bs = List.firstn k Bs ++ B :: List.skipn (S k) Bs /\ List.firstn (S k) Bs = List.firstn k Bs ++ B :: nil.
Proof.
  induction Bs as [| B0 Bs IH]; intros [| k] B H; simpl in H; try discriminate.
  - injection H as ->; simpl; split; reflexivity.
  - destruct (IH _ _ H) as [H1 H2]; split; simpl; f_equal; [ exact H1 | exact H2 ].
Qed.

(** The non-recursive arguments before an argument of a constructor are a
    well-formed context over the parameters. *)
Lemma cargs_strat_wf : forall Θ Ξ D c gs, decl_typed Θ Ξ D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 gs2, gs = gs1 ++ gs2 -> ⊢ Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hin gs1; induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
  - pose proof HD as (_ & _ & _ & HΔ & _); exact HΔ.
  - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
    pose proof (IH _ Heq) as HSt.
    destruct g as [A | t]; [| rewrite cargs_strat_snoc_rec; exact HSt ].
    rewrite cargs_strat_snoc_arg.
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & HA & _).
    specialize (HA _ _ _ _ _ Hin Heq).
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- List.app_assoc, <- params_split; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- List.app_assoc, <- params_split, List.length_app, length_nparams in Hn; rewrite List.length_app, length_nparams in HSu.
    destruct (sort_large _ _ _ _ _ _ HSu Hn HA) as [j Hj].
    econstructor; exact Hj.
Qed.

(** The domains of a recursive argument's shape before the [k]-th, over
    the non-recursive arguments before it: a well-formed context. *)
Lemma doms_prefix_wf : forall Θ Ξ D c gs, decl_typed Θ Ξ D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> forall k, k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hin gs1 t gs2 Heq; induction k as [| k IH]; intros Hk.
  - cbn [List.firstn doms_ctx List.map List.rev List.app]; exact (cargs_strat_wf _ _ _ _ _ HD Hin gs1 _ Heq).
  - pose proof (IH ltac:(lia)) as HSt.
    destruct (List.nth_error (ptyp_doms t) k) as [B |] eqn:HB; [| apply List.nth_error_None in HB; lia ].
    destruct (doms_split_nth _ _ _ HB) as [Hsp Hf].
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
    destruct (Hsh _ _ _ _ _ Hin Heq) as [_ HBt].
    pose proof (HBt _ _ _ Hsp) as HB0.
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc, <- params_split; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc, <- params_split in Hn.
    replace (List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D))
      with (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1) + ind_nn D) in Hn, HSu
      by (rewrite !List.length_app, doms_ctx_length, length_nparams; lia).
    destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j Hj].
    rewrite Hf, doms_ctx_app; cbn [doms_ctx List.map List.rev List.app].
    econstructor; exact Hj.
Qed.

(** The domains of a recursive argument's shape before the [k]-th: a
    well-formed context over the arguments before it, which [wk_pat] sends
    to the one over the non-recursive arguments before it. *)
Lemma shape_prefix_wf : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> forall k, k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D /\
      ⊢ Θ ⍮ Ξ ⍮ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D /\
      Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
        ⊢w wk_pat (List.repeat false k ++ cargs_pat gs1) : doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hc Hl Hin gs1 t gs2 Heq; induction k as [| k IH]; intros Hk.
  - cbn [List.firstn sh_ctx doms_ctx List.map List.rev List.app List.repeat].
    exact (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs1 _ Heq).
  - destruct (IH ltac:(lia)) as (HΨ & HSt & Hφ).
    destruct (List.nth_error (ptyp_doms t) k) as [B |] eqn:HB; [| apply List.nth_error_None in HB; lia ].
    destruct (doms_split_nth _ _ _ HB) as [Hsp Hf].
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
    destruct (Hsh _ _ _ _ _ Hin Heq) as [_ HBt].
    pose proof (HBt _ _ _ Hsp) as HB0.
    assert (Lk : List.length (List.firstn k (ptyp_doms t)) = k) by (rewrite List.length_firstn; lia).
    assert (HE : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc, <- params_split; exact HSt).
    destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc, <- params_split in Hn.
    replace (List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D))
      with (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1) + ind_nn D) in Hn, HSu
      by (rewrite !List.length_app, doms_ctx_length, length_nparams; lia).
    destruct (sort_large _ _ _ _ _ _ HSu Hn HB0) as [j Hj].
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ Hj Hφ) as Hj'; cbn in Hj'.
    rewrite Hf, sh_ctx_snoc, doms_ctx_app, Lk; cbn [doms_ctx List.map List.rev List.app].
    split; [ econstructor; exact Hj' | split; [ econstructor; exact Hj |] ].
    cbn [List.repeat List.app wk_pat]; eapply wf_wk_q; [ exact Hφ | exact Hj | exact Hj' ].
Qed.

(** The rest of a recursive argument's type after [k] domains of its shape
    is a type, under those domains. *)
Lemma shape_rest_wf : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t).
Proof.
  intros * HD Hc Hl Hin gs1 t gs2 k Heq Hk.
  destruct (shape_prefix_wf _ _ _ _ _ _ HD Hc Hl Hin _ _ _ Heq k Hk) as (HΨ & HSt & Hφ).
  pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & HPl & HP & _ & _ & Hsh).
  destruct (Hsh _ _ _ _ _ Hin Heq) as [_ HBt].
  assert (Lk : List.length (List.firstn k (ptyp_doms t)) = k) by (rewrite List.length_firstn; lia).
  assert (Ht : ptyp_doms t = List.firstn k (ptyp_doms t) ++ ptyp_doms (ptyp_skip k t))
    by (rewrite ptyp_doms_skip, List.firstn_skipn; reflexivity).
  destruct (rec_shape_typed _ _ p D (ptyp_skip k t) (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1)
              (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1) (List.repeat false k ++ cargs_pat gs1) HD Hc Hl)
    as [j Hj].
  - rewrite <- List.app_assoc; exact HΨ.
  - rewrite !List.length_app, List.repeat_length, length_sh_ctx, length_cargs_pat, length_cargs_ctx; lia.
  - rewrite pat_nargs_falses, pat_nargs_cargs_pat, List.length_app, doms_ctx_length; lia.
  - rewrite <- !List.app_assoc; exact Hφ.
  - rewrite ptyp_ps_skip; exact (HPl _ _ _ _ _ Hin Heq).
  - intros Bs1 B Bs2 HBs.
    pose proof (HBt (List.firstn k (ptyp_doms t) ++ Bs1) B Bs2 ltac:(rewrite Ht at 1; rewrite HBs, <- List.app_assoc; reflexivity)) as H.
    rewrite doms_ctx_app, <- List.app_assoc in H.
    rewrite <- List.app_assoc, !List.length_app, doms_ctx_length.
    replace (List.length Bs1 + (List.length (List.firstn k (ptyp_doms t)) + List.length (cargs_strat gs1)) + ind_nn D)
      with (List.length (List.firstn k (ptyp_doms t) ++ Bs1) + List.length (cargs_strat gs1) + ind_nn D)
      by (rewrite List.length_app; lia).
    exact H.
  - intros m P T HPm HT.
    rewrite ptyp_ps_skip in HPm, HT.
    assert (Hd : ptyp_depth (ptyp_skip k t) + List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1)
                 = ptyp_depth t + List.length (cargs_strat gs1))
      by (unfold ptyp_depth; rewrite ptyp_doms_skip, List.length_app, doms_ctx_length, List.length_skipn; lia).
    rewrite Hd in HT.
    pose proof (HP _ _ _ _ _ m P T Hin Heq HPm HT) as H.
    unfold ptyp_tele in H |- *; rewrite Ht, doms_ctx_app, <- List.app_assoc in H.
    rewrite <- List.app_assoc; exact H.
  - rewrite <- List.app_assoc in Hj; econstructor; exact Hj.
Qed.

Corollary shape_rest_wf' : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
      ⊢ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t).
Proof. intros * HD Hc Hl Hcon; eapply shape_rest_wf; [ exact HD | exact Hc | exact Hl | exact (cons_lookup_in _ _ _ Hcon) ]. Qed.

(** The type of a constructor is a type. *)
Lemma con_cod_typed : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    exists j, Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ⊢ apps (a_ind p) (ind_pvars D (List.length gs)) : Typeω@j.
Proof.
  intros * HD Hc Hl Hcon.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ & _ & _).
  pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _ & _).
  pose proof Hc as (_ & _ & Hs & HsS & _).
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D)
    by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
  assert (HlE : List.length (cargs_ctx p D gs ++ ind_nparams D) = List.length gs + ind_nn D)
    by (rewrite List.length_app, length_cargs_ctx, length_nparams; reflexivity).
  destruct (sort_under _ _ _ _ HD HE) as (_ & [n Hn] & HSu).
  rewrite <- List.app_assoc, <- params_split, HlE in Hn; rewrite HlE in HSu.
  pose proof (wf_ind_apps _ _ _ p D (ind_pvars D (List.length gs)) HD Hc Hl HΨ) as HR.
  assert (Hpv : ind_pvars D (List.length gs) = vars_from (List.length gs + ind_nn D) (ind_nu D) ++ vars_from (List.length gs) (ind_nn D)).
  { unfold ind_pvars; rewrite vars_from_app; f_equal; unfold ind_nn; lia. }
  assert (Hty : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id (ind_pvars D (List.length gs))]
                = (ind_sort D)[wk_shiftn (List.length gs + ind_nn D)]ʷ)
    by (rewrite Hpv; apply sort_at_vars; [ assumption | assumption | assumption | apply length_vars_from ]).
  rewrite Hty in HR.
  { eapply sort_large; [ exact HSu | exact Hn |]; apply HR.
    - unfold ind_pvars; apply length_vars_from.
    - intros k N T HN HT.
      replace (ind_pvars D (List.length gs)) with (vars_from (List.length (cargs_ctx p D gs)) (List.length (ind_params D))) in HN, HT
        by (unfold ind_pvars, ind_np; rewrite length_cargs_ctx; reflexivity).
      eapply wf_vars_tele; [ exact Hass | exact Hs | exact Hmv | exact HΨ | exact HN | exact HT ]. }
Qed.

Lemma con_ty_typed0 : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@j.
Proof.
  intros * HD Hc Hl Hcon.
  destruct (con_cod_typed _ _ _ _ _ _ HD Hc Hl Hcon) as [j Hj].
  destruct (ctx_pi_wf0 _ _ _ _ _ Hj) as [j' Hj']; exists j'.
  unfold con_ty; rewrite <- ctx_pi_app; exact Hj'.
Qed.

Lemma con_ty_typed : forall Θ Ξ Γ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ con_ty p D gs : Typeω@j.
Proof.
  intros * HD Hc Hl Hcon HΓ; destruct (con_ty_typed0 _ _ _ _ _ _ HD Hc Hl Hcon) as [j Hj]; exists j.
  eapply closed_weaken_exp; [ exact HΓ | exact Hj | eapply decl_closed_con_ty; [ exact Hc | apply cons_lookup_in; exact Hcon ] | exact I ].
Qed.

(** The motive's instance at the non-uniform parameters and the scrutinee
    is a substitution into the motive's context. *)
Lemma wf_elim_inst_sub : forall Θ Ξ Γ p D Ps M,
    decl_closed D -> List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) : elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ.
Proof.
  intros * Hc HPl HPs HM HΨ.
  pose proof Hc as (Hass & Hle & _).
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
  assert (Hrass : tele_ass (tele_sub (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps))))
    by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
  apply wf_sub_of_list_id; [| exact HΨ | rewrite length_elim_mctx, List.length_app, HNl; cbn; lia |].
  - unfold elim_mctx; constructor; [ eauto | exact Hrass ].
  - intros k N T HN HT.
    unfold elim_mctx in HT.
    change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub, length_nparams; exact HNl).
    assert (Hl2 : List.length (tele_insts (tele_sub (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps))) Id
                                (List.skipn (ind_nu D) Ps)) = ind_nn D)
      by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_nparams, HNl; lia).
    destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id (List.firstn (ind_nu D) Ps))) in HT
        by apply sb_compose_id_right.
      apply (HPs (ind_nu D + k)).
      * rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + k - ind_nu D) with k by lia; exact HN.
      * rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite params_split, tele_insts_app;
          [| apply Forall_skipn'; exact Hass | rewrite HUl, length_ind_uparams by exact Hle; reflexivity ].
        rewrite List.nth_error_app2
          by (rewrite length_tele_insts by (apply Forall_skipn'; exact Hass); rewrite HUl, length_ind_uparams by exact Hle; lia).
        rewrite length_tele_insts by (apply Forall_skipn'; exact Hass); rewrite HUl, length_ind_uparams by exact Hle.
        rewrite Nat.min_id; replace (ind_nu D + k - ind_nu D) with k by lia; exact HT.
    + rewrite List.nth_error_app2 in HN, HT by lia; rewrite HNl in HN; rewrite Hl2 in HT.
      destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
      rewrite <- HNl, map_shift_sb_of_list, vars_from_sb_of_list.
      rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id, List.firstn_skipn; exact HM.
Qed.


Section Induction.
  (** [V Θ Ξ E]: the (closed) entry [E] is valid at [Θ ⍮ Ξ]; [VD Θ Ξ D]: so
      is the declaration [D] of an inductive type. *)
  Variable V : gdeps -> gstack -> gentry -> Prop.
  Variable VD : gdeps -> gstack -> ind_decl -> Prop.

  (** An inductive alias is valid as the definition it δ-unfolds to. *)
  Definition alias_def (Δ : ctx) (p : qname) (Ns : list exp) (D : ind_decl) : gentry :=
    ge_def false false (ctx_pi Δ (ind_ty_at D Ns)) (Some (ctx_fn Δ (apps (a_ind p) Ns))).

  (** The canonical path of a valid inductive alias names an inductive type,
      whose uniform parameters its arguments are for, and the alias is valid
      as the definition it δ-unfolds to. *)
  Definition alias_ok (Θ2 : gdeps) (Ξ2 : gstack) (Δ : ctx) (p : qname) (Ns : list exp) : Prop :=
    exists D, ind_lookup Θ2 Ξ2 p = Some D /\ List.length Ns <= ind_nu D /\ V Θ2 Ξ2 (alias_def Δ p Ns D).

  Definition GV (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
    (forall p E, gc_resolve Θ1 Ξ1 p = Some E -> V Θ2 Ξ2 E) /\
    (forall p D, ind_lookup Θ1 Ξ1 p = Some D -> VD Θ2 Ξ2 D) /\
    (forall pq Δ p Ns, ind_alias_lookup Θ1 Ξ1 pq = Some (Δ, p, Ns) -> alias_ok Θ2 Ξ2 Δ p Ns).

  (** Everything resolving at [Θ ⍮ Ξ] is valid wherever [Θ ⍮ Ξ] embeds. *)
  Definition Good (Θ : gdeps) (Ξ : gstack) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 -> GV Θ Ξ Θ2 Ξ2.

  (** How a definition and an axiom are made valid: from their derivation at
      the insertion context, given that its globals are valid.  A definition
      is checked in a closed telescope [T]: the frames' parameters, or the
      uniform parameters of the inductive type whose module it is a member
      of. *)
  Hypothesis Hdef : forall Θ Ξ T A M b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ T ⊢ M : A -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
  Hypothesis Hax : forall Θ Ξ A i b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
  (** And a declaration of an inductive type. *)
  Hypothesis Hind : forall Θ Ξ D Θ2 Ξ2,
      decl_typed Θ Ξ D -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> VD Θ2 Ξ2 D.

  (** What an entry contributes is valid wherever the context it is checked
      in embeds and the entry's contributions are found. *)
  Definition GoodE (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 -> Ctb Θ2 Ξ2 (gs_tele Ξ) mp E ->
      (forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> V Θ2 Ξ2 E0) /\
      (forall T D, ge_module (gs_tele Ξ) E = Some (mr_body T (Some D)) -> VD Θ2 Ξ2 D) /\
      (forall x (ip : list String.string) T D, ge_submodule (gs_tele Ξ) E x ip = Some (mr_body T (Some D)) -> VD Θ2 Ξ2 D) /\
      (forall (ip : list String.string) Δ p Ns, ge_ind_targets E ip = Some (Δ, p, Ns) -> alias_ok Θ2 Ξ2 Δ p Ns).

  Definition GoodM (Θ : gdeps) (Ξ : gstack) (mp : qname) (Δ : ctx) (Φ : gmod) : Prop :=
    forall Θ2 Ξ2, Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 ->
      (forall ip E0, gm_resolve Φ ip = Some E0 -> V Θ2 Ξ2 E0) /\
      (forall x ip T D, gm_submodule (Δ ++ gs_tele Ξ) Φ x ip = Some (mr_body T (Some D)) -> VD Θ2 Ξ2 D) /\
      (forall ip Δa p Ns, gm_ind_target Φ ip = Some (Δa, p, Ns) -> alias_ok Θ2 Ξ2 Δa p Ns).

  Theorem global_induction_all :
    (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Good Θ Ξ) /\
    (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Good Θ Ξ) /\
    (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Good Θ Ξ) /\
    (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Good Θ Ξ) /\
    (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Good Θ Ξ) /\
    (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Good Θ Ξ) /\
    (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Good Θ Ξ) /\
    (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> GoodE Θ Ξ mp E) /\
    (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> GoodM Θ Ξ mp Δ Φ) /\
    (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> Good Θ Ξ).
  Proof.
    apply wf_mut_ind_all; intros; try assumption.
    - (* an axiom *)
      intros Θ2 Ξ2 He _; split; [| split; [ discriminate | split; [ intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? Hx; discriminate ] ] ].
      intros [| ? ?] E0 HE; cbn in HE; inversion HE; subst; eauto.
    - (* a definition *)
      intros Θ2 Ξ2 He _; split; [| split; [ discriminate | split; [ intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? Hx; discriminate ] ] ].
      intros [| ? ?] E0 HE; cbn in HE; inversion HE; subst; eauto.
    - (* a nested module *)
      intros Θ2 Ξ2 He Hc.
      destruct (H0 _ _ (Emb_nested _ _ _ _ _ _ _ He Hc)) as (HE & HU & HA).
      split; [ exact HE | split; [ intros ? ? Hx; discriminate | split; [ exact HU |] ] ].
      intros [| z ip] ? ? ? Hx; [ discriminate | exact (HA _ _ _ _ Hx) ].
    - (* an alias: it contributes no entry and no declaration *)
      intros ? ? _ _; split; [ intros ip ? Hx; cbn in Hx; discriminate | split; [ discriminate | split; [ intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? Hx; discriminate ] ] ].
    - (* an inductive type, before the members of its module *)
      intros Θ2 Ξ2 He _; split; [ intros [| ? ?] ? Hx; discriminate | split; [| split; [ intros ? ? ? ? Hx; discriminate | intros [| ? ?] ? ? ? Hx; [ discriminate | unfold ge_ind_targets, gm_ind_target in Hx; discriminate ] ] ] ].
      intros T D0 [= _ <-].
      eapply Hind; [| eassumption | exact He ].
      repeat match goal with H : decl_mvc _ |- _ => destruct H as (? & ? & ?) end.
      repeat split; eauto.
    - (* one more member of the module of an inductive type *)
      rename H0 into IHE, H2 into IHM.
      intros Θ2 Ξ2 He (Hin & Hm0 & Hmod & Hb0 & Hbod & Hia).
      assert (Hc : Ctb Θ2 Ξ2 (gs_tele ((mq, gu_body Δ Φ0) :: Ξ)) (qname_in mq y) (ge_ind pv D Φ))
        by (eapply Ctb_ind_ext; [ eassumption | repeat split; eassumption ]).
      destruct (IHE _ _ He Hc) as (HΦE & HΦD & HΦU & HΦA).
      assert (He' : Emb Θ ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv D Φ)) :: Ξ) Θ2 Ξ2)
        by (apply Emb_entry; [ exact He | exact Hc ]).
      split; [| split; [ exact HΦD | split ] ].
      + intros ip E0 Hr; cbn [ge_entries] in Hr.
        destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ]; [| exact (HΦE _ _ HΦ) ].
        destruct ip'; cbn in HE; [ injection HE as <- | discriminate ].
        eapply Hdef; [ eassumption | exact IHM | exact He' ].
      + intros z ip T D0 Hr; cbn [ge_submodule] in Hr.
        destruct (gm_submodule_ext_inv _ _ _ _ _ _ _ Hr) as [(_ & _ & HE) | [(? & ? & _ & _ & HE) | HΦ]];
          [ discriminate | discriminate | exact (HΦU _ _ _ _ HΦ) ].
      + intros [| z ip] Δa pa Nsa Hx; [ discriminate |]; cbn [ge_ind_targets] in Hx.
        destruct (gm_ind_target_ext_inv _ _ _ _ _ Hx) as [(ip' & Hip & HE) | HΦ].
        * destruct ip'; discriminate.
        * exact (HΦA (z :: ip) _ _ _ HΦ).
    - (* an inductive alias: valid as the definition it unfolds to *)
      intros Θ2 Ξ2 He _.
      split; [ intros [| ? ?] ? Hx; discriminate | split; [ intros ? ? Hx; cbn in Hx; discriminate | split; [ intros ? ? ? ? Hx; cbn in Hx; discriminate |] ] ].
      intros [| ? ?] Δa pa Nsa Hx; [| discriminate ]; cbn in Hx; injection Hx as <- <- <-.
      match goal with HD : ind_lookup _ _ _ = Some ?D1 |- _ =>
        exists D1; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ He) HD) | split; [ assumption |] ] end.
      unfold alias_def; eapply Hdef; [ eassumption | | exact He ].
      match goal with H : Good _ _ |- _ => exact H end.
    - (* the empty module *)
      intros ? ? _; split; [ intros [| ? ?] ? Hx; discriminate | split; [ intros ? ? ? ? Hx; discriminate |] ].
      intros [| ? ?] ? ? ? Hx; unfold gm_ind_target in Hx; discriminate.
    - (* extending a module *)
      rename H0 into IHΦ, H2 into IHE.
      intros Θ2 Ξ2 He.
      assert (He' : Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Emb_pre; [ apply gc_sub_grow; eassumption | exact He ]).
      destruct (IHΦ _ _ He') as (HΦE & HΦU & HΦA).
      destruct (IHE _ _ He' (Ctb_frame _ _ _ _ _ _ _ _ _ (em_res _ _ _ _ He))) as (HEE & HEM & HEU & HEA).
      split; [| split ].
      + intros ip E0 Hr; destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ']; eauto.
      + intros z ip T D Hr.
        destruct (gm_submodule_ext_inv _ _ _ _ _ _ _ Hr) as [(_ & _ & HE) | [(? & ? & _ & _ & HE) | HΦ']]; eauto.
      + intros ip Δa pa Nsa Hx.
        destruct (gm_ind_target_ext_inv _ _ _ _ _ Hx) as [(ip' & -> & HE) | HΦ']; eauto.
    - (* nothing filed *)
      intros ? ? _; split; [ intros p E Hr; unfold gc_resolve, gc_resolve_u in Hr; cbn in Hr; discriminate
                           | split; [ intros p D Hr; unfold ind_lookup, ind_lookup_u, gc_module, gc_module_u in Hr; cbn in Hr; discriminate
                                    | intros pq ? ? ? Hr; unfold ind_alias_lookup, ind_alias_lookup_u in Hr; cbn in Hr; discriminate ] ].
    - (* a filed unit: it resolves as its closed frame did *)
      rename H into Hg, H0 into IHU.
      intros Θ2 Ξ2 He.
      destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (_ & _ & [Hn _]).
      destruct (IHU _ _ (Emb_pre _ _ _ _ _ _ (gc_sub_file _ _ U Hn) He)) as (HR & HI & HA).
      split; [ intros p E Hr; rewrite gc_resolve_file in Hr; eauto | split ].
      + intros p D Hr; rewrite ind_lookup_file in Hr; eauto.
      + intros pq ? ? ? Hr; rewrite ind_alias_lookup_file in Hr; eauto.
    - (* a frame *)
      rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He.
      assert (HeΞ : Emb Θ Ξ Θ2 Ξ2) by (eapply Emb_pre; [ apply gc_sub_push; eassumption | exact He ]).
      destruct (IHU _ _ He) as (HUE & HUU & HUA).
      destruct (IHΞ _ _ HeΞ) as (HR & HI & HA).
      split; [| split ].
      + intros p E Hr; destruct (gc_resolve_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr']; eauto.
      + intros p D Hr; destruct (ind_lookup_module _ _ _ _ Hr) as [T Hm].
        destruct (gc_module_frame _ _ _ _ _ _ Hm) as [(x & ip & -> & Hm') | Hm']; [ eauto |].
        apply (HI p); exact (ind_lookup_body _ _ _ _ _ Hm').
      + intros pq ? ? ? Hr; destruct (ind_alias_lookup_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr']; eauto.
  Qed.

  Corollary global_induction : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> GV Θ Ξ Θ Ξ.
  Proof.
    intros * Hg; destruct global_induction_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H).
    exact (H _ _ Hg _ _ (Emb_refl _ _ Hg)).
  Qed.
End Induction.

(** ** What Resolution Hands Back is Well Typed *)

Definition entry_typed (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Typeω@i) /\ (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A)
  | ge_mod _ _ | ge_ind _ _ _ | ge_ind_alias _ _ _ _ => True
  end.

Definition rwf (Θ : gdeps) (Ξ : gstack) : Prop := GV entry_typed decl_typed Θ Ξ Θ Ξ.

Lemma presup_exp_typ_rwf : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    rwf Θ Ξ ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  induction 1; intros HR;
    repeat match goal with IH : rwf _ _ -> _ |- _ => specialize (IH HR) end;
    assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2; destruct_conjs.
  (* a global: its type is a type at [⋅], and closed *)
  all: try match goal with
    | Hl : gc_resolve _ _ _ = Some (ge_def _ _ ?A _), HΓ : ⊢ _ ⍮ _ ⍮ _ |- _ =>
        destruct (proj1 HR _ _ Hl) as [[i HA] _]; exists i;
        eapply closed_weaken_exp;
        [ assumption | exact HA | eapply wf_gc_resolve_type_closed; eassumption | exact I ]
    end.
  (* an inductive alias: as the definition it unfolds to *)
  all: try match goal with
    | Hl : ind_alias_lookup _ _ _ = Some _, Hd : ind_lookup _ _ _ = Some _, HΓ : ⊢ _ ⍮ _ ⍮ _ |- _ =>
        destruct (proj2 (proj2 HR) _ _ _ _ Hl) as (D' & Hd' & _ & [i HA] & _);
        rewrite Hd in Hd'; injection Hd' as <-; exists i;
        eapply closed_weaken_exp;
        [ assumption | exact HA | exact (proj1 (wf_ind_alias_closed _ _ _ _ _ _ _ _ HΓ Hl Hd)) | exact I ]
    end.
  (* inductive types: the declaration's types are types, and the motive at
     the scrutinee *)
  all: try match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, HΓ : ⊢ _ ⍮ _ ⍮ ?Γ |- _ =>
        pose proof (proj1 (proj2 HR) _ _ Hl) as HDt;
        pose proof (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HΓ) Hl) as HDc
    end.
  all: try solve [ eapply ind_ty_typed; eassumption | eapply con_ty_typed; eassumption ].
  all: try solve [
    match goal with
    | HA : wf_exp _ _ (elim_mctx _ _ _ ++ _) _ ?A |- exists _, _ ⍮ _ ⍮ _ ⊢ ?A[_] : _ =>
        eexists; eapply (sub_preserves_exp _ _ _ _ _ _ _ HA); eapply wf_elim_inst_sub; eauto using ext_eq_ctx_left
    end ].
  all: mauto 3.
  all: eexists; mauto 3.
Qed.

Lemma entry_typed_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> Good entry_typed decl_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    entry_typed Θ2 Ξ2 (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM HG He.
  assert (Hg : ⊢g Θ ⍮ Ξ) by (eapply ctx_wf_gctx, presup_exp_ctx; exact HM).
  destruct (presup_exp_typ_rwf HM (HG _ _ (Emb_refl _ _ Hg))) as [i HA].
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; apply Ht, HT | intros ? [= <-]; apply Ht; eapply ctx_fn_wf0; eassumption ].
Qed.

Lemma entry_typed_ax : forall Θ Ξ A i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> Good entry_typed decl_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    entry_typed Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; apply Ht, HT | discriminate ].
Qed.

Lemma entry_typed_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> Good entry_typed decl_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> decl_typed Θ2 Ξ2 D.
Proof. intros * HD _ He; eapply decl_typed_emb; eassumption. Qed.

(** ** The Mutual Theorem *)

Theorem presup_global :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Good entry_typed decl_typed Θ Ξ) /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> GoodE entry_typed decl_typed Θ Ξ mp E) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> GoodM entry_typed decl_typed Θ Ξ mp Δ Φ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> Good entry_typed decl_typed Θ Ξ).
Proof. exact (global_induction_all entry_typed decl_typed entry_typed_def entry_typed_ax entry_typed_ind). Qed.

Corollary gctx_rwf : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> rwf Θ Ξ.
Proof. exact (global_induction entry_typed decl_typed entry_typed_def entry_typed_ax entry_typed_ind). Qed.

(** What a use of a global needs: its type and body, in any well-formed
    context. *)
Corollary wf_glob_typ : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * HΓ Hl; destruct (proj1 (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl) as [[i HA] _].
  exists i; eapply closed_weaken_exp;
    [ assumption | exact HA | eapply wf_gc_resolve_type_closed; eassumption | exact I ].
Qed.

Corollary wf_glob_body : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A (Some M)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hl; destruct (proj1 (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl) as [_ HM].
  eapply closed_weaken_exp;
    [ assumption | apply HM; reflexivity
    | eapply wf_gc_resolve_body_closed; eassumption
    | eapply wf_gc_resolve_type_closed; eassumption ].
Qed.

(** What a use of an inductive alias needs: its canonical path names an
    inductive type, its arguments are for uniform parameters, and the
    term it δ-unfolds to is typed, in any well-formed context. *)
Corollary wf_ind_alias : forall Θ Ξ Γ pq Δ p Ns,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_alias_lookup Θ Ξ pq = Some (Δ, p, Ns) ->
    exists D, ind_lookup Θ Ξ p = Some D /\ List.length Ns <= ind_nu D /\
      (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ (ind_ty_at D Ns) : Typeω@i) /\
      Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ (apps (a_ind p) Ns) : ctx_pi Δ (ind_ty_at D Ns).
Proof.
  intros * HΓ Hl.
  destruct (proj2 (proj2 (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ))) _ _ _ _ Hl) as (D & HD & Hle & [i HA] & HM).
  destruct (wf_ind_alias_closed _ _ _ _ _ _ _ _ HΓ Hl HD) as [HsA HsM].
  exists D; split; [ exact HD | split; [ exact Hle | split ] ].
  - exists i; eapply closed_weaken_exp; [ assumption | exact HA | exact HsA | exact I ].
  - eapply closed_weaken_exp; [ assumption | apply HM; reflexivity | exact HsM | exact HsA ].
Qed.

Theorem presup_exp_typ : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * H; eapply (presup_exp_typ_rwf H), gctx_rwf, ctx_wf_gctx, presup_exp_ctx, H.
Qed.
