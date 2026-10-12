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
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> member_unfold Θ1 Ξ1 Γ H x = Some M -> member_unfold Θ2 Ξ2 Γ H x = Some M.
Proof. intros * Hs; exact (member_unfold_gc_sub _ _ _ _ Hs _ _ _ _). Qed.

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
      try solve [ econstructor; eauto using gc_sub_resolve, member_type_emb, member_unfold_emb, ind_lookup_gc_sub ].
    all: econstructor; eauto. }
  destruct H as (Hc & He & Hq & Hst & Hx & Hu & Hm).
  repeat split; intros; eauto.
Qed.

(** ** The Induction over Insertion, for an Abstract Notion of Validity *)

(** The entries an entry contributes, read below its own path. *)
Definition ge_entries (E : gentry) (ip : list String.string) : option gentry :=
  match E with
  | ge_def _ _ _ _ | ge_ind _ _ => match ip with nil => Some E | _ => None end
  | ge_mod _ U => gm_resolve (gu_mod U) ip
  end.

Lemma gm_resolve_ext_here : forall Φ x E ip,
    gm_resolve (Φ ⊳ x ↦ E) (x :: ip) = ge_entries E ip.
Proof.
  intros; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| ? [Δ' [Φ' | E']] |]; cbn; rewrite ?gm_resolve_nil; reflexivity.
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
  intros * H; unfold gc_resolve in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; exists ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_resolve_frame_here : forall Θ mp U Ξ ip,
    gc_resolve Θ ((mp, U) :: Ξ) (qname_app mp ip) = gm_resolve (gu_mod U) ip.
Proof. intros; unfold gc_resolve; cbn; rewrite qname_strip_app; reflexivity. Qed.

Lemma gc_module_frame : forall Θ mp U Ξ p r,
    gc_module Θ ((mp, U) :: Ξ) p = Some r ->
    (exists x ip, p = qname_app mp (x :: ip) /\ gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip = Some r) \/
    gc_module Θ Ξ p = Some r.
Proof.
  intros * H; unfold gc_module in *; cbn in H.
  destruct (qname_strip mp p) as [ip |] eqn:Hs.
  - left; destruct ip as [| x ip]; [ discriminate |].
    exists x, ip; split; [ apply qname_strip_app_inv; assumption | exact H ].
  - right; exact H.
Qed.

Lemma gc_module_frame_here : forall Θ mp U Ξ x ip,
    gc_module Θ ((mp, U) :: Ξ) (qname_app mp (x :: ip)) = gm_submodule (gu_params U ++ gs_tele Ξ) (gu_mod U) x ip.
Proof. intros; unfold gc_module; cbn; rewrite qname_strip_app; reflexivity. Qed.

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

(** The submodules an entry contributes, read below its own path, for an
    entry checked over the telescope [T]. *)
Definition ge_submodule (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option modres :=
  match E with
  | ge_def _ _ _ _ | ge_ind _ _ => None
  | ge_mod _ U => gm_submodule (gu_params U ++ T) (gu_mod U) x ip
  end.

Lemma gm_submodule_ext_here : forall T Φ x E z ip r,
    ge_submodule T E z ip = Some r -> gm_submodule T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [Φ' | E']] |]; cbn in H; [ discriminate | exact H | | discriminate ].
  destruct z; discriminate.
Qed.

(** The body modules an entry contributes, read below its own path. *)
Definition ge_subbody (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ | ge_ind _ _ => None
  | ge_mod _ U => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  end.

Lemma gm_subbody_ext_here : forall T Φ x E z ip r,
    ge_subbody T E z ip = Some r -> gm_subbody T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| ? [Δ' [Φ' | E']] |]; cbn in H; [ discriminate | exact H | | discriminate ].
  destruct z; discriminate.
Qed.

(** Pushing a nested module's frame embeds into any context that has its
    entries and submodules where the frame says. *)
Lemma Emb_nested : forall Θ Ξ mp Δ' Φ' Θ2 Ξ2,
    Emb Θ Ξ Θ2 Ξ2 ->
    (forall ip E, gm_resolve Φ' ip = Some E -> gc_resolve Θ2 Ξ2 (qname_app mp ip) = Some E) ->
    (forall x ip r, gm_submodule (Δ' ++ gs_tele Ξ) Φ' x ip = Some r ->
       gc_module Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) ->
    (forall x ip r, gm_subbody (Δ' ++ gs_tele Ξ) Φ' x ip = Some r ->
       gc_body Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) ->
    Emb Θ ((mp, gu_body Δ' Φ') :: Ξ) Θ2 Ξ2.
Proof.
  intros * [Hg Hs] Hin Hmod Hbod; constructor; [ assumption | split; [| split ] ].
  - intros p E Hr; destruct (gc_resolve_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'];
      eauto using gc_sub_resolve.
  - intros p r Hr; destruct (gc_module_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      eauto using gc_sub_module.
  - intros p r Hr; destruct (gc_body_frame _ _ _ _ _ _ Hr) as [(x & ip & -> & Hm) | Hr'];
      eauto using gc_sub_body.
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
  (forall c gs gs1 Ps gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
     List.length Ps = ind_nn D) /\
  (forall c gs gs1 Ps gs2 k P T, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
     List.nth_error Ps k = Some P ->
     List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps) k
       = Some T ->
     Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D ⊢ P : T) /\
  (forall Δ1 T Δ2, ind_nparams D = Δ1 ++ ce_ass T :: Δ2 ->
     Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ) /\
  List.NoDup (List.map fst (ind_cons D)).

Lemma decl_typed_emb : forall Θ Ξ Θ2 Ξ2 D, Emb Θ Ξ Θ2 Ξ2 -> decl_typed Θ Ξ D -> decl_typed Θ2 Ξ2 D.
Proof.
  intros * He (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & [i Hi] & [n Hn] & HA & HPl & HP & HN & Hnd).
  destruct (emb_preserves_wf _ _ _ _ He) as (Hc & Ht & _).
  repeat split; eauto.
Qed.

(** ** The Types of a Declaration Are Types

    The type of the type former, of a constructor and of a recursive
    argument, at a declaration [decl_typed] says is well formed. *)

Lemma params_split : forall D, ind_params D = ind_nparams D ++ ind_uparams D.
Proof. intros; unfold ind_nparams, ind_uparams; symmetry; apply List.firstn_skipn. Qed.

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

(** A recursive argument is of the type at the uniform parameters and the
    non-uniform ones it is declared at. *)
Lemma rec_arg_typed : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> List.In (c, gs) (ind_cons D) ->
    forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D gs1 ++ ind_params D ->
      Θ ⍮ Ξ ⍮ cargs_ctx p D gs1 ++ ind_params D ⊢w wk_pat (cargs_pat gs1) : cargs_strat gs1 ++ ind_params D ->
      exists j, Θ ⍮ Ξ ⍮ cargs_ctx p D gs1 ++ ind_params D
        ⊢ apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps)
        : Typeω@j.
Proof.
  intros * HD Hc Hl Hin gs1 Ps gs2 Heq HΨ Hφ.
  pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _ & _ & HA & HPl & HP & _).
  pose proof Hc as (_ & _ & Hs & HsS & _).
  specialize (HPl _ _ _ _ _ Hin Heq).
  set (pat := cargs_pat gs1).
  unfold ind_uvars.
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  assert (HE : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D gs1 ++ ind_nparams D) ++ ind_uparams D)
    by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
  assert (HlE : List.length (cargs_ctx p D gs1 ++ ind_nparams D) = List.length pat + ind_nn D)
    by (rewrite List.length_app, length_cargs_ctx, length_nparams, Hpat; reflexivity).
  assert (Huvars : vars_from (List.length pat + ind_nn D) (ind_nu D) = vars_from (List.length (cargs_ctx p D gs1 ++ ind_nparams D)) (List.length (ind_uparams D)))
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
      set (s := List.length (cargs_strat gs1) + ind_nn D).
      assert (Hti : tele_insts (ind_nparams D) (sb_of_list Id (vars_from (List.length pat + ind_nn D) (ind_nu D))) (List.map (fun P => P[wk_pat pat]ʷ) Ps)
                    = List.map (fun T => T[wk_pat pat]ʷ) (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn s)) Ps)).
      { rewrite <- !map_sub_of_wk; symmetry.
        eapply (tele_insts_sub_mvc _ (ind_nu D));
          [ apply decl_closed_nparams_ass, Hc | apply Forall_firstn'; exact Hmv | apply decl_closed_nparams_scoped, Hc |].
        intros x Hx; rewrite sb_of_list_vars by exact Hx; cbn.
        unfold s; rewrite <- pat_nargs_cargs_pat; fold pat.
        replace (x + (pat_nargs pat + ind_nn D)) with (pat_nargs pat + (ind_nn D + x)) by lia.
        rewrite wk_pat_ge; f_equal; lia. }
      rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      rewrite <- params_split.
      exact (wk_preserves_exp _ _ _ _ _ _ _ (HP _ _ _ _ _ _ _ _ Hin Heq HPk HT0) Hφ).
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
      destruct (rec_arg_typed _ _ _ _ _ _ HD Hc Hl Hin _ _ _ Heq HΨ Hφ) as [j Hj].
      split; [ econstructor; exact Hj | split; [ exact HSt |] ].
      cbn [wk_pat]; eapply wf_wk_compose; [ apply wf_wk_shift; econstructor; exact Hj | exact Hφ ].
Qed.


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
  (** [V Θ Ξ E]: the (closed) entry [E] is valid at [Θ ⍮ Ξ]. *)
  Variable V : gdeps -> gstack -> gentry -> Prop.

  Definition GV (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
    forall p E, gc_resolve Θ1 Ξ1 p = Some E -> V Θ2 Ξ2 E.

  (** Everything resolving at [Θ ⍮ Ξ] is valid wherever [Θ ⍮ Ξ] embeds. *)
  Definition Good (Θ : gdeps) (Ξ : gstack) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 -> GV Θ Ξ Θ2 Ξ2.

  (** How a definition and an axiom are made valid: from their derivation at
      the insertion context, given that its globals are valid. *)
  Hypothesis Hdef : forall Θ Ξ A M b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M))).
  Hypothesis Hax : forall Θ Ξ A i b pv Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
  (** And a declaration of an inductive type. *)
  Hypothesis Hind : forall Θ Ξ pv D Θ2 Ξ2,
      decl_typed Θ Ξ D -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> V Θ2 Ξ2 (ge_ind pv D).

  Definition GoodE (Θ : gdeps) (Ξ : gstack) (mp : qname) (E : gentry) : Prop :=
    forall Θ2 Ξ2, Emb Θ Ξ Θ2 Ξ2 ->
      (forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> gc_resolve Θ2 Ξ2 (qname_app mp ip) = Some E0) ->
      (forall x (ip : list String.string) r, ge_submodule (gs_tele Ξ) E x ip = Some r ->
         gc_module Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) ->
      (forall x (ip : list String.string) r, ge_subbody (gs_tele Ξ) E x ip = Some r ->
         gc_body Θ2 Ξ2 (qname_app mp (x :: ip)) = Some r) ->
      forall (ip : list String.string) E0, ge_entries E ip = Some E0 -> V Θ2 Ξ2 E0.

  Definition GoodM (Θ : gdeps) (Ξ : gstack) (mp : qname) (Δ : ctx) (Φ : gmod) : Prop :=
    forall Θ2 Ξ2, Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2 ->
      forall ip E0, gm_resolve Φ ip = Some E0 -> V Θ2 Ξ2 E0.

  Definition GoodU (Θ : gdeps) (Ξ : gstack) (mp : qname) (U : gunit) : Prop :=
    forall Θ2 Ξ2, Emb Θ ((mp, U) :: Ξ) Θ2 Ξ2 ->
      forall ip E0, gm_resolve (gu_mod U) ip = Some E0 -> V Θ2 Ξ2 E0.

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
      intros Θ2 Ξ2 He _ _ _ [| ? ?] E0 HE; cbn in HE; inversion HE; subst; eauto.
    - (* a definition *)
      intros Θ2 Ξ2 He _ _ _ [| ? ?] E0 HE; cbn in HE; inversion HE; subst; eauto.
    - (* a nested module *)
      intros Θ2 Ξ2 He Hin Hmod Hbod ip E0 HE.
      eapply H0; [ eapply Emb_nested; [ exact He | exact Hin | exact Hmod | exact Hbod ] | exact HE ].
    - (* an alias: it contributes no entry *)
      intros ? ? _ _ _ _ ip ? Hx; cbn in Hx; discriminate.
    - (* a declaration *)
      intros Θ2 Ξ2 He _ _ _ [| ? ?] E0 HE; cbn in HE; inversion HE; subst.
      eapply Hind; [| eassumption | exact He ].
      repeat match goal with H : decl_mvc _ |- _ => destruct H as (? & ? & ?) end.
      repeat split; eauto.
    - (* the empty module *)
      intros ? ? ? [| ? ?] ? Hx; discriminate.
    - (* extending a module *)
      rename H0 into IHΦ, H2 into IHE.
      intros Θ2 Ξ2 He ip E0 Hr.
      assert (He' : Emb Θ ((mp, gu_body Δ Φ) :: Ξ) Θ2 Ξ2)
        by (eapply Emb_pre; [ apply gc_sub_grow; eassumption | exact He ]).
      destruct (gm_resolve_ext_inv _ _ _ _ _ Hr) as [(ip' & -> & HE) | HΦ]; [| eauto ].
      eapply IHE; [ exact He' | | | | exact HE ].
      + intros ip0 E1 HE1; rewrite qname_app_in; apply (gc_sub_resolve _ _ _ _ _ _ (em_res _ _ _ _ He)).
        rewrite gc_resolve_frame_here; cbn [gu_mod]; rewrite gm_resolve_ext_here; exact HE1.
      + intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_sub_module _ _ _ _ _ _ (em_res _ _ _ _ He)).
        rewrite gc_module_frame_here; cbn [gu_mod gu_params]; apply gm_submodule_ext_here; exact Hr0.
      + intros z ip0 r Hr0; rewrite qname_app_in; apply (gc_sub_body _ _ _ _ _ _ (em_res _ _ _ _ He)).
        rewrite gc_body_frame_here; cbn [gu_mod gu_params]; apply gm_subbody_ext_here; exact Hr0.
    - (* nothing filed *)
      intros ? ? _ p E Hr; unfold gc_resolve in Hr; cbn in Hr; discriminate.
    - (* a filed unit: it resolves as its closed frame did *)
      rename H into Hg, H0 into IHU.
      intros Θ2 Ξ2 He p E Hr; rewrite gc_resolve_file in Hr.
      destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (_ & _ & [Hn _]).
      eapply IHU; [ eapply Emb_pre; [ apply gc_sub_file; exact Hn | exact He ] | exact Hr ].
    - (* a frame *)
      rename H0 into IHΞ, H2 into IHU.
      intros Θ2 Ξ2 He p E Hr.
      destruct (gc_resolve_frame _ _ _ _ _ _ Hr) as [(ip & -> & Hm) | Hr'].
      + eapply IHU; eassumption.
      + eapply IHΞ; [| exact Hr' ].
        eapply Emb_pre; [ apply gc_sub_push; eassumption | exact He ].
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
  | ge_mod _ _ => True
  | ge_ind _ D => decl_typed Θ Ξ D
  end.

Definition rwf (Θ : gdeps) (Ξ : gstack) : Prop := GV entry_typed Θ Ξ Θ Ξ.

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
        destruct (HR _ _ Hl) as [[i HA] _]; exists i;
        eapply closed_weaken_exp;
        [ assumption | exact HA | eapply wf_gc_resolve_type_closed; eassumption | exact I ]
    end.
  (* inductive types: the declaration's types are types, and the motive at
     the scrutinee *)
  all: try match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, HΓ : ⊢ _ ⍮ _ ⍮ ?Γ |- _ =>
        let Hres := fresh "Hres" in
        destruct (ind_lookup_resolve _ _ _ _ Hl) as [? Hres];
        pose proof (HR _ _ Hres) as HDt; cbn in HDt;
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

Lemma entry_typed_def : forall Θ Ξ A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> Good entry_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    entry_typed Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M))).
Proof.
  intros * HM HG He.
  assert (Hg : ⊢g Θ ⍮ Ξ) by (eapply ctx_wf_gctx, presup_exp_ctx; exact HM).
  destruct (presup_exp_typ_rwf HM (HG _ _ (Emb_refl _ _ Hg))) as [i HA].
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; apply Ht, HT | intros ? [= <-]; apply Ht; eapply ctx_fn_wf0; eassumption ].
Qed.

Lemma entry_typed_ax : forall Θ Ξ A i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> Good entry_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    entry_typed Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; apply Ht, HT | discriminate ].
Qed.

Lemma entry_typed_ind : forall Θ Ξ pv D Θ2 Ξ2,
    decl_typed Θ Ξ D -> Good entry_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> entry_typed Θ2 Ξ2 (ge_ind pv D).
Proof. intros * HD _ He; eapply decl_typed_emb; eassumption. Qed.

(** ** The Mutual Theorem *)

Theorem presup_global :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> GoodE entry_typed Θ Ξ mp E) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> GoodM entry_typed Θ Ξ mp Δ Φ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> Good entry_typed Θ Ξ).
Proof. exact (global_induction_all entry_typed entry_typed_def entry_typed_ax entry_typed_ind). Qed.

Corollary gctx_rwf : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> rwf Θ Ξ.
Proof. exact (global_induction entry_typed entry_typed_def entry_typed_ax entry_typed_ind). Qed.

(** What a use of a global needs: its type and body, in any well-formed
    context. *)
Corollary wf_glob_typ : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ Hl) as [[i HA] _].
  exists i; eapply closed_weaken_exp;
    [ assumption | exact HA | eapply wf_gc_resolve_type_closed; eassumption | exact I ].
Qed.

Corollary wf_glob_body : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A (Some M)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ Hl) as [_ HM].
  eapply closed_weaken_exp;
    [ assumption | apply HM; reflexivity
    | eapply wf_gc_resolve_body_closed; eassumption
    | eapply wf_gc_resolve_type_closed; eassumption ].
Qed.

Theorem presup_exp_typ : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * H; eapply (presup_exp_typ_rwf H), gctx_rwf, ctx_wf_gctx, presup_exp_ctx, H.
Qed.
