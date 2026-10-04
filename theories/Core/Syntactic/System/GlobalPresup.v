(** * Presupposition

    Presupposition is proved for all fourteen judgments at once.  A global is used
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

(** [wf_let] at a universe, which [Type@j[Id,,M]] is by computation only. *)
Lemma wf_let_typ : forall Θ Ξ Γ A M B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : Type@j[Id,,M]) as Hl by (eapply wf_let; eassumption).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_zeta_typ : forall Θ Ξ Γ A M B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : Type@j[Id,,M]) as Hl
      by (eapply wf_exp_eq_let_zeta; eassumption).
  exact Hl.
Qed.

(** The same for a local module. *)
Lemma wf_let_mod_typ : forall Θ Ξ Γ U B j,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : Type@j[Id ,,ₘ me_lit U]) as Hl by (eapply wf_let_mod; [ eassumption | econstructor; eauto using presup_exp_ctx | eassumption ]).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_mod_zeta_typ : forall Θ Ξ Γ U B j,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Type@j[Id ,,ₘ me_lit U]) as Hl
      by (eapply wf_exp_eq_let_mod_zeta; [ eassumption | econstructor; eauto using presup_exp_ctx | eassumption ]).
  exact Hl.
Qed.

#[export]
Hint Resolve wf_let_typ wf_exp_eq_let_zeta_typ wf_let_mod_typ wf_exp_eq_let_mod_zeta_typ : mctt.

Lemma ctx_pi_wf : forall Θ Ξ Δ Γ A i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Type@j.
Proof.
  induction Δ as [| [B | B N | U] Δ IH]; intros * HΔ HA; cbn in *; [ eauto | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Type@?k |- _ =>
      eapply IH; [ eauto using presup_exp_ctx |];
      econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
    end.
  - (** A definition is generalized as a [let], which is a type at the type's
        own level. *)
    eapply IH; [ eauto using presup_exp_ctx |].
    eapply wf_let_typ; eassumption.
  - (** So is a module slot, as a [let module]. *)
    eapply IH; [ eauto using presup_unit_eq_ctx |].
    eapply wf_let_mod_typ; eassumption.
Qed.

Lemma ctx_fn_wf : forall Θ Ξ Δ Γ A M i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  induction Δ as [| [B | B N | U] Δ IH]; intros * HΔ HA HM; cbn in *; [ assumption | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Type@?k |- _ =>
      eapply IH with (i := max k i); [ eauto using presup_exp_ctx | |];
      [ econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
      | econstructor; eassumption ]
    end.
  - (** The body's [let] has the type [A[Id,,N]], which is the type's [let] by
        ζ. *)
    assert (Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ ℓ B ≔ N in A : Type@i) by (eapply wf_let_typ; eassumption).
    eapply IH with (i := i); [ eauto using presup_exp_ctx | eassumption |].
    eapply wf_exp_subtyp'; [ eapply wf_let; eassumption |].
    eapply wf_subtyp_refl; [ eassumption |].
    eapply wf_exp_eq_sym, wf_exp_eq_let_zeta_typ; eassumption.
  - assert (Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ ℓₘ U in A : Type@i) by (eapply wf_let_mod_typ; eassumption).
    eapply IH with (i := i); [ eauto using presup_unit_eq_ctx | eassumption |].
    eapply wf_exp_subtyp'; [ eapply wf_let_mod; eassumption |].
    eapply wf_subtyp_refl; [ eassumption |].
    eapply wf_exp_eq_sym, wf_exp_eq_let_mod_zeta_typ; eassumption.
Qed.

Corollary ctx_pi_wf0 : forall Θ Ξ Δ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Type@j.
Proof.
  intros; eapply ctx_pi_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption ].
Qed.

Corollary ctx_fn_wf0 : forall Θ Ξ Δ A M i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
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

(** Member types, δ-reducts and member checks grow with resolution. *)
Lemma member_type_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ H ch R,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> member_type Θ1 Ξ1 Γ H ch R -> member_type Θ2 Ξ2 Γ H ch R.
Proof. intros * Hs; exact (proj1 (member_type_gc_sub _ _ _ _ Hs) _ _ _ _). Qed.

Lemma member_unfold_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ H x M,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> member_unfold Θ1 Ξ1 Γ H x = Some M -> member_unfold Θ2 Ξ2 Γ H x = Some M.
Proof. intros * Hs; exact (member_unfold_gc_sub _ _ _ _ Hs _ _ _ _). Qed.

Lemma member_ok_emb : forall Θ1 Ξ1 Θ2 Ξ2 Γ H n,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> member_ok Θ1 Ξ1 Γ H n -> member_ok Θ2 Ξ2 Γ H n.
Proof.
  intros * Hs [(A & HA) | (A & HA)]; [ left | right ]; exists A; eapply member_type_emb; eassumption.
Qed.

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
      try solve [ econstructor; eauto using gc_sub_resolve, member_type_emb, member_unfold_emb ].
    (** The body unit's member checks are under binders. *)
    all: econstructor; eauto; intros; eauto using member_ok_emb;
      match goal with IH : forall _ _ _, _ -> forall _ _, _ |- _ => eapply IH; eauto end. }
  destruct H as (Hc & He & Hq & Hst & Hx & Hu & Hm).
  repeat split; intros; eauto.
Qed.

(** ** The Induction over Insertion, for an Abstract Notion of Validity *)

(** The entries an entry contributes, read below its own path. *)
Definition ge_entries (E : gentry) (ip : list String.string) : option gentry :=
  match E with
  | ge_def _ _ _ _ => match ip with nil => Some E | _ => None end
  | ge_mod U => gm_resolve (gu_mod U) ip
  end.

Lemma gm_resolve_ext_here : forall Φ x E ip,
    gm_resolve (Φ ⊳ x ↦ E) (x :: ip) = ge_entries E ip.
Proof.
  intros; cbn; rewrite String.eqb_refl.
  destruct ip, E as [| [Δ' [Φ' | E']]]; cbn; rewrite ?gm_resolve_nil; reflexivity.
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
  | ge_def _ _ _ _ => None
  | ge_mod U => gm_submodule (gu_params U ++ T) (gu_mod U) x ip
  end.

Lemma gm_submodule_ext_here : forall T Φ x E z ip r,
    ge_submodule T E z ip = Some r -> gm_submodule T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| [Δ' [Φ' | E']]]; cbn in H; [ discriminate | exact H |].
  destruct z; discriminate.
Qed.

(** The body modules an entry contributes, read below its own path. *)
Definition ge_subbody (T : ctx) (E : gentry) (x : String.string) (ip : list String.string) : option (ctx * gmod) :=
  match E with
  | ge_def _ _ _ _ => None
  | ge_mod U => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  end.

Lemma gm_subbody_ext_here : forall T Φ x E z ip r,
    ge_subbody T E z ip = Some r -> gm_subbody T (Φ ⊳ x ↦ E) x (z :: ip) = Some r.
Proof.
  intros * H; cbn; rewrite String.eqb_refl.
  destruct E as [| [Δ' [Φ' | E']]]; cbn in H; [ discriminate | exact H |].
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

Lemma wf_gdep_fresh : forall Θ d,
    wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> gds_fresh fp Θ.
Proof.
  induction 1; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] |]; eauto.
Qed.

(** The telescope of the frames' parameters is a well-formed context: the
    innermost frame's module was checked over it, one frame out, and pushing
    the frame is an embedding. *)
Lemma wf_gs_tele : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ.
Proof.
  intros Θ [| [mp U] Ξ] Hg; [ constructor; exact Hg |].
  pose proof (wf_gctx_stack _ _ Hg) as Hs; inversion Hs as [| ? ? ? ? Hs0 HU Hff]; subst.
  assert (HP : ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ)
    by (inversion HU as [? ? ? ? ? HΦ]; subst; exact (wf_gmod_ctx _ _ _ _ _ HΦ)).
  destruct (emb_preserves_wf Θ Ξ Θ ((mp, U) :: Ξ)) as (Hc & _).
  - constructor; [ exact Hg | apply gc_sub_push; exact Hff ].
  - exact (Hc _ HP).
Qed.

Lemma wf_gdep_lookup : forall Θ d,
    wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> gd_lookup d fp = Some U.
Proof.
  induction 1 as [| Θ d fp U Hd IH HU Hfr Hfr']; intros fq V Hin; cbn in Hin; [ contradiction |].
  unfold gd_lookup, path_beq in *; cbn.
  destruct Hin as [[= <- <-] | Hin].
  - destruct (path_eq_dec fp fp); [ reflexivity | contradiction ].
  - destruct (path_eq_dec fq fp) as [-> |]; [| eauto ].
    exfalso; apply (Hfr' (List.in_map fst _ _ Hin)).
Qed.

(** Every frame of a well-formed stack belongs to a unit not filed. *)
Lemma wf_gstack_frames : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall mp U, List.In (mp, U) Ξ -> gds_lookup Θ (q_unit mp) = None.
Proof.
  induction 1 as [| Θ Ξ mq V HΞ IH HV Hff]; intros mp U Hin; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [| eauto ].
  destruct Ξ as [| [mr W] Ξ']; cbn in Hff.
  - apply gds_fresh_no_lookup; exact (proj1 Hff).
  - destruct Hff as (x & -> & _); cbn; apply (IH mr W); left; reflexivity.
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
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Type@i -> Good Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
      V Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).

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

  Definition GoodD (Θ : gdeps) (d : gdep) : Prop :=
    forall fp U, List.In (fp, U) d -> GoodU Θ nil (q_abs fp nil) U.

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
    (forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> GoodU Θ Ξ mp U) /\
    (forall Θ d, wf_gdep Θ d -> GoodD Θ d) /\
    (forall Θ, wf_gdeps Θ -> Good Θ nil) /\
    (forall Θ Ξ, wf_gstack Θ Ξ -> Good Θ Ξ) /\
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
    - (* the empty level *)
      intros ? ? [].
    - (* filing a unit at a level *)
      intros fq V' [[= <- <-] | Hin]; eauto.
    - (* no levels *)
      intros ? ? _ p E Hr; unfold gc_resolve in Hr; cbn in Hr.
      unfold gds_lookup, gd_lookup in Hr; cbn in Hr; discriminate.
    - (* a level on top *)
      rename H0 into IHΘ, H2 into IHd.
      pose proof (wf_gdep_fresh _ _ H1) as Hfr.
      intros Θ2 Ξ2 He p E Hr; unfold gc_resolve in Hr; cbn [gs_find] in Hr.
      destruct (gds_lookup (d :: Θ) (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
      unfold gds_lookup in Hl; cbn [List.concat] in Hl.
      apply gd_lookup_app_inv in Hl as [Hl | Hl].
      + apply (IHd _ _ (gd_lookup_in _ _ _ Hl) Θ2 Ξ2) with (ip := q_chain p); [| exact Hr ].
        eapply Emb_pre; [ apply gc_sub_file; eassumption | exact He ].
      + apply (IHΘ Θ2 Ξ2) with (p := p).
        * eapply Emb_pre; [ apply gc_sub_level; eassumption | exact He ].
        * unfold gc_resolve; cbn [gs_find]; unfold gds_lookup; rewrite Hl; exact Hr.
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
    intros * Hg; destruct global_induction_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
    exact (H _ _ Hg _ _ (Emb_refl _ _ Hg)).
  Qed.
End Induction.

(** ** What Resolution Hands Back is Well Typed *)

Definition entry_typed (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Type@i) /\ (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A)
  | ge_mod _ => True
  end.

Definition rwf (Θ : gdeps) (Ξ : gstack) : Prop := GV entry_typed Θ Ξ Θ Ξ.

Lemma presup_exp_typ_rwf : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    rwf Θ Ξ ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
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
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Type@i -> Good entry_typed Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    entry_typed Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  destruct (emb_preserves_wf _ _ _ _ He) as (_ & Ht & _).
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; apply Ht, HT | discriminate ].
Qed.

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
  (forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> GoodU entry_typed Θ Ξ mp U) /\
  (forall Θ d, wf_gdep Θ d -> GoodD entry_typed Θ d) /\
  (forall Θ, wf_gdeps Θ -> Good entry_typed Θ nil) /\
  (forall Θ Ξ, wf_gstack Θ Ξ -> Good entry_typed Θ Ξ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> Good entry_typed Θ Ξ).
Proof. exact (global_induction_all entry_typed entry_typed_def entry_typed_ax). Qed.

Corollary gctx_rwf : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> rwf Θ Ξ.
Proof. exact (global_induction entry_typed entry_typed_def entry_typed_ax). Qed.

(** What a use of a global needs: its type and body, in any well-formed
    context. *)
Corollary wf_glob_typ : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
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
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * H; eapply (presup_exp_typ_rwf H), gctx_rwf, ctx_wf_gctx, presup_exp_ctx, H.
Qed.
