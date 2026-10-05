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

Lemma wf_wk_shiftn_app : forall Θ E T,
    ⊢ Θ ⍮ E ++ T ->
    ⊢ Θ ⍮ T ->
    Θ ⍮ E ++ T ⊢w wk_shiftn (length E) : T.
Proof.
  intros; econstructor; [ eassumption | assumption | | |];
    intros; [ apply ctx_lookup_app_r | apply ctx_lookup_def_app_r | apply ctx_lookup_mod_app_r ]; assumption.
Qed.

Lemma ctx_app_wf_right : forall Θ E T, ⊢ Θ ⍮ E ++ T -> ⊢ Θ ⍮ T.
Proof.
  induction E as [| B E IH]; intros * H; cbn in *; [ assumption |].
  apply IH; eapply ctx_decomp_tail; eassumption.
Qed.

(** [wf_let] at a universe, which [Type@j[Id,,M]] is by computation only. *)
Lemma wf_let_typ : forall Θ Γ oA A M B i j,
    Θ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Γ ▸ A ≔ M ⊢ B : Type@j ->
    let_ann oA A ->
    Θ ⍮ Γ ⊢ a_let (b_def oA M) B : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Γ ⊢ a_let (b_def oA M) B : Type@j[Id,,M]) as Hl by (eapply wf_let; cycle 3; [ solve_let_ann | eassumption .. ]).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_zeta_typ : forall Θ Γ oA A M B i j,
    Θ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Γ ▸ A ≔ M ⊢ B : Type@j ->
    let_ann oA A ->
    Θ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ B[Id,,M] : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ B[Id,,M] : Type@j[Id,,M]) as Hl
      by (eapply wf_exp_eq_let_zeta; cycle 3; [ solve_let_ann | eassumption .. ]).
  exact Hl.
Qed.

(** The same for a local module. *)
Lemma wf_let_mod_typ : forall Θ Γ U B j,
    Θ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Γ ▹ₘ U ⊢ B : Type@j ->
    Θ ⍮ Γ ⊢ ℓₘ U in B : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Γ ⊢ ℓₘ U in B : Type@j[Id ,,ₘ me_lit U]) as Hl by (eapply wf_let_mod; [ eassumption | econstructor; eauto using presup_exp_ctx | eassumption ]).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_mod_zeta_typ : forall Θ Γ U B j,
    Θ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Γ ▹ₘ U ⊢ B : Type@j ->
    Θ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Type@j.
Proof.
  intros.
  assert (Θ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Type@j[Id ,,ₘ me_lit U]) as Hl
      by (eapply wf_exp_eq_let_mod_zeta; [ eassumption | econstructor; eauto using presup_exp_ctx | eassumption ]).
  exact Hl.
Qed.

#[export]
Hint Resolve wf_let_typ wf_exp_eq_let_zeta_typ wf_let_mod_typ wf_exp_eq_let_mod_zeta_typ : mctt.

Lemma ctx_pi_wf : forall Θ Δ Γ A i,
    ⊢ Θ ⍮ Δ ++ Γ ->
    Θ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    exists j, Θ ⍮ Γ ⊢ ctx_pi Δ A : Type@j.
Proof.
  induction Δ as [| [B | B N | U] Δ IH]; intros * HΔ HA; cbn in *; [ eauto | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⊢ B : Type@?k |- _ =>
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

Lemma ctx_fn_wf : forall Θ Δ Γ A M i,
    ⊢ Θ ⍮ Δ ++ Γ ->
    Θ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    Θ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  induction Δ as [| [B | B N | U] Δ IH]; intros * HΔ HA HM; cbn in *; [ assumption | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⊢ B : Type@?k |- _ =>
      eapply IH with (i := max k i); [ eauto using presup_exp_ctx | |];
      [ econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
      | econstructor; eassumption ]
    end.
  - (** The body's [let] has the type [A[Id,,N]], which is the type's [let] by
        ζ. *)
    assert (Θ ⍮ Δ ++ Γ ⊢ ℓ B ≔ N in A : Type@i) by (eapply wf_let_typ; cycle 3; [ solve_let_ann | eassumption .. ]).
    eapply IH with (i := i); [ eauto using presup_exp_ctx | eassumption |].
    eapply wf_exp_subtyp'; [ eapply wf_let; cycle 3; [ solve_let_ann | eassumption .. ] |].
    eapply wf_subtyp_refl; [ eassumption |].
    eapply wf_exp_eq_sym, wf_exp_eq_let_zeta_typ; cycle 3; [ solve_let_ann | eassumption .. ].
  - assert (Θ ⍮ Δ ++ Γ ⊢ ℓₘ U in A : Type@i) by (eapply wf_let_mod_typ; eassumption).
    eapply IH with (i := i); [ eauto using presup_unit_eq_ctx | eassumption |].
    eapply wf_exp_subtyp'; [ eapply wf_let_mod; eassumption |].
    eapply wf_subtyp_refl; [ eassumption |].
    eapply wf_exp_eq_sym, wf_exp_eq_let_mod_zeta_typ; eassumption.
Qed.

Corollary ctx_pi_wf0 : forall Θ Δ A i,
    Θ ⍮ Δ ⊢ A : Type@i ->
    exists j, Θ ⍮ ⋅ ⊢ ctx_pi Δ A : Type@j.
Proof.
  intros; eapply ctx_pi_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption ].
Qed.

Corollary ctx_fn_wf0 : forall Θ Δ A M i,
    Θ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Δ ⊢ M : A ->
    Θ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  intros; eapply ctx_fn_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption.. ].
Qed.

(** A closed judgment holds in any context. *)
Lemma closed_weaken_exp : forall Θ Γ M A,
    ⊢ Θ ⍮ Γ ->
    Θ ⍮ ⋅ ⊢ M : A ->
    exp_scoped 0 M -> exp_scoped 0 A ->
    Θ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ HM HsM HsA.
  rewrite <- (exp_closed_wk M (wk_shiftn (length Γ)) HsM),
    <- (exp_closed_wk A (wk_shiftn (length Γ)) HsA).
  eapply wk_preserves_exp; [ exact HM |].
  pose proof (wf_wk_shiftn_app Θ Γ nil) as Hw; rewrite List.app_nil_r in Hw.
  apply Hw; [ assumption | constructor; eapply ctx_wf_gctx; eassumption ].
Qed.

(** ** Embeddings

    [Emb Θ1 Θ2]: the target is well formed and everything filed at the source
    is filed, the same, at the target. *)

Record Emb (Θ1 Θ2 : gctx) : Prop :=
  { em_wf : ⊢g Θ2
  ; em_res : Θ1 ⊑ Θ2 }.

Lemma Emb_refl : forall Θ, ⊢g Θ -> Emb Θ Θ.
Proof. intros; constructor; [ assumption | apply gc_sub_refl ]. Qed.

(** An embedding preceded by a growth of the global context. *)
Lemma Emb_pre : forall Θ1 Θ Θ2, Θ1 ⊑ Θ -> Emb Θ Θ2 -> Emb Θ1 Θ2.
Proof. intros * H [Hg He]; constructor; [ assumption | eapply gc_sub_trans; eassumption ]. Qed.

(** Member types and δ-reducts grow with the global context. *)
Lemma member_type_emb : forall Θ1 Θ2 Γ H ch R,
    Θ1 ⊑ Θ2 -> member_type Θ1 Γ H ch R -> member_type Θ2 Γ H ch R.
Proof. intros * Hs; exact (proj1 (member_type_gc_sub _ _ Hs) _ _ _ _). Qed.

Lemma member_unfold_emb : forall Θ1 Θ2 Γ H x M,
    Θ1 ⊑ Θ2 -> member_unfold Θ1 Γ H x = Some M -> member_unfold Θ2 Γ H x = Some M.
Proof. intros * Hs; exact (member_unfold_gc_sub _ _ Hs _ _ _ _). Qed.

(** A judgment moves along an embedding unchanged. *)
Theorem emb_preserves_wf : forall Θ1 Θ2,
    Emb Θ1 Θ2 ->
    (forall Γ, ⊢ Θ1 ⍮ Γ -> ⊢ Θ2 ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ1 ⍮ Γ ⊢ M ≈ M' : A -> Θ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ1 ⍮ Γ ⊢ A ⊆ A' -> Θ2 ⍮ Γ ⊢ A ⊆ A') /\
    (forall Γ Ψ Ψ', Θ1 ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ2 ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Γ U U', Θ1 ⍮ Γ ⊢ᵘ U ≈ U' -> Θ2 ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Γ H H', Θ1 ⍮ Γ ⊢ᵐ H ≈ H' -> Θ2 ⍮ Γ ⊢ᵐ H ≈ H').
Proof.
  intros * [Hg Hs].
  assert (H :
    (forall Θ Γ, ⊢ Θ ⍮ Γ -> Θ = Θ1 -> ⊢ Θ2 ⍮ Γ) /\
    (forall Θ Γ A M, Θ ⍮ Γ ⊢ M : A -> Θ = Θ1 -> Θ2 ⍮ Γ ⊢ M : A) /\
    (forall Θ Γ A M M', Θ ⍮ Γ ⊢ M ≈ M' : A -> Θ = Θ1 -> Θ2 ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Θ Γ A A', Θ ⍮ Γ ⊢ A ⊆ A' -> Θ = Θ1 -> Θ2 ⍮ Γ ⊢ A ⊆ A') /\
    (forall Θ Γ Ψ Ψ', Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = Θ1 -> Θ2 ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Θ Γ U U', Θ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = Θ1 -> Θ2 ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Θ Γ H H', Θ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = Θ1 -> Θ2 ⍮ Γ ⊢ᵐ H ≈ H')).
  { apply syntactic_wf_mut_ind; intros; subst;
      repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
      try solve [ econstructor; eauto using gc_sub_unit, gc_sub_const, member_type_emb, member_unfold_emb ].
    all: econstructor; eauto. }
  destruct H as (Hc & He & Hq & Hst & Hx & Hu & Hm).
  repeat split; intros; eauto.
Qed.

(** ** The Induction over the Global Context, for an Abstract Notion of
       Validity

    [VC Θ A oM]: the constant of type [A] and body [oM], if any, is valid at
    [Θ];
    [VU Θ U]: the unit [U] is.  Everything filed at [Θ] is valid wherever
    [Θ] embeds, provided a constant and a unit are made valid from their
    derivations at the global context below them, given that it is. *)

(** What the rule filing a constant checks: its body, or for an axiom its
    type. *)
Definition const_wf (Θ : gctx) (A : typ) (oM : option exp) : Prop :=
  match oM with
  | Some M => Θ ⍮ ⋅ ⊢ M : A
  | None => exists i, Θ ⍮ ⋅ ⊢ A : Type@i
  end.

Lemma wf_gctx_cons_inv : forall d Θ, ⊢g d :: Θ ->
    ⊢g Θ /\
    match d with
    | gd_unit fp U => Θ ⍮ ⋅ ⊢ᵘ U ≈ U /\ gc_unit Θ fp = None
    | gd_const c A oM b => const_wf Θ A oM /\ gc_const Θ c = None
    end.
Proof.
  intros * H; inversion H; subst; split; cbn; eauto;
    eapply ctx_wf_gctx; eauto using presup_unit_eq_ctx, presup_exp_ctx.
Qed.

Lemma wf_gctx_cons_sub : forall d Θ, ⊢g d :: Θ -> Θ ⊑ d :: Θ.
Proof.
  intros [fp U | c A M b] Θ H; apply wf_gctx_cons_inv in H as (_ & _ & Hn);
    [ apply gc_sub_cons_unit | apply gc_sub_cons_const ]; exact Hn.
Qed.

Section Induction.
  Variable VC : gctx -> typ -> option exp -> Prop.
  Variable VU : gctx -> gunit -> Prop.

  Definition GV (Θ1 Θ2 : gctx) : Prop :=
    (forall c A oM b, gc_const Θ1 c = Some (A, oM, b) -> VC Θ2 A oM) /\
    (forall fp U, gc_unit Θ1 fp = Some U -> VU Θ2 U).

  Definition Good (Θ : gctx) : Prop := forall Θ2, Emb Θ Θ2 -> GV Θ Θ2.

  Hypothesis Hconst : forall Θ A oM Θ2, const_wf Θ A oM -> Good Θ -> Emb Θ Θ2 -> VC Θ2 A oM.
  Hypothesis Hunit : forall Θ U Θ2, Θ ⍮ ⋅ ⊢ᵘ U ≈ U -> Good Θ -> Emb Θ Θ2 -> VU Θ2 U.

  Theorem global_induction_good : forall Θ, ⊢g Θ -> Good Θ.
  Proof.
    induction Θ as [| d Θ IH]; intros Hg Θ2 He.
    - split; intros; discriminate.
    - pose proof (wf_gctx_cons_sub _ _ Hg) as Hs.
      destruct (wf_gctx_cons_inv _ _ Hg) as [HΘ Hd].
      assert (He' : Emb Θ Θ2) by (eapply Emb_pre; eassumption).
      destruct (IH HΘ _ He') as [IHc IHu].
      destruct d as [fq V | c' A' M' b']; destruct Hd as [Hd Hn]; split; intros * Hl; cbn in Hl.
      + eauto.
      + destruct (path_beq fp fq); [ injection Hl as <-; eauto | eauto ].
      + destruct (qname_beq c c'); [ injection Hl as <- <- <-; eauto | eauto ].
      + eauto.
  Qed.

  Corollary global_induction : forall Θ, ⊢g Θ -> GV Θ Θ.
  Proof. intros * Hg; exact (global_induction_good _ Hg _ (Emb_refl _ Hg)). Qed.
End Induction.

(** ** What the Global Context Files is Well Typed *)

Definition const_typed (Θ : gctx) (A : exp) (oM : option exp) : Prop :=
  (exists i, Θ ⍮ ⋅ ⊢ A : Type@i) /\ (forall M, oM = Some M -> Θ ⍮ ⋅ ⊢ M : A).

Definition unit_typed (Θ : gctx) (U : gunit) : Prop := Θ ⍮ ⋅ ⊢ᵘ U ≈ U.

Definition rwf (Θ : gctx) : Prop := GV const_typed unit_typed Θ Θ.

Lemma presup_exp_typ_rwf : forall {Θ Γ M A},
    Θ ⍮ Γ ⊢ M : A ->
    rwf Θ ->
    exists i, Θ ⍮ Γ ⊢ A : Type@i.
Proof.
  induction 1; intros HR;
    repeat match goal with IH : rwf _ -> _ |- _ => specialize (IH HR) end;
    assert (⊢ Θ ⍮ Γ) by mauto 2; destruct_conjs.
  (* a constant: its type is a type at [⋅], and closed *)
  all: try match goal with
    | Hl : gc_const _ _ = Some (?A, _, _), HΓ : ⊢ _ ⍮ _ |- _ =>
        destruct (proj1 (HR : GV const_typed unit_typed _ _) _ _ _ _ Hl) as [[i HA] _]; exists i;
        eapply closed_weaken_exp;
        [ assumption | exact HA | exact (proj1 (wf_gc_const_closed _ _ _ _ _ _ HΓ Hl)) | exact I ]
    end.
  all: mauto 3.
  all: eexists; mauto 3.
Qed.

Lemma const_typed_intro : forall Θ A oM Θ2,
    const_wf Θ A oM -> Good const_typed unit_typed Θ -> Emb Θ Θ2 -> const_typed Θ2 A oM.
Proof.
  intros * HM HG He.
  destruct (emb_preserves_wf _ _ He) as (_ & Ht & _).
  destruct oM as [M |]; cbn in HM.
  - assert (Hg : ⊢g Θ) by (eapply ctx_wf_gctx, presup_exp_ctx; exact HM).
    destruct (presup_exp_typ_rwf HM (HG _ (Emb_refl _ Hg))) as [i HA].
    split; [ exists i; apply Ht, HA | intros ? [= <-]; apply Ht, HM ].
  - destruct HM as [i HA]; split; [ exists i; apply Ht, HA | discriminate ].
Qed.

Lemma unit_typed_intro : forall Θ U Θ2,
    Θ ⍮ ⋅ ⊢ᵘ U ≈ U -> Good const_typed unit_typed Θ -> Emb Θ Θ2 -> unit_typed Θ2 U.
Proof.
  intros * HU HG He.
  destruct (emb_preserves_wf _ _ He) as (_ & _ & _ & _ & _ & Hu & _).
  apply Hu, HU.
Qed.

Corollary gctx_rwf : forall Θ, ⊢g Θ -> rwf Θ.
Proof. exact (global_induction const_typed unit_typed const_typed_intro unit_typed_intro). Qed.

(** What a use of a constant needs: its type and body, in any well-formed
    context; and what a use of a unit needs: that it is well formed. *)
Corollary wf_const_typ : forall Θ Γ c A oM b,
    ⊢ Θ ⍮ Γ ->
    gc_const Θ c = Some (A, oM, b) ->
    exists i, Θ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * HΓ Hl; destruct (proj1 (gctx_rwf _ (ctx_wf_gctx _ _ HΓ) : GV const_typed unit_typed _ _) _ _ _ _ Hl) as [[i HA] _].
  exists i; eapply closed_weaken_exp;
    [ assumption | exact HA | exact (proj1 (wf_gc_const_closed _ _ _ _ _ _ HΓ Hl)) | exact I ].
Qed.

Corollary wf_const_body : forall Θ Γ c A M b,
    ⊢ Θ ⍮ Γ ->
    gc_const Θ c = Some (A, Some M, b) ->
    Θ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hl; destruct (proj1 (gctx_rwf _ (ctx_wf_gctx _ _ HΓ) : GV const_typed unit_typed _ _) _ _ _ _ Hl) as [_ HM].
  pose proof (wf_gc_const_closed _ _ _ _ _ _ HΓ Hl) as [HA HMs].
  eapply closed_weaken_exp; [ eassumption | exact (HM _ eq_refl) | exact HMs | exact HA ].
Qed.

Corollary wf_unit_lookup : forall Θ Γ fp U,
    ⊢ Θ ⍮ Γ ->
    gc_unit Θ fp = Some U ->
    Θ ⍮ ⋅ ⊢ᵘ U ≈ U.
Proof. intros * HΓ Hl; exact (proj2 (gctx_rwf _ (ctx_wf_gctx _ _ HΓ) : GV const_typed unit_typed _ _) _ _ Hl). Qed.

Theorem presup_exp_typ : forall {Θ Γ M A},
    Θ ⍮ Γ ⊢ M : A ->
    exists i, Θ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * H; eapply (presup_exp_typ_rwf H), gctx_rwf, ctx_wf_gctx, presup_exp_ctx, H.
Qed.
