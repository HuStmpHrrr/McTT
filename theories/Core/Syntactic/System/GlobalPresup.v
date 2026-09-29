(** * Presupposition

    Presupposition is proved for all eleven judgments at once.  A global is used
    at its resolved type without premising that it is a type, and a definition's
    type is not checked separately from its body; that each is a type is what
    presupposition of the *entry's* own derivation gives, and that derivation is
    part of [⊢g], so the induction has to range over the global judgments too. *)

From Stdlib Require Import Lia List PeanoNat Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Structural.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Inserting Bindings below the Local Context *)

Lemma ctx_lookup_app_r : forall E T x A,
    T ∋ #x : A ->
    E ++ T ∋ #(x + length E) : A[wk_shiftn (length E)]w.
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, (exp_wk_wk_eq _ _ _ wk_shiftn_zero), exp_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- (exp_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- exp_wk_wk.
    constructor; auto.
Qed.

(** A lookup in [L ++ T] is in [L], or in [T] past it. *)
Lemma ctx_lookup_app_inv : forall L T x A,
    L ++ T ∋ #x : A ->
    L ∋ #x : A \/ exists y A0, x = y + length L /\ T ∋ #y : A0 /\ A = A0[wk_shiftn (length L)]w.
Proof.
  induction L as [| B L IH]; intros * H; cbn in *.
  - right; exists x, A; rewrite Nat.add_0_r, (exp_wk_wk_eq _ _ _ wk_shiftn_zero), exp_wk_id; auto.
  - inversion H; subst; [ left; constructor |].
    destruct (IH _ _ _ ltac:(eassumption)) as [| (y & A1 & -> & HT & ->)];
      [ left; constructor; assumption |].
    right; exists y, A1; split; [ lia |]; split; [ assumption |].
    rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia.
Qed.

(** From [⋅]: everything in scope is past the new bindings. *)
Lemma wf_wk_shiftn : forall Θ Ξ E,
    ⊢ Θ ⍮ Ξ ⍮ E ->
    Θ ⍮ Ξ ⍮ E ⊢w wk_shiftn (length E) : ⋅.
Proof.
  intros; econstructor; [ eassumption | constructor; eauto using ctx_wf_gctx |].
  intros; apply ctx_lookup_app_r; assumption.
Qed.

(** Below a closed context: its own bindings do not move. *)
Lemma wf_wk_closed_insert : forall Θ Ξ L E,
    ⊢ Θ ⍮ Ξ ⍮ L ->
    ctx_scoped 0 L ->
    ⊢ Θ ⍮ Ξ ⍮ L ++ E ->
    Θ ⍮ Ξ ⍮ L ++ E ⊢w wk_qn (length L) (wk_shiftn (length E)) : L.
Proof.
  intros * HL Hsc HLE; econstructor; try eassumption.
  intros x A Hlk; apply ctx_lookup_app_inv in Hlk as [Hlk | (y & A0 & -> & HT & ->)].
  - pose proof (ctx_lookup_lt Hlk).
    pose proof (ctx_scoped_lookup _ _ _ _ Hsc Hlk) as HA; rewrite Nat.add_0_r in HA.
    rewrite wk_qn_lt by assumption.
    rewrite (exp_scoped_wk_id _ _ _ HA) by (intros; apply wk_qn_lt; assumption).
    rewrite <- List.app_assoc; apply ctx_lookup_app_l; assumption.
  - rewrite wk_qn_ge by lia; rewrite Nat.add_sub.
    replace (wk_shiftn (length E) y + length L) with (y + length (L ++ E))
      by (rewrite List.length_app; cbn; lia).
    rewrite exp_wk_wk.
    rewrite (exp_wk_wk_eq _ _ (wk_shiftn (length (L ++ E))))
      by (intros z; cbn; rewrite wk_qn_ge, Nat.add_sub, List.length_app by lia; cbn; lia).
    apply ctx_lookup_app_r; assumption.
Qed.

(** A closed context extends any well-formed one below it. *)
Lemma ctx_closed_extend : forall Θ Ξ L E,
    ⊢ Θ ⍮ Ξ ⍮ L ->
    ctx_scoped 0 L ->
    ⊢ Θ ⍮ Ξ ⍮ E ->
    ⊢ Θ ⍮ Ξ ⍮ L ++ E.
Proof.
  induction L as [| B L IH]; intros E HL Hsc HE; cbn in *; [ assumption |].
  destruct Hsc as [HB HLs]; rewrite Nat.add_0_r in HB.
  inversion HL as [| ? ? ? ? ? HBt]; subst.
  assert (⊢ Θ ⍮ Ξ ⍮ L) by eauto using presup_exp_ctx.
  assert (⊢ Θ ⍮ Ξ ⍮ L ++ E) by eauto.
  apply wf_ctx_extend with (i := i).
  change (Type@i) with (Type@i[wk_qn (length L) (wk_shiftn (length E))]w).
  rewrite <- (exp_scoped_wk_id B (length L) (wk_qn (length L) (wk_shiftn (length E))))
    by (assumption || (intros; apply wk_qn_lt; assumption)).
  eapply wk_preserves_exp; [ eassumption |].
  apply wf_wk_closed_insert; assumption.
Qed.

(** ** Localizing the Parameters in Scope

    The parameters of the frames are in scope but not local, so nothing can be
    generalized over them.  A judgment still holds with a copy of them made
    local: its terms keep their meaning, since the copy sits exactly where the
    variables they name were, and a global's type is closed. *)

Section Localize.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Htele : ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ.

  Lemma localize_wf :
    (forall Θ' Ξ' Γ, ⊢ Θ' ⍮ Ξ' ⍮ Γ -> Θ' = Θ -> Ξ' = Ξ -> ⊢ Θ ⍮ Ξ ⍮ Γ ++ gs_tele Ξ) /\
    (forall Θ' Ξ' Γ A M, Θ' ⍮ Ξ' ⍮ Γ ⊢ M : A -> Θ' = Θ -> Ξ' = Ξ ->
        Θ ⍮ Ξ ⍮ Γ ++ gs_tele Ξ ⊢ M : A) /\
    (forall Θ' Ξ' Γ A M M', Θ' ⍮ Ξ' ⍮ Γ ⊢ M ≈ M' : A -> Θ' = Θ -> Ξ' = Ξ ->
        Θ ⍮ Ξ ⍮ Γ ++ gs_tele Ξ ⊢ M ≈ M' : A) /\
    (forall Θ' Ξ' Γ A A', Θ' ⍮ Ξ' ⍮ Γ ⊢ A ⊆ A' -> Θ' = Θ -> Ξ' = Ξ ->
        Θ ⍮ Ξ ⍮ Γ ++ gs_tele Ξ ⊢ A ⊆ A').
  Proof.
    apply syntactic_wf_mut_ind; intros; subst;
      repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
      cbn in *; try assumption; try solve [ econstructor; eauto ].
    all: econstructor; [ eassumption | apply ctx_lookup_app_l; assumption ].
  Qed.
End Localize.

(** The parameters in scope form a well-formed context of their own.  For
    [U :: Ξ]: [U]'s parameters over a local copy of [Ξ]'s is well formed by
    localization, and closed; putting [U]'s parameters below it and pushing the
    frame is exactly [gs_tele (U :: Ξ)]. *)
Lemma tele_wf : forall Ξ Θ, ⊢g Θ ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ.
Proof.
  induction Ξ as [| U Ξ IH]; intros Θ Hg0; [ constructor; assumption |].
  destruct (wf_gctx_pop _ _ _ Hg0) as [Hg HU].
  pose proof (IH _ Hg) as HT.
  destruct (localize_wf _ _ HT) as (Hloc & _).
  pose proof (Hloc _ _ _ HU eq_refl eq_refl) as HUT.
  assert (ctx_scoped 0 (gu_params U ++ gs_tele Ξ)) as Hsc.
  { destruct wf_scoped as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgs).
    destruct (Hgs _ _ Hg0) as [Hs _]; cbn [gs_scoped] in Hs; destruct Hs as (Hp & _ & Hs).
    apply ctx_scoped_app; split; [ rewrite Nat.add_0_r; exact Hp | apply gs_scoped_tele, Hs ]. }
  pose proof (ctx_closed_extend _ _ _ _ HUT Hsc HU) as Hext.
  destruct (push_preserves_wf _ _ _ Hg0) as (Hpc & _).
  rewrite gs_tele_cons; apply Hpc; assumption.
Qed.

(** ** Generalizing *)

Lemma ctx_pi_wf : forall Θ Ξ Δ Γ A i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Type@j.
Proof.
  induction Δ as [| B Δ IH]; intros * HΔ HA; cbn in *; [ eauto |].
  inversion HΔ; subst.
  match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Type@?k |- _ =>
    eapply IH; [ eauto using presup_exp_ctx |];
    econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
  end.
Qed.

Lemma ctx_fn_wf : forall Θ Ξ Δ Γ A M i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  induction Δ as [| B Δ IH]; intros * HΔ HA HM; cbn in *; [ assumption |].
  inversion HΔ; subst.
  match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : Type@?k |- _ =>
    eapply IH with (i := max k i); [ eauto using presup_exp_ctx | |];
    [ econstructor; [ eapply lift_exp_max_left; exact HB | eapply lift_exp_max_right; exact HA ]
    | econstructor; eassumption ]
  end.
Qed.

(** ** Growing a Frame's Module

    A frame is the module so far; what resolves in it keeps resolving, the same
    way, once the module has one more entry. *)

Lemma gc_lookup_grow : forall Θ Δm Φ x E R r Δ b A B,
    Θ ⍮ gu_mk Δm Φ :: R ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
    Θ ⍮ gu_mk Δm (Φ ⊳ x ↦ E) :: R ∋ᵍ r ⇒ Δ ⍮ ge_def b A B.
Proof.
  intros * Hlk; inversion Hlk; subst; [| econstructor; eassumption ].
  (* the telescope handed back depends on the frames' parameters only *)
  destruct n as [| n].
  - match goal with H : List.nth_error _ 0 = Some _ |- _ => cbn in H; injection H as <- end.
    change (gs_tele (List.skipn 0 (gu_mk Δm Φ :: R)))
      with (gs_tele (List.skipn 0 (gu_mk Δm (Φ ⊳ x ↦ E) :: R))).
    apply (gcl_rel _ _ 0 (gu_mk Δm (Φ ⊳ x ↦ E))); [ reflexivity |].
    apply gml_old; assumption.
  - change (gs_tele (List.skipn (S n) (gu_mk Δm Φ :: R)))
      with (gs_tele (List.skipn (S n) (gu_mk Δm (Φ ⊳ x ↦ E) :: R))).
    econstructor; eassumption.
Qed.

(** Transport with nothing to open: resolution carries over as it is, and the
    parameters in scope are the same. *)
Corollary rebase_preserves_wf : forall Θ1 Θ2 Ξ1 Ξ2,
    (forall r Δ b A B, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b A B -> Θ2 ⍮ Ξ2 ∋ᵍ r ⇒ Δ ⍮ ge_def b A B) ->
    gs_tele Ξ1 = gs_tele Ξ2 ->
    ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅ ->
    (forall Γ, ⊢ Θ1 ⍮ Ξ1 ⍮ Γ -> ⊢ Θ2 ⍮ Ξ2 ⍮ Γ) /\
    (forall Γ A M, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ M : A -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ M : A).
Proof.
  intros * Hr Ht Hb.
  pose proof (exp_open_ext_id _ path_open_here) as He0.
  pose proof (list_open_ext_id (p_rel 0 nil) He0) as Hl.
  destruct (open_preserves_wf Θ1 Θ2 Ξ1 Ξ2 nil nil (p_rel 0 nil)) as (Hc & He & _);
    [ intros * Hlk; rewrite path_open_here, Hl, He0; destruct B; cbn; rewrite ?He0; auto
    | rewrite Hl, Ht; reflexivity
    | assumption |].
  split; intros.
  - pose proof (Hc _ _ _ ltac:(eassumption) eq_refl eq_refl Γ (eq_sym (List.app_nil_r Γ))) as H'.
    rewrite Hl, List.app_nil_r in H'; exact H'.
  - pose proof (He _ _ _ _ _ ltac:(eassumption) eq_refl eq_refl Γ (eq_sym (List.app_nil_r Γ))) as H'.
    rewrite Hl, !He0, List.app_nil_r in H'; exact H'.
Qed.

Corollary grow_preserves_wf : forall Θ Δm Φ x E R,
    ⊢g Θ ⍮ gu_mk Δm (Φ ⊳ x ↦ E) :: R ->
    (forall Γ, ⊢ Θ ⍮ gu_mk Δm Φ :: R ⍮ Γ -> ⊢ Θ ⍮ gu_mk Δm (Φ ⊳ x ↦ E) :: R ⍮ Γ) /\
    (forall Γ A M, Θ ⍮ gu_mk Δm Φ :: R ⍮ Γ ⊢ M : A ->
        Θ ⍮ gu_mk Δm (Φ ⊳ x ↦ E) :: R ⍮ Γ ⊢ M : A).
Proof.
  intros; apply rebase_preserves_wf;
    [ intros; eapply gc_lookup_grow; eassumption | reflexivity | constructor; assumption ].
Qed.

(** Resolution, up to equations on what it hands back. *)

Lemma gcl_rel_eq : forall Θ Ξ n U ip Δ b A B p Δ0 A0 B0,
    List.nth_error Ξ n = Some U ->
    gu_mod U ∋ ip ⇒ Δ ⍮ ge_def b A B ->
    p = p_rel n ip ->
    Δ0 = (Δ ++ gs_tele (List.skipn n Ξ))[p_rel n nil]p ->
    A0 = A[p_rel n nil]p ->
    B0 = B[p_rel n nil]p ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ0 ⍮ ge_def b A0 B0.
Proof. intros; subst; econstructor; eassumption. Qed.

Lemma gcl_abs_eq : forall Θ Ξ fp U ip Δ b A B p Δ0 A0 B0,
    gds_lookup Θ fp = Some U ->
    gu_mod U ∋ ip ⇒ Δ ⍮ ge_def b A B ->
    p = p_abs fp ip ->
    Δ0 = (Δ ++ gs_tele (U :: nil))[p_abs fp nil]p ->
    A0 = A[p_abs fp nil]p ->
    B0 = B[p_abs fp nil]p ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ0 ⍮ ge_def b A0 B0.
Proof. intros; subst; econstructor; eassumption. Qed.

(** ** Reading out through a Nested Module

    The frame of a nested module [x] sits on the frame of the module declaring
    it.  Once that module has [x], the nested module's members are its members
    [x.ip], a frame further out is one frame nearer, and the nested module's
    parameters become local. *)

Lemma gc_lookup_pop : forall Θ Δm Φ x Δ' Φ' R r Δ b A B,
    Θ ⍮ gu_mk Δ' Φ' :: gu_mk Δm Φ :: R ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
    Θ ⍮ gu_mk Δm (Φ ⊳ x ↦ ge_mod Δ' Φ') :: R ∋ᵍ r[p_rel 0 (x :: nil)]p
      ⇒ Δ[p_rel 0 (x :: nil)]p ⍮ ge_def b A[p_rel 0 (x :: nil)]p B[p_rel 0 (x :: nil)]p.
Proof.
  intros * Hlk; inversion Hlk; subst.
  - match goal with H : List.nth_error _ ?n = Some _ |- _ =>
      rename H into Hn; destruct n as [| [| n]]; cbn [List.nth_error] in Hn
    end.
    + injection Hn as <-.
      eapply (gcl_rel_eq _ _ 0 (gu_mk Δm (Φ ⊳ x ↦ ge_mod Δ' Φ')));
        [ reflexivity | apply gml_in; eassumption | reflexivity | .. ];
        open_id path_open_here; [| reflexivity | reflexivity ].
      cbn [List.skipn]; rewrite (gs_tele_cons (gu_mk Δ' Φ')), !list_open_app;
        open_comp (path_open_shift_in x).
      rewrite <- !List.app_assoc; reflexivity.
    + injection Hn as <-.
      eapply (gcl_rel_eq _ _ 0 (gu_mk Δm (Φ ⊳ x ↦ ge_mod Δ' Φ')));
        [ reflexivity | apply gml_old; eassumption | reflexivity | .. ];
        open_comp (path_open_shift_succ_in 0 x); reflexivity.
    + eapply (gcl_rel_eq _ _ (S n)); [ eassumption | eassumption | reflexivity | .. ];
        open_comp (path_open_shift_succ_in (S n) x); reflexivity.
  - eapply gcl_abs_eq; [ eassumption | eassumption | reflexivity | .. ];
      open_comp (path_open_abs_absorb fp (p_rel 0 (x :: nil))); reflexivity.
Qed.

Corollary pop_preserves_wf : forall Θ Δm Φ x Δ' Φ' R,
    ⊢ Θ ⍮ gu_mk Δm (Φ ⊳ x ↦ ge_mod Δ' Φ') :: R ⍮ Δ' ->
    forall Γ A M, Θ ⍮ gu_mk Δ' Φ' :: gu_mk Δm Φ :: R ⍮ Γ ⊢ M : A ->
      Θ ⍮ gu_mk Δm (Φ ⊳ x ↦ ge_mod Δ' Φ') :: R ⍮ Γ[p_rel 0 (x :: nil)]p ++ Δ'
        ⊢ M[p_rel 0 (x :: nil)]p : A[p_rel 0 (x :: nil)]p.
Proof.
  intros * HΔ'.
  destruct (open_preserves_wf Θ Θ (gu_mk Δ' Φ' :: gu_mk Δm Φ :: R)
              (gu_mk Δm (Φ ⊳ x ↦ ge_mod Δ' Φ') :: R) nil Δ' (p_rel 0 (x :: nil)))
    as (_ & He & _);
    [ intros; apply gc_lookup_pop; assumption
    | cbn [List.app]; rewrite (gs_tele_cons (gu_mk Δ' Φ')); open_comp (path_open_shift_in x);
      reflexivity
    | assumption |].
  intros * HM; exact (He _ _ _ _ _ HM eq_refl eq_refl Γ (eq_sym (List.app_nil_r Γ))).
Qed.

(** ** Filing a Level

    What a new level files is fresh in the levels below, so resolution in them
    is unchanged; and at the empty stack only filed units resolve, whose paths
    no opening moves. *)

Lemma wf_gdep_fresh : forall Θ d,
    wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> gds_fresh fp Θ.
Proof.
  induction 1; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] |]; eauto.
Qed.

Lemma wf_gdep_unit : forall Θ d,
    wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> Θ ⍮ nil ⊢u U.
Proof.
  induction 1; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] |]; eauto.
Qed.

Lemma wf_gdep_lookup : forall Θ d,
    wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> gd_lookup d fp = Some U.
Proof.
  induction 1 as [| Θ d U fp Hd IH HU Hfr Hfr']; intros fq V Hin; cbn in Hin; [ contradiction |].
  unfold gd_lookup, path_beq in *; cbn.
  destruct Hin as [[= <- <-] | Hin].
  - destruct (path_eq_dec fp fp); [ reflexivity | contradiction ].
  - destruct (path_eq_dec fq fp) as [-> |]; [| eauto ].
    exfalso; apply (Hfr' (List.in_map fst _ _ Hin)).
Qed.

Lemma gd_lookup_app_none : forall d d' fp,
    gd_lookup d fp = None ->
    gd_lookup (d ++ d') fp = gd_lookup d' fp.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; cbn; intros * H; [ reflexivity |].
  destruct (path_beq fp (fst fV)); [ discriminate | auto ].
Qed.

Lemma gds_lookup_level : forall Θ d fp U,
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    gds_lookup Θ fp = Some U ->
    gds_lookup (d :: Θ) fp = Some U.
Proof.
  unfold gds_lookup; intros * Hfr Hl; cbn [List.concat].
  destruct (gd_lookup d fp) as [V |] eqn:Hd.
  - apply gd_lookup_in, Hfr, gds_fresh_no_lookup in Hd; unfold gds_lookup in Hd; congruence.
  - rewrite gd_lookup_app_none; assumption.
Qed.

Lemma gc_lookup_level : forall Θ d a r Δ b A B,
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    Θ ⍮ nil ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
    d :: Θ ⍮ nil ∋ᵍ r[a]p ⇒ Δ[a]p ⍮ ge_def b A[a]p B[a]p.
Proof.
  intros * Hfr Hlk; inversion Hlk; subst.
  - match goal with Hn : List.nth_error nil ?n = Some _ |- _ => destruct n; discriminate end.
  - eapply gcl_abs_eq; [ apply gds_lookup_level; eassumption | eassumption | reflexivity | .. ];
      open_comp (path_open_abs_absorb fp a); reflexivity.
Qed.

Corollary level_preserves_wf : forall Θ d a,
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    ⊢ d :: Θ ⍮ nil ⍮ ⋅ ->
    (forall Γ, ⊢ Θ ⍮ nil ⍮ Γ -> ⊢ d :: Θ ⍮ nil ⍮ Γ[a]p) /\
    (forall Γ A M, Θ ⍮ nil ⍮ Γ ⊢ M : A -> d :: Θ ⍮ nil ⍮ Γ[a]p ⊢ M[a]p : A[a]p).
Proof.
  intros * Hfr Hb.
  destruct (open_preserves_wf Θ (d :: Θ) nil nil nil nil a) as (Hc & He & _);
    [ intros; apply gc_lookup_level; assumption | reflexivity | assumption |].
  split; intros * H; rewrite <- (List.app_nil_r Γ[a]p).
  - exact (Hc _ _ _ H eq_refl eq_refl Γ (eq_sym (List.app_nil_r Γ))).
  - exact (He _ _ _ _ _ H eq_refl eq_refl Γ (eq_sym (List.app_nil_r Γ))).
Qed.

(** A unit filed at [fp] is read out of its own frame by [p_abs fp []], and its
    parameters become local. *)
Lemma gc_lookup_file : forall Θ d fp U r Δ b A B,
    wf_gdep Θ d ->
    List.In (fp, U) d ->
    Θ ⍮ U :: nil ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
    d :: Θ ⍮ nil ∋ᵍ r[p_abs fp nil]p ⇒ Δ[p_abs fp nil]p ⍮ ge_def b A[p_abs fp nil]p B[p_abs fp nil]p.
Proof.
  intros * Hd Hin Hlk; inversion Hlk; subst.
  - match goal with H : List.nth_error _ ?n = Some _ |- _ =>
      destruct n as [| n]; cbn in H; [ injection H as <- | destruct n; discriminate ]
    end.
    eapply gcl_abs_eq;
      [ unfold gds_lookup; cbn [List.concat]; apply gd_lookup_app; eapply wf_gdep_lookup; eassumption
      | eassumption | reflexivity | .. ];
      open_comp (path_open_rel_abs 0 fp); reflexivity.
  - eapply gcl_abs_eq;
      [ apply gds_lookup_level; [ eapply wf_gdep_fresh; eassumption | eassumption ]
      | eassumption | reflexivity | .. ];
      open_comp (path_open_abs_absorb fp0 (p_abs fp nil)); reflexivity.
Qed.

Corollary file_preserves_exp : forall Θ d fp U,
    wf_gdep Θ d ->
    List.In (fp, U) d ->
    ⊢ d :: Θ ⍮ nil ⍮ (gs_tele (U :: nil))[p_abs fp nil]p ->
    forall Γ A M, Θ ⍮ U :: nil ⍮ Γ ⊢ M : A ->
      d :: Θ ⍮ nil ⍮ Γ[p_abs fp nil]p ++ (gs_tele (U :: nil))[p_abs fp nil]p
        ⊢ M[p_abs fp nil]p : A[p_abs fp nil]p.
Proof.
  intros * Hd Hin Hb.
  destruct (open_preserves_wf Θ (d :: Θ) (U :: nil) nil nil (gs_tele (U :: nil))[p_abs fp nil]p
              (p_abs fp nil)) as (_ & He & _);
    [ intros; eapply gc_lookup_file; eassumption
    | rewrite gs_tele_nil, List.app_nil_r; reflexivity
    | assumption |].
  intros * HM; exact (He _ _ _ _ _ HM eq_refl eq_refl Γ (eq_sym (List.app_nil_r Γ))).
Qed.

(** ** What Resolution Hands Back is Well Typed *)

Definition rwf (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall p Δ b A B,
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b A B ->
    (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A).

(** A module's members, in the frame the module pushes. *)
Definition mod_typed (Θ : gdeps) (Ξ : gstack) (Δm : ctx) (Φ : gmod) : Prop :=
  forall ip Δ b A B,
    Φ ∋ ip ⇒ Δ ⍮ ge_def b A B ->
    (exists i, Θ ⍮ gu_mk Δm Φ :: Ξ ⍮ Δ ⊢ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ gu_mk Δm Φ :: Ξ ⍮ Δ ⊢ M : A).

Definition entry_typed (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ A B =>
      (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Type@i) /\ (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A)
  | ge_mod Δ Φ => mod_typed Θ Ξ Δ Φ
  end.

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
  eapply wk_preserves_exp; [ exact HM | apply wf_wk_shiftn; exact HΓ ].
Qed.

(** ... and in the stack with one more frame, the frame's parameters being local
    to begin with. *)
Lemma push_closed_exp : forall Θ U Ξ M A,
    ⊢g Θ ⍮ U :: Ξ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A ->
    exp_scoped 0 M -> exp_scoped 0 A ->
    Θ ⍮ U :: Ξ ⍮ ⋅ ⊢ M[p_rel 1 nil]p : A[p_rel 1 nil]p.
Proof.
  intros * Hg HM HsM HsA.
  destruct (wf_gctx_pop _ _ _ Hg) as [_ HU].
  destruct (push_preserves_wf _ _ _ Hg) as (_ & Hp & _).
  apply (Hp nil); cbn [List.app].
  apply closed_weaken_exp; assumption.
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

(** Generalizing a member over the telescope it is checked under. *)
Lemma generalize_frame : forall Θ Ξ Δ A B i,
    ⊢g Θ ⍮ Ξ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    (forall M, B = Some M -> Θ ⍮ Ξ ⍮ Δ ⊢ M : A) ->
    (exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_pi (Δ ++ gs_tele Ξ) A : Type@j) /\
    (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_fn (Δ ++ gs_tele Ξ) M : ctx_pi (Δ ++ gs_tele Ξ) A).
Proof.
  intros * Hg HA HM.
  destruct (localize_wf _ _ (tele_wf _ _ Hg)) as (_ & He & _).
  pose proof (He _ _ _ _ _ HA eq_refl eq_refl) as HA'.
  split; [ eapply ctx_pi_wf0; eassumption |].
  intros M HB; eapply ctx_fn_wf0; [ eassumption | exact (He _ _ _ _ _ (HM _ HB) eq_refl eq_refl) ].
Qed.

Lemma rwf_push : forall Θ U Ξ,
    ⊢g Θ ⍮ U :: Ξ ->
    rwf Θ Ξ ->
    mod_typed Θ Ξ (gu_params U) (gu_mod U) ->
    rwf Θ (U :: Ξ).
Proof.
  intros * Hg HR HU p Δ b A B Hlk.
  destruct (wf_gctx_pop _ _ _ Hg) as [Hg' _].
  assert (⊢ Θ ⍮ Ξ ⍮ ⋅) as HΞ by (constructor; assumption).
  inversion Hlk; subst.
  - match goal with H : List.nth_error _ ?n = Some _ |- _ =>
      rename H into Hn; destruct n as [| n]; cbn [List.nth_error List.skipn] in Hn |- *
    end.
    + (* a member of the new frame *)
      injection Hn as <-; destruct U as [Δm Φ].
      match goal with Hin : gu_mod _ ∋ _ ⇒ _ ⍮ _ |- _ => destruct (HU _ _ _ _ _ Hin) as [[i HA] HM] end.
      open_id path_open_here; exact (generalize_frame _ _ _ _ _ _ Hg HA HM).
    + (* further out: push it *)
      match goal with Hin : gu_mod _ ∋ _ ⇒ _ ⍮ _ |- _ =>
        pose proof (gcl_rel Θ Ξ _ _ _ _ _ _ _ Hn Hin) as Hl0
      end.
      pose proof (wf_gc_lookup_closed _ _ _ _ _ _ _ _ HΞ Hl0) as [HsA HsM].
      destruct (HR _ _ _ _ _ Hl0) as [[i HA] HM].
      split.
      * exists i; pose proof (push_closed_exp _ U _ _ _ Hg HA HsA I) as H'.
        rewrite ctx_pi_open in H'; open_comp (path_open_shift_shift n) in H'; exact H'.
      * intros M' HB; match goal with _ : gu_mod _ ∋ _ ⇒ _ ⍮ ge_def _ _ ?B0 |- _ =>
          destruct B0 as [M |]; cbn in HB; inversion HB; subst end.
        pose proof (push_closed_exp _ U _ _ _ Hg (HM _ eq_refl) HsM HsA) as H'.
        rewrite ctx_pi_open, ctx_fn_open in H'; open_comp (path_open_shift_shift n) in H'; exact H'.
  - (* a filed unit, read out as before *)
    match goal with
    | Hfp : gds_lookup _ _ = Some _, Hin : gu_mod _ ∋ _ ⇒ _ ⍮ _ |- _ =>
        pose proof (gcl_abs Θ Ξ _ _ _ _ _ _ _ Hfp Hin) as Hl0
    end.
    pose proof (wf_gc_lookup_closed _ _ _ _ _ _ _ _ HΞ Hl0) as [HsA HsM].
    destruct (HR _ _ _ _ _ Hl0) as [[i HA] HM].
    split.
    + exists i; pose proof (push_closed_exp _ U _ _ _ Hg HA HsA I) as H'.
      rewrite ctx_pi_open in H'; open_comp (path_open_abs_absorb fp (p_rel 1 nil)) in H'; exact H'.
    + intros M' HB; match goal with _ : gu_mod _ ∋ _ ⇒ _ ⍮ ge_def _ _ ?B0 |- _ =>
          destruct B0 as [M |]; cbn in HB; inversion HB; subst end.
      pose proof (push_closed_exp _ U _ _ _ Hg (HM _ eq_refl) HsM HsA) as H'.
      rewrite ctx_pi_open, ctx_fn_open in H';
        open_comp (path_open_abs_absorb fp (p_rel 1 nil)) in H'; exact H'.
Qed.

(** Filing a level: a unit of the new level is read out of its own frame, and
    one of the levels below is resolved as before. *)

Lemma gc_lookup_level_same : forall Θ d r Δ b A B,
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    Θ ⍮ nil ∋ᵍ r ⇒ Δ ⍮ ge_def b A B ->
    d :: Θ ⍮ nil ∋ᵍ r ⇒ Δ ⍮ ge_def b A B.
Proof.
  intros * Hfr Hlk; inversion Hlk; subst.
  - match goal with Hn : List.nth_error nil ?n = Some _ |- _ => destruct n; discriminate end.
  - econstructor; [ apply gds_lookup_level |]; eassumption.
Qed.

Lemma rwf_level : forall Θ d,
    wf_gdeps Θ ->
    wf_gdep Θ d ->
    rwf Θ nil ->
    (forall fp U, List.In (fp, U) d -> mod_typed Θ nil (gu_params U) (gu_mod U)) ->
    rwf (d :: Θ) nil.
Proof.
  intros * HΘ Hd HR HU p Δ b A B Hlk.
  assert (⊢ d :: Θ ⍮ nil ⍮ ⋅) as Hb
    by (apply wf_ctx_empty, wf_gctx_intro, wf_gstack_nil, wf_gdeps_cons; assumption).
  pose proof (wf_gdep_fresh _ _ Hd) as Hfr.
  inversion Hlk; subst.
  - match goal with Hn : List.nth_error nil ?n = Some _ |- _ => destruct n; discriminate end.
  - match goal with Hfp : gds_lookup _ _ = Some _ |- _ => rename Hfp into Hl end.
    unfold gds_lookup in Hl; cbn [List.concat] in Hl.
    apply gd_lookup_app_inv in Hl as [Hl | Hl].
    + (* filed at the new level *)
      apply gd_lookup_in in Hl as Hin.
      pose proof (wf_gdep_unit _ _ Hd _ _ Hin) as HUw.
      match goal with H : gu_mod _ ∋ _ ⇒ _ ⍮ _ |- _ => destruct (HU _ _ Hin _ _ _ _ _ H) as [[i HA] HM] end.
      assert (⊢ d :: Θ ⍮ nil ⍮ (gs_tele (U :: nil))[p_abs fp nil]p) as Ht.
      { destruct (level_preserves_wf _ _ (p_abs fp nil) Hfr Hb) as [Hlc _].
        rewrite gs_tele_cons, gs_tele_nil, List.app_nil_r; open_comp (path_open_rel_abs 1 fp).
        apply Hlc; eapply wf_gmod_ctx, wf_gunit_mod; exact HUw. }
      destruct U as [Δu Φu].
      pose proof (file_preserves_exp _ _ _ _ Hd Hin Ht) as Hf.
      pose proof (Hf _ _ _ HA) as HA'; change (Type@i[p_abs fp nil]p) with (Type@i) in HA'.
      rewrite list_open_app; split; [ eapply ctx_pi_wf0; eassumption |].
      intros M' HB; match goal with _ : gu_mod _ ∋ _ ⇒ _ ⍮ ge_def _ _ ?B0 |- _ =>
        destruct B0 as [M |]; cbn in HB; inversion HB; subst end.
      eapply ctx_fn_wf0; [ eassumption | apply Hf, HM; reflexivity ].
    + (* filed below *)
      match goal with H : gu_mod _ ∋ _ ⇒ _ ⍮ _ |- _ =>
        pose proof (gcl_abs Θ nil _ _ _ _ _ _ _ Hl H) as Hl0 end.
      destruct (HR _ _ _ _ _ Hl0) as [[i HA] HM].
      destruct (rebase_preserves_wf Θ (d :: Θ) nil nil) as [_ He];
        [ intros; apply gc_lookup_level_same; assumption | reflexivity | assumption |].
      split; [ exists i; apply He, HA | intros; apply He, HM; assumption ].
Qed.

(** Extending a module: [x] itself was checked in the module so far, a member
    of a nested module [x] in the frame [x] pushed, and an earlier member in the
    module so far. *)
Lemma mod_typed_ext : forall Θ Ξ Δ Φ x E,
    ⊢g Θ ⍮ gu_mk Δ (Φ ⊳ x ↦ E) :: Ξ ->
    mod_typed Θ Ξ Δ Φ ->
    Θ ⍮ gu_mk Δ Φ :: Ξ ⊢e E ->
    entry_typed Θ (gu_mk Δ Φ :: Ξ) E ->
    mod_typed Θ Ξ Δ (Φ ⊳ x ↦ E).
Proof.
  intros * Hg HΦ HE HEt ip Δ1 b A B Hlk.
  destruct (grow_preserves_wf _ _ _ _ _ _ Hg) as [Hgc Hge].
  inversion Hlk; subst.
  - cbn in HEt; destruct HEt as [[i HA] HM].
    split; [ exists i; apply Hge, HA | intros; apply Hge; auto ].
  - cbn [entry_typed] in HEt.
    match goal with HE : _ ⍮ ?W :: _ ⊢e ge_mod ?D _ |- _ =>
      assert (⊢ Θ ⍮ gu_mk Δ (Φ ⊳ x ↦ ge_mod D _) :: Ξ ⍮ D) as HΔ'
        by (apply Hgc; inversion HE; subst; eapply wf_gmod_ctx; eassumption)
    end.
    match goal with H : _ ∋ _ ⇒ _ ⍮ ge_def _ _ _ |- _ =>
      destruct (HEt _ _ _ _ _ H) as [[i HA] HM]; rename H into Hin
    end.
    split.
    + exists i; change (Type@i) with (Type@i[p_rel 0 (x :: nil)]p).
      apply pop_preserves_wf; assumption.
    + intros M' HB; match type of Hin with _ ∋ _ ⇒ _ ⍮ ge_def _ _ ?B0 =>
        destruct B0 as [M |]; cbn in HB; inversion HB; subst end.
      apply pop_preserves_wf; [ assumption | apply HM; reflexivity ].
  - match goal with H : Φ ∋ _ ⇒ _ ⍮ _ |- _ => destruct (HΦ _ _ _ _ _ H) as [[i HA] HM] end.
    split; [ exists i; apply Hge, HA | intros; apply Hge; auto ].
Qed.

(** ** Presupposition for Typing, relative to Resolution *)

Lemma presup_exp_typ_rwf : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    rwf Θ Ξ ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  induction 1; intros HR;
    repeat match goal with IH : rwf _ _ -> _ |- _ => specialize (IH HR) end;
    assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2; destruct_conjs.
  (* a global: its generalized type is a type at [⋅], and closed *)
  all: try match goal with
    | Hl : _ ⍮ _ ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ _, HΓ : ⊢ _ ⍮ _ ⍮ _ |- _ =>
        destruct (HR _ _ _ _ _ Hl) as [[i HA] _]; exists i;
        apply closed_weaken_exp;
        [ assumption | exact HA | eapply wf_gc_lookup_type_closed; eassumption | exact I ]
    end.
  all: mauto 3.
  - eexists; mauto 3.
  - eexists; mauto 3.
Qed.

(** ** The Mutual Theorem *)

Theorem presup_global :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> rwf Θ Ξ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> rwf Θ Ξ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> rwf Θ Ξ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> rwf Θ Ξ) /\
  (forall Θ Ξ E, Θ ⍮ Ξ ⊢e E -> entry_typed Θ Ξ E) /\
  (forall Θ Ξ Δ Φ, Θ ⍮ Ξ ⍮ Δ ⊢m Φ -> mod_typed Θ Ξ Δ Φ) /\
  (forall Θ Ξ U, Θ ⍮ Ξ ⊢u U -> mod_typed Θ Ξ (gu_params U) (gu_mod U)) /\
  (forall Θ d, wf_gdep Θ d ->
      forall fp U, List.In (fp, U) d -> mod_typed Θ nil (gu_params U) (gu_mod U)) /\
  (forall Θ, wf_gdeps Θ -> rwf Θ nil) /\
  (forall Θ Ξ, wf_gstack Θ Ξ -> rwf Θ Ξ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> rwf Θ Ξ).
Proof.
  apply wf_mut_ind_all; intros; try assumption.
  - (* an axiom *)
    cbn; split; [ eauto | discriminate ].
  - (* a definition: its type is a type by presupposition of its body *)
    cbn; split; [ eapply presup_exp_typ_rwf; eassumption | intros ? [= <-]; assumption ].
  - (* the empty module *)
    intros ? * Hlk; inversion Hlk.
  - apply mod_typed_ext; try assumption.
    assert (⊢g Θ ⍮ Ξ) by eauto using ctx_wf_gctx, wf_gmod_ctx.
    constructor; constructor; [ apply wf_gctx_stack; assumption |].
    constructor; cbn; constructor; assumption.
  - contradiction.
  - match goal with H : List.In _ (_ :: _) |- _ => destruct H as [[= <- <-] |] end; eauto.
  - intros ? * Hlk; inversion Hlk; subst;
      [ match goal with Hn : List.nth_error nil ?n = Some _ |- _ => destruct n; discriminate end
      | discriminate ].
  - apply rwf_level; assumption.
  - apply rwf_push; [ constructor; constructor | |]; assumption.
Qed.

Corollary gctx_rwf : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> rwf Θ Ξ.
Proof. apply presup_global. Qed.

(** What a use of a global needs: its generalized type and body, in any
    well-formed context. *)
Corollary wf_glob_typ : forall Θ Ξ Γ p Δ b A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b A B ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Type@i.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ _ _ _ Hl) as [[i HA] _].
  exists i; apply closed_weaken_exp;
    [ assumption | exact HA | eapply wf_gc_lookup_type_closed; eassumption | exact I ].
Qed.

Corollary wf_glob_body : forall Θ Ξ Γ p Δ b A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b A (Some M) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ _ _ _ Hl) as [_ HM].
  apply closed_weaken_exp;
    [ assumption | apply HM; reflexivity
    | eapply wf_gc_lookup_body_closed; eassumption
    | eapply wf_gc_lookup_type_closed; eassumption ].
Qed.

Theorem presup_exp_typ : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * H; eapply (presup_exp_typ_rwf H), gctx_rwf, ctx_wf_gctx, presup_exp_ctx, H.
Qed.
