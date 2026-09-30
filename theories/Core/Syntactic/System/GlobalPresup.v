(** * Presupposition

    Presupposition is proved for all eleven judgments at once.  A global is used
    at its resolved type without premising that it is a type, and a definition's
    type is not checked separately from its body; that each is a type is what
    presupposition of the *entry's* own derivation gives, and that derivation is
    part of [⊢g], so the induction has to range over the global judgments too.

    What the induction carries for a module is [ins_typed]: each member,
    generalized, well typed in the frame it was inserted into.  That is what
    [Discharge] needs to close a frame, member by member. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Discharge.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

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
Lemma closed_weaken_exp : forall Θ Ξ Γ M A cs cs',
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A ->
    exp_scoped 0 cs M -> exp_scoped 0 cs' A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ HM HsM HsA.
  rewrite <- (exp_closed_wk M _ (wk_shiftn (length Γ)) HsM),
    <- (exp_closed_wk A _ (wk_shiftn (length Γ)) HsA).
  eapply wk_preserves_exp; [ exact HM |].
  pose proof (wf_wk_shiftn_app Θ Ξ Γ nil) as Hw; rewrite List.app_nil_r in Hw.
  apply Hw; [ assumption | constructor; eapply ctx_wf_gctx; eassumption ].
Qed.

(** ** Pushing Frames *)

Lemma gctx_suffix : forall Ξa Θ Ξb, ⊢g Θ ⍮ Ξa ++ Ξb -> ⊢g Θ ⍮ Ξb.
Proof.
  induction Ξa; intros * H; cbn in *; [ assumption |].
  apply IHΞa, (wf_gctx_pop _ _ _ H).
Qed.

Lemma push_many : forall Ξa Θ Ξb Γ A M,
    ⊢g Θ ⍮ Ξa ++ Ξb ->
    Θ ⍮ Ξb ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξa ++ Ξb ⍮ Γ[↑ₘ (length Ξa)]ᵐ ⊢ M[↑ₘ (length Ξa)]ᵐ : A[↑ₘ (length Ξa)]ᵐ.
Proof.
  induction Ξa as [| U Ξa IH]; intros * Hg HM; cbn [length List.app] in *.
  - rewrite ctx_msub_shift_zero, !exp_msub_shift_zero; assumption.
  - destruct (push_preserves_wf _ _ _ Hg) as (_ & Hp & _).
    pose proof (Hp _ _ _ (IH _ _ _ _ _ (proj1 (wf_gctx_pop _ _ _ Hg)) HM)) as H.
    rewrite ctx_msub_shift_shift, !exp_msub_shift_shift in H; exact H.
Qed.

(** A parameter's type is a type wherever the parameter is in scope: pushed
    past the frames nearer in, then read off the frame's parameters. *)
Lemma wf_param_typ : forall Θ Ξ Γ n U k T,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.nth_error Ξ n = Some U ->
    gu_params U ∋ #k : T ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ T[↑ₘ (S n)]ᵐ[sb_params n] : Type@i.
Proof.
  intros * HΓ Hn Hk.
  destruct (List.nth_error_split _ _ Hn) as (Ξa & Ξb & -> & Hlen).
  assert (Hg : ⊢g Θ ⍮ (Ξa ++ U :: nil) ++ Ξb)
    by (rewrite <- List.app_assoc; eapply ctx_wf_gctx; eassumption).
  destruct (wf_gctx_pop _ _ _ (gctx_suffix Ξa _ _ ltac:(rewrite <- List.app_assoc in Hg; exact Hg)))
    as [_ HP].
  destruct (ctx_lookup_wf _ _ _ _ _ HP Hk) as [i HT].
  pose proof (push_many _ _ _ _ _ _ Hg HT) as HT'.
  rewrite List.length_app, Nat.add_comm in HT'; cbn in HT'; rewrite Hlen in HT'.
  rewrite <- List.app_assoc in HT'; cbn in HT'.
  exists i; change (Type@i) with (Type@i[sb_params n]).
  eapply sub_preserves_exp; [ exact HT' |].
  econstructor; [ assumption | eapply presup_exp_ctx; exact HT' |].
  intros x B Hl; destruct (ctx_lookup_msub_inv _ _ _ _ Hl) as (B0 & Hl0 & ->).
  rewrite (exp_msub_ext _ _ _ (ms_qn_shift _ _)).
  econstructor; [ assumption | | eassumption ].
  rewrite List.nth_error_app2 by lia; rewrite Hlen, Nat.sub_diag; reflexivity.
Qed.

(** ** Levels *)

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

(** ** What Resolution Hands Back is Well Typed *)

Definition rwf (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall p Δ b pv A B,
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A).

Definition entry_typed (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ pv A B =>
      (exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Type@i) /\ (forall M, B = Some M -> Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A)
  | ge_mod Δ Φ => ins_typed Θ Ξ Δ Φ
  end.

(** A member, typed in the frame it was inserted into, is typed in the whole
    module. *)
Lemma ins_typed_full : forall Θ Ξ P Φ ip Δ b pv A B,
    ins_typed Θ Ξ P Φ ->
    ⊢ Θ ⍮ gu_mk P Φ :: Ξ ⍮ ⋅ ->
    Φ ∋ ip ⇒ Δ ⍮ ge_def b pv A B ->
    (exists i, Θ ⍮ gu_mk P Φ :: Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Type@i) /\
    (forall M, B = Some M -> Θ ⍮ gu_mk P Φ :: Ξ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A).
Proof.
  intros * Hins Hb Hl.
  destruct (gm_lookup_ins _ _ _ _ Hl) as [Φq Hi].
  destruct (frame_grow _ _ _ _ _ (gm_ins_prefix _ _ _ _ _ Hi) Hb) as (_ & He & _).
  destruct (Hins _ _ _ _ _ _ _ Hi) as [[i HT] HM].
  split; [ exists i; auto | intros; auto ].
Qed.

Lemma rwf_push : forall Θ U Ξ,
    ⊢g Θ ⍮ U :: Ξ ->
    rwf Θ Ξ ->
    ins_typed Θ Ξ (gu_params U) (gu_mod U) ->
    rwf Θ (U :: Ξ).
Proof.
  intros * Hg HR HU p Δ b pv A B Hlk.
  assert (Hb : ⊢ Θ ⍮ U :: Ξ ⍮ ⋅) by (constructor; assumption).
  assert (HΞ : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; exact (proj1 (wf_gctx_pop _ _ _ Hg))).
  destruct (push_preserves_wf _ _ _ Hg) as (_ & Hp & _).
  inversion Hlk as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst.
  - destruct n as [| n]; cbn in Hn.
    + (* a member of the new frame *)
      injection Hn as <-; destruct U as [P Φ].
      rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero.
      eapply ins_typed_full; eassumption.
    + (* further out: push it *)
      pose proof (gcl_rel Θ Ξ _ _ _ _ _ _ _ _ Hn Hm) as Hl0.
      destruct (HR _ _ _ _ _ _ Hl0) as [[i HA] HM].
      split.
      * exists i; pose proof (Hp nil _ _ HA) as H'; cbn [ctx_msub msubst MSub_ctx] in H'.
        rewrite ctx_pi_msub, (exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_msub_shift_shift,
          exp_msub_shift_shift in H'; exact H'.
      * intros M' HB; destruct B0 as [M0 |]; cbn in HB; inversion HB; subst.
        pose proof (Hp nil _ _ (HM _ eq_refl)) as H'; cbn [ctx_msub msubst MSub_ctx] in H'.
        rewrite ctx_pi_msub, ctx_fn_msub, !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_msub_shift_shift,
          !exp_msub_shift_shift in H'; exact H'.
  - (* a filed unit, read out as before: pushing moves nothing in it *)
    pose proof (gcl_abs Θ Ξ _ _ _ _ _ _ _ _ Hf Hm) as Hl0.
    assert (HΘ : units_scoped Θ) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ HΞ)).
    assert (Hfix : ms_abs_fix (↑ₘ 1)) by (intros ? ?; reflexivity).
    destruct (gc_lookup_abs_nil _ _ _ _ _ _ _ _ HΘ Hl0 ltac:(intros ? ?; discriminate)) as (HΔ & HA0 & HB0).
    destruct (HR _ _ _ _ _ _ Hl0) as [[i HA] HM].
    revert HA HM HΔ HA0 HB0.
    generalize (Δ0[close (p_abs fp nil) (length (gu_params U0))]ᵐ ++ gu_params U0) as Δa.
    generalize A0[ms_close (p_abs fp nil) (length (gu_params U0)) (length Δ0)]ᵐ as Aa.
    generalize B0[ms_close (p_abs fp nil) (length (gu_params U0)) (length Δ0)]ᵐ as Ba.
    intros * HA HM HΔ HA0 HB0.
    assert (HsA : exp_scoped 0 nil (ctx_pi Δa Aa)) by (apply ctx_pi_scoped; rewrite ?Nat.add_0_r; assumption).
    split.
    + exists i; pose proof (Hp nil _ _ HA) as H'; cbn [ctx_msub msubst MSub_ctx] in H'.
      rewrite (exp_msub_nil _ _ _ HsA Hfix) in H'; exact H'.
    + intros M' ->; cbn in HB0.
      assert (HsM : exp_scoped 0 nil (ctx_fn Δa M')) by (apply ctx_fn_scoped; rewrite ?Nat.add_0_r; assumption).
      pose proof (Hp nil _ _ (HM _ eq_refl)) as H'; cbn [ctx_msub msubst MSub_ctx] in H'.
      rewrite (exp_msub_nil _ _ _ HsA Hfix), (exp_msub_nil _ _ _ HsM Hfix) in H'; exact H'.
Qed.

(** Filing a level: a unit of the new level is closed as it is filed, and one of
    the levels below is resolved as before. *)
Lemma rwf_level : forall Θ d,
    wf_gdeps Θ ->
    wf_gdep Θ d ->
    rwf Θ nil ->
    (forall fp U, List.In (fp, U) d -> ins_typed Θ nil (gu_params U) (gu_mod U)) ->
    rwf (d :: Θ) nil.
Proof.
  intros * HΘ Hd HR HU p Δ b pv A B Hlk.
  assert (Hb : ⊢ d :: Θ ⍮ nil ⍮ ⋅)
    by (apply wf_ctx_empty, wf_gctx_intro, wf_gstack_nil, wf_gdeps_cons; assumption).
  pose proof (wf_gdep_fresh _ _ Hd) as Hfr.
  assert (Hgrow : Θ ⊑ d :: Θ)
    by (unfold gds_sub; intros; apply gds_lookup_level; assumption).
  inversion Hlk as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst;
    [ destruct n; discriminate |].
  pose proof Hf as Hl; unfold gds_lookup in Hl; cbn [List.concat] in Hl.
  apply gd_lookup_app_inv in Hl as [Hl | Hl].
  - (* filed at the new level: closed as it is filed *)
    apply gd_lookup_in in Hl as Hin.
    pose proof (wf_gdep_unit _ _ Hd _ _ Hin) as HUw; inversion HUw; subst.
    pose proof (HU _ _ Hin) as HUi.
    destruct U as [PU ΦU]; cbn in *.
    destruct (gm_lookup_ins _ _ _ _ Hm) as [Φq Hi].
    destruct (closable_file Θ (d :: Θ) fp PU ΦU ltac:(assumption) HUi Hf Hgrow Hb
                (S (gm_count Φq)) Φq _ _ _ _ _ _ ltac:(lia) Hi) as [[i HT] HM].
    rewrite ctx_pi_app, <- ctx_pi_close.
    split; [ eapply ctx_pi_wf0; eassumption |].
    intros M' HB; destruct B0 as [M0 |]; cbn in HB; inversion HB; subst.
    rewrite ctx_fn_app, <- ctx_fn_close; eapply ctx_fn_wf0; [ eassumption | apply HM; reflexivity ].
  - (* filed below *)
    pose proof (gcl_abs Θ nil _ _ _ _ _ _ _ _ Hl Hm) as Hl0.
    destruct (HR _ _ _ _ _ _ Hl0) as [[i HA] HM].
    destruct (levels_grow Θ (d :: Θ) nil Hgrow Hb) as (_ & He & _).
    split; [ exists i; apply He, HA | intros; apply He, HM; assumption ].
Qed.

(** Extending a module: [x] itself was checked in the module so far, a member
    of a nested module [x] is closed as it was inserted, and an earlier member
    was typed already. *)
Lemma ins_typed_ext : forall Θ Ξ P Φ x E,
    Θ ⍮ Ξ ⍮ P ⊢m Φ ⊳ x ↦ E ->
    ins_typed Θ Ξ P Φ ->
    entry_typed Θ (gu_mk P Φ :: Ξ) E ->
    ins_typed Θ Ξ P (Φ ⊳ x ↦ E).
Proof.
  intros * Hw HΦ HE Φq ip Δ b pv A B Hi.
  inversion Hi as [| ? ? ? ? ? ? ? ? ? ? ? Hi' | ? ? ? ? ? ? ? Hi']; subst.
  - exact HE.
  - cbn [entry_typed] in HE.
    destruct (closable_pop Θ Ξ P Φ x Δ' Φ' Hw HE (S (gm_count Φp')) Φp' _ _ _ _ _ _ ltac:(lia) Hi')
      as [[i HT] HM].
    rewrite ctx_pi_app, <- ctx_pi_close.
    split; [ eapply ctx_pi_wf0; eassumption |].
    intros M' HB; destruct B0 as [M0 |]; cbn in HB; inversion HB; subst.
    rewrite ctx_fn_app, <- ctx_fn_close; eapply ctx_fn_wf0; [ eassumption | apply HM; reflexivity ].
  - eauto.
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
    | Hl : _ ⍮ _ ∋ᵍ _ ⇒ _ ⍮ ge_def _ _ _ _, HΓ : ⊢ _ ⍮ _ ⍮ _ |- _ =>
        destruct (HR _ _ _ _ _ _ Hl) as [[i HA] _]; exists i;
        eapply (closed_weaken_exp _ _ _ _ _ _ nil);
        [ assumption | exact HA | eapply wf_gc_lookup_type_closed; eassumption | exact I ]
    end.
  (* a parameter *)
  all: try solve [ eapply wf_param_typ; eassumption ].
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
  (forall Θ Ξ Δ Φ, Θ ⍮ Ξ ⍮ Δ ⊢m Φ -> ins_typed Θ Ξ Δ Φ) /\
  (forall Θ Ξ U, Θ ⍮ Ξ ⊢u U -> ins_typed Θ Ξ (gu_params U) (gu_mod U)) /\
  (forall Θ d, wf_gdep Θ d ->
      forall fp U, List.In (fp, U) d -> ins_typed Θ nil (gu_params U) (gu_mod U)) /\
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
    intros ? * Hi; inversion Hi.
  - apply ins_typed_ext; [ econstructor | |]; eassumption.
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
Corollary wf_glob_typ : forall Θ Ξ Γ p Δ b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Type@i.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ _ _ _ _ Hl) as [[i HA] _].
  exists i; eapply (closed_weaken_exp _ _ _ _ _ _ nil);
    [ assumption | exact HA | eapply wf_gc_lookup_type_closed; eassumption | exact I ].
Qed.

Corollary wf_glob_body : forall Θ Ξ Γ p Δ b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A (Some M) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  intros * HΓ Hl; destruct (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ _ _ _ _ Hl) as [_ HM].
  eapply closed_weaken_exp;
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
