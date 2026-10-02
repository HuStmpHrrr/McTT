(** * Member Types under Weakening and Substitution

    The syntactic helpers of [Members] commute with the operations: a
    telescope, a body and a member chain are moved entry by entry, under the
    binders before each entry.  The relation [member_type] and the function
    [member_unfold] commute with a weakening and with a substitution that sends
    every module slot to the same unit ([wf_sub]'s module field), and they grow
    with the global context. *)

From Stdlib Require Import Lia List PeanoNat Morphisms.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Scoping.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Lifting under Many Binders *)

Lemma wk_qn_add : forall a b φ, wk_eq (wk_qn a (wk_qn b φ)) (wk_qn (a + b) φ).
Proof. induction a; intros; cbn; [ reflexivity | apply wk_q_cong, IHa ]. Qed.

Lemma sb_qn_add : forall a b σ, sb_eq (sb_qn a (sb_qn b σ)) (sb_qn (a + b) σ).
Proof. induction a; intros; cbn; [ reflexivity | apply sb_q_cong, IHa ]. Qed.

(** ** Telescopes *)

Lemma tele_wk_app : forall Ψ Δ φ,
    tele_wk (Ψ ++ Δ) φ = tele_wk Ψ (wk_qn (length Δ) φ) ++ tele_wk Δ φ.
Proof.
  induction Ψ; intros; cbn; [ reflexivity |].
  rewrite IHΨ; f_equal; apply centry_wk_wk_eq.
  rewrite length_app, wk_qn_add; reflexivity.
Qed.

Lemma tele_sub_app : forall Ψ Δ σ,
    tele_sub (Ψ ++ Δ) σ = tele_sub Ψ (sb_qn (length Δ) σ) ++ tele_sub Δ σ.
Proof.
  induction Ψ; intros; cbn; [ reflexivity |].
  rewrite IHΨ; f_equal; apply centry_sub_sb_eq.
  rewrite length_app, sb_qn_add; reflexivity.
Qed.

Lemma ctx_pi_wk : forall Δ A φ,
    (ctx_pi Δ A)[φ]ʷ = ctx_pi (tele_wk Δ φ) A[wk_qn (length Δ) φ]ʷ.
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

Lemma ctx_pi_sub : forall Δ A σ,
    (ctx_pi Δ A)[σ] = ctx_pi (tele_sub Δ σ) A[sb_qn (length Δ) σ].
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

Lemma ctx_fn_wk : forall Δ M φ,
    (ctx_fn Δ M)[φ]ʷ = ctx_fn (tele_wk Δ φ) M[wk_qn (length Δ) φ]ʷ.
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

Lemma ctx_fn_sub : forall Δ M σ,
    (ctx_fn Δ M)[σ] = ctx_fn (tele_sub Δ σ) M[sb_qn (length Δ) σ].
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

(** ** Bodies *)

Lemma body_ctx_wk : forall Φ φ, body_ctx (gmod_wk Φ φ) = tele_wk (body_ctx Φ) φ.
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | ] | Φ IH c]; intros; cbn; auto;
    rewrite IH, length_body_ctx; reflexivity.
Qed.

Lemma body_ctx_sub : forall Φ σ, body_ctx (gmod_sub Φ σ) = tele_sub (body_ctx Φ) σ.
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | ] | Φ IH c]; intros; cbn; auto;
    rewrite IH, length_body_ctx; reflexivity.
Qed.

Lemma gm_names_wk : forall Φ φ, gm_names (gmod_wk Φ φ) = gm_names Φ.
Proof. induction Φ; intros; cbn; rewrite ?IHΦ; reflexivity. Qed.

Lemma gm_names_sub : forall Φ σ, gm_names (gmod_sub Φ σ) = gm_names Φ.
Proof. induction Φ; intros; cbn; rewrite ?IHΦ; reflexivity. Qed.

Lemma gm_prefix_upto_wk : forall Φ x φ,
    gm_prefix_upto (gmod_wk Φ φ) x = option_map (fun Φ' => gmod_wk Φ' φ) (gm_prefix_upto Φ x).
Proof.
  induction Φ; intros; cbn; auto.
  destruct (String.eqb x s); auto.
Qed.

Lemma gm_prefix_upto_sub : forall Φ x σ,
    gm_prefix_upto (gmod_sub Φ σ) x = option_map (fun Φ' => gmod_sub Φ' σ) (gm_prefix_upto Φ x).
Proof.
  induction Φ; intros; cbn; auto.
  destruct (String.eqb x s); auto.
Qed.

Lemma gm_checks_wk : forall Φ φ,
    gm_checks (gmod_wk Φ φ) =
    map (fun '(Φ0, c) => (gmod_wk Φ0 φ, bcheck_wk c (wk_qn (gm_binders Φ0) φ))) (gm_checks Φ).
Proof. induction Φ; intros; cbn; rewrite ?IHΦ; reflexivity. Qed.

Lemma gm_checks_sub : forall Φ σ,
    gm_checks (gmod_sub Φ σ) =
    map (fun '(Φ0, c) => (gmod_sub Φ0 σ, bcheck_sub c (sb_qn (gm_binders Φ0) σ))) (gm_checks Φ).
Proof. induction Φ; intros; cbn; rewrite ?IHΦ; reflexivity. Qed.

(** The prefix of a body up to an entry is a prefix of its context. *)
Lemma gm_prefix_upto_body_ctx : forall Φ x Φx,
    gm_prefix_upto Φ x = Some Φx -> exists Ψ, body_ctx Φ = Ψ ++ body_ctx Φx.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * H; cbn in H; try discriminate.
  - destruct (String.eqb x y); [ injection H as <-; exists nil; reflexivity |].
    destruct (IH _ _ H) as [Ψ HΨ]; cbn.
    destruct E as [? ? ? [] | ]; rewrite HΨ; eexists (_ :: Ψ); reflexivity.
  - exact (IH _ _ H).
Qed.

Lemma gm_checks_body_ctx : forall Φ Φ0 c,
    In (Φ0, c) (gm_checks Φ) -> exists Ψ, body_ctx Φ = Ψ ++ body_ctx Φ0.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c0]; intros * H; cbn in H; try contradiction.
  - destruct (IH _ _ H) as [Ψ HΨ]; cbn.
    destruct E as [? ? ? [] | ]; rewrite HΨ; eexists (_ :: Ψ); reflexivity.
  - destruct H as [[= <- <-] | H]; [ exists nil; reflexivity | exact (IH _ _ H) ].
Qed.

(** ** Module Expressions *)

Lemma member_ref_wk : forall ch H φ,
    (member_ref H ch)[φ]ʷ = member_ref (modexp_wk H φ) ch.
Proof. induction ch as [| x [| y ch] IH]; intros; cbn; auto; apply IH. Qed.

Lemma member_ref_sub : forall ch H σ,
    (member_ref H ch)[σ] = member_ref H[σ]ᵐ ch.
Proof. induction ch as [| x [| y ch] IH]; intros; cbn; auto; apply IH. Qed.

Lemma apps_wk : forall args M φ, (apps M args)[φ]ʷ = apps M[φ]ʷ (map (fun N => N[φ]ʷ) args).
Proof. induction args; intros; cbn; auto; apply IHargs. Qed.

Lemma apps_sub : forall args M σ, (apps M args)[σ] = apps M[σ] (map (fun N => N[σ]) args).
Proof. induction args; intros; cbn; auto; apply IHargs. Qed.

(** A root that a weakening or a same-unit substitution sends to a root. *)
Definition me_root (H : modexp) : Prop :=
  match H with
  | me_path _ | me_var _ | me_lit _ => True
  | _ => False
  end.

Lemma modexp_spine_root : forall H R args pre, modexp_spine H = (R, args, pre) -> me_root R.
Proof.
  induction H; intros * Hs; cbn in Hs; try (injection Hs as <- <- <-; exact I);
    destruct (modexp_spine H) as [[R' args'] pre']; injection Hs as <- <- <-; eauto.
Qed.

Lemma modexp_spine_wk : forall H R args pre φ,
    modexp_spine H = (R, args, pre) ->
    modexp_spine (modexp_wk H φ) = (modexp_wk R φ, map (fun N => N[φ]ʷ) args, pre).
Proof.
  induction H as [| | H IHH y | H IHH N |]; intros * Hs; cbn in Hs |- *; try (injection Hs as <- <- <-; reflexivity).
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ eq_refl); reflexivity.
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ eq_refl), map_app; reflexivity.
Qed.

Lemma me_noargs_wk : forall H φ, me_noargs H -> me_noargs (modexp_wk H φ).
Proof. induction H; intros; cbn in *; auto. Qed.



(** ** The [Π] of a Type *)

Lemma pi_view_wk : forall A φ B C,
    pi_view A = Some (B, C) -> pi_view A[φ]ʷ = Some (B[φ]ʷ, C[wk_q φ]ʷ).
Proof.
  induction A; intros * H; try destruct b as [B0 N | U]; cbn in H |- *; try discriminate.
  - injection H as <- <-; reflexivity.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal.
    + symmetry; apply exp_wk_sub_extend.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; symmetry; apply exp_wk_shift_wk_q.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq; intros [| x]; reduce_index; reflexivity.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; f_equal; symmetry; apply gunit_wk_shift_wk_q.
Qed.

Lemma pi_view_sub : forall A σ B C,
    pi_view A = Some (B, C) -> pi_view A[σ] = Some (B[σ], C[q σ]).
Proof.
  induction A; intros * H; try destruct b as [B0 N | U]; cbn in H |- *; try discriminate.
  - injection H as <- <-; reflexivity.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
Qed.

(** ** Scoping of Member Types *)

Lemma ctx_scoped_lookup_mod : forall Γ x U n,
    ctx_scoped n Γ -> Γ ∋ #x ⇒ₘ U -> gunit_scoped (length Γ + n) U.
Proof.
  intros * HΓ Hlk; induction Hlk; cbn in *; destruct_all;
    eapply gunit_scoped_wk; eauto; cbn; lia.
Qed.

Lemma gmod_scoped_body_ctx : forall Φ n, gmod_scoped n Φ -> ctx_scoped n (body_ctx Φ).
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | ] | Φ IH c]; intros * HΦ; cbn in *; destruct_all;
    repeat split; auto; rewrite length_body_ctx; assumption.
Qed.

Lemma gm_prefix_upto_scoped : forall Φ x Φx n,
    gm_prefix_upto Φ x = Some Φx -> gmod_scoped n Φ -> gmod_scoped n Φx.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * H HΦ; cbn in *; try discriminate; destruct_all.
  - destruct (String.eqb x y); [ injection H as <-; cbn; auto | eauto ].
  - eauto.
Qed.

Lemma pi_view_scoped : forall A B C n,
    pi_view A = Some (B, C) -> exp_scoped n A -> exp_scoped n B /\ exp_scoped (S n) C.
Proof.
  induction A; intros * H HA; try destruct b as [B0 N | U]; cbn in H, HA; try discriminate; destruct_all.
  - injection H as <- <-; auto.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ]; injection H as <- <-.
    destruct (IHA _ _ _ eq_refl H1) as [HB HC]; split.
    + eapply exp_scoped_sub; [ eassumption |]; intros [| x] ?; reduce_index; cbn [sentry_scoped wk_shift]; auto; lia.
    + eapply exp_scoped_sub; [ eassumption |].
      intros [| [| x]] ?; reduce_index; cbn [sentry_scoped wk_shift]; try lia.
      eapply exp_scoped_wk; [ eassumption |]; cbn; lia.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ]; injection H as <- <-.
    destruct (IHA _ _ _ eq_refl H1) as [HB HC]; split.
    + eapply exp_scoped_sub; [ eassumption |]; intros [| x] ?; reduce_index; cbn [sentry_scoped wk_shift]; auto; lia.
    + eapply exp_scoped_sub; [ eassumption |].
      intros [| [| x]] ?; reduce_index; cbn [sentry_scoped wk_shift]; try lia.
      eapply gunit_scoped_wk; [ eassumption |]; cbn; lia.
Qed.

Lemma member_type_scoped : forall Θ Ξ,
    (forall Γ H ch k A, member_type Θ Ξ Γ H ch k A ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> modexp_scoped (length Γ) H -> exp_scoped (length Γ) A) /\
    (forall Γ U ch k A, unit_member_type Θ Ξ Γ U ch k A ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> gunit_scoped (length Γ) U -> exp_scoped (length Γ) A).
Proof.
  intros Θ Ξ; apply member_type_both_ind; intros; cbn in *; destruct_all.
  - match goal with Hc : gctx_closed _ _, Hr : gc_resolve _ _ _ = _ |- _ => destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc Hr) as [HA _] end.
    eapply exp_scoped_mono; [| eassumption ]; lia.
  - match goal with Hc : gctx_closed _ _, Hr : gc_module _ _ _ = _ |- _ => pose proof (gctx_closed_module _ _ _ _ Hc Hr) as HT end; cbn in HT.
    eapply exp_scoped_mono; [| apply ctx_pi_scoped; [ eassumption | cbn; exact I ] ]; lia.
  - match goal with Hc : gctx_closed _ _, Hr : gc_module _ _ _ = _ |- _ => pose proof (gctx_closed_module _ _ _ _ Hc Hr) as HU end; cbn in HU.
    match goal with IH : _ -> _ -> _ -> exp_scoped 0 ?A |- exp_scoped _ ?A => eapply exp_scoped_mono; [| apply IH; [ assumption | exact I | exact HU ] ]; lia end.
  - match goal with IH : _ -> _ -> gunit_scoped _ ?U -> _, Hl : _ ∋ # _ ⇒ₘ ?U, HΓ : ctx_scoped 0 _ |- _ =>
      apply IH; [ assumption | assumption |]; pose proof (ctx_scoped_lookup_mod _ _ _ _ HΓ Hl) as HU; rewrite Nat.add_0_r in HU; exact HU end.
  - auto.
  - match goal with IH : _ -> _ -> _ -> _ |- _ => apply IH; assumption end.
  - match goal with Hp : pi_view _ = Some _, IH : _ -> _ -> _ -> exp_scoped _ ?A |- _ => destruct (pi_view_scoped _ _ _ _ Hp (IH ltac:(assumption) ltac:(assumption) ltac:(assumption))) as [_ HC] end.
    apply exp_scoped_sub1; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; apply ctx_pi_scoped; [ assumption | exact I ].
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    match goal with Hp : gm_prefix_upto _ _ = _, HΦ : gmod_scoped _ ?Φ |- _ => pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HΦ) as HΦ' end; cbn in HΦ'; destruct_all.
    apply ctx_pi_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    rewrite length_app, length_body_ctx, <- Nat.add_assoc; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    match goal with Hp : gm_prefix_upto _ _ = _, HΦ : gmod_scoped _ ?Φ |- _ => pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HΦ) as HΦ' end; cbn in HΦ'; destruct_all.
    apply ctx_pi_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    rewrite length_app, length_body_ctx, <- Nat.add_assoc.
    match goal with IH : _ -> _ -> _ -> exp_scoped _ ?A |- exp_scoped _ ?A =>
      replace (gm_binders Φ' + (length Δ + length Γ)) with (length (body_ctx Φ' ++ Δ ++ Γ)) by (rewrite !length_app, length_body_ctx; lia); apply IH end.
    + assumption.
    + apply ctx_scoped_app_iff; split; [| apply ctx_scoped_app_iff; split; assumption ].
      rewrite length_app; apply gmod_scoped_body_ctx; assumption.
    + rewrite !length_app, length_body_ctx; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    apply ctx_pi_scoped; [ assumption |].
    rewrite <- length_app; match goal with IH : _ -> _ -> _ -> exp_scoped _ ?A |- exp_scoped _ ?A => apply IH end;
      [ assumption | apply ctx_scoped_app_iff; split; assumption | rewrite length_app; assumption ].
Qed.

(** ** Member Types under a Weakening *)

(** A weakening sends a module slot to a slot of the same unit. *)
Definition wk_mod_compat (φ : wk) (Γ Δ : ctx) : Prop :=
  forall x U, Δ ∋ #x ⇒ₘ U -> Γ ∋ #(φ x) ⇒ₘ gunit_wk U φ.

Lemma wk_mod_compat_q : forall φ Γ Δ e,
    wk_mod_compat φ Γ Δ -> wk_mod_compat (wk_q φ) (centry_wk e φ :: Γ) (e :: Δ).
Proof.
  intros * Hφ x U Hlk; inversion Hlk; subst; cbn.
  - rewrite gunit_wk_shift_wk_q; constructor.
  - rewrite gunit_wk_shift_wk_q; constructor; auto.
Qed.

Lemma wk_mod_compat_ext : forall Ψ φ Γ Δ,
    wk_mod_compat φ Γ Δ -> wk_mod_compat (wk_qn (length Ψ) φ) (tele_wk Ψ φ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using wk_mod_compat_q. Qed.

Lemma gm_prefix_upto_ext_wk : forall Φ x Φ' E φ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    gm_prefix_upto (gmod_wk Φ φ) x = Some (gm_ext (gmod_wk Φ' φ) x (gentry_wk E (wk_qn (gm_binders Φ') φ))).
Proof. intros * H; rewrite gm_prefix_upto_wk, H; reflexivity. Qed.

Lemma gm_prefix_upto_mod_wk : forall Φ x Φ' U φ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_mod U)) ->
    gm_prefix_upto (gmod_wk Φ φ) x = Some (gm_ext (gmod_wk Φ' φ) x (ge_mod (gunit_wk U (wk_qn (gm_binders Φ') φ)))).
Proof. intros * H; rewrite gm_prefix_upto_wk, H; reflexivity. Qed.

Lemma gm_prefix_upto_def_wk : forall Φ x Φ' b pv A B φ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    gm_prefix_upto (gmod_wk Φ φ) x =
    Some (gm_ext (gmod_wk Φ' φ) x (ge_def b pv A[wk_qn (gm_binders Φ') φ]ʷ
                                        (option_map (fun M => M[wk_qn (gm_binders Φ') φ]ʷ) B))).
Proof. intros * H; rewrite gm_prefix_upto_wk, H; cbn; destruct B; reflexivity. Qed.

(** The type of a body member after a weakening of its unit. *)
Lemma ctx_pi_body_wk : forall Φ' Δ A φ,
    (ctx_pi (body_ctx Φ' ++ Δ) A)[φ]ʷ =
    ctx_pi (body_ctx (gmod_wk Φ' (wk_qn (length Δ) φ)) ++ tele_wk Δ φ)
      A[wk_qn (gm_binders Φ') (wk_qn (length Δ) φ)]ʷ.
Proof.
  intros; rewrite ctx_pi_wk, tele_wk_app, body_ctx_wk; f_equal.
  apply exp_wk_wk_eq; rewrite wk_qn_add, length_app, length_body_ctx; reflexivity.
Qed.

Lemma member_type_wk : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    (forall Δ H ch k A, member_type Θ Ξ Δ H ch k A ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Ξ Γ (modexp_wk H φ) ch k A[φ]ʷ) /\
    (forall Δ U ch k A, unit_member_type Θ Ξ Δ U ch k A ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> unit_member_type Θ Ξ Γ (gunit_wk U φ) ch k A[φ]ʷ).
Proof.
  intros Θ Ξ Hc; apply member_type_both_ind; intros; cbn [modexp_wk].
  - destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc e) as [HA _].
    rewrite exp_closed_wk by assumption; eapply mt_path_def; eassumption.
  - pose proof (gctx_closed_module _ _ _ _ Hc e) as HT; cbn in HT.
    rewrite exp_closed_wk by (apply ctx_pi_scoped; [ assumption | exact I ]); eapply mt_path_mod; eassumption.
  - pose proof (gctx_closed_module _ _ _ _ Hc e) as HU; cbn in HU.
    rewrite exp_closed_wk; [ eapply mt_path_alias; eassumption |].
    exact (proj2 (member_type_scoped Θ Ξ) nil U r k A u Hc I HU).
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - rewrite exp_wk_sub_extend; econstructor; [ eauto | apply pi_view_wk; eassumption ].
  - rewrite gunit_wk_mk, ctx_pi_wk; cbn; constructor.
  - rewrite gunit_wk_mk, ctx_pi_body_wk; eapply umt_def.
    apply gm_prefix_upto_def_wk with (1 := e).
  - rewrite gunit_wk_mk, ctx_pi_body_wk; eapply umt_mod.
    + apply gm_prefix_upto_mod_wk with (1 := e).
    + replace (body_ctx (gmod_wk Φ' (wk_qn (length Δ) φ)) ++ tele_wk Δ φ ++ Γ0)
        with (tele_wk (body_ctx Φ' ++ Δ) φ ++ Γ0)
        by (rewrite tele_wk_app, body_ctx_wk, <- List.app_assoc; reflexivity).
      replace (gunit_wk Uy (wk_qn (gm_binders Φ') (wk_qn (length Δ) φ)))
        with (gunit_wk Uy (wk_qn (length (body_ctx Φ' ++ Δ)) φ))
        by (apply gunit_wk_wk_eq; rewrite wk_qn_add, length_app, length_body_ctx; reflexivity).
      replace A[wk_qn (gm_binders Φ') (wk_qn (length Δ) φ)]ʷ
        with A[wk_qn (length (body_ctx Φ' ++ Δ)) φ]ʷ
        by (apply exp_wk_wk_eq; rewrite wk_qn_add, length_app, length_body_ctx; reflexivity).
      apply H; rewrite List.app_assoc; apply wk_mod_compat_ext; assumption.
  - rewrite gunit_wk_mk, ctx_pi_wk; cbn; constructor.
    apply H; apply wk_mod_compat_ext; assumption.
Qed.

(** ** Member Types under a Substitution *)

(** A substitution sends a module slot to the unit it holds, transported: as a
    literal, or as a slot holding that unit. *)
Definition sub_mod_compat (σ : sub) (Γ Δ : ctx) : Prop :=
  forall x U, Δ ∋ #x ⇒ₘ U ->
    σ x = se_mod (me_lit U[σ]ᵘ) \/ exists y, σ x = se_var y /\ Γ ∋ #y ⇒ₘ U[σ]ᵘ.

(** The root of a module expression, if it is a slot, is a module slot of
    [Γ].  A same-unit substitution sends such a root to a root. *)
Fixpoint me_slot_root (Γ : ctx) (H : modexp) : Prop :=
  match H with
  | me_mem H _ | me_app H _ => me_slot_root Γ H
  | me_var x => exists U, Γ ∋ #x ⇒ₘ U
  | _ => True
  end.

Lemma modexp_spine_sub : forall H R args pre σ Γ Δ,
    sub_mod_compat σ Γ Δ ->
    me_slot_root Δ H ->
    modexp_spine H = (R, args, pre) ->
    modexp_spine H[σ]ᵐ = (R[σ]ᵐ, map (fun N => N[σ]) args, pre).
Proof.
  induction H as [| n | H IHH y | H IHH N |]; intros * Hσ Hr Hs; cbn in Hr, Hs |- *;
    try (injection Hs as <- <- <-; reflexivity).
  - injection Hs as <- <- <-; destruct Hr as [U HU]; cbn.
    destruct (Hσ _ _ HU) as [-> | (y & -> & _)]; reflexivity.
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ _ _ Hσ Hr eq_refl); reflexivity.
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ _ _ Hσ Hr eq_refl), map_app; reflexivity.
Qed.

Lemma me_noargs_sub : forall H σ Γ Δ,
    sub_mod_compat σ Γ Δ -> me_slot_root Δ H -> me_noargs H -> me_noargs H[σ]ᵐ.
Proof.
  induction H as [| n | H IHH y | H IHH N |]; intros * Hσ Hr HH; cbn in *; eauto.
  destruct Hr as [U HU]; destruct (Hσ _ _ HU) as [-> | (y & -> & _)]; exact I.
Qed.

Lemma sub_mod_compat_q : forall σ Γ Δ e,
    sub_mod_compat σ Γ Δ -> sub_mod_compat (q σ) (centry_sub e σ :: Γ) (e :: Δ).
Proof.
  intros * Hσ x U Hlk; inversion Hlk; subst; cbn.
  - right; exists 0; rewrite sb_q_zero, gunit_wk_shift_sub_q; split; [ reflexivity | constructor ].
  - rewrite sb_q_succ, gunit_wk_shift_sub_q.
    match goal with Hl : _ ∋ # _ ⇒ₘ _ |- _ => destruct (Hσ _ _ Hl) as [-> | (y & -> & Hy)] end; [ left; reflexivity |].
    right; exists (S y); split; [ reflexivity | constructor; assumption ].
Qed.

Lemma sub_mod_compat_ext : forall Ψ σ Γ Δ,
    sub_mod_compat σ Γ Δ -> sub_mod_compat (sb_qn (length Ψ) σ) (tele_sub Ψ σ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using sub_mod_compat_q. Qed.

Lemma gm_prefix_upto_mod_sub : forall Φ x Φ' U σ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_mod U)) ->
    gm_prefix_upto (gmod_sub Φ σ) x = Some (gm_ext (gmod_sub Φ' σ) x (ge_mod U[sb_qn (gm_binders Φ') σ]ᵘ)).
Proof. intros * H; rewrite gm_prefix_upto_sub, H; reflexivity. Qed.

Lemma gm_prefix_upto_def_sub : forall Φ x Φ' b pv A B σ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    gm_prefix_upto (gmod_sub Φ σ) x =
    Some (gm_ext (gmod_sub Φ' σ) x (ge_def b pv A[sb_qn (gm_binders Φ') σ]
                                        (option_map (fun M => M[sb_qn (gm_binders Φ') σ]) B))).
Proof. intros * H; rewrite gm_prefix_upto_sub, H; cbn; destruct B; reflexivity. Qed.

Lemma ctx_pi_body_sub : forall Φ' Δ A σ,
    (ctx_pi (body_ctx Φ' ++ Δ) A)[σ] =
    ctx_pi (body_ctx (gmod_sub Φ' (sb_qn (length Δ) σ)) ++ tele_sub Δ σ)
      A[sb_qn (gm_binders Φ') (sb_qn (length Δ) σ)].
Proof.
  intros; rewrite ctx_pi_sub, tele_sub_app, body_ctx_sub; f_equal.
  apply exp_sub_sb_eq; rewrite sb_qn_add, length_app, length_body_ctx; reflexivity.
Qed.

Lemma member_type_sub : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    (forall Δ H ch k A, member_type Θ Ξ Δ H ch k A ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Ξ Γ H[σ]ᵐ ch k A[σ]) /\
    (forall Δ U ch k A, unit_member_type Θ Ξ Δ U ch k A ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> unit_member_type Θ Ξ Γ U[σ]ᵘ ch k A[σ]).
Proof.
  intros Θ Ξ Hc; apply member_type_both_ind; intros; cbn [modexp_sub].
  - destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc e) as [HA _].
    rewrite exp_closed_sub by assumption; eapply mt_path_def; eassumption.
  - pose proof (gctx_closed_module _ _ _ _ Hc e) as HT; cbn in HT.
    rewrite exp_closed_sub by (apply ctx_pi_scoped; [ assumption | exact I ]); eapply mt_path_mod; eassumption.
  - pose proof (gctx_closed_module _ _ _ _ Hc e) as HU; cbn in HU.
    rewrite exp_closed_sub; [ eapply mt_path_alias; eassumption |].
    exact (proj2 (member_type_scoped Θ Ξ) nil U r k A u Hc I HU).
  - destruct (H0 _ _ c) as [-> | (y & -> & Hy)]; cbn [sentry_modexp].
    + eapply mt_lit; eauto.
    + eapply mt_var; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - rewrite exp_sub_extend_sub, <- exp_sub_q_extend; econstructor; [ eauto | apply pi_view_sub; eassumption ].
  - rewrite gunit_sub_mk, ctx_pi_sub; cbn; constructor.
  - rewrite gunit_sub_mk, ctx_pi_body_sub; eapply umt_def.
    apply gm_prefix_upto_def_sub with (1 := e).
  - rewrite gunit_sub_mk, ctx_pi_body_sub; eapply umt_mod.
    + apply gm_prefix_upto_mod_sub with (1 := e).
    + replace (body_ctx (gmod_sub Φ' (sb_qn (length Δ) σ)) ++ tele_sub Δ σ ++ Γ0)
        with (tele_sub (body_ctx Φ' ++ Δ) σ ++ Γ0)
        by (rewrite tele_sub_app, body_ctx_sub, <- List.app_assoc; reflexivity).
      replace (Uy[sb_qn (gm_binders Φ') (sb_qn (length Δ) σ)]ᵘ)
        with (Uy[sb_qn (length (body_ctx Φ' ++ Δ)) σ]ᵘ)
        by (apply gunit_sub_sb_eq; rewrite sb_qn_add, length_app, length_body_ctx; reflexivity).
      replace A[sb_qn (gm_binders Φ') (sb_qn (length Δ) σ)]
        with A[sb_qn (length (body_ctx Φ' ++ Δ)) σ]
        by (apply exp_sub_sb_eq; rewrite sb_qn_add, length_app, length_body_ctx; reflexivity).
      apply H; rewrite List.app_assoc; apply sub_mod_compat_ext; assumption.
  - rewrite gunit_sub_mk, ctx_pi_sub; cbn; constructor.
    apply H; apply sub_mod_compat_ext; assumption.
Qed.

(** ** Expansions and δ-Reducts under the Operations *)

(** The three forms an expansion takes. *)
Lemma member_expansion_inv : forall U ch M,
    member_expansion U ch = Some M ->
    (exists Δ E, U = gu_mk Δ (md_alias E) /\ ch <> nil /\ M = ctx_fn Δ (member_ref E ch)) \/
    (exists Δ Φ x Φ' b A B, U = gu_body Δ Φ /\ ch = x :: nil /\
       gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b false A B)) /\
       M = ctx_fn (body_ctx (gm_ext Φ' x (ge_def b false A B)) ++ Δ) (a_var 0)) \/
    (exists Δ Φ y ch' Φ' Uy, U = gu_body Δ Φ /\ ch = y :: ch' /\ ch' <> nil /\
       gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) /\
       M = ctx_fn (body_ctx (gm_ext Φ' y (ge_mod Uy)) ++ Δ) (member_ref (me_var 0) ch')).
Proof.
  intros [Δ [Φ | E]] [| x ch'] M H; unfold member_expansion in H; try discriminate.
  - right.
    destruct (gm_prefix_upto Φ x) as [Φx |] eqn:Ex; [| discriminate ].
    destruct Φx as [| Φ' y [b [|] A B | Uy] | Φ' c]; try discriminate;
      destruct ch' as [| z ch'']; try discriminate; injection H as <-.
    + pose proof Ex as Ex'; unfold gm_prefix_upto in Ex'.
      assert (y = x) as ->.
      { clear - Ex. induction Φ as [| Φ IH w E | Φ IH c]; cbn in Ex; try discriminate; auto.
        destruct (String.eqb_spec x w) as [-> |]; [ congruence | auto ]. }
      left; do 7 eexists; repeat split; eassumption.
    + assert (y = x) as ->.
      { clear - Ex. induction Φ as [| Φ IH w E | Φ IH c]; cbn in Ex; try discriminate; auto.
        destruct (String.eqb_spec x w) as [-> |]; [ congruence | auto ]. }
      right; do 6 eexists; repeat split; try eassumption; discriminate.
  - left; injection H as <-; do 2 eexists; repeat split; discriminate.
Qed.

Lemma member_expansion_alias : forall Δ E ch,
    ch <> nil -> member_expansion (gu_mk Δ (md_alias E)) ch = Some (ctx_fn Δ (member_ref E ch)).
Proof. intros * Hch; destruct ch; [ contradiction | reflexivity ]. Qed.

Lemma member_expansion_def : forall Δ Φ x Φ' b A B,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b false A B)) ->
    member_expansion (gu_body Δ Φ) (x :: nil) =
    Some (ctx_fn (body_ctx (gm_ext Φ' x (ge_def b false A B)) ++ Δ) (a_var 0)).
Proof. intros * H; unfold member_expansion; rewrite H; reflexivity. Qed.

Lemma member_expansion_mod : forall Δ Φ y ch' Φ' Uy,
    ch' <> nil ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
    member_expansion (gu_body Δ Φ) (y :: ch') =
    Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_mod Uy)) ++ Δ) (member_ref (me_var 0) ch')).
Proof. intros * Hch H; unfold member_expansion; rewrite H; destruct ch'; [ contradiction | reflexivity ]. Qed.

Lemma member_expansion_wk : forall U ch M φ,
    member_expansion U ch = Some M ->
    member_expansion (gunit_wk U φ) ch = Some M[φ]ʷ.
Proof.
  intros * H; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & b & A & B & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_wk_mk; cbn [moddef_wk].
  - rewrite member_expansion_alias by assumption; rewrite ctx_fn_wk, member_ref_wk; reflexivity.
  - erewrite member_expansion_def by (apply gm_prefix_upto_def_wk; eassumption).
    rewrite ctx_fn_wk, tele_wk_app; destruct B; cbn [body_ctx tele_wk option_map centry_wk];
      rewrite body_ctx_wk, length_body_ctx; cbn; reflexivity.
  - erewrite member_expansion_mod by first [ assumption | apply gm_prefix_upto_mod_wk; eassumption ].
    rewrite ctx_fn_wk, tele_wk_app; cbn [body_ctx tele_wk centry_wk]; rewrite body_ctx_wk, length_body_ctx;
      f_equal; f_equal; cbn [exp_wk bnd_wk length].
    rewrite member_ref_wk; f_equal; f_equal; rewrite ?length_app, ?length_body_ctx;
      apply gunit_wk_wk_eq; rewrite wk_qn_add; reflexivity.
Qed.

Lemma member_expansion_sub : forall U ch M σ,
    member_expansion U ch = Some M ->
    member_expansion U[σ]ᵘ ch = Some M[σ].
Proof.
  intros * H; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & b & A & B & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_sub_mk; cbn [moddef_sub].
  - rewrite member_expansion_alias by assumption; rewrite ctx_fn_sub, member_ref_sub; reflexivity.
  - erewrite member_expansion_def by (apply gm_prefix_upto_def_sub; eassumption).
    rewrite ctx_fn_sub, tele_sub_app; destruct B; cbn [body_ctx tele_sub option_map centry_sub];
      rewrite body_ctx_sub, length_body_ctx; cbn; reflexivity.
  - erewrite member_expansion_mod by first [ assumption | apply gm_prefix_upto_mod_sub; eassumption ].
    rewrite ctx_fn_sub, tele_sub_app; cbn [body_ctx tele_sub centry_sub]; rewrite body_ctx_sub, length_body_ctx;
      f_equal; f_equal; cbn [exp_sub bnd_sub length].
    rewrite member_ref_sub; f_equal; f_equal; rewrite ?length_app, ?length_body_ctx;
      apply gunit_sub_sb_eq; rewrite sb_qn_add; reflexivity.
Qed.

Lemma member_ref_scoped : forall ch H n, modexp_scoped n H -> exp_scoped n (member_ref H ch).
Proof. induction ch as [| x [| y ch] IH]; intros; cbn; auto. apply IH; cbn; assumption. Qed.

Lemma member_expansion_scoped : forall U ch M n,
    member_expansion U ch = Some M -> gunit_scoped n U -> exp_scoped n M.
Proof.
  intros * H HU; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & b & A & B & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_scoped_mk in HU; destruct HU as [HΔ HD]; cbn in HD.
  - apply ctx_fn_scoped; [ assumption | apply member_ref_scoped; assumption ].
  - pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HD) as HΦ.
    apply ctx_fn_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    rewrite length_app; destruct B; cbn; lia.
  - pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HD) as HΦ.
    apply ctx_fn_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    apply member_ref_scoped; cbn; rewrite length_app; cbn; lia.
Qed.

(** What the δ-reduct of a path is: a filed definition, or the expansion of a
    member of a closed alias. *)
Lemma member_unfold_path_closed : forall Θ Ξ qp ch M,
    gctx_closed Θ Ξ -> member_unfold_ch Θ Ξ nil (me_path qp) ch = Some M -> exp_scoped 0 M.
Proof.
  intros * Hc H; cbn in H.
  destruct (gc_resolve Θ Ξ (path_app qp ch)) as [[b [|] A B | U] |];
    try (injection H as <-; exact I);
    destruct (gc_module Θ Ξ (path_app qp ch)) as [[T | U' r] |] eqn:Em; try discriminate;
    pose proof (gctx_closed_module _ _ _ _ Hc Em) as HU; cbn in HU;
    eapply member_expansion_scoped; eassumption.
Qed.

Lemma member_unfold_wk : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    forall H Δ ch M Γ φ,
      wk_mod_compat φ Γ Δ ->
      member_unfold_ch Θ Ξ Δ H ch = Some M ->
      member_unfold_ch Θ Ξ Γ (modexp_wk H φ) ch = Some M[φ]ʷ.
Proof.
  intros Θ Ξ Hc; induction H as [qp | x | H IH y | H IH N | U]; intros * Hφ HM.
  - rewrite exp_closed_wk; [ exact HM |].
    eapply member_unfold_path_closed; [ eassumption |]; cbn in HM |- *; exact HM.
  - cbn in HM |- *.
    destruct (ctx_find_mod Δ x) as [U |] eqn:EU; [| discriminate ].
    apply ctx_find_mod_spec, Hφ, ctx_find_mod_spec in EU; rewrite EU.
    apply member_expansion_wk; assumption.
  - cbn in *; eauto.
  - cbn in *; destruct (member_unfold_ch Θ Ξ Δ H ch) as [M0 |] eqn:E0; [| discriminate ].
    injection HM as <-; erewrite IH by eassumption; reflexivity.
  - cbn in *; apply member_expansion_wk; assumption.
Qed.

Lemma member_unfold_sub : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    forall H Δ ch M Γ σ,
      sub_mod_compat σ Γ Δ ->
      member_unfold_ch Θ Ξ Δ H ch = Some M ->
      member_unfold_ch Θ Ξ Γ H[σ]ᵐ ch = Some M[σ].
Proof.
  intros Θ Ξ Hc; induction H as [qp | x | H IH y | H IH N | U]; intros * Hσ HM.
  - rewrite exp_closed_sub; [ exact HM |].
    eapply member_unfold_path_closed; [ eassumption |]; cbn in HM |- *; exact HM.
  - cbn in HM |- *.
    destruct (ctx_find_mod Δ x) as [U |] eqn:EU; [| discriminate ].
    apply ctx_find_mod_spec in EU; destruct (Hσ _ _ EU) as [-> | (y & -> & Hy)]; cbn.
    + apply member_expansion_sub; assumption.
    + apply ctx_find_mod_spec in Hy; rewrite Hy; apply member_expansion_sub; assumption.
  - cbn in *; eauto.
  - cbn in *; destruct (member_unfold_ch Θ Ξ Δ H ch) as [M0 |] eqn:E0; [| discriminate ].
    injection HM as <-; erewrite IH by eassumption; reflexivity.
  - cbn in *; apply member_expansion_sub; assumption.
Qed.

(** ** Member Types as the Global Context Grows *)

(** A path through an alias names no definition, and a path naming a module
    names no definition. *)
Lemma gm_submodule_resolve : forall Φ T x ip r,
    gm_submodule T Φ x ip = Some r -> gm_resolve Φ (x :: ip) = None.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; try discriminate; [| eapply IH; exact H ].
  destruct (String.eqb x y); [| eapply IH; exact H ].
  destruct E as [b pv A B | [Δ [Φ' | E']]]; try discriminate.
  - destruct ip as [| z ip']; [ reflexivity |].
    eapply IH; exact H.
  - destruct ip; reflexivity.
Qed.

Lemma gc_module_resolve : forall Θ Ξ p r,
    gc_module Θ Ξ p = Some r -> gc_resolve Θ Ξ p = None.
Proof.
  intros * H; unfold gc_module, gc_resolve in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |]; cbn; [ discriminate | eapply gm_submodule_resolve; exact H |].
  destruct (gds_lookup Θ (p_unit p)); [| discriminate ].
  destruct (p_mems p) as [| x ip]; cbn in *; [ destruct (gu_mod g); reflexivity || apply gm_resolve_nil | eapply gm_submodule_resolve; exact H ].
Qed.

Lemma member_type_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    (forall Γ H ch k A, member_type Θ1 Ξ1 Γ H ch k A -> member_type Θ2 Ξ2 Γ H ch k A) /\
    (forall Γ U ch k A, unit_member_type Θ1 Ξ1 Γ U ch k A -> unit_member_type Θ2 Ξ2 Γ U ch k A).
Proof.
  intros * Hs; apply member_type_both_ind; intros; econstructor; eauto using gc_sub_resolve, gc_sub_module.
Qed.

Lemma member_unfold_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    forall H Γ ch M, member_unfold_ch Θ1 Ξ1 Γ H ch = Some M -> member_unfold_ch Θ2 Ξ2 Γ H ch = Some M.
Proof.
  intros * Hs; induction H as [qp | x | H IH y | H IH N | U]; intros * HM; cbn in *; auto.
  - destruct (gc_resolve Θ1 Ξ1 (path_app qp ch)) as [[b [|] A B | U] |] eqn:Er.
    + destruct (gc_module Θ1 Ξ1 (path_app qp ch)) as [[T | U r] |] eqn:Em; try discriminate.
      rewrite (gc_module_resolve _ _ _ _ Em) in Er; discriminate.
    + rewrite (gc_sub_resolve _ _ _ _ _ _ Hs Er); exact HM.
    + destruct (gc_module Θ1 Ξ1 (path_app qp ch)) as [[T | U' r] |] eqn:Em; try discriminate.
      rewrite (gc_module_resolve _ _ _ _ Em) in Er; discriminate.
    + destruct (gc_module Θ1 Ξ1 (path_app qp ch)) as [[T | U r] |] eqn:Em; try discriminate.
      pose proof (gc_sub_module _ _ _ _ _ _ Hs Em) as Em2.
      rewrite (gc_module_resolve _ _ _ _ Em2), Em2; exact HM.
  - destruct (member_unfold_ch Θ1 Ξ1 Γ H ch) eqn:E; [| discriminate ].
    rewrite (IH _ _ _ E); exact HM.
Qed.
